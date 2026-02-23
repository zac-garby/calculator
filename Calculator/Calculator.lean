import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

open Nat
open Option
open List
open Lean Meta Elab Term Macro Command

namespace Tactic
namespace Calculation

set_option linter.style.multiGoal false
set_option linter.style.longLine false
set_option linter.hashCommand false

def refold_def (fn within : Expr) : MetaM Expr := do
  Meta.transform within
    fun e => do
      let fn_args := (<- whnf fn).getAppArgs
      let rem := e.getAppNumArgs - fn_args.size
      let bs := e.getBoundedAppArgs rem
      let e_fn := e.getBoundedAppFn rem
      if <- isDefEq e_fn (<- whnf fn) then
        return .done (mkAppN fn bs)
      return .continue

-- finds 'name' in the local LCtx, so make sure you're in context
def unroll_def (name : Name) (target : Expr) : MetaM Expr := do
  let ctx <- getLCtx
  let (some decl) := ctx.findFromUserName? name | throwError m!"no assumption with name: {name}"
  let search_fn := decl.toExpr
  Meta.transform target fun e => do
    if e.getAppFn' != search_fn then return .continue
    let e' <- whnf e
    let back <- refold_def search_fn e'
    return .done back

elab (name := byDefTactic) "unroll" v:ident : tactic => Tactic.withMainContext do
  let target <- Tactic.getMainTarget
  let new <- unroll_def v.getId target
  let goal <- Tactic.getMainGoal
  let new_goal <- goal.replaceTargetDefEq new
  Tactic.replaceMainGoal [new_goal]

def define_clause (bind_name : Name) (args : TSyntaxArray `ident) (to_term : TSyntax `term) : Tactic.TacticM Unit := do
  let body_node: TSyntax `term <- `(fun $args* => $to_term)
  let mctx <- getMCtx
  match mctx.findUserName? bind_name with
  | none => throwUnknownNameWithSuggestions bind_name
  | some mv => do
    if (<- mv.getTag) == bind_name then do
      let mv_ty <- mv.getType'
      let to_expr <- elabTerm body_node (some mv_ty)
      if <- mv.isAssigned then
        if !(<- isDefEq (.mvar mv) to_expr) then
          throwError m!"cannot re-define {<- mv.getTag} as {to_expr}\n  (already assigned to {Expr.mvar mv})"
      else
        mv.assignIfDefEq to_expr

elab (name := defineTactic) "define" mod:("only")? v:ident args:ident* " := " to_term:term : tactic => do
  define_clause v.getId args to_term
  if !mod.isSome then
    Tactic.withMainContext do
      Tactic.evalTactic (<- `(tactic| try rfl))

elab "define'" p:term ":=" to_term:term : tactic => do
  match p with
  | `($f:ident $pat:term $rest*) => do
    let pat <- liftMacroM <| expandMacros pat
    let (con_stx, named, con_args_stx, ell) <- Term.expandApp pat
    if !named.isEmpty || ell then throwUnsupportedSyntax
    let con <- match con_stx with
      | `($fId:ident)  => pure fId
      | _ => throwErrorAt pat "expected a constructor application, but got {indentD pat}"
    let some (Expr.const (.str _ con_name) _) <- resolveId? con "pattern"
      | throwError "expected {con} to be a constructor"
    let clause_name := Name.str f.getId con_name
    let con_args <- con_args_stx.mapM fun
      | .stx s => if s.isIdent then pure s else throwErrorAt s "expected an identifier"
      | _ => unreachable!
    for rv in rest do if !rv.raw.isIdent then throwErrorAt rv "expected an identifier"
    let body_args := TSyntaxArray.mk (con_args ++ rest)
    let body_node: TSyntax `term <- `(fun $body_args* => $to_term)
    dbg_trace f!"con: {con_name}
    args: {con_args_stx}
    clause = {clause_name}
    f = {f.getId}
    rest: {rest}"
    let s <- saveState
    let main <- Tactic.getMainGoal
    main.withContext do
      let search_fn <- elabTerm f none
      let fn <- elabTerm body_node none
      let fn_ty <- inferType fn
      _ <- Meta.transform fn (fun e => do
        if <- isDefEq e.getAppFn search_fn then
          dbg_trace f!"search {<- ppExpr search_fn} in sub: {<- ppExpr e}"
        return .continue)
      let (ms, bs, r) <- forallMetaTelescopeReducing fn_ty (some 1)
      logInfo m!"got {ms} to {r}"
    s.restore
    return ()
  | _ => throwUnsupportedSyntax

#allow_unused_tactic! defineTactic

def of_inductive_ty (ty : Expr) : MetaM (Name × List (Name × Expr)) := do
  let ty <- whnf ty
  match ty.getAppFn with
  | .const name us => match (<- getEnv).find? name with
    | some (.inductInfo i) =>
      let ctors <- i.ctors.mapM fun ctor => do
        let cinfo <- getConstInfo ctor
        match ctor.componentsRev with
        | fn_name :: _ => return (fn_name, cinfo.type.instantiateLevelParams i.levelParams us)
        | [] => throwError f!"can't figure out name for constructor: {ctor}"
      return (name, ctors)
    | _ => throwError "not an inductive type"
  | _ => throwError "not a known constant type"

def match_struct_fields (goal_type : Expr) : TermElabM (Array Expr × Array (Name × Expr)) := do
  matchConstStructure goal_type.getAppFn
    (fun _ => do throwError "target {<- ppExpr goal_type} is not a structure")
    fun ival us ctor => do
      let sinfo := getStructureInfo (<- getEnv) ival.name
      let fields := sinfo.fieldNames
      let mut type <- instantiateTypeLevelParams ctor.toConstantVal us
      let mut params : Array Expr := #[]
      for _ in *...ctor.numParams do
        let .forallE _ d b _ := type | throwError "unexpected constructor type"
        let param <- mkFreshExprMVar d
        params := params.push param
        type := b.instantiate1 param
      let mut field_mvars := #[]
      for _ in fields do
        let .forallE arg_name d b bi := type | throwError "unexpected constructor type"
        if bi.isImplicit then throwError "unexpected implicit param {arg_name}"
        let mvar <- mkFreshExprMVar d
        field_mvars := field_mvars.push (arg_name, mvar)
        type := b.instantiate1 mvar
      if !(<- isDefEq type goal_type) then
        throwError "oops, somehow constructed the wrong structure type {<- ppExpr type}"
      return (params, field_mvars)

def intro_let_in_main_goal (name : Name) (ty val : Expr) (isDef : Bool := true)
  : Tactic.TacticM FVarId := do
  let mut main_mv <- Tactic.getMainGoal
  if isDef then
    main_mv <- main_mv.define name ty val
  else
    main_mv <- main_mv.assert name ty val
  let (fv, new_main) <- main_mv.intro1P
  Tactic.replaceMainGoal [new_main]
  return fv

def calc_intro_for (field_name : Name) (fields : Array (Name × Expr)) (as_name : Name := field_name)
    : Tactic.TacticM (FVarId × List (Name × Expr))
  := do
  let (field_ty, inp_ty, mot_ty) <- match fields.find? (fun (n, _) => n = field_name) with
    | none => throwUnknownNameWithSuggestions field_name (extraMsg := m!", could be any of {fields.map (·.fst)}")
    | some (_, field) => do
      let field_type <- inferType field >>= instantiateMVars
      match field_type.arrow? with
      | none => throwError m!"cannot calculate non-arrow-type {field_type} of '{field_name}'"
      | some t => pure (field_type, t)
  -- find the recursor
  let (inp_ty_name, ctors) <- of_inductive_ty inp_ty
  let recursor <- mkConstWithFreshMVarLevels (.str inp_ty_name "rec")
  let rec_ty <- inferType recursor
  -- make the motive (a const function)
  let motive_stx <- `(fun x => $(<- mot_ty.toSyntax))
  let motive <- elabTerm motive_stx none
  -- instantiate the recursor's implicit parameters to new mvars
  -- until we get to the motive. then assign this to our motive, defined above
  let mut (ms, bs, r) <- forallMetaTelescopeReducing rec_ty (some 1)
  while bs.back!.isImplicit do
    let mv := ms.back!.mvarId!
    let (ms', bs', r') <- forallMetaTelescopeReducing r (some 1)
    unless ms'.size == 1 do
      throwError f!"wrong type!"
    if (<- mv.getTag).eqStr "motive" then
      mv.assignIfDefEq motive
    if bs'.back!.isExplicit then break
    (ms, bs, r) := (ms ++ ms', bs ++ bs', r')
  -- get explicit_rec_ty, the recursor type with only explicit (algebra) arguments remaining.
  -- make new mvars for these algebras, and give them useful usernames
  let explicit_rec_ty <- instantiateExprMVars r
  let (algebra_mv_exps, _, concl_ty) <- forallMetaTelescopeReducing explicit_rec_ty (some ctors.length)
  let algebras := zip algebra_mv_exps.toList ctors
  for (exp, ctor, _) in algebras do
    let mv := exp.mvarId!
    let username := ctor.updatePrefix as_name
    mv.setUserName username
    -- we also intro each recursor algebra as a local hypothesis in the main goal
    _ <- intro_let_in_main_goal username (<- mv.getType) (.mvar mv)
    Tactic.appendGoals [mv]
  if !(<- isDefEq concl_ty field_ty) then
    throwError m!"that's weird, the recursor's conclusion is the wrong type\n{concl_ty}\n  vs\n{field_ty}"
  let final_ty <- instantiateExprMVars concl_ty
  -- add a 'let ... = ...' for this constructor to the main goal, and then intro it as a hypothesis
  let field_body := mkAppN recursor (ms ++ algebra_mv_exps)
  let fv <- intro_let_in_main_goal as_name final_ty field_body
  return (fv, algebras.map fun (mv, n, _) => (n, mv))

declare_syntax_cat calc_name
syntax ident : calc_name
syntax ident "as" ident : calc_name

elab (name := calculateTactic) "calculate " vs:calc_name,* : tactic => Tactic.withMainContext do
  -- look at main goal, get its fields
  let main_goal <- Tactic.getMainGoal
  let main_type <- main_goal.getType''
  let (_, spec_fields) <- match_struct_fields main_type
  if vs.getElems.size == 0 then
    logWarning f!"use `calculate` followed by any of {spec_fields.toList.map fun (n, _) => n}"
  -- for each ident 'v' listed:
  let fvs <- vs.getElems.mapM fun s => do
    dbg_trace f!"got s = {s}"
    match s with
    | `(calc_name| $v:ident) =>
      let field_name := v.getId
      let (fv, algebras) <- calc_intro_for field_name spec_fields
      return (field_name, field_name, fv, algebras)
    | `(calc_name| $v:ident as $r:ident) =>
      let field_name := v.getId
      let as_name := r.getId
      let (fv, algebras) <- calc_intro_for field_name spec_fields (as_name := as_name)
      return (field_name, as_name, fv, algebras)
    | _ => throwUnsupportedSyntax
  -- split the main goal into its constructor fields, and set each one to the corresponding
  -- recursor binding from above
  let main_mv <- Tactic.getMainGoal
  let field_mvs <- main_mv.constructor
  Tactic.pushGoals field_mvs
  for (field_name, as_name, fv, _) in fvs do
    for field_mv in field_mvs do
      if (<- field_mv.getTag) == field_name then
        field_mv.assign (.fvar fv)
        let t <- inferType (.mvar field_mv)
        let (forall_args, _, _) <- forallMetaTelescopeReducing t
        field_mv.withContext do
          let lhs := mkAppN (.mvar field_mv) forall_args
          let rhs <- reduce lhs
          let mut eq <- mkEq lhs rhs
          eq <- mkForallFVars forall_args eq
          let mut proof <- mkEqRefl lhs
          proof <- mkLambdaFVars forall_args proof
          _ <- intro_let_in_main_goal (.str as_name "eq_def") eq proof (isDef := false)

-- def rev {a} : List a → List a
--   | [] => []
--   | x :: xs => rev xs ++ [x]

-- def test {a} :
--   Σ' aux : List a -> List a -> List a,
--   ∀ xs ys, aux xs ys = rev xs ++ ys := by
--   calculate fst
--   intro xs
--   induction xs <;> intro ys
--   case nil =>
--     rewrite [rev, List.nil_append]
--     -- define fst.cons x xs ih ys := fst
--     define' fst (x::xs) ys := fst xs (x :: ys)
--     -- define' fst (x::xs) foo bar := ys
--     -- unroll fst
--     -- rfl
--   case cons x xs ih =>
--     rewrite [rev]
--     rewrite [List.append_assoc]
--     rewrite [List.cons_append, List.nil_append]
--     rewrite [<- ih]
--     unroll fst
--     generalize fst xs = h
--     rfl

def test2 {a} :
  Σ' len : List a -> Nat,
  len [] = 0 ∧ ∀ xs x, len (x :: xs) = len xs + 1 := by
  calculate fst as len
  constructor
  · define len.nil := 0
  · intro xs
    induction xs
    case cons y ys ih =>
      intro x
      rw [ih]
      unroll len
      rw [<- ih]
      generalize len (y :: ys) = l_xs
      define len.cons x xs l_xs := l_xs + 1
    case nil =>
      intro x
      dsimp [len]

end Calculation
end Tactic
