import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive
import ProofWidgets.Data.Html

namespace Tactic.Calculation

set_option linter.hashCommand false
set_option linter.style.setOption false
set_option pp.fieldNotation false

open Option List
open Lean Meta Elab Term Macro Command Mathlib.Tactic Qq

macro "don't" "care" : term => `(panic! "found out the hard way that we do actually care")

elab "todo" : tactic => return ()
elab "todo" "[" term "]" : tactic => return ()
def no_proof := "todo"

def match_struct_fields (goal_type : Expr)
  : MetaM (Array Expr × Array (Name × Expr)) := do
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

elab (name := refoldTactic) "refold" v:ident : tactic => Tactic.withMainContext do
  let target <- Tactic.getMainTarget
  let name := v.getId
  let ctx <- getLCtx
  let (some decl) := ctx.findFromUserName? name | throwError m!"no assumption with name: {name}"
  let search_fn := decl.toExpr
  let new <- refold_def search_fn target
  let goal <- Tactic.getMainGoal
  let new_goal <- goal.replaceTargetDefEq new
  Tactic.replaceMainGoal [new_goal]

def stx_from_names (names : List Name) : TSyntaxArray `ident
  := TSyntaxArray.mk <| .mk <| names.map fun n => mkIdent n

def get_rec_name (n : Name) : Name := .mkSimple s!"rec.{n}"

def desugar_clause_args (inp_ty : Expr) (con_args : List Name) (clause_args : List Expr)
  : MetaM (List Name)
  := do
  let rec_con_args <- rec_args (zip con_args clause_args)
  return con_args ++ rec_con_args
  where
    rec_args (cds : List (Name × Expr)) : MetaM (List Name) := match cds with
    | [] => pure []
    | (n, t) :: cds => do
      let ct <- inferType t
      if <- isDefEq ct inp_ty then
        return get_rec_name n :: (<- rec_args cds)
      else
        rec_args cds

def desugar_clause_def
  (clause_of : Name)
  (clause inp_ty : Expr)
  (con_args rest_args : List Name) -- the args for the recursor, but without the IH's
  (to_term : TSyntax `term)
  : Tactic.TacticM Expr := do
  let search_fn <- elabTerm (mkIdent clause_of) none
  let clause_ty <- inferType clause
  let (clause_args, _, _) <- forallMetaTelescopeReducing clause_ty
  let ns <- desugar_clause_args inp_ty con_args clause_args.toList
  let body_args := ns ++ rest_args
  let body_node : TSyntax `term <- `(fun $(stx_from_names body_args)* => $to_term)
  let body_fn <- elabTerm body_node (some clause_ty)
  Meta.transform body_fn <| fun e => do
    -- if we find an 'e' which is an application of the function being defined...
    if <- isDefEq e.getAppFn search_fn then
      let ((.fvar fv)::args) := e.getAppArgs.toList
        | throwError "can't make recursive call: {<- ppExpr e}"
      let arg_name <- fv.getUserName
      let rec_name := get_rec_name arg_name
      let lctx <- getLCtx
      for fv in lctx.getFVars do
        if (<- fv.fvarId!.getUserName) = rec_name then
          let e := mkAppN fv args.toArray
          return .visit e
      throwError "didn't find {rec_name} as a fv (bug!)"
    return .continue

def define_mv (bind_name : Name) (to_expr : Expr) : Tactic.TacticM Unit := do
  let mctx <- getMCtx
  match mctx.findUserName? bind_name with
  | none => throwUnknownNameWithSuggestions bind_name
  | some mv => do
    if (<- mv.getTag) == bind_name then do
      if <- mv.isAssigned then
        if !(<- isDefEq (.mvar mv) to_expr) then
          throwError m!"cannot re-define {<- mv.getTag} as {to_expr}\n\
          (already assigned to {<- ppExpr (.mvar mv)})"
      else
        mv.assignIfDefEq to_expr

def count_implicit_args (ty : Expr) : Nat := match ty with
  | .forallE _ _ b .implicit => 1 + count_implicit_args b
  | .lam _ _ b .implicit => 1 + count_implicit_args b
  | _ => 0

partial def get_id (stx : Syntax) : Option Name := match stx.getKind with
  | `ident => pure stx.getId
  | ``Lean.Parser.Term.dotIdent => get_id stx[1]
  | ``Lean.Parser.Term.explicit => get_id stx[1]
  | ``Lean.Parser.Term.hole => some (.str .anonymous "_")
  | _ => none

def collect_ctor_pattern (stx : Syntax) : TermElabM (Syntax × Array Name) := do
  if let some _ := get_id stx then
    return (stx, #[])
  else if stx.getKind == ``Lean.Parser.Term.app then
    let (fn, #[], args, false) <- expandApp stx
      | throwErrorAt stx "invalid constructor application here"
    let arg_names <- args.mapM fun
      | .stx s => match get_id s with
        | some name => pure name
        | none => throwErrorAt s "unexpected non-ident constructor argument: {s.getKind}"
      | _ => unreachable!
    return (fn, arg_names)
  else
    throwErrorAt stx "unexpected syntax in pattern: {stx.getKind.toString}"

elab (name := defineTacticSugared) "define" mod:("only")? p:term " := " to_term:term : tactic
  => do
  let main_goal <- Tactic.withMainContext Tactic.getMainGoal
  let mctx <- Tactic.withMainContext getMCtx
  match p with
  | `($f:ident) => do
    let (some mv) := mctx.findUserName? f.getId
      | throwErrorAt f "the name {f.getId} is undefined"
    let mv_ty <- mv.getType''
    let to_expr <- elabTerm to_term (some mv_ty)
    define_mv f.getId to_expr
  | `($f:ident $pat:term $rest*) => do
    let (some search_fn_mv) := mctx.findUserName? f.getId
      | throwErrorAt f "the name {f.getId} is undefined"
    let search_ty <- search_fn_mv.getType''
    let some (inp_ty, _) := search_ty.arrow?
      | throwErrorAt f "unexpected argument in definition of non-function {f}"
    -- expand out the constructor argument's pattern to figure out the name
    -- of the constructor and its (explicit) arguments
    let pat <- liftMacroM <| expandMacros pat
    let (con_stx, con_arg_names) <- collect_ctor_pattern pat
    let con <- elabTerm con_stx (some inp_ty)
    let con_ty <- inferType con
    let num_implicit := count_implicit_args con_ty
    let con_arg_names := con_arg_names.drop num_implicit
    let (con_fn, _) := con.getAppFnArgs
    let clause_name <- match con_fn with
    | .str _ con_name => pure (Name.str f.getId con_name)
    | _ => throwErrorAt pat "expected a constructor, but got {con_fn}"
    let mctx <- getMCtx
    let some clause_expr := mctx.findUserName? clause_name |> (·.map (Expr.mvar ·))
      | throwErrorAt f "unknown defining clause for {f}, for pattern: {pat})"
    let rest_names <- rest.toList.mapM fun s => match s.raw with
      | `($i:ident) => pure i.getId
      | s => throwErrorAt s "expected an ident (matching on 'define' arguments is not allowed yet)"
    -- construct a new function, 'fn', to define as the body
    let fn <- Tactic.withMainContext <| desugar_clause_def
      f.getId clause_expr inp_ty
      con_arg_names.toList rest_names to_term
    define_mv clause_name fn
    if !mod.isSome then
      main_goal.withContext do
        Tactic.evalTactic (<- `(tactic| try rfl))
  | _ => throwUnsupportedSyntax

#allow_unused_tactic! defineTacticSugared

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

def calc_intro_other (as_name : Name) (field_ty : Expr)
  : Tactic.TacticM Expr := do
  let field_body <- mkFreshExprMVar (some field_ty)
  field_body.mvarId!.setUserName as_name
  let _ <- intro_let_in_main_goal as_name field_ty (.mvar (field_body.mvarId!))
  Tactic.appendGoals [field_body.mvarId!]
  return field_body

def calc_intro_for (field_name : Name) (fields : Array (Name × Expr)) (as_name : Name := field_name)
    : Tactic.TacticM Expr
  := do
  let some (_, field) := fields.find? fun (n, _) => n = field_name
    | throwUnknownNameWithSuggestions field_name (extraMsg :=
      m!", could be any of {fields.map (·.fst)}")
  let field_ty <- inferType field >>= instantiateMVars
  calc_intro_other as_name field_ty

elab "refine " vs:ident,* " => " tac:tactic : tactic => Tactic.withMainContext do
  let ids <- vs.getElems.mapM fun v => do
    let id := v.getId
    if (<- getMCtx).findUserName? id |>.isNone then
      throwErrorAt v "unknown goal called '{id}'"
    pure id
  let goals <- Tactic.getGoals
  let goals' <- goals.flatMapM fun goal => do
    let decl <- goal.getDecl
    if ids.elem decl.userName then
      Tactic.evalTacticAt tac goal
    else
      pure [goal]
  Tactic.setGoals goals'
  for v in vs.getElems do
    Tactic.evalTactic (<- `(tactic| try refold $v))

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
  let vals <- vs.getElems.mapM fun s => do
    match s with
    | `(calc_name| $v:ident) =>
      let field_name := v.getId
      let val <- calc_intro_for field_name spec_fields
      return (field_name, field_name, val)
    | `(calc_name| $v:ident as $r:ident) =>
      let field_name := v.getId
      let as_name := r.getId
      let val <- calc_intro_for field_name spec_fields (as_name := as_name)
      return (field_name, as_name, val)
    | _ => throwUnsupportedSyntax
  -- split the main goal into its constructor fields, and set each one to the corresponding
  -- recursor binding from above
  let main_mv <- Tactic.getMainGoal
  let field_mvs <- main_mv.constructor
  Tactic.pushGoals field_mvs
  for (field_name, as_name, val) in vals do
    for field_mv in field_mvs do
      if (<- field_mv.getTag) == field_name then
        field_mv.assign val
        field_mv.setUserName as_name

macro "exists_mono" : tactic =>
  `(tactic| (repeat' apply Exists.imp; intro))

private partial def splitHyp (fv : FVarId) : Tactic.TacticM Unit :=
  Tactic.withMainContext do
    let goal <- Tactic.getMainGoal
    let checkpoint <- Meta.saveState
    try
      let subgoals <- goal.cases fv
      if let #[sg] := subgoals then
        Tactic.replaceMainGoal [sg.mvarId]
        for fieldExpr in sg.fields do
          if let some fieldFV := fieldExpr.fvarId? then
            splitHyp fieldFV
      else
        checkpoint.restore
    catch | _ => checkpoint.restore

elab "unpkg" "[" fv:ident "]" : tactic => Tactic.withMainContext do
  let fvar <- getFVarFromUserName fv.getId
  splitHyp fvar.fvarId!

elab "unpkg" : tactic => Tactic.withMainContext do
  let un <- mkFreshUserName (.mkSimple "it")
  let mv <- Tactic.getMainGoal
  let (fv, mv') <- mv.intro un
  Tactic.replaceMainGoal [mv']
  splitHyp fv

local infixl: 50 " <;> " => Tactic.andThenOnSubgoals

open Tactic

def restructureCore (tacs : TSyntaxArray `tactic) : TacticM Unit := do
  _ <- tryTactic (evalTactic (<- `(tactic| contradiction)))
  _ <- tryTactic (evalTactic (<- `(tactic| assumption)))
  iterateUntilFailure do
    let gs <- getUnsolvedGoals
    allGoals <|
      liftMetaTactic (fun m => do pure [(<- m.intros!).2]) <;>
      Tauto.distribNot <;>
      liftMetaTactic (MVarId.casesMatching casesMatch
        (recursive := true) (throwOnNoMatch := false)) <;>
      (do _ <- tryTactic (evalTactic (<- `(tactic| contradiction)))) <;>
      liftMetaTactic (fun m => do pure [(<- m.intros!).2]) <;>
      liftMetaTactic (constructorMatching · ctorMatch
        (recursive := true) (throwOnNoMatch := false)) <;>
      do _ <- tryTactic (evalTactic (<- `(tactic| assumption)))
    allGoals <| for tac in tacs do
      _ <- tryTactic (evalTactic tac)
    let gs' <- getUnsolvedGoals
    if gs == gs' then failure
    pure ()
  where
    casesMatch (e : Q(Prop)) : MetaM Bool := match e with
    | ~q(_ ∧ _) => pure true
    | ~q(_ ∨ _) => pure true
    | ~q(Exists _) => pure true
    | ~q(False) => pure true
    | _ => pure false
    ctorMatch (e : Q(Prop)) : MetaM Bool := match e with
    | ~q(_ ∧ _) => pure true
    | ~q(_ ↔ _) => pure true
    | ~q(True) => pure true
    | _ => pure false

def restructure (tacs : TSyntaxArray `tactic) : TacticM Unit := focus do
  _ <- tryTactic (evalTactic (<- `(tactic| unpkg)))
  restructureCore tacs
  allGoals <| iterateUntilFailure do
    let gs <- getUnsolvedGoals
    for tac in tacs do
      _ <- tryTactic (evalTactic tac)
    _ <- tryTactic
      <|  evalTactic (<- `(tactic| rfl))
      <|> evalTactic (<- `(tactic| solve_by_elim))
      <|> liftMetaTactic (constructorMatching · ctorMatch)
    let gs' <- getUnsolvedGoals
    if gs == gs' then failure
    pure ()
  where
    ctorMatch (e : Q(Prop)) : MetaM Bool := match e with
    | ~q(_ ∧ _) => pure true
    | ~q(_ ↔ _) => pure true
    | ~q(Exists _) => pure true
    | ~q(True) => pure true
    | _ => pure false

elab "restructuring" "[" tacs:tactic* "]" : tactic => restructure tacs
elab "restructuring" : tactic => restructure #[]

end Tactic.Calculation
