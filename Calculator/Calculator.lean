import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive
import Calculator.Suggestion
import ProofWidgets.Data.Html

open Nat
open Option
open List
open Lean Meta Elab Term Macro Command

namespace Tactic
namespace Calculation

/- Things I want:

* 'define' tactic support for constructors with dotted constructors e.g.
    define comp (x.add y) := ...

* 'define' tactic support for pattern matching in non-constructor arguments e.g.
    define exec (.add c') (m :: n :: s) := exec c' ((n + m) :: s)

* let the define suggester discover definitions which are more general, and
  require us to abstract from terms, e.g
    exec c ((eval x + eval y) :: s) = exec c.add (eval y :: eval x :: s)
      can be solved by
    exec c ((m + n) :: s) = exec c.add (n :: m :: s)

* calculating data-types!
    probably have to be 'pseudo'-types, as data themselves

* better errorrs for e.g. (ys is not defined as an argument)
    define aux (x :: xs) s := aux xs (x :: ys)
-/

set_option linter.style.multiGoal false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedVariables false

macro "don't" "care" : term => `(panic! "found that we do actually care")

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

def get_recursor (ty : Expr) : MetaM (Name × Expr × Expr) := do
  let (ty_name, _) <- of_inductive_ty ty
  let rec_name := Name.str ty_name "rec"
  let rec_exp <- mkConstWithFreshMVarLevels rec_name
  let rec_ty <- inferType rec_exp
  return (rec_name, rec_exp, rec_ty)

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
          throwError m!"cannot re-define {<- mv.getTag} as {to_expr}\n    (already assigned to {Expr.mvar mv})"
      else
        mv.assignIfDefEq to_expr

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

elab (name := defineTactic) "define!" mod:("only")? v:ident args:ident* " := " to_term:term : tactic
  => do
  define_clause v.getId args to_term
  if !mod.isSome then
    Tactic.withMainContext do
      Tactic.evalTactic (<- `(tactic| try rfl))

def count_implicit_args (ty : Expr) : Nat := match ty with
  | .forallE _ _ b .implicit => 1 + count_implicit_args b
  | .lam _ _ b .implicit => 1 + count_implicit_args b
  | _ => 0

def collect_pattern_ids (stx : Syntax) : Array Name :=
  match stx with
  | .ident _ _ name _ => #[name]
  | .node _ _ args =>
    args.foldl (init := #[]) fun acc s =>
      acc ++ collect_pattern_ids s
  | _ => #[]

partial def get_id (stx : Syntax) : Option Name := match stx.getKind with
  | `ident => pure stx.getId
  | ``Lean.Parser.Term.dotIdent => get_id stx[1]
  | ``Lean.Parser.Term.explicit => get_id stx[1]
  | ``Lean.Parser.Term.hole => some (.str .anonymous "_")
  | _ => none

def collect_ctor_pattern (stx : Syntax) : TermElabM (Syntax × Array Name) := do
  let (stx', s) ← (CollectPatternVars.collect stx).run {}
  if let some fn := get_id stx' then
    return (stx', #[])
  else if stx'.getKind == ``Lean.Parser.Term.app then
    let (fn, #[], args, false) <- expandApp stx'
      | throwErrorAt stx "invalid constructor application here"
    let arg_names <- args.mapM fun
      | .stx s => match get_id s with
        | some name => pure name
        | none => throwErrorAt s "unexpected non-ident constructor argument: {s.getKind}"
      | _ => unreachable!
    return (fn, arg_names)
  else
    throwErrorAt stx "unexpected syntax in pattern: {stx'.getKind.toString}"

elab (name := defineTacticSugared) "define" mod:("only")? p:term " := " to_term:term : tactic
  => match p with
  | `($f:ident $pat:term $rest*) => do
    let main_goal <- Tactic.withMainContext Tactic.getMainGoal
    let mctx <- Tactic.withMainContext getMCtx
    let (some search_fn_mv) := mctx.findUserName? f.getId
      | throwErrorAt f "the name {f} is undefined in {mctx.decls.toList.map fun (_, b) => b.userName}"
    let search_ty <- search_fn_mv.getType''
    let some (inp_ty, _) := search_ty.arrow?
      | throwErrorAt f "cannot define a clause in non-function {f}"
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

#allow_unused_tactic! defineTactic
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
  let (_, ctors) <- of_inductive_ty inp_ty
  let (_, recursor, rec_ty) <- get_recursor inp_ty
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
        field_mv.setUserName as_name

open Server
open ProofWidgets
open Jsx
open SelectInsertParamsClass Lean.SubExpr

def sep (s : String := "8px") : Html := <span style={json% { marginRight: $s }} />

def pretty_mvars (s : String) : String :=
  match s.splitOn "?m." with
  | [] => ""
  | [s] => s
  | s::ss => s ++ "[⋯]" ++ "[⋯]".toSlice.intercalate (ss.map fun s ↦ s.dropWhile Char.isDigit)

structure CalcParams extends SelectInsertParams where
  isFirst : Bool
  indent : Nat
  deriving SelectInsertParamsClass, RpcEncodable

def expr_component (e : Expr) : MetaM Html := do
  if e.hasExprMVar then
    let str := pretty_mvars (toString <| <- ppExpr e)
    return <span className="font-code">{.text str}</span>
  else
    let e' <- WithRpcRef.mk (<- ExprWithCtx.save e)
    return .ofComponent InteractiveExpr { expr := e' } #[]

@[suggest]
def suggest_already_eq : CalcSuggester := fun _goal _params lhs rhs => do
  if <- withNewMCtxDepth (isDefEq lhs rhs) then
    return #[{
      hint := "Already equal"
    }]
  else
    return #[]

@[suggest]
def suggest_apply_hyp : CalcSuggester := fun goal _params lhs _ => do
  let mv := goal.mvarId
  let lctx := (<- mv.getDecl).lctx |>.sanitizeNames.run' {options := (<- getOptions)}
  let mut suggestions : Array Suggestion := #[]
  for i in lctx.decls do
    let some d := i | continue
    try
      let r <- mv.rewrite lhs d.toExpr
      suggestions := suggestions.push {
        hint := "Apply hypothesis"
        info? := some
          <span>
            <strong className="goal-hyp">
              {.text (toString f!"{d.userName}")}
            </strong>
            <span className="font-code"> : </span>
            {<- expr_component d.type}
          </span>
        new_lhs? := r.eNew
        proof? := some s!"rw [{d.userName}]"
      }
    catch | _ => pure ()
  return suggestions

def simp_suggester
  (hint : String) (tac : String) (kind : Tactic.SimpKind) (allow_defeq := false)
  : CalcSuggester := fun _goal _params lhs _rhs => do
  let simp_ctx <- mkSimpContext (hasStar := true) (kind := kind)
  let (res, stats) <- Meta.simp lhs simp_ctx
  let lhs' := res.expr
  if lhs == lhs' then
    return #[]
  else if <- isDefEq lhs lhs' then
    if !allow_defeq then return #[]
    return #[{
      hint := s!"Simply (rfl)"
      new_lhs? := lhs'
      proof? := some "rfl"
      info? := some (.text "reflexivity")
    }]
  else
    let md_ctx := MessageDataContext.mk (<- getEnv) (<- getMCtx) (<- getLCtx) {}
    let thms <- stats.usedTheorems.toArray.mapM fun o => do
      let md <- ppOrigin o
      md.format md_ctx
    let fmt := Format.joinSep thms.toList ", "
    return #[{
      hint := hint
      new_lhs? := lhs'
      info? := some <span className="font-code">{.text fmt.pretty}</span>
      proof? := some s!"{tac} only [{fmt}]"
    }]

@[suggest]
def suggest_dsimp : CalcSuggester
  := simp_suggester "Simplify (dsimp)" "dsimp" .dsimp (allow_defeq := true)

@[suggest]
def suggest_simp : CalcSuggester
  := simp_suggester "Simplify (simp)" "simp" .simp

@[suggest]
def suggest_define : CalcSuggester := fun goal _params lhs rhs => do
  let mv := goal.mvarId
  let lhs_stx <- PrettyPrinter.delab lhs
  let rhs_stx <- PrettyPrinter.delab rhs
  let tac <- `(tactic| define $rhs_stx := $lhs_stx)
  let save <- Meta.saveState
  let ctx <- getLCtx
  let proof <- ContextInfo.ppSyntax goal.ctx.val ctx tac
  let (mvs, _) <- runTactic mv (<- `(tactic| try { $tac }))
  save.restore
  match mvs with
    | [] => return #[{
        hint := "Define"
        proof? := some (toString proof)
        info? := <span className="font-code">
          {<- expr_component rhs}
          {sep}{.text ":="}{sep}
          {<- expr_component lhs}
        </span>
      }]
    | _ => return #[]

@[suggest]
def suggest_cong : CalcSuggester := fun goal params lhs rhs => do
  let (lfn, largs) := lhs.getAppFnArgs
  let (rfn, rargs) := rhs.getAppFnArgs
  if lfn = rfn && largs.size = rargs.size then
    try_cong goal params lfn (Array.zip largs rargs).toList
  else
    return #[]
  where
    pairwise_eq := fun (l, r) => withNewMCtxDepth (isDefEq l r)
    try_cong (goal params) (_fn : Name) (args : List (Expr × Expr)) : MetaM (Array Suggestion) := do
      let (_, (l, r) :: post) <- args.partitionM pairwise_eq
        | do return #[] -- in this case, all args already equal...
      if !(<- post.allM pairwise_eq) then return #[]
      all_suggestions goal params l r

@[suggest]
def suggest_replace_subexpr : CalcSuggester := fun goal params _lhs _rhs => do
  let subs := getGoalLocations params.selectedLocations
  let sel_left := subs.any fun L => #[0, 1].isPrefixOf L.toArray
  let sel_right := subs.any fun L => #[1].isPrefixOf L.toArray
  let mut goal_ty <- goal.mvarId.getType''
  for pos in subs do
    goal_ty <- insertMetaVar goal_ty pos
  let some (_, lhs', rhs') <- getCalcRelation? goal_ty
    | throwError "invalid 'calc' step when replacing subexpressions, relation expected{indentD goal_ty}"
  if !sel_left && !sel_right then
    return #[]
  return #[{
    hint := "Rewrite"
    new_lhs? := if sel_left then some lhs' else none
    new_rhs? := if sel_right then some rhs' else none
    info? := some (.text "some new goal")
  }]

def unpack_calc_goal (goal_ty : Expr)
  : MetaM (String × Expr × String × Expr × String) := do
  let some (rel, lhs, rhs) <- Term.getCalcRelation? goal_ty
    | throwError "invalid 'calc' step, relation expected{indentD goal_ty}"
  let app := mkApp2 rel (<- mkFreshExprMVar none) (<- mkFreshExprMVar none)
  let app_s <- ppExpr app <&> toString
  let some rel_s := (app_s |>.splitOn)[1]?
    | throwError "couldn't find relation symbol in {app}"
  let lhs_s := (toString <| <- ppExpr lhs).renameMetaVar
  let rhs_s := (toString <| <- ppExpr rhs).renameMetaVar
  pure (rel_s, lhs, lhs_s, rhs, rhs_s)

def wrap_new_step_str (str indent : String) : String :=
  if str.isEmpty then
    str
  else
    let lines := str.lines
    let ind_len := indent.length
    let lines' := lines.toList.flatMap fun line =>
      if ind_len + line.positions.length > 80 then
        match line |>.split ":=" |>.toList with
          | (step::rest) => [step, indent ++ "  :=" ++ String.intercalate ":=" (rest.map (·.toString))]
          | _ => [line]
      else
        [line]
    String.intercalate "\n" (lines'.map (·.toString))

@[server_rpc_method]
def rpc : (params : CalcParams) -> RequestM (RequestTask Html) :=
  fun params => RequestM.withWaitFindSnapAtPos params.pos fun _snap => do
    let doc <- RequestM.readDoc
    let body <- match params.goals.toList with
    | [] => pure (<p>{.text "Nothing left to prove here"}</p>)
    | main_goal :: _ => main_goal.ctx.val.runMetaM {} <| main_goal.mvarId.withContext do
      let mv := main_goal.mvarId
      let mty <- mv.getType''
      let (rel, lhs, lhs_s, rhs, rhs_s) <- try
        unpack_calc_goal mty
      catch | _ => return <p>{.text "Place your cursor in a step's proof slot to use this"}</p>
      let spc := String.replicate params.indent ' '
      let mut suggestions <- all_suggestions main_goal { params with } lhs rhs
      if suggestions.isEmpty then
        return <p>{.text "No suggestions"}</p>
      let ul_style := json%{
        listStyleType: "\"⚡ \"",
        paddingLeft: "20px"
      }
      let ul <- Html.element "ul" #[("style", ul_style)] <$> suggestions.mapM fun sugg => do
        let proof_s := sugg.proof?.getD "{}"
        let info := sugg.info? |>.map (fun i => <span>{.text "by "}{i}</span>)  |>.getD (.text "")
        let (new_text, content) <- match sugg.new_lhs?, sugg.new_rhs? with
          | some lhs', some rhs' => do
            let lhs'_s := (toString <| <- ppExpr lhs').renameMetaVar
            let rhs'_s := (toString <| <- ppExpr rhs').renameMetaVar
            let new_line := if params.isFirst
              then s!"{lhs_s}\n{spc}  \
                        {rel} {lhs'_s} := by \{}\n{spc}\
                      _ {rel} {rhs'_s} := by \{}\n{spc}\
                      _ {rel} {rhs_s} := by \{}"
              else s!"_ {rel} {lhs'_s} := by \{}\n{spc}\
                      _ {rel} {rhs'_s} := by \{}\n{spc}\
                      _ {rel} {rhs_s} := by \{}"
            pure (new_line,
              #[<br />,
                <span className="font-code">
                  {<- expr_component lhs}
                  {sep}{.text rel}{sep}
                  {<- expr_component rhs}
                </span>,
                <br />,
                <span>{sep}{.text "===>"}{sep}{info}</span>,
                <br />,
                <span className="font-code">
                  {<- expr_component lhs'}
                  {sep}{.text rel}{sep}
                  {<- expr_component rhs'}
                </span>
              ])
          | some lhs', none => do
            let lhs'_s := (toString <| <- ppExpr lhs').renameMetaVar
            let new_line := if params.isFirst
              then s!"{lhs_s}\n{spc}  \
                      {rel} {lhs'_s} := by {proof_s}\n{spc}_ {rel} {rhs_s} := by \{}"
              else s!"_ {rel} {lhs'_s} := by {proof_s}\n{spc}_ {rel} {rhs_s} := by \{}"
            pure (new_line,
              #[<br />,
                <span className="font-code">
                  {<- expr_component lhs}
                  {sep}{.text rel}{sep}
                  {.text "···"}
                </span>,
                <br />,
                <span>{sep}{.text "===>"}{sep}{info}</span>,
                <br />,
                <span className="font-code">
                  {<- expr_component lhs'}
                  {sep}{.text rel}{sep}
                  {.text "···"}
                </span>
              ])
          | none, some rhs' => do
            let rhs'_s := (toString <| <- ppExpr rhs').renameMetaVar
            let new_line := if params.isFirst
              then s!"{lhs_s}\n{spc}  \
                        {rel} {rhs'_s} := by {proof_s}\n{spc}_ {rel} {rhs_s} := by \{}"
              else s!"_ {rel} {rhs'_s} := by {proof_s}\n{spc}_ {rel} {rhs_s} := by \{}"
            pure (new_line,
              #[<br />,
                <span className="font-code">
                  {.text "···"}
                  {sep}{.text rel}{sep}
                  {<- expr_component rhs}
                </span>,
                <br />,
                <span>{sep}{.text "===>"}{sep}{info}</span>,
                <br />,
                <span className="font-code">
                  {.text "···"}
                  {sep}{.text rel}{sep}
                  {<- expr_component rhs'}
                </span>
              ])
          | none, none => do
            if sugg.proof?.isSome then
              let new_line := if params.isFirst
                then s!"{lhs_s}\n{spc}  \
                          {rel} {rhs_s} := by {proof_s}"
                else s!"_ {rel} {rhs_s} := by {proof_s}"
              pure (new_line, #[.text "(closes this goal)", <br />, info])
            else
              let new_line := if params.isFirst
                then s!"{lhs_s}\n{spc}  \
                          {rel} {rhs_s} := by {proof_s}"
                else s!""
              pure (new_line, #[
                .text "(removes this step)",
                <br />,
                <span className="font-code">
                  {<- expr_component lhs}
                  {sep}{.text rel}{sep}
                  {<- expr_component rhs}
                </span>,
                <br />,
                info
              ])
        let replaceRange := if new_text.isEmpty then
          .mk (.mk params.replaceRange.start.line 0)
              (.mk params.replaceRange.end.line.succ 0)
        else
          params.replaceRange
        let new_text := wrap_new_step_str new_text spc
        let new_selection := match new_text.find? "?_" with
          | none => (new_text.rawEndPos.dec, new_text.rawEndPos.dec)
          | some p => (p.offset, p.offset.inc.inc)
        pure <li style={json% { marginBottom: "10px" }}>
          {.ofComponent MakeEditLink
            (.ofReplaceRange doc.meta replaceRange new_text (some new_selection))
            #[<span style={json% { marginRight: "5px", fontWeight: "bold" }}>
                {.text s!"[{sugg.hint}] "}
              </span>]}
          {... content}
        </li>
      pure <p>{.text s!"Suggested next steps:"}{ul}</p>
    return <details «open»={decide (params.goals.size > 0)}>
        <summary className="mv2 pointer">{.text "Calculator 🧮"}</summary>
        {body}
      </details>

@[widget_module]
def panel : Component CalcParams :=
  mk_rpc_widget% rpc

elab_rules : tactic
| `(tactic|calc%$calcstx $steps) => do
  let mut isFirst := true
  for step in ← Lean.Elab.Term.mkCalcStepViews steps do
    let some replaceRange := (<- getFileMap).lspRangeOfStx? step.ref | continue
    let json := json% {
      "isFirst": $(isFirst),
      "replaceRange": $(replaceRange),
      "indent": $(replaceRange.start.character)
    }
    Widget.savePanelWidgetInfo panel.javascriptHash (pure json) step.proof
    isFirst := false
  Tactic.evalCalc (← `(tactic|calc%$calcstx $steps))

@[simp]
def rev {a} : List a → List a
  | [] => []
  | x :: xs => rev xs ++ [x]

structure RevSpec a : Type where
  aux : List a -> List a -> List a
  correct : ∀ xs ys, rev xs ++ ys = aux xs ys

def correct {a} : RevSpec a := by
  calculate aux
  intro xs
  induction xs <;> intro ys
  case nil =>
    define aux [] ys := ys
  case cons x xs ih =>
    calc rev (x :: xs) ++ ys
     _ = rev xs ++ [x] ++ ys := by rfl
     _ = rev xs ++ x :: ys
      := by simp only [append_assoc, cons_append, nil_append]
     _ = aux xs (x :: ys) := by rw [ih]
     _ = aux (x :: xs) ys := by define aux (x :: xs) ys := aux xs (x :: ys)

end Calculation
end Tactic
