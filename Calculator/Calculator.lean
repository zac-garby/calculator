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

set_option linter.style.multiGoal false
set_option linter.style.longLine false
set_option linter.hashCommand false
-- set_option linter.unusedVariables false

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

elab (name := defineTacticSugared) "define" mod:("only")? p:term " := " to_term:term : tactic
  => match p with
  | `($f:ident $pat:term $rest*) => do
    let mctx <- Tactic.withMainContext getMCtx
    let (some search_fn_mv) := mctx.findUserName? f.getId
      | throwErrorAt f "the name {f} is undefined in {mctx.decls.toList.map fun (_, b) => b.userName}"
    let search_ty <- search_fn_mv.getType''
    let some (inp_ty, _) := search_ty.arrow?
      | throwErrorAt f "cannot define a clause in non-function {f}"
    let pat <- liftMacroM <| expandMacros pat
    let (con_stx, named, con_args_stx, ell) <- Term.expandApp pat
    let con_stx <- if con_stx.isMissing
      then pure pat
      else if !named.isEmpty || ell then throwUnsupportedSyntax
      else pure con_stx
    let con_exp <- elabPattern (.mk con_stx) (some inp_ty)
    let con_name <- match con_exp.getAppFn with
    | .const (.str _ con_name) _ => pure con_name
    | e => throwError "expected a constructor, but got {indentD pat} (application with {<- ppExpr e})"
    let clause_name := Name.str f.getId con_name
    let mctx <- getMCtx
    let some clause_expr := mctx.findUserName? clause_name |> (·.map (Expr.mvar ·))
      | throwErrorAt f "unknown defining clause for {f}, for pattern: {pat})"
    let con_args <- con_args_stx.mapM fun
      | .stx s => if s.isIdent then pure s else throwErrorAt s "expected an identifier"
      | _ => unreachable!
    for rv in rest do if !rv.raw.isIdent then throwErrorAt rv "expected an identifier"
    -- construct a new function, 'fn',
    let con_arg_names := con_args.toList.map (·.getId)
    let rest_names <- rest.toList.mapM fun s => match s.raw with
      | `($i:ident) => pure i.getId
      | s => throwErrorAt s "expected an identifier"
    let fn <- Tactic.withMainContext <| desugar_clause_def
      f.getId clause_expr inp_ty
      con_arg_names rest_names to_term
    define_mv clause_name fn
    if !mod.isSome then
      Tactic.withMainContext do
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

/- Things I want:
 * A nicer define syntax like:  define aux (x :: xs) ys := aux xs (x :: ys)
 * A tactic to introduce the "obvious" definition
   so if my goal is
    aux xs (x :: ys) = aux (x :: xs) ys
   it can figure out that this works as a definition (generalizing x :: xs)
 * A widget to show possible things to do in a calculation proof
-/

open Server
open ProofWidgets
open Jsx
open SelectInsertParamsClass Lean.SubExpr

structure CalcParams extends SelectInsertParams where
  isFirst : Bool
  indent : Nat
  deriving SelectInsertParamsClass, RpcEncodable

@[suggest]
def suggest_apply_hyp : CalcSuggester := fun goal lhs _ => do
  let mv := goal.mvarId
  let lctx := (<- mv.getDecl).lctx |>.sanitizeNames.run' {options := (<- getOptions)}
  let mut suggestions : Array Suggestion := #[]
  for i in lctx.decls do
    let some d := i | continue
    try
      let r <- mv.rewrite lhs d.toExpr
      let hyp_ty <- WithRpcRef.mk (<- ExprWithCtx.save d.type)
      suggestions := suggestions.push {
        hint := "Apply hypothesis"
        info? := some
          <span>
            <strong className="goal-hyp">
              {.text (toString f!"{d.userName}")}
            </strong>
            <span className="font-code"> : </span>
            {.ofComponent InteractiveExpr { expr := hyp_ty } #[]}
          </span>
        newLhs? := r.eNew
        proofStr? := some s!"rw [{d.userName}]"
      }
    catch | _ => pure ()
  return suggestions

@[suggest]
def suggest_dsimp : CalcSuggester := fun _ lhs _ => do
  let simp_ctx <- mkSimpContext
  let (lhs', stats) <- Meta.dsimp lhs simp_ctx
  if lhs == lhs' then
    return #[]
  else if <- isDefEq lhs lhs' then
    return #[{
      hint := "Reduce"
      newLhs? := lhs'
      proofStr? := some "rfl"
      info? := some (.text "by reflexivity")
    }]
  else
    let thms <- stats.usedTheorems.toArray.mapM fun o =>
      toString <$> ppExpr (mkConst o.key [])
    let thms_s := String.join (thms.toList.intersperse ", ")
    return #[{
      hint := "Simplify (definitional)"
      newLhs? := lhs'
      info? := some
        <span>
          {.text "using "}
          <span className="font-code">{.text thms_s}</span>
        </span>
      proofStr? := some s!"dsimp only [{thms_s}]"
    }]

@[suggest]
def suggest_simp : CalcSuggester := fun _ lhs _ => do
  let simp_ctx <- mkSimpContext
  let (res, stats) <- Meta.simp lhs simp_ctx
  let lhs' := res.expr
  if lhs == lhs' || (<- isDefEq lhs lhs') then
    return #[]
  else
    let thms <- stats.usedTheorems.toArray.mapM fun o =>
      toString <$> ppExpr (mkConst o.key [])
    let thms_s := String.join (thms.toList.intersperse ", ")
    return #[{
      hint := "Simplify"
      newLhs? := lhs'
      info? := some
        <span>
          {.text "using "}
          <span className="font-code">{.text thms_s}</span>
        </span>
      proofStr? := some s!"simp only [{thms_s}]"
    }]

@[suggest]
def suggest_define : CalcSuggester := fun goal lhs rhs => do
  let mv := goal.mvarId
  let lhs_stx <- PrettyPrinter.delab lhs
  let rhs_stx <- PrettyPrinter.delab rhs
  let tac <- `(tactic| define $rhs_stx := $lhs_stx)
  let ctx <- getLCtx
  let proof <- ContextInfo.ppSyntax goal.ctx.val ctx tac
  let (mvs, _) <- runTactic mv (<- `(tactic| try { $tac }))
  match mvs with
    | [] => return #[{
        hint := "Define"
        proofStr? := some (toString proof)
        info? := <span>{.text "Let: "} <span className="font-code">{.text s!"{<- ppExpr rhs} := LHS"}</span></span>
      }]
    | _ => return #[]

def sep (s : String := "5px") : Html := <span style={json% { marginRight: $s }} />

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

def all_suggestions : CalcSuggester := fun goal lhs rhs => do
  let env <- getEnv
  let sugg_names := suggester_ext.getState env
  sugg_names.foldlM (init := #[]) fun acc n => do
    let some f_info := env.find? n | throwError "couldn't find suggester: {n}"
    let f <- unsafe evalExpr CalcSuggester (f_info.type) (mkConst n)
    let suggs <- f goal lhs rhs
    pure (suggs ++ acc)

@[server_rpc_method]
def rpc : (params : CalcParams) -> RequestM (RequestTask Html) :=
  fun params => RequestM.withWaitFindSnapAtPos params.pos fun _snap => do
    let doc <- RequestM.readDoc
    let body <- match params.goals.toList with
    | [] => pure (<p>{.text "Nothing left to prove here"}</p>)
    | main_goal :: _ => main_goal.ctx.val.runMetaM {} <| main_goal.mvarId.withContext do
      let mv := main_goal.mvarId
      let mty <- mv.getType''
      let (rel, lhs, lhs_s, rhs, rhs_s) <- unpack_calc_goal mty
      let spc := String.replicate params.indent ' '
      let mut suggestions <- all_suggestions main_goal lhs rhs
      if suggestions.isEmpty then
        return <p>{.text "No suggestions"}</p>
      let ul_style := json%{
        listStyleType: "\"⚡ \"",
        paddingLeft: "20px"
      }
      let ul <- Html.element "ul" #[("style", ul_style)] <$> suggestions.mapM fun sugg => do
        let proof_s := sugg.proofStr?.getD "{}"
        let (new_line, content) <- match sugg.newLhs? with
          | some lhs' => do
            let exp <- ExprWithCtx.save lhs' >>= (WithRpcRef.mk ·)
            let lhs'_s := (toString <| <- ppExpr lhs').renameMetaVar
            let new_line := if params.isFirst
              then s!"{lhs_s} {rel} {lhs'_s} := by {proof_s}\n{spc}_ {rel} {rhs_s} := by \{}"
              else s!"_ {rel} {lhs'_s} := by {proof_s}\n{spc}_ {rel} {rhs_s} := by \{}"
            pure (new_line,
              <span>
                {.text "LHS"}{sep "8px"}{.text "↦"}{sep "8px"}
                {Html.ofComponent InteractiveExpr { expr := exp } #[]}
              </span>)
          | none => do
            let new_line := if params.isFirst
              then s!"{lhs_s} {rel} {rhs_s} := by {proof_s}"
              else s!"_ {rel} {rhs_s} := by {proof_s}"
            pure (new_line, .text "(unify LHS and RHS)")
        let new_selection := some (new_line.rawEndPos.dec, new_line.rawEndPos.dec)
        pure <li style={json% { marginBottom: "10px" }}>
          {.ofComponent MakeEditLink
            (.ofReplaceRange doc.meta params.replaceRange new_line new_selection)
            #[<span style={json% { marginRight: "5px", fontWeight: "bold" }}>
                {.text s!"[{sugg.hint}] "}
              </span>]}
          {content}
          <br />
          <span style={json% { marginRight: "5px" }}></span>
          {sugg.info?.getD (.text "")}
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
     _ = rev xs ++ x :: ys := by simp only [append_assoc, cons_append, nil_append]
     _ = aux xs (x :: ys) := by rw [ih]
     _ = aux (x :: xs) ys := by define aux (x :: xs) ys := aux xs (x :: ys)

end Calculation
end Tactic
