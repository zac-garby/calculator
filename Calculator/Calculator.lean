import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive
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
        -- let t <- inferType (.mvar field_mv)
        -- let (forall_args, _, _) <- forallMetaTelescopeReducing t
        -- field_mv.withContext do
          -- let lhs := mkAppN (.mvar field_mv) forall_args
          -- let rhs <- reduce lhs
          -- let mut eq <- mkEq lhs rhs
          -- eq <- mkForallFVars forall_args eq
          -- let mut proof <- mkEqRefl lhs
          -- proof <- mkLambdaFVars forall_args proof
          -- _ <- intro_let_in_main_goal (.str as_name "eq_def") eq proof (isDef := false)

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
open scoped Jsx
open SelectInsertParamsClass Lean.SubExpr

structure CalcParams extends SelectInsertParams where
  isFirst : Bool
  indent : Nat
  deriving SelectInsertParamsClass, RpcEncodable

structure Suggestion where
  hint : String
  info? : Option Html := none
  newLhs : Expr
  proofStr? : Option String := none

abbrev CalcSuggester := (mv : MVarId) -> (lhs : Expr) -> MetaM (Array Suggestion)

def suggest_apply_hyp : CalcSuggester := fun mv lhs => do
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
        newLhs := r.eNew
        proofStr? := some s!"rw [{d.userName}]"
      }
    catch | _ => pure ()
  return suggestions

def suggest_dsimp : CalcSuggester := fun _ lhs => do
  let simp_ctx <- mkSimpContext
  let (lhs', stats) <- Meta.dsimp lhs simp_ctx
  if lhs == lhs' then
    return #[]
  else if <- isDefEq lhs lhs' then
    return #[{
      hint := "Reduce"
      newLhs := lhs'
      proofStr? := some "rfl"
      info? := some (.text "by reflexivity")
    }]
  else
    let thms <- stats.usedTheorems.toArray.mapM fun o =>
      toString <$> ppExpr (mkConst o.key [])
    let thms_str := String.join (thms.toList.intersperse ", ")
    return #[{
      hint := "Simplify (definitional)"
      newLhs := lhs'
      info? := some
        <span>
          {.text "using "}
          <span className="font-code">{.text thms_str}</span>
        </span>
      proofStr? := some s!"dsimp only [{thms_str}]"
    }]

def suggest_simp : CalcSuggester := fun _ lhs => do
  let simp_ctx <- mkSimpContext
  let (res, stats) <- Meta.simp lhs simp_ctx
  let lhs' := res.expr
  if lhs == lhs' || (<- isDefEq lhs lhs') then
    return #[]
  else
    let thms <- stats.usedTheorems.toArray.mapM fun o =>
      toString <$> ppExpr (mkConst o.key [])
    let thms_str := String.join (thms.toList.intersperse ", ")
    return #[{
      hint := "Simplify"
      newLhs := lhs'
      info? := some
        <span>
          {.text "using "}
          <span className="font-code">{.text thms_str}</span>
        </span>
      proofStr? := some s!"simp only [{thms_str}]"
    }]

@[server_rpc_method]
def rpc : (params : CalcParams) -> RequestM (RequestTask Html) :=
  fun params =>
  RequestM.withWaitFindSnapAtPos params.pos fun _ => do
    let doc <- RequestM.readDoc
    let body <- match params.goals.toList with
    | [] => pure (<p>{.text "Nothing left to prove here"}</p>)
    | main_goal :: _ => main_goal.ctx.val.runMetaM {} <| main_goal.mvarId.withContext do
      let mv := main_goal.mvarId
      let md <- mv.getDecl
      let mty := md.type.consumeMData
      let some (_, lhs, rhs) <- getCalcRelation? mty
        | pure <p>{.text "The goal isn't an equality!"}</p>
      let lhsStr := (toString <| <- ppExpr lhs).renameMetaVar
      let rhsStr := (toString <| <- ppExpr rhs).renameMetaVar
      let spc := String.replicate params.indent ' '
      let mut suggestions : Array Suggestion
        := (<- suggest_apply_hyp mv lhs)
        ++ (<- suggest_dsimp mv lhs)
        ++ (<- suggest_simp mv lhs)
      if suggestions.isEmpty then
        return <p>{.text "No suggestions"}</p>
      let ul_style := json%{
        listStyleType: "\"⚡ \"",
        paddingLeft: "20px"
      }
      let ul := Html.element "ul" #[("style", ul_style)] <|
        <- suggestions.mapM fun sugg => do
          let exp_with_ctx <- ExprWithCtx.save sugg.newLhs
          let exp <- WithRpcRef.mk exp_with_ctx
          let newLhsStr := (toString <| <- ppExpr sugg.newLhs).renameMetaVar
          let proofStr := sugg.proofStr?.getD "{}"
          let new_line := if params.isFirst then
            s!"{lhsStr} = {newLhsStr} := by {proofStr}\n{spc}_ = {rhsStr} := by \{}"
          else
            s!"_ = {newLhsStr} := by {proofStr}\n{spc}_ = {rhsStr} := by \{}"
          let new_selection := some (new_line.rawEndPos.dec, new_line.rawEndPos.dec)
          pure <li>
            <span style={json% { marginRight: "5px" }}>
              {.text s!"{sugg.hint}: "}
            </span>
            {sugg.info?.getD (.text "")}
            <br />
            {.ofComponent MakeEditLink
              (.ofReplaceRange doc.meta params.replaceRange new_line new_selection)
              #[ .text s!"[Apply] " ]}
            <span style={json% { paddingInline: "8px" }}>{.text "↦"}</span>
            {.ofComponent InteractiveExpr { expr := exp } #[]}
          </li>
      pure <p>{.text s!"Suggested next steps ({suggestions.size}):"}{ul}</p>
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
    define aux.nil ys := ys
  case cons x xs ih =>
    calc rev (x :: xs) ++ ys
          --  = (rev xs ++ [x]) ++ ys := by rfl
        --  _ = rev xs ++ ([x] ++ ys) := by rw [@append_assoc]
        --  _ = rev xs ++ x :: ys := by dsimp only [cons_append, nil_append]
         _ = rev xs ++ [x] ++ ys := by rfl
         _ = rev xs ++ x :: ys := by simp only [append_assoc, cons_append, nil_append]
         _ = aux xs (x :: ys) := by rw [ih]
         _ = aux (x :: xs) ys := by {}
        --  _ = aux xs (x :: ys) := by rw [ih]
        --  _ = aux (x :: xs) ys := by define aux.cons x xs aux_xs ys := aux_xs (x :: ys)

end Calculation
end Tactic
