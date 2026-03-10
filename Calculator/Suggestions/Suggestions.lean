import Mathlib.Tactic.Common
import Calculator.Suggestions.SuggesterExt
import Calculator.Tactics
import ProofWidgets.Data.Html
import Lean.Server.InfoUtils


namespace Tactic.Calculation

open Lean Meta Elab Term ProofWidgets Jsx SelectInsertParamsClass SubExpr Server

def sep (s : String := "8px") : Html := <span style={json% { marginRight: $s }} />

def with_extra (edits : Array Lsp.TextEdit)
  (props : MakeEditLinkProps) : MakeEditLinkProps :=
  { props with edit := { props.edit with edits
    := (props.edit.edits.append edits) } }

def pretty_mvars (s : String) : String :=
  match s.splitOn "?m." with
  | [] => ""
  | [s] => s
  | s::ss => s ++ "(⋯)" ++ "(⋯)".toSlice.intercalate (ss.map fun s ↦ s.dropWhile Char.isDigit)

partial def inside_let {a}
  (e : Expr) (f : Expr -> List (Name × Expr) -> MetaM a) (vs : List (Name × Expr) := []) : MetaM a
  := match e with
  | .letE n ty val body _nondep =>
    withLetDecl n ty val fun x =>
      inside_let (body.instantiateRev #[x]) f ((n, x) :: vs)
  | _ => f e vs

def inst_let_body (e : Expr) (vs : List (Name × Expr × Expr × Expr)) :=
  let V := vs.toArray.map fun (_, _, _, x) => x
  e.instantiate V

partial def unzip_lets {a}
  (l r : Expr) (f : Expr -> Expr -> Array (Name × Expr × Expr × Expr) -> MetaM a)
  (vs : List (Name × Expr × Expr × Expr) := [])
  : MetaM a := match l, r with
  | .letE name ty val body_l _, .letE name' _ val' body_r _ => do
    if name != name' || !(<- isDefEq val val') then
      f (inst_let_body l vs) (inst_let_body r vs) vs.toArray
    else
      withLetDecl name ty val fun x =>
        unzip_lets body_l body_r f ((name, ty, val, x) :: vs)
  | _, _ => f (inst_let_body l vs) (inst_let_body r vs) vs.toArray

def lift_let (s : CalcSuggester) : CalcSuggester := fun goal doc params lhs rhs =>
  unzip_lets lhs rhs fun lhs' rhs' vs => do
    let vs' := vs.toList
    let lhs' := inst_let_body lhs' vs'
    let rhs' := inst_let_body rhs' vs'
    let suggs <- s goal doc params lhs' rhs'
    return suggs.map fun sugg => { sugg with
      new_lhs? := sugg.new_lhs?.map (letify vs')
      new_rhs? := sugg.new_rhs?.map (letify vs')
    }
  where letify (vs : List (Name × Expr × Expr × Expr)) (body : Expr) : Expr
    := match vs with
       | [] => body
       | (n, t, v, x) :: vs =>
        let fv := x.fvarId!
        let body := FVarSubst.apply
          (.empty |>.insert fv (.bvar 0))
          (body.liftLooseBVars 0 1)
        .letE n t v (letify vs body) false

def expr_component (e : Expr) : MetaM Html :=
  inside_let e fun e vs => do
    if e.hasExprMVar then
      let mut str := toString <| <- ppExpr e
      str := pretty_mvars str
      if !vs.isEmpty then str := s!"let ⋯; {str}"
      return <span className="font-code">{.text str}</span>
    else
      let e' <- WithRpcRef.mk (<- ExprWithCtx.save e)
      return <span className="font-code">
        {if vs.isEmpty then .text "" else .text "let ⋯; "}
        {.ofComponent InteractiveExpr { expr := e' } #[]}
      </span>

def all_suggestions : CalcSuggester := fun doc params goal lhs rhs => do
  let env <- getEnv
  let sugg_names := suggester_ext.getState env
  let suggs <- sugg_names.foldlM (init := #[]) fun acc n => do
    let some f_info := env.find? n | throwError "couldn't find suggester: {n}"
    let f <- unsafe evalExpr CalcSuggester (f_info.type) (mkConst n)
    let suggs <- f doc params goal lhs rhs
    pure (acc ++ suggs)
  pure suggs.toList.eraseDups.toArray

@[suggest]
def suggest_already_eq : CalcSuggester := fun _goal _doc _params lhs rhs => do
  if <- withNewMCtxDepth (isDefEq lhs rhs) then
    return #[{
      hint := "Already equal"
    }]
  else
    return #[]

@[suggest]
def suggest_apply_hyp : CalcSuggester := lift_let <| fun goal _doc _params lhs _ => do
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
          </span>
        new_lhs? := r.eNew
        proof? := some s!"rw [{d.userName}]"
      }
    catch | _ => pure ()
  return suggestions

def simp_cfg : Simp.Config := { singlePass := true }

private def get_dsimp (ctx : Simp.Context) (exp : Expr) : MetaM (Option (Expr × Format)) := do
  let (exp', stats) <- Meta.dsimp exp ctx
  if exp == exp' then
    return none
  else
    let md_ctx := MessageDataContext.mk (<- getEnv) (<- getMCtx) (<- getLCtx) {}
    let thms <- stats.usedTheorems.toArray.mapM fun o => do
      let md <- ppOrigin o
      md.format md_ctx
    let fmt := Format.joinSep thms.toList ", "
    if thms.isEmpty then return none
    return some (exp', fmt)

@[suggest]
def suggest_dsimp : CalcSuggester
  := lift_let <| fun _doc _goal _params lhs _rhs => do
  let simp_ctx <- mkSimpContext (hasStar := true) (cfg := simp_cfg)
  let lhs_result <- get_dsimp simp_ctx lhs
  -- let rhs_result <- get_dsimp simp_ctx rhs
  let lhss <- lhs_result.toArray.mapM fun (lhs', fmt) => do
    if <- isDefEq lhs lhs' then return ({
      hint := "Simplify: rfl"
      new_lhs? := lhs'
      proof? := some "rfl"
      info? := some (.text "reflexivity")
    } : Suggestion)
    else return ({
      hint := "Simplify LHS: dsimp"
      new_lhs? := lhs'
      info? := some <span className="font-code">{.text fmt.pretty}</span>
      proof? := some s!"dsimp only [{fmt}]"
    } : Suggestion)
  -- let rhss := rhs_result.toArray.map fun (rhs', fmt) => ({
  --   hint := "Simplify RHS: dsimp"
  --   new_rhs? := rhs'
  --   info? := some <span className="font-code">{.text fmt.pretty}</span>
  --   proof? := some s!"dsimp only [{fmt}]"
  -- } : Suggestion)
  return lhss

def get_simp (ctx : Simp.Context) (exp : Expr) : MetaM (Option (Expr × Format)) := do
  let (res, stats) <- Meta.simp exp ctx
  let exp' := res.expr
  if exp == exp' then
    return none
  else
    let md_ctx := MessageDataContext.mk (<- getEnv) (<- getMCtx) (<- getLCtx) {}
    let thms <- stats.usedTheorems.toArray.mapM fun o => do
      let md <- ppOrigin o
      md.format md_ctx
    let fmt := Format.joinSep thms.toList ", "
    if thms.isEmpty then return none
    return some (exp', fmt)

@[suggest]
def suggest_simp : CalcSuggester
  := lift_let <| fun _doc _goal _params lhs _rhs => do
  let no_star_lhs <- get_simp (<- mkSimpContext (hasStar := false) (cfg := simp_cfg)) lhs
  let with_star_lhs <- get_simp (<- mkSimpContext (hasStar := true) (cfg := simp_cfg)) lhs
  let lhss := (no_star_lhs.toArray ++ with_star_lhs.toArray).map fun (lhs', fmt) => {
    hint := "Simplify LHS: simp"
    new_lhs? := lhs'
    info? := <span className="font-code">{.text fmt.pretty}</span>
    proof? := s!"simp only [{fmt}]"
  }
  -- let no_star_rhs <- get_simp (<- mkSimpContext (hasStar := false) (cfg := simp_cfg)) rhs
  -- let with_star_rhs <- get_simp (<- mkSimpContext (hasStar := true) (cfg := simp_cfg)) rhs
  -- let rhss := (no_star_rhs.toArray ++ with_star_rhs.toArray).map fun (rhs', fmt) => {
  --   hint := "Simplify RHS: simp"
  --   new_rhs? := rhs'
  --   info? := <span className="font-code">{.text fmt.pretty}</span>
  --   proof? := s!"simp only [{fmt}]"
  -- }
  return lhss

@[suggest]
def suggest_trivial : CalcSuggester :=
  lift_let <| fun goal _doc _params _lhs _rhs => do
  let mv := goal.mvarId
  let save <- Meta.saveState
  let (mvs, _) <- runTactic mv (<- `(tactic| try trivial))
  save.restore
  match mvs with
    | [] => return #[{
      hint := "Trivial"
      proof? := "trivial"
    }]
    | _ => return #[]

@[suggest]
def suggest_define : CalcSuggester :=
  lift_let <| fun goal _doc _params lhs rhs => do
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

def get_selected_exprs {Params : Type} [SelectInsertParamsClass Params]
  (params : Params) (goal_ty : Expr) : MetaM (Array Expr) := do
  let subs := getGoalLocations (selectedLocations params)
  subs.mapM fun pos => viewSubexpr (fun _ e => pure e) pos goal_ty

private partial def find_substrings_aux {str} (s : String) acc (start : String.Pos str)
  := match start.find? s with
    | none => acc
    | some p => (p.offset, p.offset.increaseBy s.length) :: find_substrings_aux s acc p.next!

def find_substrings (s src : String) : List (String.Pos.Raw × String.Pos.Raw)
  := find_substrings_aux s [] src.startPos

private partial def unarrow (ty : Expr) : (List Expr × Expr) := match ty.arrow? with
  | some (a, b) => let (xs, r) := unarrow b; (a :: xs, r)
  | none => ([], ty)

@[suggest]
def suggest_new_constructor : CalcSuggester := fun goal doc params _lhs rhs => do
  if !rhs.isLet && rhs.hasExprMVar then
    let mvars := rhs.collectMVars {} |>.result
    for mv in mvars do
      let decl <- mv.getDecl
      let ty <- whnf decl.type
      let (_, ty) := unarrow ty
      let some ind <- matchConstInduct ty.getAppFn
        (fun () => pure none)
        (fun ind _levels => pure (some ind))
        | return #[]
      let mut selected <- get_selected_exprs params (<- goal.mvarId.getType)
      selected := selected
      let cargs <- try
          selected.mapM fun exp => do
            let ty <- inferType exp
            return (exp, ty)
        catch | _ => return #[]
      let con_ty <- mkArrowN (cargs.map fun (_, t) => t) ty
      let some decl_range <- findDeclarationRanges? ind.name
        | return #[]
      let insert_line := decl_range.range.endPos.line
      let insert_range : Lsp.Range
        := .mk (.mk insert_line 0) (.mk insert_line 0)
      let indent <- ind.ctors.foldlM (fun ind ctor => do
        if let some ranges <- findDeclarationRanges? ctor then
          return ind.max ranges.range.toLspRange.start.character
        return 0) 2
      let mv_app := rhs.findExt? fun e =>
        if e.getAppFn' == .mvar mv then .found else .visit
      let mv_name <- ppExpr (mv_app.getD (.mvar mv)) <&> toString
      let con_name := "ctor"
      let ty_name <- ppExpr (.const ind.name []) <&> toString
      let insert_text := s!"{String.replicate indent ' '}| {con_name} : {<- ppExpr con_ty}\n"
      let select_range := match insert_text.find? con_name with
        | none => (insert_text.rawStartPos, insert_text.rawEndPos.prev insert_text)
        | some p => (p.offset, p.offset.increaseBy con_name.length)
      let con_app := mkAppN (.const (.str (.str .anonymous ty_name) con_name) [])
        (cargs.map fun (ex, _) => ex)
      let src := doc.meta.text
      let holes_to_replace := find_substrings mv_name src.source
      let hole_fill <- ppExpr con_app
      let hole_edits : List Lsp.TextEdit := holes_to_replace.map fun (s, e) =>
        { range := .mk (src.leanPosToLspPos (src.toPosition s))
                       (src.leanPosToLspPos (src.toPosition e)),
          newText := s!"({hole_fill})" }
      return #[{
        hint := ""
        info? := <span>
          <span className="font-code">
            {.text s!"define: {con_name} : "}
            {<- expr_component con_ty},<br />
            {.text s!"let {mv_name} := "}
            {<- expr_component con_app}
            <br />
          </span>
          <span style={json%{ fontSize: "0.8rem", color: "grey" }}>
            (Using selected goal sub-terms as arguments)
          </span>
        </span>
        custom_button? := Html.ofComponent MakeEditLink
          (.ofReplaceRange doc.meta insert_range insert_text (some select_range)
            |> with_extra hole_edits.toArray)
          #[<span style={json% { marginRight: "5px", fontWeight: "bold" }}>
            {.text s!"[New {ty_name} constructor]"}</span>]
      }]
  return #[]

@[suggest]
def factor_common_subexpr : CalcSuggester :=
  lift_let <| fun goal _doc params lhs rhs => do
    let selected <- get_selected_exprs params (<- goal.mvarId.getType)
    if selected.isEmpty then return #[]
    let common := selected.filter fun e => e.occurs lhs && e.occurs rhs
    common
      -- |>.toList
      -- |>.mergeSort (fun e1 e2 => e2.approxDepth < e1.approxDepth)
      -- |>.eraseDupsBy (fun e1 e2 => e1.occurs e2 || e2.occurs e1)
      -- |>.toArray
      |>.mapM fun e => do
      let t <- inferType e
      let lhs' := lhs.replace fun e' => if e == e' then Expr.bvar 0 else none
      let rhs' := rhs.replace fun e' => if e == e' then Expr.bvar 0 else none
      return {
        hint := s!"Factor common: '{<- ppExpr e}'"
        new_lhs? := Expr.letE `u t e lhs' false
        new_rhs? := Expr.letE `u t e rhs' false
        proof? := "rfl"
      }

@[suggest]
def suggest_cong : CalcSuggester :=
  lift_let <| fun goal doc params lhs rhs => do
  let (lfn, largs) := lhs.getAppFnArgs
  let (rfn, rargs) := rhs.getAppFnArgs
  if lfn = rfn && largs.size = rargs.size then
    try_cong goal doc params lfn (Array.zip largs rargs).toList
  else
    return #[]
  where
    pairwise_eq := fun (l, r) => withNewMCtxDepth (isDefEq l r)
    try_cong goal doc params _fn args : MetaM (Array Suggestion) := do
      let (pre, (l, r) :: post) <- args.partitionM pairwise_eq
        | do return #[] -- in this case, all args already equal...
      if !(<- post.allM pairwise_eq) then return #[]
      let arg_idx := pre.length + 1
      let suggs <- all_suggestions goal doc params l r
      pure <| suggs.map fun s => { s with
        info? := s.info?.map fun info =>
          <span>
            {info}<br />
            <span style={json%{ fontSize: "0.8rem", color: "grey" }}>
              {.text s!"(By congruence over argument no. {arg_idx})"}
            </span>
          </span>
      }

private def get_selections (locs : Array GoalsLocation) : (Array Pos × Bool × Bool) :=
  let subs := getGoalLocations locs
  let sel_left := subs.any fun L => #[0, 1].isPrefixOf L.toArray
  let sel_right := subs.any fun L => #[1].isPrefixOf L.toArray
  (subs, sel_left, sel_right)

@[suggest]
def suggest_replace_subexpr : CalcSuggester := fun goal _doc params _lhs _rhs => do
  let (subs, sel_left, sel_right) := get_selections params.selectedLocations
  let mut goal_ty <- goal.mvarId.getType
  for pos in subs do
    goal_ty <- insertMetaVar goal_ty pos
  let some (_, lhs', rhs') <- getCalcRelation? goal_ty
    | return #[]
  if !sel_left && !sel_right then
    return #[]
  return #[{
    hint := "Rewrite"
    new_lhs? := if sel_left then some lhs' else none
    new_rhs? := if sel_right then some rhs' else none
    info? := some (.text "some further proof / definition")
  }]

@[suggest]
def suggest_expand_subexpr : CalcSuggester := fun goal _doc params lhs rhs => do
  let (subs, sel_left, sel_right) := get_selections params.selectedLocations
  let mut goal_ty <- goal.mvarId.getType
  for pos in subs do
    goal_ty <- replaceSubexpr whnf pos goal_ty
  let some (_, lhs', rhs') <- getCalcRelation? goal_ty
    | return #[]
  let done_left := sel_left && lhs != lhs'
  let done_right := sel_right && rhs != rhs'
  if !done_left && !done_right then
    return #[]
  return #[{
    hint := "Expand terms"
    new_lhs? := if done_left then some lhs' else none
    new_rhs? := if done_right then some rhs' else none
    info? := <span className="font-code">rfl</span>
    proof? := "rfl"
  }]

-- Try to fold `sub` into `name ?args` by unifying via isDefEq.
-- Returns the instantiated application if all args are determined.
private def tryFoldWith (name : Name) (sub : Expr) : MetaM (Option Expr) := do
  let some ci := (<- getEnv).find? name | return none
  unless ci.hasValue do return none
  let save <- Meta.saveState
  try
    let levels <- ci.levelParams.mapM fun _ => mkFreshLevelMVar
    let e := Lean.mkConst name levels
    let ty := ci.type.instantiateLevelParams ci.levelParams levels
    let (args, _, _) <- forallMetaTelescopeReducing ty
    let app := mkAppN e args
    if <- isDefEq app sub then
      let app' <- instantiateMVars app
      save.restore
      if !app'.hasMVar then return some app'
    save.restore
  catch _ => save.restore
  return none

-- Opposite of suggest_expand_subexpr: for each selected subterm, look for a
-- definition in the current file whose unfolding is definitionally equal to it,
-- and suggest replacing the subterm with that definition applied to arguments.
-- E.g. turns (∃ n : ℤ, e ⇓ ↑n ∧ ↑n ∈ Ty.Int) into ⊨ e : .Int
@[suggest]
def suggest_fold_subexpr : CalcSuggester := fun goal _doc params lhs rhs => do
  let (subs, sel_left, sel_right) := get_selections params.selectedLocations
  if !sel_left && !sel_right then return #[]
  let env <- getEnv
  let candidates : List Name := env.constants.map₂.toList.filterMap fun (name, ci) =>
    if ci.hasValue && !name.isAnonymous then some name else none
  if candidates.isEmpty then return #[]
  let mut suggestions : Array Suggestion := #[]
  for candName in candidates do
    let mut goal_ty <- goal.mvarId.getType
    let mut anyFolded := false
    for pos in subs do
      let sub <- viewSubexpr (fun _ e => pure e) pos goal_ty
      if let some folded <- tryFoldWith candName sub then
        goal_ty <- replaceSubexpr (fun _ => pure folded) pos goal_ty
        anyFolded := true
    unless anyFolded do continue
    let some (_, lhs', rhs') <- getCalcRelation? goal_ty | continue
    let done_left := sel_left && lhs != lhs'
    let done_right := sel_right && rhs != rhs'
    unless done_left || done_right do continue
    let name_s := toString (<- ppExpr (<- mkConstWithFreshMVarLevels candName))
    suggestions := suggestions.push {
      hint := "Fold"
      new_lhs? := if done_left then some lhs' else none
      new_rhs? := if done_right then some rhs' else none
      info? := some <span className="font-code">{.text name_s}</span>
      proof? := "rfl"
    }
  return suggestions

end Tactic.Calculation
