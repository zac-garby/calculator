import Mathlib.Tactic.Common
import Calculator.Suggestions.SuggesterExt
import Calculator.Tactics
import ProofWidgets.Data.Html
import Lean.Server.InfoUtils


namespace Tactic.Calculation

open Lean Meta Elab Term ProofWidgets Jsx SelectInsertParamsClass SubExpr Server

def todo : MetaM (TSyntax `tactic) := `(tactic| todo)

def sep (s : String := "8px") : Html := <span style={json% { marginRight: $s }} />

def with_extra (edits : Array Lsp.TextEdit)
  (props : MakeEditLinkProps) : MakeEditLinkProps :=
  { props with edit := { props.edit with edits
    := (props.edit.edits.append edits) } }

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

/-- Lift a suggester through shared let-bindings on lhs and rhs. -/
def lift_let (s : CalcSuggester) : CalcSuggester := fun goal doc params lhs rhs =>
  unzip_lets lhs rhs fun lhs' rhs' vs => do
    let vs' := vs.toList
    let lhs' := inst_let_body lhs' vs'
    let rhs' := inst_let_body rhs' vs'
    let suggs <- s goal doc params lhs' rhs'
    return suggs.map fun sugg => { sugg with
      intermediates := sugg.intermediates.map fun (e, p) => (letify vs' e, p)
    }
  where
    letify (vs : List (Name × Expr × Expr × Expr)) (body : Expr) : Expr
    := match vs with
       | [] => body
       | (n, t, v, x) :: vs =>
        let body := body.abstract #[x]
        .letE n t v (letify vs body) false

def expr_component (e : Expr) : MetaM Html :=
  inside_let e fun e vs => do
    let eRef <- WithRpcRef.mk (<- ExprWithCtx.save e)
    return <span className="font-code">
      {if vs.isEmpty then .text "" else .text "let ⋯; "}
      {.ofComponent InteractiveExpr { expr := eRef } #[]}
    </span>

private def get_selections (locs : Array GoalsLocation) : (Array Pos × Bool × Bool) :=
  let subs := getGoalLocations locs
  let sel_left := subs.any fun L => #[0, 1].isPrefixOf L.toArray
  let sel_right := subs.any fun L => #[1].isPrefixOf L.toArray
  (subs, sel_left, sel_right)

/-- Pretty-print a tactic syntax node to a string using reprint. -/
def ppTactic (tac : TSyntax `tactic) : MetaM Html := do
  let fmt <- PrettyPrinter.ppTactic tac
  let str := fmt.pretty (width := 80)
  return <span className="font-code">{.text str}</span>

def simp_cfg : Simp.Config := { singlePass := true }

/-- Parse a tactic string into TSyntax. -/
private def strToTactic (s : String) : MetaM (TSyntax `tactic) := do
  match Lean.Parser.runParserCategory (<- getEnv) `tactic s with
  | .ok stx => return ⟨stx⟩
  | .error e => throwError "strToTactic: {e}"

private def get_dsimp (ctx : Simp.Context) (exp : Expr)
    : MetaM (Option (Expr × TSyntax `tactic)) := do
  let (exp', stats) <- Meta.dsimp exp ctx
  if exp == exp' then return none
  let origins := stats.usedTheorems.toArray
  if origins.isEmpty then return none
  let mut names : List String := []
  for o in origins do
    match o with
    | .decl n _ _  => names := names ++ [toString n]
    | .fvar fv     => names := names ++ [toString (<- fv.getDecl).userName]
    | .stx _ syn   =>
      let n := syn.getId
      unless n.isAnonymous do names := names ++ [toString n]
    | .other _     => pure ()
  if names.isEmpty then return none
  return some (exp', <- strToTactic s!"dsimp only [{", ".intercalate names}]")

def get_simp (ctx : Simp.Context) (exp : Expr)
    : MetaM (Option (Expr × TSyntax `tactic)) := do
  let (res, stats) <- Meta.simp exp ctx
  let exp' := res.expr
  if exp == exp' then return none
  let origins := stats.usedTheorems.toArray
  if origins.isEmpty then return none
  let mut names : List String := []
  for o in origins do
    match o with
    | .decl n _ _  => names := names ++ [toString n]
    | .fvar fv     => names := names ++ [toString (<- fv.getDecl).userName]
    | .stx _ syn   =>
      let n := syn.getId
      unless n.isAnonymous do names := names ++ [toString n]
    | .other _     => pure ()
  if names.isEmpty then return none
  return some (exp', <- strToTactic s!"simp only [{", ".intercalate names}]")

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

def all_suggestions : CalcSuggester := fun doc params goal lhs rhs => do
  let env <- getEnv
  let sugg_names := suggester_ext.getState env
  let suggs <- sugg_names.foldlM (init := #[]) fun acc n => do
    let some f_info := env.find? n | throwError "couldn't find suggester: {n}"
    let f <- unsafe evalExpr CalcSuggester (f_info.type) (mkConst n)
    let suggs <- f doc params goal lhs rhs
    return (acc ++ suggs)
  return suggs.toList.mergeSort.eraseDups.toArray

@[suggest]
def suggest_already_eq : CalcSuggester := fun _goal _doc _params lhs rhs => do
  if <- withNewMCtxDepth (isDefEq lhs rhs) then
    return #[{
      hint := "Already equal"
      intermediates := #[]
      finalProof := none
      precedence := 100
      info? := Html.text "Remove this step, as it's not needed."
    }]
  else
    return #[]

@[suggest]
def suggest_apply_hyp : CalcSuggester := lift_let <| fun goal _doc _params lhs _ => do
  let mv := goal.mvarId
  let lctx := (<- mv.getDecl).lctx |>.sanitizeNames.run' {options := (<- getOptions)}
  let mut suggestions : Array SuggestionSpec := #[]
  for i in lctx.decls do
    let some d := i | continue
    try
      let r <- mv.rewrite lhs d.toExpr
      let proof <- strToTactic s!"rw [{d.userName}]"
      suggestions := suggestions.push {
        hint := "Apply hypothesis"
        info? := some
          <span>
            Using hypothesis:<br />{sep}
            <strong className="goal-hyp">
              {.text (toString f!"{d.userName}")}
            </strong>
            {sep}:{sep}
            {<- expr_component d.type}
          </span>
        intermediates := #[(r.eNew, proof)]
        finalProof := some (<- todo)
        precedence := 70
      }
    catch | _ => pure ()
  return suggestions

@[suggest]
def suggest_dsimp : CalcSuggester
  := lift_let <| fun _doc _goal _params lhs _rhs => do
  let simp_ctx <- mkSimpContext (hasStar := true) (cfg := simp_cfg)
  let lhs_result <- get_dsimp simp_ctx lhs
  let lhss <- lhs_result.mapM fun (lhs', tac) => do
    if <- isDefEq lhs lhs' then
      return {
        hint := "Simplify LHS: rfl"
        intermediates := #[(lhs', <- `(tactic| rfl))]
        finalProof := (<- todo)
        info? := some (.text "Trivially simplify by definition")
        precedence := 80
      }
    else
      return {
        hint := "Simplify LHS: dsimp"
        intermediates := #[(lhs', tac)]
        finalProof := <- todo
        info? := <- ppTactic tac
        precedence := 50
      }
  return lhss.toArray

@[suggest]
def suggest_simp : CalcSuggester
  := lift_let <| fun _goal _doc _params lhs _rhs => do
  let no_star_lhs  <- get_simp (<- mkSimpContext (hasStar := false) (cfg := simp_cfg)) lhs
  let with_star_lhs <- get_simp (<- mkSimpContext (hasStar := true) (cfg := simp_cfg)) lhs
  let lhss <- (no_star_lhs.toArray ++ with_star_lhs.toArray).mapM fun (lhs', tac) =>
    return {
      hint := "Simplify LHS: simp"
      intermediates := #[(lhs', tac)]
      finalProof := <- todo
      info? := <- ppTactic tac
      precedence := 49
    }
  return lhss

@[suggest]
def suggest_simp_all : CalcSuggester
  := lift_let <| fun goal _doc _params _lhs _rhs => do
  let mv := goal.mvarId
  let save <- Meta.saveState
  let (mvs, _) <- runTactic mv (<- `(tactic| try simp_all))
  save.restore
  match mvs with
    | [] => return #[{
      hint := "Solve by simplification"
      intermediates := #[]
      finalProof := some (<- `(tactic| simp_all?))
      precedence := 48
      info? := Html.text "Using simp_all, we can make the LHS into the RHS."
    }]
    | _ => return #[]

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
      intermediates := #[]
      finalProof := some (<- `(tactic| trivial))
      precedence := 100
      info? := Html.text "Close this goal using the trivial tactic."
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
  let (mvs, _) <- runTactic mv (<- `(tactic| try { $tac }))
  save.restore
  match mvs with
    | [] => return #[({
        hint := "Define"
        precedence := 70
        intermediates := #[]
        finalProof := some tac
        info? := <div>
          Give a (partial) definition of {<- expr_component (rhs.getAppFn)}:
          <br />
          <span className="font-code">
            {<- expr_component rhs}{sep}{.text ":="}{sep}{<- expr_component lhs}
          </span>
        </div>
      })]
    | _ => return #[]

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
      return #[({
        hint := ""
        intermediates := #[]
        finalProof := none
        precedence := 40
        info? := <span>
          <span>
            {.text s!"Add new constructor:"}<br />{sep}
            <span className="font-code">{.text con_name} : </span>
            {<- expr_component con_ty},<br />
            {.text s!"Then, instantiate hole:"}<br />{sep}
            <span className="font-code">{.text mv_name} := </span>
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
            {.text s!"[New constructor in '{ty_name}']"}</span>]
      })]
  return #[]

@[suggest]
def suggest_factor_common_subexpr : CalcSuggester :=
  lift_let <| fun goal _doc params lhs rhs => do
    let selected <- get_selected_exprs params (<- goal.mvarId.getType)
    if selected.isEmpty then return #[]
    let (lhs', rhs') <- loop selected.toList lhs rhs
    let rfl_tac  <- `(tactic| rfl)
    let hole_tac <- todo
    return match lhs == lhs', rhs == rhs' with
    | true, true => #[]
    | true, false => #[({
        precedence := 200
        info? := Html.text "Abstract selected sub-terms via let-bindings"
        hint := s!"Factor sub-terms (RHS)"
        intermediates := #[(rhs', rfl_tac)]
        finalProof := some hole_tac
        canCong := false
      })]
    | false, true => #[({
        precedence := 200
        info? := Html.text "Abstract selected sub-terms via let-bindings"
        hint := s!"Factor sub-terms (LHS)"
        intermediates := #[(lhs', rfl_tac)]
        finalProof := some hole_tac
        canCong := false
      })]
    | false, false => #[({
        precedence := 201
        info? := Html.text "Abstract sub-terms common to LHS and RHS via let-bindings"
        hint := s!"Factor sub-terms"
        intermediates := #[(lhs', rfl_tac), (rhs', hole_tac)]
        finalProof := some rfl_tac
        canCong := false
      })]
  where
    abstract (e body : Expr) (name : Name) := do
      let t <- inferType e
      let fv <- mkFreshFVarId
      let body' := body.replace fun e' => if e == e' then Expr.fvar fv else none
      if body == body' then return body
      return Expr.letE name t e (body'.abstract #[.fvar fv]) false
    loop (common : List Expr) (lhs rhs : Expr) : MetaM (Expr × Expr) := match common with
      | [] => return (lhs, rhs)
      | e :: es => do
        let t <- inferType e
        let name := (<- getLCtx).getUnusedName `u
        let lhs' <- abstract e lhs name
        let rhs' <- abstract e rhs name
        withLetDecl name t e fun _ => loop es lhs' rhs'

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
    try_cong goal doc params _fn args : MetaM (Array SuggestionSpec) := do
      let (pre, (l, r) :: post) <- args.partitionM pairwise_eq
        | do return #[]
      if !(<- post.allM pairwise_eq) then return #[]
      let arg_idx := pre.length + 1
      let suggs <- all_suggestions goal doc params l r
      pure <| suggs.filter (·.canCong) |>.map fun s => { s with
        info? := s.info?.map fun info =>
          <span>
            {info}<br />
            <span style={json%{ fontSize: "0.8rem", color: "grey" }}>
              {.text s!"(By congruence over argument no. {arg_idx})"}
            </span>
          </span>
        precedence := s.precedence - 1
      }

@[suggest]
def suggest_replace_subexpr : CalcSuggester := fun goal _doc params _lhs _rhs => do
  goal.mvarId.withContext do
  let (subs, sel_left, sel_right) := get_selections params.selectedLocations
  let mut goal_ty <- goal.mvarId.getType
  for pos in subs do
    let mv_name <- getUnusedUserName (.str .anonymous "hole")
    goal_ty <- replaceSubexpr (fun _ => mkFreshExprMVar none (userName := mv_name)) pos goal_ty
  let some (_, lhs', rhs') <- getCalcRelation? goal_ty
    | return #[]
  if !sel_left && !sel_right then
    return #[]
  let hole_tac <- todo
  let intermediates :=
    (if sel_left  then #[(lhs', hole_tac)] else #[]) ++
    (if sel_right then #[(rhs', hole_tac)] else #[])
  return #[({
    hint := "Rewrite"
    intermediates := intermediates
    finalProof := some hole_tac
    info? := some (.text "Replace this subterm with a hole; fill this in manually afterwards.")
    precedence := 250
    canCong := false
  })]

@[suggest]
def suggest_expand_subexpr : CalcSuggester := fun goal _doc params lhs rhs => do
  let (subs, sel_left, sel_right) := get_selections params.selectedLocations
  let mut goal_ty <- goal.mvarId.getType
  for pos in subs do
    goal_ty <- replaceSubexpr whnf pos goal_ty
  let some (_, lhs', rhs') <- getCalcRelation? goal_ty
    | return #[]
  let done_left  := sel_left  && lhs != lhs'
  let done_right := sel_right && rhs != rhs'
  if !done_left && !done_right then
    return #[]
  let rfl_tac  <- `(tactic| rfl)
  let hole_tac <- todo
  let intermediates :=
    (if done_left  then #[(lhs', rfl_tac)]  else #[]) ++
    (if done_right then #[(rhs', hole_tac)] else #[])
  return #[({
    precedence := 200
    hint := "Expand terms"
    intermediates := intermediates
    finalProof := some hole_tac
    info? := some (.text "Expand definitions to weak-head normal form, by definition.")
    canCong := false
  })]

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

@[suggest]
def suggest_fold_subexpr : CalcSuggester := fun goal _doc params lhs rhs => do
  let (subs, sel_left, sel_right) := get_selections params.selectedLocations
  if !sel_left && !sel_right then return #[]
  let env <- getEnv
  let candidates : List Name := env.constants.map₂.toList.filterMap fun (name, ci) =>
    if ci.hasValue && !name.isAnonymous then some name else none
  if candidates.isEmpty then return #[]
  let rfl_tac  <- `(tactic| rfl)
  let hole_tac <- todo
  let mut suggestions : Array SuggestionSpec := #[]
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
    let done_left  := sel_left  && lhs != lhs'
    let done_right := sel_right && rhs != rhs'
    unless done_left || done_right do continue
    let name_s := toString (<- ppExpr (<- mkConstWithFreshMVarLevels candName))
    let intermediates :=
      (if done_left  then #[(lhs', rfl_tac)]  else #[]) ++
      (if done_right then #[(rhs', hole_tac)] else #[])
    suggestions := suggestions.push ({
      hint := "Fold"
      precedence := 220
      intermediates := intermediates
      finalProof := some rfl_tac
      info? := some <span className="font-code">{.text name_s}</span>
      canCong := false
    })
  return suggestions

/-- Like `replaceSubexpr` but the replacement callback may return multiple results.
Each result is re-abstracted over any binders traversed, exactly as `replaceSubexpr` does
for a single result. This means `replace` may safely reference free variables introduced
by enclosing binders (e.g. the `v` from `∃ v, ...`). -/
private def replaceSubexprMulti
    (replace : Expr → MetaM (List Expr)) (p : SubExpr.Pos) (root : Expr) : MetaM (List Expr) :=
  aux replace p.toArray.toList root
where
  coord (g : Expr → MetaM (List Expr)) (n : Nat) (e : Expr) : MetaM (List Expr) := do
    match n, e with
    | 0, .app f a          => return (← g f).map (e.updateApp! · a)
    | 1, .app f a          => return (← g a).map (e.updateApp! f ·)
    | 0, .lam _ y b _      => return (← g y).map (e.updateLambdaE! · b)
    | 1, .lam n y b c      => withLocalDecl n c y fun x => do
        (← g (b.instantiateRev #[x])).mapM (mkLambdaFVars #[x] ·)
    | 0, .forallE _ y b _  => return (← g y).map (e.updateForallE! · b)
    | 1, .forallE n y b c  => withLocalDecl n c y fun x => do
        (← g (b.instantiateRev #[x])).mapM (mkForallFVars #[x] ·)
    | 0, .letE _ y a b _   => return (← g y).map (e.updateLetE! · a b)
    | 1, .letE _ y a b _   => return (← g a).map (e.updateLetE! y · b)
    | 2, .letE n y a b _   => withLetDecl n y a fun x => do
        (← g (b.instantiate1 x)).mapM (mkLetFVars #[x] ·)
    | 0, .proj _ _ b       => return (← g b).map e.updateProj!
    | n, .mdata _ a        => return (← coord g n a).map e.updateMData!
    | 3, _                 => throwError "Lensing on types is not supported"
    | c, e                 => throwError "Invalid coordinate {c} for {e}"
  aux (g : Expr → MetaM (List Expr)) : List Nat → Expr → MetaM (List Expr)
    | [],            e => g e
    | head :: tail, e => coord (aux g tail) head e

@[suggest]
def suggest_restructuring : CalcSuggester := fun goal _doc _params _lhs _rhs => do
  let mv := goal.mvarId
  let save <- Meta.saveState
  let (mvs, _) <- runTactic mv (<- `(tactic| try restructuring))
  save.restore
  match mvs with
    | [] => return #[{
      hint := "Restructure"
      intermediates := #[]
      finalProof := some (<- `(tactic| restructuring))
      precedence := 100
      info? := Html.text "Close this goal by general destructuring and constructing."
    }]
    | _ => return #[]

@[suggest]
def suggest_constructor_case : CalcSuggester := fun goal _doc params lhs rhs => do
  let goal_ty <- goal.mvarId.getType
  let (poss, _sel_left, _sel_right) := get_selections params.selectedLocations
  let some _ <- getCalcRelation? goal_ty | return #[]
  if poss.isEmpty then return #[]
  -- Expand non-deterministically: each position may yield multiple replacement goal types
  let mut goal_tys : Array Expr := #[goal_ty]
  for pos in poss do
    let mut new_goal_tys : Array Expr := #[]
    for gt in goal_tys do
      let results <- replaceSubexprMulti (fun sub => (tryCtors sub).force) pos gt
      new_goal_tys := new_goal_tys ++ results.toArray
    goal_tys := new_goal_tys
  if goal_tys.isEmpty then return #[]
  let hole_tac <- todo
  let rst_tac <- `(tactic| restructuring)
  let mut suggs : Array SuggestionSpec := #[]
  for gt in goal_tys do
    let some (_, lhs', rhs') <- getCalcRelation? gt | continue
    let changed_lhs := lhs' != lhs
    let changed_rhs := rhs' != rhs
    unless changed_lhs || changed_rhs do continue
    let intermediates :=
      (if changed_lhs then #[(lhs', rst_tac)] else #[]) ++
      (if changed_rhs then #[(rhs', rst_tac)] else #[])
    suggs := suggs.push {
      hint := "Constructor case"
      precedence := 150
      intermediates := intermediates
      finalProof := some hole_tac
      info? := some (.text "Expand by inductive constructor")
      canCong := false
    }
  return suggs
  where
    buildConj : List Expr → Expr
      | []      => mkConst ``True
      | [p]     => p
      | p :: ps => ps.foldl (fun acc q => mkApp2 (mkConst ``And) acc q) p
    tryCtors (e : Expr) : MLList MetaM Expr := do
      let e_whnf <- whnf e
      let .const indName _ := e_whnf.getAppFn | failure
      let env <- getEnv
      let some (.inductInfo indInfo) := env.find? indName | failure
      let ctorName <- MLList.ofList indInfo.ctors
      let some result <- tryCtor e ctorName | failure
      return result
    tryCtor (e : Expr) (ctorName : Name) : MetaM (Option Expr) := do
      let env <- getEnv
      let some ctorCi := env.find? ctorName | return none
      let levels <- ctorCi.levelParams.mapM fun _ => mkFreshLevelMVar
      let ctorTy := ctorCi.type.instantiateLevelParams ctorCi.levelParams levels
      let (argMVars, _, resultTy) <- forallMetaTelescopeReducing ctorTy
      -- Check that the inductive head matches
      let e_whnf <- whnf e
      let r_whnf <- whnf resultTy
      unless <- isDefEq e_whnf.getAppFn r_whnf.getAppFn do return none
      let e_args := e_whnf.getAppArgs
      let r_args := r_whnf.getAppArgs
      unless e_args.size == r_args.size do return none
      -- Match index args pairwise; fall back to an equality constraint on failure
      let mut extraEqs : Array Expr := #[]
      for (eArg, rArg) in e_args.zip r_args do
        let saved <- Meta.saveState
        if <- isDefEq rArg eArg then
          pure ()
        else
          saved.restore
          let rArgInst <- instantiateMVars rArg
          extraEqs := extraEqs.push (<- mkEq eArg rArgInst)
      -- Collect Prop-typed premise types (after instantiation)
      let mut premiseTypes : Array Expr := #[]
      for mv in argMVars do
        let ty <- inferType mv
        if <- isProp ty then
          premiseTypes := premiseTypes.push (<- instantiateMVars ty)
      premiseTypes := premiseTypes ++ extraEqs
      if premiseTypes.isEmpty then return none
      -- Collect uninstantiated data (non-Prop) mvars to existentially quantify
      let mut dataMVarIds : Array (MVarId × Expr) := #[]
      let mut seen : Std.HashSet MVarId := {}
      for mv in argMVars do
        let inst <- instantiateMVars mv
        if let .mvar mvId := inst then
          unless seen.contains mvId do
            seen := seen.insert mvId
            let ty <- instantiateMVars (<- inferType mv)
            unless <- isProp ty do
              dataMVarIds := dataMVarIds.push (mvId, ty)
      -- Build the conjunction of premises, then wrap in ∃ for each data mvar
      let mut conj := buildConj premiseTypes.toList
      for (mvId, ty) in dataMVarIds.reverse do
        -- Use a phantom FVar as a placeholder for this mvar
        let fvId : FVarId := { name := <- mkFreshId }
        let replFn : Expr → Option Expr := fun
          | .mvar id => if id == mvId then some (.fvar fvId) else none
          | _        => none
        conj := conj.replace replFn
        let ty' := ty.replace replFn
        let bodyAbs := conj.abstract #[.fvar fvId]
        let lvl <- getLevel ty'
        let mvDecl <- mvId.getDecl
        conj := mkApp2 (mkConst ``Exists [lvl]) ty' (.lam mvDecl.userName ty' bodyAbs .default)
      return some conj

end Tactic.Calculation
