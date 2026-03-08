import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive
import Calculator.SuggesterExt
import Calculator.Tactics
import ProofWidgets.Data.Html
import Lean.Server.InfoUtils


namespace Tactic.Calculation

open Option List
open Lean Meta Elab Term Macro Command
open Server
open ProofWidgets
open Jsx
open SelectInsertParamsClass Lean.SubExpr

def sep (s : String := "8px") : Html := <span style={json% { marginRight: $s }} />

def withExtra (edits : Array Lsp.TextEdit)
  (props : MakeEditLinkProps) : MakeEditLinkProps :=
  { props with edit := { props.edit with edits
    := (props.edit.edits.append edits) } }

def pretty_mvars (s : String) : String :=
  match s.splitOn "?m." with
  | [] => ""
  | [s] => s
  | s::ss => s ++ "[⋯]" ++ "[⋯]".toSlice.intercalate (ss.map fun s ↦ s.dropWhile Char.isDigit)

def expr_component (e : Expr) : MetaM Html := do
  if e.hasExprMVar then
    let str := pretty_mvars (toString <| <- ppExpr e)
    return <span className="font-code">{.text str}</span>
  else
    let e' <- WithRpcRef.mk (<- ExprWithCtx.save e)
    return .ofComponent InteractiveExpr { expr := e' } #[]

@[suggest]
def suggest_already_eq : CalcSuggester := fun _goal _doc _params lhs rhs => do
  if <- withNewMCtxDepth (isDefEq lhs rhs) then
    return #[{
      hint := "Already equal"
    }]
  else
    return #[]

@[suggest]
def suggest_apply_hyp : CalcSuggester := fun goal _doc _params lhs _ => do
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

@[suggest]
def suggest_dsimp : CalcSuggester
  := fun _doc _goal _params lhs _rhs => do
  let simp_ctx <- mkSimpContext (hasStar := true) (cfg := simp_cfg)
  let (lhs', stats) <- Meta.dsimp lhs simp_ctx
  if lhs == lhs' then
    return #[]
  else if <- isDefEq lhs lhs' then
    return #[{
      hint := s!"Simplify: rfl"
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
      hint := "Simplify: dsimp"
      new_lhs? := lhs'
      info? := some <span className="font-code">{.text fmt.pretty}</span>
      proof? := some s!"dsimp only [{fmt}]"
    }]

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
    return some (exp', fmt)

@[suggest]
def suggest_simp : CalcSuggester
  := fun _doc _goal _params lhs rhs => do
  let no_star_lhs <- get_simp (<- mkSimpContext (hasStar := false) (cfg := simp_cfg)) lhs
  let with_star_lhs <- get_simp (<- mkSimpContext (hasStar := true) (cfg := simp_cfg)) lhs
  let lhss := (no_star_lhs.toArray ++ with_star_lhs.toArray).map fun (lhs', fmt) => {
    hint := "Simplify LHS: simp"
    new_lhs? := lhs'
    info? := <span className="font-code">{.text fmt.pretty}</span>
    proof? := s!"simp only [{fmt}]"
  }
  let no_star_rhs <- get_simp (<- mkSimpContext (hasStar := false) (cfg := simp_cfg)) rhs
  let with_star_rhs <- get_simp (<- mkSimpContext (hasStar := true) (cfg := simp_cfg)) rhs
  let rhss := (no_star_rhs.toArray ++ with_star_rhs.toArray).map fun (rhs', fmt) => {
    hint := "Simplify RHS: simp"
    new_rhs? := rhs'
    info? := <span className="font-code">{.text fmt.pretty}</span>
    proof? := s!"simp only [{fmt}]"
  }
  return lhss ++ rhss

@[suggest]
def suggest_trivial : CalcSuggester := fun goal _doc _params _lhs _rhs => do
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
def suggest_define : CalcSuggester := fun goal _doc _params lhs rhs => do
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

@[suggest]
def suggest_new_constructor : CalcSuggester := fun goal doc params _lhs rhs => do
  if rhs.hasExprMVar then
    let mvars := rhs.collectMVars {} |>.result
    for mv in mvars do
      let decl <- mv.getDecl
      let ty <- whnf decl.type
      let some ind <- matchConstInduct ty.getAppFn
        (fun () => pure none)
        (fun ind _levels => pure (some ind))
        | return #[]
      let selected <- get_selected_exprs params (<- goal.mvarId.getType)
      let cargs <- selected.mapM fun exp => do
        let sel <- whnf exp
        let ty <- inferType sel
        let un <- if sel.isFVar then
          sel.fvarId!.getUserName
        else
          mkFreshUserName (.str .anonymous "arg")
        return (un, exp, ty)
      let con_ty <- mkArrowN (cargs.map fun (_, _, t) => t) ty
      let some decl_range <- findDeclarationRanges? ind.name
        | return #[]
      let insert_line := decl_range.range.endPos.line
      let insert_range : Lsp.Range
        := .mk (.mk insert_line 0) (.mk insert_line 0)
      let indent <- ind.ctors.foldlM (fun ind ctor => do
        if let some ranges <- findDeclarationRanges? ctor then
          return ind.max ranges.range.toLspRange.start.character
        return 0) 2
      let mv_name <- ppExpr (.mvar mv) <&> toString
      let con_name := "ctor"
      let ty_name <- ppExpr (.const ind.name []) <&> toString
      let insert_text := s!"{String.replicate indent ' '}| {con_name} : {<- ppExpr con_ty}\n"
      let select_range := match insert_text.find? con_name with
        | none => (insert_text.rawStartPos, insert_text.rawEndPos.prev insert_text)
        | some p => (p.offset, p.offset.increaseBy con_name.length)
      let con_app := mkAppN (.const (.str (.str .anonymous ty_name) con_name) [])
        (cargs.map fun (_, ex, _) => ex)
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
            |> withExtra hole_edits.toArray)
          #[<span style={json% { marginRight: "5px", fontWeight: "bold" }}>
            {.text s!"[New {ty_name} constructor]"}</span>]
      }]
  return #[]

@[suggest]
def suggest_cong : CalcSuggester := fun goal doc params lhs rhs => do
  let (lfn, largs) := lhs.getAppFnArgs
  let (rfn, rargs) := rhs.getAppFnArgs
  if lfn = rfn && largs.size = rargs.size then
    try_cong goal doc params lfn (Array.zip largs rargs).toList
  else
    return #[]
  where
    pairwise_eq := fun (l, r) => withNewMCtxDepth (isDefEq l r)
    try_cong (goal doc params) (_fn : Name)
      (args : List (Expr × Expr)) : MetaM (Array Suggestion) := do
      let (pre, (l, r) :: post) <- args.partitionM pairwise_eq
        | do return #[] -- in this case, all args already equal...
      if !(<- post.allM pairwise_eq) then return #[]
      let arg_idx := pre.length + 1
      let suggs <- all_suggestions goal doc params l r
      pure <| suggs.map fun s =>
        { s with
          info? := s.info?.map fun info
            => <span>
              {info}<br />
              <span style={json%{ fontSize: "0.8rem", color: "grey" }}>
                {.text s!"(By congruence over argument no. {arg_idx})"}
              </span>
            </span> }

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
  let some ci := (← getEnv).find? name | return none
  unless ci.hasValue do return none
  let save ← Meta.saveState
  try
    let levels ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
    let e := Lean.mkConst name levels
    let ty := ci.type.instantiateLevelParams ci.levelParams levels
    let (args, _, _) ← forallMetaTelescopeReducing ty
    let app := mkAppN e args
    if ← isDefEq app sub then
      let app' ← instantiateMVars app
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
  let env ← getEnv
  let candidates : List Name := env.constants.map₂.toList.filterMap fun (name, ci) =>
    if ci.hasValue && !name.isAnonymous then some name else none
  if candidates.isEmpty then return #[]
  let mut suggestions : Array Suggestion := #[]
  for candName in candidates do
    let mut goal_ty ← goal.mvarId.getType
    let mut anyFolded := false
    for pos in subs do
      let sub ← viewSubexpr (fun _ e => pure e) pos goal_ty
      if let some folded ← tryFoldWith candName sub then
        goal_ty ← replaceSubexpr (fun _ => pure folded) pos goal_ty
        anyFolded := true
    unless anyFolded do continue
    let some (_, lhs', rhs') ← getCalcRelation? goal_ty | continue
    let done_left := sel_left && lhs != lhs'
    let done_right := sel_right && rhs != rhs'
    unless done_left || done_right do continue
    let name_s := toString (← ppExpr (← mkConstWithFreshMVarLevels candName))
    suggestions := suggestions.push {
      hint := "Fold"
      new_lhs? := if done_left then some lhs' else none
      new_rhs? := if done_right then some rhs' else none
      info? := some <span className="font-code">{.text name_s}</span>
      proof? := "rfl"
    }
  return suggestions

private def splitWhitespace (s : String) : List String
  := s.splitToList (·.isWhitespace)
    |>.filter (!·.isEmpty)

def unpack_calc_goal (goal_ty : Expr)
  : MetaM (String × Expr × String × Expr × String) := do
  let some (rel, lhs, rhs) <- Term.getCalcRelation? goal_ty
    | throwError "invalid 'calc' step, relation expected{indentD goal_ty}"
  let app := mkApp2 rel (<- mkFreshExprMVar none) (<- mkFreshExprMVar none)
  let app_s <- ppExpr app <&> toString
  let app_split := splitWhitespace app_s
  let some rel_s := app_split[1]?
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
      if ind_len + line.positions.length > 70 then
        match line |>.split ":=" |>.toList with
          | (step::rest) => [step, indent ++ "  :="
            ++ String.intercalate ":=" (rest.map (·.toString))]
          | _ => [line]
      else
        [line]
    String.intercalate "\n" (lines'.map (·.toString))

private def new_selection (str : String) : (String.Pos.Raw × String.Pos.Raw) :=
  if let some p := str.find? "?_" then
    (p.offset, p.offset.increaseBy "?_".length)
  else if let some p := str.find? no_proof then
    (p.offset, p.offset.increaseBy no_proof.length)
  else
    (str.rawEndPos.dec, str.rawEndPos.dec)

@[server_rpc_method]
def suggestion_rpc : (params : CalcParams) -> RequestM (RequestTask Html) :=
  fun params => RequestM.withWaitFindSnapAtPos params.pos fun _snap => do
    let doc <- RequestM.readDoc
    let body <- match params.goals.toList with
    | [] => pure #[<p>{.text "Nothing left to prove here"}</p>]
    | main_goal :: _ => main_goal.ctx.val.runMetaM {} <| main_goal.mvarId.withContext do
      let mv := main_goal.mvarId
      let mty <- mv.getType''
      let (rel, lhs, lhs_s, rhs, rhs_s) <- try
        unpack_calc_goal mty
      catch | _ => return #[<p>{.text "Place your cursor in a step's proof slot to use this"}</p>]
      let spc := String.replicate params.indent ' '
      let mut suggestions <- all_suggestions main_goal doc params lhs rhs
      if suggestions.isEmpty then
        return #[<p>{.text "No suggestions"}</p>]
      let ul_style := json%{
        listStyleType: "\"⚡ \"",
        paddingLeft: "20px"
      }
      let ul <- Html.element "ul" #[("style", ul_style)] <$> suggestions.mapM fun sugg => do
        let proof_s := sugg.proof?.getD no_proof
        let info := <div style={json% { display: "inline-block", verticalAlign: "top" }}>
          {sugg.info? |>.map (fun i => <span>{.text "by "}{i}</span>) |>.getD (.text "")}
        </div>
        let mut (new_lhs, new_rhs) := (sugg.new_lhs?, sugg.new_rhs?)
        if new_lhs == rhs then
          new_lhs := none
        let (new_text, content) <- match new_lhs, new_rhs with
          | some lhs', some rhs' => do
            let lhs'_s := (toString <| <- ppExpr lhs').renameMetaVar
            let rhs'_s := (toString <| <- ppExpr rhs').renameMetaVar
            let new_line := if params.isFirst
              then s!"{lhs_s}\n{spc}\
                      _ {rel} {lhs'_s} := by {no_proof}\n{spc}\
                      _ {rel} {rhs'_s} := by {no_proof}\n{spc}\
                      _ {rel} {rhs_s} := by {no_proof}"
              else s!"_ {rel} {lhs'_s} := by {no_proof}\n{spc}\
                      _ {rel} {rhs'_s} := by {no_proof}\n{spc}\
                      _ {rel} {rhs_s} := by {no_proof}"
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
              then s!"{lhs_s}\n{spc}\
                      _ {rel} {lhs'_s} := by {proof_s}\n{spc}_ {rel} {rhs_s} := by {no_proof}"
              else s!"_ {rel} {lhs'_s} := by {proof_s}\n{spc}_ {rel} {rhs_s} := by {no_proof}"
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
              then s!"{lhs_s}\n{spc}\
                      _ {rel} {rhs'_s} := by {proof_s}\n{spc}_ {rel} {rhs_s} := by {no_proof}"
              else s!"_ {rel} {rhs'_s} := by {proof_s}\n{spc}_ {rel} {rhs_s} := by {no_proof}"
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
                then s!"{lhs_s}\n{spc}\
                        _ {rel} {rhs_s} := by {proof_s}"
                else s!"_ {rel} {rhs_s} := by {proof_s}"
              pure (new_line, #[.text "(closes this goal)", <br />, info])
            else if sugg.custom_button?.isSome then
              let new_line := if params.isFirst
                then s!"{lhs_s}\n{spc}\
                        _ {rel} {rhs_s} := by {proof_s}"
                else s!"_ {rel} {rhs_s} := by {proof_s}"
              pure (new_line, #[info])
            else
              let new_line := if params.isFirst
                then rhs_s
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
        let new_sel := new_selection new_text
        let btn := sugg.custom_button?.getD (.ofComponent MakeEditLink
            (.ofReplaceRange doc.meta replaceRange new_text (some new_sel))
            #[<span style={json% { marginRight: "5px", fontWeight: "bold" }}>
                {.text s!"[{sugg.hint}] "}
              </span>])
        pure <li style={json% { marginBottom: "10px" }}>
          {btn}
          {... content}
        </li>
      pure #[
        <p style={json%{ fontSize: "0.8rem", color: "grey" }}>
          Shift-click sub-terms in the {sep}<span className="font-code">⊢</span>{sep}
          goal above to select them. Selected sub-terms can be generalised over and replaced.
        </p>,
        <p>
          <b>{.text s!"Suggestions:"}</b>
          {ul}
        </p>
      ]
    return <details «open»={decide (params.goals.size > 0)}>
        <summary className="mv2 pointer">{.text "🧮 Calculator"}</summary>
        {... body}
      </details>

-- MCP integration: structured suggestion output (no HTML)

-- structure CalcDataParams where
--   pos : Lsp.Position
--   selectedLocations : Array GoalsLocation := #[]
--   deriving RpcEncodable

-- structure SuggestionResult where
--   hint : String
--   proof : Option String := none
--   new_lhs : Option String := none
--   new_rhs : Option String := none
--   deriving RpcEncodable

-- @[server_rpc_method]
-- def calc_suggestions_data : CalcDataParams → RequestM (RequestTask (Array SuggestionResult)) :=
--   fun params => RequestM.withWaitFindSnapAtPos params.pos fun snap => do
--     let doc ← RequestM.readDoc
--     let text := doc.meta.text
--     let hoverPos := text.lspPosToUtf8Pos params.pos
--     let goals := snap.infoTree.goalsAt? text hoverPos
--     match goals with
--     | [] => return #[]
--     | { ctxInfo := ci, tacticInfo := ti, useAfter, .. } :: _ =>
--       let ci' := if useAfter
--         then { ci with mctx := ti.mctxAfter }
--         else { ci with mctx := ti.mctxBefore }
--       let mvs := if useAfter then ti.goalsAfter else ti.goalsBefore
--       match mvs with
--       | [] => return #[]
--       | mv :: _ =>
--         let suggs ← ci'.runMetaM {} <| mv.withContext do
--           let mty ← mv.getType''
--           let some (_, lhs, rhs) ← Term.getCalcRelation? mty
--             | return #[]
--           let iGoal ← Widget.goalToInteractive mv
--           let calcParams : CalcParams := {
--             pos := params.pos
--             goals := #[iGoal]
--             selectedLocations := params.selectedLocations
--             replaceRange := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
--             isFirst := false
--             indent := 0
--           }
--           let suggestions ← all_suggestions iGoal doc calcParams lhs rhs
--           suggestions.mapM fun s => do
--             return {
--               hint := s.hint
--               proof := s.proof?
--               new_lhs := ← s.new_lhs?.mapM fun e => return toString (← ppExpr e)
--               new_rhs := ← s.new_rhs?.mapM fun e => return toString (← ppExpr e)
--             }
--         return suggs.toArray

end Tactic.Calculation
