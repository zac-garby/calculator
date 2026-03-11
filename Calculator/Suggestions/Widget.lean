import Mathlib.Tactic.Common
import Calculator.Suggestions.Suggestions
import Calculator.Tactics
import ProofWidgets.Data.Html


namespace Tactic.Calculation

open Lean Meta Elab Server ProofWidgets Jsx

private def wrap_width := 80

def pretty_mvars (s : String) : String :=
  match s.splitOn "?m." with
  | [] => ""
  | [s] => s
  | s::ss => s ++ "(⋯)" ++ "(⋯)".toSlice.intercalate (ss.map fun s ↦ s.dropWhile Char.isDigit)

def splitWhitespace (s : String) : List String
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
  let lhs_s := pretty_mvars (toString <| <- ppExpr lhs)
  let rhs_s := pretty_mvars (toString <| <- ppExpr rhs)
  pure (rel_s, lhs, lhs_s, rhs, rhs_s)

def wrap_new_step_str (str indent : String) : String :=
  let split_sep := ":= by"
  if str.isEmpty then
    str
  else
    let lines := str.lines
    let ind_len := indent.length
    let lines' := lines.toList.flatMap fun line =>
      if ind_len + line.positions.length > wrap_width then
        match line |>.split split_sep |>.toList with
          | (step::rest) => [step, indent ++ "  " ++ split_sep
            ++ String.intercalate split_sep (rest.map (·.toString))]
          | _ => [line]
      else
        [line]
    String.intercalate "\n" (lines'.map (·.toString))

private def new_selection (str : String) : (String.Pos.Raw × String.Pos.Raw) :=
  if let some p := str.find? "?hole" then
    (p.offset, p.offset.increaseBy "?hole".length)
  else if let some p := str.find? no_proof then
    (p.offset, p.offset.increaseBy no_proof.length)
  else
    (str.rawEndPos.dec, str.rawEndPos.dec)

/-- Render a sequence of expressions as a chain: `e₀ rel e₁ rel e₂ …` -/
private def render_chain (rel : String) (exprs : List Expr) : MetaM (Array Html) := do
  let mut parts : Array Html := #[]
  -- let mut first := true
  for (e, i) in exprs.zipIdx do
    let first := i == 0
    let last := i == exprs.length - 1
    let mut cmp <- expr_component e
    let style := if first || last
      then json% { opacity: "60%" }
      else json% { textDecoration: "underline" }
    if first
      then parts := parts ++ #[ghost]
      else parts := parts ++ #[<br />, sep, .text rel, sep]
    parts := parts.push <span style={style}>{cmp}</span>
  return parts
  where
    ghost := <span style={json% { opacity: "0%" }}>
      {sep} {.text rel} {sep}
    </span>

@[server_rpc_method]
def suggestion_rpc : (params : CalcParams) -> RequestM (RequestTask Html) :=
  fun params => RequestM.withWaitFindSnapAtPos params.pos fun _snap => do
    let doc <- RequestM.readDoc
    let body <- match params.goals.toList with
    | [] => pure #[<p>{.text "Nothing left to prove here"}</p>]
    | main_goal :: _ => main_goal.ctx.val.runMetaM {} <| main_goal.mvarId.withContext do
      let mv := main_goal.mvarId
      let mty <- mv.getType''
      let (rel, lhs, _, rhs, _) <- try
        unpack_calc_goal mty
      catch | _ => return #[<p>{.text "Place your cursor in a step's proof slot to use this"}</p>]
      let col := params.indent + 3 + rel.length
      let lhs_s := (<- ppExpr lhs)
        |>.pretty (width := wrap_width) (indent := params.indent) (column := params.indent)
        |> pretty_mvars
      let rhs_s := (<- ppExpr rhs)
        |>.pretty (width := wrap_width) (indent := col) (column := col)
        |> pretty_mvars
      let spc := String.replicate params.indent ' '
      let mut suggestions <- all_suggestions main_goal doc params lhs rhs
      if suggestions.isEmpty then
        return #[<p>{.text "No suggestions"}</p>]
      let ul_style := json%{
        listStyleType: "\"⚡ \"",
        paddingLeft: "20px"
      }
      let ul <- Html.element "ul" #[("style", ul_style)] <$> suggestions.mapM fun sugg => do
        -- Build the sequence of (target_expr, proof_tactic) for all steps.
        -- intermediates: each (e, tac) = "_ rel e := by tac"
        -- finalProof some p: adds "_ rel rhs := by p"
        -- finalProof none: step is removed (lhs ≡ rhs definitionally)
        let intermed_steps : List (Expr × TSyntax `tactic) := sugg.intermediates.toList
        let allSteps : List (Expr × TSyntax `tactic) :=
          match sugg.finalProof with
          | some p => intermed_steps ++ [(rhs, p)]
          | none   => intermed_steps
        -- Build replacement step strings
        let step_strs : List String <- allSteps.mapM fun (e, tac) => do
          let e_s := (<- ppExpr e)
            |>.pretty (width := wrap_width) (indent := col) (column := col)
          let tac_s := (<- PrettyPrinter.ppTactic tac)
            |>.pretty (width := wrap_width) (indent := col)
                      (column := col + 4)
          return s!"_ {rel} {e_s}\n{spc}    := by {tac_s}"
        let info_html : Html :=
          <div style={json% { paddingTop: "5px", paddingBottom: "5px" }}>
            {sugg.info? |>.getD (.text "")}
          </div>
        let result : String × Array Html <-
          match allSteps with
          | [] =>
            -- finalProof = none, no intermediates: remove this step
            let new_line := if params.isFirst then rhs_s else ""
            pure (new_line, #[
              .text "(rewrites this step)",
              info_html
            ])
          | [(_, _)] =>
            -- Single step: closes the goal directly
            let new_line := if params.isFirst
              then s!"{lhs_s}\n{spc}{step_strs[0]!}"
              else step_strs[0]!
            pure (new_line, #[
              .text "(closes this goal)",
              info_html
            ])
          | _ =>
            -- Multiple steps: show the chain
            let new_line := if params.isFirst
              then s!"{lhs_s}\n{spc}" ++ String.intercalate s!"\n{spc}" step_strs
              else String.intercalate s!"\n{spc}" step_strs
            -- Display: current goal → new chain of expressions
            let intermed_exprs := intermed_steps.map (·.1)
            let all_exprs := [lhs] ++ intermed_exprs ++ [rhs]
            let new_chain <- render_chain rel all_exprs
            -- let old_chain <- render_chain rel [lhs, rhs]
            pure (new_line, #[
              info_html,
              <span className="font-code">{... new_chain}</span>
            ])
        let (new_text, content) := result
        let replaceRange := if new_text.isEmpty then
          .mk (.mk params.replaceRange.start.line 0)
              (.mk params.replaceRange.end.line.succ 0)
        else
          params.replaceRange
        let new_sel := new_selection new_text
        -- let new_text := wrap_new_step_str new_text spc
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

end Tactic.Calculation
