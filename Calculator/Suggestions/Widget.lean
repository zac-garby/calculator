import Mathlib.Tactic.Common
import Calculator.Suggestions.Suggestions
import Calculator.Tactics
import ProofWidgets.Data.Html


namespace Tactic.Calculation

open Lean Meta Elab Server ProofWidgets Jsx

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

private def show_side (e : Expr) : MetaM String :=
  inside_let e fun body vs => do
    let fmt <- ppExpr body
    let mut str := toString fmt |>.renameMetaVar
    if !vs.isEmpty then str := s!"let ...; {str}"
    return str

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
                      _ {rel} {lhs'_s} := by {proof_s}\n{spc}\
                      _ {rel} {rhs'_s} := by {no_proof}\n{spc}\
                      _ {rel} {rhs_s} := by {no_proof}"
              else s!"_ {rel} {lhs'_s} := by {proof_s}\n{spc}\
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
              pure (new_line, #[<br />, info])
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

end Tactic.Calculation

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
--     let doc <- RequestM.readDoc
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
--         let suggs <- ci'.runMetaM {} <| mv.withContext do
--           let mty <- mv.getType''
--           let some (_, lhs, rhs) <- Term.getCalcRelation? mty
--             | return #[]
--           let iGoal <- Widget.goalToInteractive mv
--           let calcParams : CalcParams := {
--             pos := params.pos
--             goals := #[iGoal]
--             selectedLocations := params.selectedLocations
--             replaceRange := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
--             isFirst := false
--             indent := 0
--           }
--           let suggestions <- all_suggestions iGoal doc calcParams lhs rhs
--           suggestions.mapM fun s => do
--             return {
--               hint := s.hint
--               proof := s.proof?
--               new_lhs := <- s.new_lhs?.mapM fun e => return toString (<- ppExpr e)
--               new_rhs := <- s.new_rhs?.mapM fun e => return toString (<- ppExpr e)
--             }
--         return suggs.toArray
