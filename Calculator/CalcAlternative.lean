import Mathlib.Tactic.Common
import Calculator.Calculator

namespace Tactic.Calculation.Alternate

open Lean Meta Elab Term Tactic Parser Tactic Command

open Tactic.Calculation.Alternate

-- partial def finishExplanationBlock (nesting : Nat) : ParserFn := fun c s =>
--   let i := s.pos
--   if h : c.atEnd i then eoi s
--   else
--     let curr := c.get' i h
--     let i    := c.next' i h
--     if curr == '-' then
--       if h : c.atEnd i then eoi s
--       else
--         let curr := c.get' i h
--         if curr == '}' then -- "-/" end of comment
--           if nesting == 1 then s.next' c i h
--           else finishExplanationBlock (nesting-1) c (s.next' c i h)
--         else
--           finishExplanationBlock nesting c (s.setPos i)
--     else if curr == '{' then
--       if h : c.atEnd i then eoi s
--       else
--         let curr := c.get' i h
--         if curr == '-' then finishExplanationBlock (nesting+1) c (s.next' c i h)
--         else finishExplanationBlock nesting c (s.setPos i)
--     else finishExplanationBlock nesting c (s.setPos i)
-- where
--   eoi s := s.mkUnexpectedError (pushMissing := true) "unterminated comment"

-- def explanationBody : Parser := {
--   fn := rawFn (finishExplanationBlock 1) (trailingWs := true)
-- }

-- @[combinator_parenthesizer explanationBody, expose]
-- def explanationBody.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
-- @[combinator_formatter explanationBody, expose]
-- def explanationBody.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

declare_syntax_cat relOp
declare_syntax_cat relStep

syntax "step_by " relOp "[" term "," term "]" : relStep

syntax justification :=
  interpolatedStr(term)?
  ppSpace ("by " tacticSeqIndentGt)

syntax step := relOp justification ppLine colEq term:51

syntax "calculator" ppLine withPosition(term:51 (ppLine step)*)
  : tactic

syntax unicode(" = ", " ≡ ") : relOp
syntax unicode(" <- ", " ← ") : relOp
syntax unicode(" -> ", " → ") : relOp

syntax "rel[" relOp "]" : term

def implies (p q) := p → q

macro_rules
  | `(relStep| step_by = [$lhs, $rhs]) => `($lhs = $rhs)
  | `(relStep| step_by → [$lhs, $rhs]) => `(implies $lhs $rhs)
  | `(relStep| step_by ← [$lhs, $rhs]) => `(implies $rhs $lhs)

open TSyntax Compat in
def mkCalcStepViews (fst : Term) (steps : Array (TSyntax ``step))
    : TermElabM (Array CalcStepView) := do
  let mut views : Array CalcStepView <- withRef fst do
    let term <- `($fst = _)
    let proof <- `(rfl)
    pure #[{ ref := fst, term, proof }]
  for step in steps do
    match step with
    | `(step| $rel $[$comment]? by $tac $rhs) => do
      let relExp <- withRef step do
        liftMacroM (expandMacros (<- `(relStep| step_by $rel [_, $rhs])))
      match relExp with
      | `(term| $relFn) => do
        let proof <- withRef tac `(by $tac)
        views := views.push { ref := step, term := relFn, proof }
    | _ => throwUnsupportedSyntax
  return views

def sendWidgetInfo (step : CalcStepView) (tmIndent relIndent : Nat) : TacticM Unit := do
  let some range := (<- getFileMap).lspRangeOfStx? step.ref | return
  let json := json% {
    "isFirst": false,
    "replaceRange": $({ range with start := { range.start with character := relIndent } }),
    "indent": $tmIndent,
    "relIndent": $relIndent,
    "altStyle": true
  }
  match step.ref with
  | `(step| $_rel $[$comment]? by $tac $rhs) => do
    let _ <- Term.elabTerm rhs none
    Widget.savePanelWidgetInfo panel.javascriptHash (pure json) tac
  | _ => return ()

elab_rules : tactic
| `(tactic|calculator%$tk $fst:term $steps:step*) => withRef tk do
  Tactic.closeMainGoalUsing `calc (checkNewUnassigned := false) fun target tag => do
    Tactic.withTacticInfoContext tk do
      let stepViews ← mkCalcStepViews fst steps
      -- Send info to widget to render suitable calculation suggestions for each step
      let mut lhs := fst
      let some lhsRange := (<- getFileMap).lspRangeOfStx? lhs | throwUnsupportedSyntax
      for view in stepViews do
        match view.ref with
        | `(step| $rel $[$comment]? by $_tac $rhs) => do
          let some relRange := (<- getFileMap).lspRangeOfStx? rel | throwUnsupportedSyntax
          sendWidgetInfo view lhsRange.start.character relRange.start.character
          lhs := rhs
        | _ => continue -- First line
      -- Process all of the steps
      let target := (← instantiateMVars target).consumeMData
      let (val, mvarIds) ← Tactic.withCollectingNewGoalsFrom
        (parentTag := tag) (tagSuffix := `calculator)
        <| Tactic.runTermElab do
        let (val, valType) ← Term.elabCalcSteps stepViews
        if (← isDefEq valType target) then
          -- If the produced proof value is of the correct type already, then just
          -- return it immediately.
          return val
        -- Otherwise, try to synthesise a final unifying step
        let some (_rel, lhs, rhs) ← Term.getCalcRelation? valType | unreachable!
        if let some (er, elhs, erhs) ← Term.getCalcRelation? target then
          if ← isDefEq lhs elhs <&&> isDefEq (← inferType rhs) (← inferType elhs) then
            let lastStep := mkApp2 er rhs erhs
            let lastStepGoal ← mkFreshExprSyntheticOpaqueMVar lastStep (tag := tag ++ `calc.step)
            try
              let (val', valType') ← Term.mkCalcTrans val valType lastStepGoal lastStep
              if (← isDefEq valType' target) then
                return val'
            catch _ =>
              pure ()
        -- Calc extension failed, so let's go back and mimic the `calc` expression
        Term.ensureHasTypeWithErrorMsgs target val
          (mkImmedErrorMsg := fun _ => Term.throwCalcFailure stepViews)
          (mkErrorMsg := fun _ => Term.throwCalcFailure stepViews)
      pushGoals mvarIds
      return val

elab stx:"calculator?" rel:relOp : tactic => Tactic.withMainContext do
  let (_rel, lhs, rhs) <- getCalcRelation
  let s <- `(tactic| calculator
  $(<- Lean.PrettyPrinter.delab lhs)
    = by todo
  $(<- Lean.PrettyPrinter.delab rhs))
  Tactic.TryThis.addSuggestions stx #[.suggestion s] (header := "Create calculator tactic:")
  Tactic.evalTactic (<- `(tactic|sorry))

-- @[simp]
-- def rev {a} : List a → List a
--   | [] => []
--   | x :: xs => rev xs ++ [x]

-- structure RevSpec a : Type where
--   fastrev : List a -> List a -> List a
--   correct : ∀ xs ys, rev xs ++ ys = fastrev xs ys

-- def eg : 1 = 1 := by
--   calculator
--     1

-- def revCalc {a} : RevSpec a := by
--   calculate fastrev
--   give fastrev by recursion
--   intro xs
--   (induction xs) <;> intro ys
--   case nil =>
--     calculator
--     rev [] ++ ys
--       = by rfl
--     ys
--       = by give fastrev [] ys := ys
--     fastrev [] ys
--   case cons x xs ih => calculator
--       rev (x :: xs) ++ ys
--     = by simp only [rev]
--       rev xs ++ [x] ++ ys
--     = by simp only [List.append_assoc]
--       rev xs ++ ([x] ++ ys)
--     = by rfl
--       rev xs ++ x :: ys
--     = by rw [ih]
--       fastrev xs (x :: ys)
--     = by give fastrev (x :: xs) ys := fastrev xs (x :: ys)
--       fastrev (x :: xs) ys


end Tactic.Calculation.Alternate
