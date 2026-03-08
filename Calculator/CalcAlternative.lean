import Mathlib.Tactic.Common
import Calculator.Calculator

namespace Tactic.Calculation.Alternate

open Lean Meta Elab Term Macro Command Tactic

syntax step := term " by " Parser.Tactic.tacticSeqIndentGt
syntax steps := ppLine ppIndent(atomic(step)*)
syntax finalStep := ppLine ppIndent(term)
syntax "calcs" steps finalStep " ∎"? : tactic

def unpkgCalcStep (step : TSyntax ``step) : TermElabM (Term × Term) :=
  match step with
  | `(step| $t:term by $w) => return (t, <- `(by $w))
  | _ => throwUnsupportedSyntax

def mkCalcStepView (step : TSyntax ``step) : TermElabM CalcStepView :=
  withRef step do
    match step with
    | `(step| $t:term by $w:tactic) => return { ref := step, term := t, proof := <- `(by { $w }) }
    | _ => throwUnsupportedSyntax

def mkCalcStepViews (steps : TSyntax ``steps) (last : Term)
  : TermElabM (Array CalcStepView) :=
  match steps with
  | `(steps| $fst $rest*) => do
    let mut (t1, prf) <- unpkgCalcStep fst
    let mut steps := #[{ ref := fst, term := <- `($t1 = _), proof := <- ``(rfl) }]
    for step in rest do
      let `(step| $t by $w) := step | throwUnsupportedSyntax
      steps := steps.push { ref := step, term := t, proof := prf }
      prf <- `(by $w)
    steps := steps.push { ref := last, term := last, proof := prf }
    return steps
  | _ => throwUnsupportedSyntax

elab_rules : tactic
| `(tactic|calcs%$tk $steps $last:term $[∎]?) => withRef tk do
  Tactic.closeMainGoalUsing `calc (checkNewUnassigned := false) fun target tag => do
    Tactic.withTacticInfoContext steps do
      let steps <- mkCalcStepViews steps last
      let target := (<- instantiateMVars target).consumeMData
      let (val, mvarIds) <- Tactic.withCollectingNewGoalsFrom
        (parentTag := tag) (tagSuffix := `calcs)
        <| Tactic.runTermElab do
        let (val, valType) <- Term.elabCalcSteps steps
        if (<- isDefEq valType target) then
          -- Immediately the right type, no need for further processing.
          return val
        let some (_, lhs, rhs) <- Term.getCalcRelation? valType | unreachable!
        if let some (er, elhs, erhs) <- Term.getCalcRelation? target then
          -- Feature: if the goal is `x ~ y`, try extending the `calc` with `_ ~ y` with a
          -- new "last step" goal.
          if <- isDefEq lhs elhs <&&> isDefEq (<- inferType rhs) (<- inferType elhs) then
            let lastStep := mkApp2 er rhs erhs
            let lastStepGoal <- mkFreshExprSyntheticOpaqueMVar lastStep (tag := tag ++ `calc.step)
            try
              let (val', valType') <- Term.mkCalcTrans val valType lastStepGoal lastStep
              if (<- isDefEq valType' target) then
                return val'
            catch _ =>
              pure ()
        -- Calc extension failed, so let's go back and mimic the `calc` expression
        Term.ensureHasTypeWithErrorMsgs target val
          (mkImmedErrorMsg := fun _ => Term.throwCalcFailure steps)
          (mkErrorMsg := fun _ => Term.throwCalcFailure steps)
      pushGoals mvarIds
      return val

section Testing

open Tactic.Calculation

@[simp]
def rev {a} : List a → List a
  | [] => []
  | x :: xs => rev xs ++ [x]

structure RevSpec a : Type where
  fastrev : List a -> List a -> List a
  correct : ∀ xs ys, rev xs ++ ys = fastrev xs ys

def revCalc {a} : RevSpec a := by
  calculate fastrev
  refine fastrev => apply List.rec
  intro xs
  induction xs <;> intro ys
  case nil =>
    calcs
      (rev [] ++ ys)
        by rfl
      (_ = ys)
        by define fastrev [] ys := ys
      (_ = fastrev [] ys)


end Testing

end Tactic.Calculation.Alternate
