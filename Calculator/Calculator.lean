import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive
import Calculator.Suggestions
import Calculator.Tactics

open Nat
open Option
open List
open Lean Meta Elab Term Macro Command Tactic

namespace Tactic
namespace Calculation

/- Things I want:
* Make dsimp / simp / etc work on RHS not just LHS

* 'define' tactic support for constructors with dotted constructors e.g.
    define comp (x.add y) := ...

* 'define' tactic support for pattern matching in non-constructor arguments e.g.
    define exec (.add c') (m :: n :: s) := exec c' ((n + m) :: s)

* let the define suggester discover definitions which are more general, and
  require us to abstract from terms, e.g
    exec c ((eval x + eval y) :: s) = exec c.add (eval y :: eval x :: s)
      can be solved by
    exec c ((m + n) :: s) = exec c.add (n :: m :: s)

* better errors for e.g. (ys is not defined as an argument)
    define aux (x :: xs) s := aux xs (x :: ys)

* Keep track of which "calculation step" was introduced (at meta level?) so that
  we can produce a human-readable / typesetted proof string

* Have a tactic / hint for calc mode which tries to apply suggestions, exploring the
  space, until it succeeds (kinda like `grind` etc)

* If we've partially refined the proof of a step by hand (i.e. written some tactics) but it's
  not closed yet, the suggester still makes suggestions, but they are not applied properly.

-/

set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option linter.unusedVariables false
set_option pp.fieldNotation false

@[widget_module]
def panel : ProofWidgets.Component CalcParams :=
  mk_rpc_widget% suggestion_rpc

def getCalcRelation? (e : Expr) : TacticM (Option (Expr × Expr × Expr)) := do
  if let some (a, b) := e.arrow? then
    let rel <- Term.elabTerm (<- `(· -> ·)) none
    return (rel, a, b)
  else if e.getAppNumArgs < 2 then
    return none
  else
    return some (e.appFn!.appFn!, e.appFn!.appArg!, e.appArg!)

def getCalcRelation : TacticM (Expr × Expr × Expr) := do
  let goalType <- whnfR (<- Tactic.getMainTarget)
  let rel <- getCalcRelation? goalType
  match rel with
  | some rel => return rel
  | none => throwError "cannot calculate a non-relation goal:{indentD goalType}"

private def getCloserSuffix : TacticM (Option (TacticM (TSyntax `tactic))) := do
  let (rel, _, _) <- getCalcRelation
  -- Eq is fine: simp closes `a = a` via isDefEq, no extra step needed
  if rel.getAppFn.constName? == some `Eq then
    return none
  -- For any other relation, check if there's a Std.Refl instance
  let instTy <- mkAppM ``Std.Refl #[rel]
  if (<- synthInstance? instTy).isSome then
    return some `(tactic| try rfl)
  return none

private def appendToProof (suffix : TacticM (TSyntax `tactic)) (step : Syntax)
  : TacticM (TSyntax k) :=
  withRef step do
    let sf <- suffix
    match step with
    | `(calcStep| $tm := by $prf) | `(calcFirstStep| $tm := by $prf) =>
      let proof <- withRef prf
        `(tacticSeq| { ($prf) <;> $(<- withRef prf suffix) })
      .mk <$> `(calcStep| $tm := by $proof)
    | _ => return .mk step

elab_rules : tactic
| `(tactic|calc%$calcstx $steps) => do
  let mut isFirst := true
  for step in <- Lean.Elab.Term.mkCalcStepViews steps do
    let some replaceRange := (<- getFileMap).lspRangeOfStx? step.ref | continue
    let json := json% {
      "isFirst": $(isFirst),
      "replaceRange": $(replaceRange),
      "indent": $(replaceRange.start.character)
    }
    Widget.savePanelWidgetInfo panel.javascriptHash (pure json) step.proof
    isFirst := false
  let suffix <- getCloserSuffix
  let steps <- if let some suffix := suffix then
    match steps with
    | `(calcSteps|
        $step0:calcFirstStep
        $rest*) => do
      let step0' <- appendToProof suffix step0
      let rest' <- rest.mapM (appendToProof suffix)
      `(calcSteps|
        $step0'
        $rest'*)
    | _ => do
      logWarningAt steps "tried to add suffix to steps, but couldn't match. bug?"
      pure steps
    else pure steps
  evalCalc (<- `(tactic|calc%$calcstx $steps))

elab stx:"calc?" : tactic => Tactic.withMainContext do
  discard <| getCalcRelation
  let s <- `(tactic| calc $(<- Lean.PrettyPrinter.delab (<- Tactic.getMainTarget)) := by todo)
  Tactic.TryThis.addSuggestions stx #[.suggestion s] (header := "Create calc tactic:")
  Tactic.evalTactic (<- `(tactic|sorry))

end Calculation
end Tactic
