import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive
import Calculator.Suggestions
import Calculator.Tactics

open Nat
open Option
open List
open Lean Meta Elab Term Macro Command

namespace Tactic
namespace Calculation

/- Things I want:

* 'define' tactic support for constructors with dotted constructors e.g.
    define comp (x.add y) := ...

* 'define' tactic support for pattern matching in non-constructor arguments e.g.
    define exec (.add c') (m :: n :: s) := exec c' ((n + m) :: s)

* let the define suggester discover definitions which are more general, and
  require us to abstract from terms, e.g
    exec c ((eval x + eval y) :: s) = exec c.add (eval y :: eval x :: s)
      can be solved by
    exec c ((m + n) :: s) = exec c.add (n :: m :: s)

* calculating data-types!
    probably have to be 'pseudo'-types, as data themselves

* better errorrs for e.g. (ys is not defined as an argument)
    define aux (x :: xs) s := aux xs (x :: ys)
-/

set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option pp.fieldNotation false

@[widget_module]
def panel : ProofWidgets.Component CalcParams :=
  mk_rpc_widget% suggestion_rpc

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
  Tactic.evalCalc (<- `(tactic|calc%$calcstx $steps))

elab stx:"calc?" : tactic => Tactic.withMainContext do
  let goalType <- whnfR (<- Tactic.getMainTarget)
  unless (<- Lean.Elab.Term.getCalcRelation? goalType).isSome do
    throwError "Cannot start a calculation: the goal{indentExpr goalType}\nis not a relation."
  let s <- `(tactic| calc $(<- Lean.PrettyPrinter.delab (<- Tactic.getMainTarget)) := by [ ? ])
  Tactic.TryThis.addSuggestions stx #[.suggestion s] (header := "Create calc tactic:")
  Tactic.evalTactic (<- `(tactic|sorry))

end Calculation
end Tactic
