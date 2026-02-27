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

@[simp]
def rev {a} : List a → List a
  | [] => []
  | x :: xs => rev xs ++ [x]

structure RevSpec a : Type where
  aux : List a -> List a -> List a
  foo : Nat
  correct : ∀ xs ys, rev xs ++ ys = aux xs ys

def correct {a} : RevSpec a := by
  calculate aux, foo as bar
  refine aux => apply List.rec
  define bar := 5
  intro xs
  induction xs <;> intro ys
  case nil => calc
    rev [] ++ ys
    _ = ys := by rfl
    _ = aux [] ys := by define aux [] ys := ys
  case cons x xs ih => calc
    rev (x :: xs) ++ ys
    _ = rev xs ++ [x] ++ ys := by rfl
    _ = rev xs ++ ([x] ++ ys) := by simp only [List.append_assoc]
    _ = aux xs ([x] ++ ys) := by rw [ih]
    _ = aux xs (x :: ys) := by rfl
    _ = aux (x :: xs) ys
      := by define aux (x :: xs) ys := aux xs (x :: ys)

inductive Exp : Type
  | val : Nat -> Exp
  | add : Exp -> Exp -> Exp
  deriving BEq

compile_inductive% Exp

@[simp]
def eval : Exp -> Nat
  | .val n => n
  | .add x y => eval x + eval y

inductive Code where
  | push : ℕ → Code → Code
  | add : Code → Code
  | halt : Code

compile_inductive% Code

abbrev Stack := List Nat

structure CompSpec where
  comp : Exp -> Code -> Code
  exec : Code -> Stack -> Stack
  correct : ∀ e c s, exec c (eval e :: s) = exec (comp e c) s

def comp_calc : CompSpec := by
  calculate comp, exec
  refine comp => apply Exp.rec
  refine exec => apply Code.rec
  intro e
  induction e <;> intros c s
  -- Case val n:
  case val n => calc
    exec c (eval (Exp.val n) :: s)
    _ = exec c (n :: s) := by rfl
    _ = exec (Code.push n c) s
      := by define exec (Code.push n c) s := exec c (n :: s)
    _ = exec (comp (Exp.val n) c) s
      := by define comp (Exp.val n) c := (Code.push n c)
  case add x y ih_x ih_y => calc
    exec c (eval (Exp.add x y) :: s)
    _ = exec c ((eval x + eval y) :: s) := by rfl
    _ = exec (Code.add c) (eval x :: eval y :: s)
      := by define exec (.add c) s := match s with
          | (m::n::s) => exec c ((m + n) :: s)
          | _ => don't care
    _ = exec (comp x (Code.add c)) (eval y :: s) := by simp only [ih_x]
    _ = exec (comp y (comp x (Code.add c))) s := by simp only [ih_y]
    _ = exec (comp (Exp.add x y) c) s
      := by define comp (Exp.add x y) c := comp y (comp x (Code.add c))
  case halt =>
    exact id

end Calculation
end Tactic
