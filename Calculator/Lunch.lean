import Calculator.Calculator
import Mathlib.Tactic.Common

set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option pp.fieldNotation false

@[simp]
def rev {a} : List a -> List a
  | [] => []
  | x :: xs => rev xs ++ [x]

def correct {a} :
  Σ' fastrev : List a -> List a -> List a,
  ∀ xs ys, rev xs ++ ys = fastrev xs ys := by
  calculate fst as fastrev
  intro xs
  induction xs <;> intro ys
  case nil => calc
    rev [] ++ ys
    _ = ys := by rfl
    _ = fastrev [] ys := by define fastrev [] ys := ys
  case cons x xs ih => calc
    rev (x :: xs) ++ ys
    _ = (rev xs ++ [x]) ++ ys := by rfl
    _ = rev xs ++ ([x] ++ ys) := by simp only [List.append_assoc]
    _ = fastrev xs ([x] ++ ys) := by rw [ih]
    _ = fastrev xs (x :: ys) := by rfl
    _ = fastrev (x :: xs) ys
      := by define fastrev (x :: xs) ys := fastrev xs (x :: ys)

#print correct

inductive Exp : Type
  | val : Nat -> Exp
  | add : Exp -> Exp -> Exp
  deriving BEq

@[simp]
def eval : Exp -> Nat
  | .val n => n
  | .add x y => eval x + eval y

inductive Code where
  | push : ℕ → Code → Code
  | add : Code → Code

abbrev Stack := List Nat

compile_inductive% Exp
compile_inductive% Code

structure CompSpec where
  comp : Exp -> Code -> Code
  exec : Code -> Stack -> Stack
  correct : ∀ e c s, exec c (eval e :: s) = exec (comp e c) s

def comp_calc : CompSpec := by
  calculate comp, exec
  · intro e
    induction e <;> intros c s
    case val n =>
      calc
        exec c (eval (Exp.val n) :: s)
        _ = exec c (n :: s) := by rfl
        _ = exec (Code.push n c) s
          := by define exec (Code.push n c) s := exec c (n :: s)
        _ = exec (comp (Exp.val n) c) s
          := by define comp (Exp.val n) c := (Code.push n c)
    case add x y ih_x ih_y =>
      calc
        exec c (eval (Exp.add x y) :: s)
        _ = exec c ((eval x + eval y) :: s) := by rfl
        _ = exec (Code.add c) (eval x :: eval y :: s)
          := by define exec (Code.add c) s := match s with
              | (m :: n :: s) => exec c ((m + n) :: s)
              | _ => don't care
        _ = exec (comp x (Code.add c)) (eval y :: s) := by simp [ih_x]
        _ = exec (comp y (comp x (Code.add c))) s := by simp [ih_y]
        _ = exec (comp (Exp.add x y) c) s
          := by define comp (Exp.add x y) c := comp y (comp x (Code.add c))

#print comp_calc
