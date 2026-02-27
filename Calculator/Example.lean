import Calculator.Calculator
import Mathlib.Tactic.Common

open Tactic.Calculation

set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option pp.fieldNotation false

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
