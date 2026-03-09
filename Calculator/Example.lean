import Calculator.Calculator
import Mathlib.Tactic.Common

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
  case nil => calc
    rev [] ++ ys
    _ = ys := by rfl
    _ = fastrev [] ys := by define fastrev [] ys := ys
  case cons x xs ih => calc
    rev (x :: xs) ++ ys
    _ = rev xs ++ [x] ++ ys := by rfl
    _ = rev xs ++ ([x] ++ ys)
      := by simp only [List.append_assoc]
    _ = fastrev xs ([x] ++ ys) := by rw [ih]
    _ = fastrev xs (x :: ys) := by rfl
    _ = fastrev (x :: xs) ys
      := by define fastrev (x :: xs) ys := fastrev xs (x :: ys)

def fastrev {a} : List a -> List a := fun xs => revCalc.fastrev xs []

def test {a} : List a -> List a -> List a := by
  calculate ⊢ as f
  refine f => apply List.rec
  define f [] ys := ys
  define f (x::xs) ys := f xs ys

#print test
#eval test [1, 2] [4, 5]

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
  -- Case add x y:
  case add x y ih_x ih_y => calc
    exec c (eval (Exp.add x y) :: s)
    _ = exec c ((eval x + eval y) :: s) := by rfl
    _ = exec (Code.add c) (eval x :: eval y :: s)
      := by define partial exec (.add c) (m :: n :: s) := exec c ((m + n) :: s)
    _ = exec (comp x (Code.add c)) (eval y :: s) := by simp only [ih_x]
    _ = exec (comp y (comp x (Code.add c))) s := by simp only [ih_y]
    _ = exec (comp (Exp.add x y) c) s
      := by define comp (Exp.add x y) c := comp y (comp x (Code.add c))
  case halt =>
    exact id

#print comp_calc
