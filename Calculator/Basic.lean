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

def improvement {a} :
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
    _ = rev xs ++ [x] ++ ys := by rfl
    _ = rev xs ++ ([x] ++ ys) := by simp only [List.append_assoc]
    _ = fastrev xs ([x] ++ ys) := by rw [ih]
    _ = fastrev xs (x :: ys) := by rfl
    _ = fastrev (x :: xs) ys
      := by define fastrev (x :: xs) ys := fastrev xs (x :: ys)

/-
fastrev xs ys = rev xs ++ ys

Case: xs = []
rev [] ++ ys
  = [] ++ ys
  = ys
so let fastrev [] ys := ys
-/
