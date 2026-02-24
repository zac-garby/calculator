import Calculator.Calculator
import Mathlib.Tactic.Common

open Tactic.Calculation

set_option linter.style.multiGoal false

def rev {a} : List a → List a
  | [] => []
  | x :: xs => rev xs ++ [x]

def test {a} :
  Σ' app : List a -> List a -> List a -> List a,
  ∀ xs ys zs, app xs ys zs = xs ++ ys ++ zs := by
  calculate fst
  intro xs
  induction xs <;> intro ys zs
  case nil =>
    rewrite [List.nil_append]
    rfl
  case cons x xs ih =>
    dsimp
    rewrite [<- ih]
    unroll fst
    generalize fst xs = h
    rfl

def test2 {a} :
  Σ' len : List a -> Nat,
  len [] = 0 ∧ ∀ xs x, len (x :: xs) = len xs + 1 := by
  calculate fst as len
  constructor
  · define len.nil := 0
  · intro xs
    induction xs
    case cons y ys ih =>
      intro x
      rw [ih]
      unroll len
      rw [<- ih]
      generalize len (y :: ys) = l_xs
      define len.cons x xs l_xs := l_xs + 1
    case nil =>
      intro x
      dsimp [len]

#print test
#eval test.fst [1, 2] [3, 4] [5, 6]

-- structure RevSpec a : Type where
--   aux : List a -> List a -> List a
--   correct : ∀ xs ys, aux xs ys = rev xs ++ ys

-- def correct {a} : RevSpec a := by
--   calculate aux
--   intro xs
--   induction xs <;> intro ys
--   case nil =>
--     define aux.nil ys := ys
--   case cons x xs ih =>
--     rw [rev]
--     rw [List.append_assoc]
--     define aux.cons x xs aux_xs ys := aux_xs (x :: ys)
--     unroll aux
--     rw [<- ih]
--     rw [List.cons_append, List.nil_append]

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
  | push : Nat -> Code -> Code
  | add : Code -> Code
  | halt : Code

compile_inductive% Code

abbrev Stack := List Nat

structure CompSpec where
  comp : Exp -> Code -> Code
  exec : Code -> Stack -> Stack
  correct : ∀ e c s, exec c (eval e :: s) = exec (comp e c) s

def comp_calc_non_equational : CompSpec := by
  calculate comp, exec
  intro e
  induction e <;> intros c s
  case val n =>
    rewrite [eval]
    define exec.push n c' exec_c' s := exec_c' (n :: s)
    define comp.val n c := .push n c
  case add x y ih_x ih_y =>
    rw [eval]
    have h : exec c ((eval x + eval y) :: s) = exec (.add c) (eval y :: eval x :: s) := by
      define exec.add c' exec_c' s := match s with
            | m :: n :: s' => exec_c' ((n + m) :: s')
            | _ => exec_c' s
    rw [h]
    simp only [ih_y, ih_x]
    define comp.add x y cx cy c := cx (cy (.add c))
  case exec.halt =>
    intro
    assumption

def comp_calc : CompSpec := by
  calculate comp, exec
  intro e
  induction e <;> intros c s
  -- Define exec.halt
  define exec.halt s := s
  -- Case val n:
  case val n => calc
        exec c (eval (.val n) :: s)
      = exec c (n :: s) := by rw [eval]
    _ = exec (.push n c) s
        := by define exec.push n c' exec_c' s := exec_c' (n :: s)
    _ = exec (comp (.val n) c) s
        := by define comp.val n c := .push n c
  -- Case add x y:
  case add x y ih_x ih_y => calc
        exec c (eval (.add x y) :: s)
      = exec c ((eval x + eval y) :: s)
        := by rw [eval]
    _ = exec (.add c) (eval y :: eval x :: s)
        := by define exec.add c' exec_c' s := match s with
            | m :: n :: s' => exec_c' ((n + m) :: s')
            | _ => exec_c' s
    _ = exec (comp y (.add c)) (eval x :: s)
        := by simp [ih_y]
    _ = exec (comp x (comp y (.add c))) s
        := by simp [ih_x]
    _ = exec (comp (.add x y) c) s
        := by define comp.add x y comp_x comp_y c := comp_x (comp_y (.add c))

#eval comp_calc.comp (.add (.val 1) (.val 2)) .halt
#eval comp_calc.exec (comp_calc.comp (.add (.val 1) (.val 2)) .halt) []
#print comp_calc

def comp_calc' : CompSpec := by
  calculate comp, exec
  intro e
  induction e <;> intros c s
  -- Case val n:
  case val n => calc
        exec c (eval (.val n) :: s)
      = exec c (n :: s) := by rw [eval]
    _ = exec (.push n c) s
        := by define exec.push n c' exec_c' s := exec_c' (n :: s)
    _ = exec (comp (.val n) c) s
        := by define comp.val n c := .push n c
  -- Case add x y:
  case add x y ih_x ih_y =>
    calc
      exec c (eval (x.add y) :: s) = exec c ((eval x + eval y) :: s) := by sorry
      _ = exec (.add c) (eval y :: eval x :: s) := by sorry
      _ = exec (comp y (.add c)) (eval x :: s) := by sorry
      _ = exec (comp (x.add y) c) s := by sorry
  -- Case halt:
