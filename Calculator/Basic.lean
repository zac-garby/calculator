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
  · define len [] := 0
  · intro xs
    induction xs
    case cons y ys ih =>
      intro x
      rw [ih]
      define len (x :: xs) := len xs + 1
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

#check Exp.rec

def comp_calc_non_equational : CompSpec := by
  calculate comp, exec
  intro e
  induction e <;> intros c s
  case val n =>
    rewrite [eval]
    define exec (.push n c') s := exec c' (n :: s)
    define comp (.val n c) := .push n c
  case add x y ih_x ih_y =>
    rw [eval]
    have h : exec c ((eval x + eval y) :: s) = exec (.add c) (eval y :: eval x :: s) := by
      define exec (.add c') s := match s with
            | m :: n :: s' => exec c' ((n + m) :: s')
            | _ => exec c' s
    rw [h]
    simp only [ih_y, ih_x]
    define comp (.add x y) c := comp x (comp y (.add c))
  case exec.halt =>
    intro
    assumption

def comp_calc : CompSpec := by
  calculate comp, exec
  intro e
  induction e <;> intros c s
  -- Define exec.halt
  define exec (.halt s) := s
  -- Case val n:
  case val n => calc
    exec c (eval (Exp.val n) :: s)
    _ = exec c (n :: s) := by rfl
    _ = exec (Code.push n c) s
      := by define exec (Code.push n c) s := exec c (n :: s)
    _ = exec (comp (Exp.val n) c) s
      := by define comp (Exp.val n) c := Code.push n c
  case add x y ih_x ih_y => calc
    exec c (eval (.add x y) :: s)
      = exec c ((eval x + eval y) :: s) := by rfl
    _ = exec (.add c) (eval y :: eval x :: s)
      := by define exec (.add c') s := match s with
            | m :: n :: s' => exec c' ((n + m) :: s')
            | _ => don't care
    _ = exec (comp x (comp y c.add)) s := by simp only [ih_y, ih_x]
    _ = exec (comp (.add x y) c) s
      := by define comp (x.add y) c := comp x (comp y c.add)

#eval comp_calc.comp (.add (.val 1) (.val 2)) .halt
#eval comp_calc.exec (comp_calc.comp (.add (.val 1) (.val 2)) .halt) []
#print comp_calc
