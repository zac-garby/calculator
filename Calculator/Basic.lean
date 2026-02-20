import Calculator.Calculator

open Tactic.Calculation

def rev {a} : List a → List a
  | [] => []
  | x :: xs => rev xs ++ [x]

structure RevSpec {a} : Type where
  aux : List a -> List a -> List a
  correct : ∀ xs ys, aux xs ys = rev xs ++ ys

structure RevSpec' : Type where
  aux : List Int -> List Int -> List Int
  correct : ∀ xs ys, aux xs ys = rev xs ++ ys

inductive Exp : Type
  | val : Nat -> Exp
  | add : Exp -> Exp -> Exp
  deriving BEq

compile_inductive% Exp

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

def comp_calc : CompSpec := by
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
  -- Case halt:
  case exec.halt =>
    intro
    assumption

#eval comp_calc.comp (.add (.val 1) (.val 2)) .halt
#eval comp_calc.exec (comp_calc.comp (.add (.val 1) (.val 2)) .halt) []
#print comp_calc
