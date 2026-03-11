import Calculator.Calculator
import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

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
    _ = ys
        := by rfl
    _ = fastrev [] ys
        := by define fastrev [] ys := ys
  case cons x xs ih => calc
    rev (x :: xs) ++ ys
    _ = rev xs ++ [x] ++ ys
        := by rfl
    _ = rev xs ++ ([x] ++ ys)
        := by simp only [List.append_assoc]
    _ = fastrev xs ([x] ++ ys)
        := by rw [ih]
    _ = fastrev xs (x :: ys)
        := by rfl
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
open Exp
open Code

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
  case val n =>
    calc
      exec c (eval (Exp.val n) :: s)
      _ = exec c (n :: s) := by rfl
      _ = exec (Code.push n c) s
        := by define exec (Code.push n c) s := exec c (n :: s)
      _ = exec (comp (Exp.val n) c) s
        := by define comp (Exp.val n) c := Code.push n c
  case add x y ih_x ih_y =>
    calc
      exec c (eval (Exp.add x y) :: s)
      _ = exec c ((eval x + eval y) :: s) := by rfl
      _ = let u_1 := eval y; let u := eval x;
          exec c ((u + u_1) :: s) := by rfl
      _ = let u_1 := eval y; let u := eval x;
          exec (Code.add c) (u :: u_1 :: s)
          := by define exec (Code.add c) (u :: u_1 :: s) := exec c ((u + u_1) :: s)
      _ = exec (Code.add c) (eval x :: eval y :: s) := by rfl
      _ = exec (comp x (Code.add c)) (eval y :: s)
          := by simp only [ih_x]
      _ = exec (comp y (comp x (Code.add c))) s
          := by simp only [ih_y]
      _ = exec (comp (Exp.add x y) c) s
          := by define comp (Exp.add x y) c := comp y (comp x (Code.add c))

#print comp_calc

section Test

open Lean Elab Lean.PrettyPrinter Delaborator

syntax (name := myWith) "with " (ident " := " term),* "; " term : term
@[term_elab myWith]
def with_elab : Term.TermElab := fun stx ty => match stx with
  | `(with $[$ns:ident := $vs:term],*; $body) => do
    let stx <- ns.zip vs |>.foldlM (fun s (n, v) => `(let $n := $v; $(.mk s))) body
    Term.elabTerm stx ty
  | _ => throwUnsupportedSyntax

-- @[delab letE]
-- def delab_let : Delab := do
--   let e <- SubExpr.getExpr
--   inside_let e fun body vs => do vs.foldlM (fun s (n, v) => do
--     `(with $(mkIdent n) := $(<- delab v); $s)) (<- delab body)

end Test
