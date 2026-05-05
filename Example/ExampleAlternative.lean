import Calculator.Calculator
import Calculator.CalcAlternative
import Mathlib.Tactic.Common
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Util.CompileInductive

namespace Calculator.Example.Alternative

open Tactic.Calculation
open Tactic.Calculation.Alternate

open List

/-

Want to be able to introduce "global" let-bindings during calculations.

So like,

calculator
  exec c (eval (add x y) :: s)
    = by rfl
  exec c ((eval x + eval y) :: s)
    = by let m = eval x; let n = eval y
  exec c ((m + n) :: s)
    ...
-/

def f {a b} : (a × b) -> (b × a) := by calculator
  (a × b)
    → "hello world! it's a comment here"
      by apply Prod.swap
  (b × a)

@[simp]
def rev {a} : List a → List a
  | [] => []
  | x :: xs => rev xs ++ [x]

structure RevSpec a : Type where
  fastrev : List a -> List a -> List a
  correct : ∀ xs ys, rev xs ++ ys = fastrev xs ys

def revCalc {a} : RevSpec a := by
  calculate fastrev
  give fastrev by recursion
  intro xs
  (induction xs) <;> intro ys
  case nil => calculator
      rev [] ++ ys
    = by rfl
      ys
    = by give fastrev [] ys := ys
      fastrev [] ys
  case cons x xs ih => calculator
      rev (x :: xs) ++ ys
    = by simp only [rev]
      rev xs ++ [x] ++ ys
    = by simp only [List.append_assoc]
      rev xs ++ ([x] ++ ys)
    = by rfl
      rev xs ++ x :: ys
    = by rw [ih]
      fastrev xs (x :: ys)
    = by give fastrev (x :: xs) ys := fastrev xs (x :: ys)
      fastrev (x :: xs) ys

section Compiler

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
  give comp by recursion
  give exec by recursion
  intro e
  induction e <;> intros c s
  case val n => calculator
      exec c (eval (val n) :: s)
    = by rfl
      exec c (n :: s)
    = by give exec (push n c) s := exec c (n :: s)
      exec (push n c) s
    = by give comp (val n) c := push n c
      exec (comp (val n) c) s
  case add x y ih_x ih_y => calculator
      exec c (eval (add x y) :: s)
    = by rfl
      exec c ((eval x + eval y) :: s)
    = by
        give exec (add c) s by cases of s
        give exec (add c) (x :: xs) by cases of xs
        give h : exec (add c) (x :: y :: ys) := exec c ((x + y) :: ys)
        rw [h]
        exact []
        exact []
      exec (add c) (eval x :: eval y :: s)
    = by simp only [ih_x]
      exec (comp x (Code.add c)) (eval y :: s)
    = by simp only [ih_y]
      exec (comp y (comp x (Code.add c))) s
    = by give comp (Exp.add x y) c := comp y (comp x (Code.add c))
      exec (comp (Exp.add x y) c) s

end Compiler

section Relational

section Syntax

inductive Val where
  | ofInt : Int -> Val
  | ofBool : Bool -> Val

instance : Coe Int Val where coe := Val.ofInt
instance : Coe Nat Val where coe n := Val.ofInt ↑n
instance : Coe Bool Val where coe := Val.ofBool
instance {n} : OfNat Val n where ofNat := ↑n

inductive Tm where
  | ofVal : Val -> Tm
  | add : Tm -> Tm -> Tm
  | if_ : Tm -> Tm -> Tm -> Tm

attribute [coe] Val.ofInt
attribute [coe] Val.ofBool
attribute [coe] Tm.ofVal

instance : Add Tm where add := Tm.add
instance : Coe Val Tm where coe := Tm.ofVal
instance {n} : OfNat Tm n where ofNat := Tm.ofVal ↑n

notation "If " c " then " x " else " y => Tm.if_ c x y

inductive IsVal : Tm -> Prop where
  | is : IsVal (.ofVal _)

abbrev Value := { x : Tm // IsVal x }

end Syntax

section Semantics

inductive Eval : Tm -> Val -> Prop where
  | val : {v : Val}
    -> Eval v v
  | add : {e e' : Tm} -> {n n' : Int}
    -> Eval e n -> Eval e' n' -> Eval (e + e') (n + n')
  | if_t : {e e₁ e₂ : Tm} -> {v : Val}
    -> Eval e true -> Eval e₁ v -> Eval (If e then e₁ else e₂) v
  | if_f : {e e₁ e₂ : Tm} -> {v : Val}
    -> Eval e false -> Eval e₂ v -> Eval (If e then e₁ else e₂) v

scoped infix:60 " ⇓ " => Eval

@[simp, grind .] theorem Eval.rfl {T : Type} [Coe T Val] {v : T} : v ⇓ v := by apply Eval.val
@[simp, grind .] theorem Eval.rfl.val {v : Val} : v ⇓ v := by apply Eval.val
@[simp, grind .] theorem Eval.rfl.int {n : Int} : n ⇓ n := by apply Eval.val
@[simp, grind .] theorem Eval.rfl.nat {n : Nat} : n ⇓ n := by apply Eval.val

end Semantics

section Types

inductive Ty where
  | Int : Ty
  | Bool : Ty

inductive HasTy : (v : Val) -> (t : Ty) -> Prop where
  | isInt : HasTy (.ofInt _) .Int
  | isBool : HasTy (.ofBool _) .Bool

instance : Membership Val Ty where
  mem t v := HasTy v t

abbrev TyRel := Tm -> Ty -> Prop

class Sound (rel : TyRel) where
  soundness : ∀ {e t}, rel e t -> ∃ v, e ⇓ v ∧ v ∈ t

end Types

def semTy : TyRel := fun e t => ∃ v, e ⇓ v ∧ v ∈ t
scoped notation:50 "⊨ " e:50 " : " t:50 => semTy e t

variable
  (v v' : Val)
  (e e' e₁ e₂ : Tm)
  (t t' : Ty)

end Relational

end Calculator.Example.Alternative
