import Calculator.Calculator
import Calculator.Implication
import Mathlib.Tactic.Common
import Mathlib.Tactic.Order

set_option linter.unusedTactic false

namespace Calculator.Example.Rel

open Tactic.Calculation

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

notation "if_ " c " then " x " else " y => Tm.if_ c x y

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
    -> Eval e true -> Eval e₁ v -> Eval (if_ e then e₁ else e₂) v
  | if_f : {e e₁ e₂ : Tm} -> {v : Val}
    -> Eval e false -> Eval e₂ v -> Eval (if_ e then e₁ else e₂) v

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

section Calculations

open Calculator.Syntax.Implication

def semTy : TyRel := fun e t => ∃ v, e ⇓ v ∧ v ∈ t
scoped notation:50 "⊨ " e:50 " : " t:50 => semTy e t

variable
  (v v' : Val)
  (e e' e₁ e₂ : Tm)
  (t t' : Ty)

def semTy.val : Σ' (p : Prop), p -> ⊨ v : t := by
  calculate fst as premise
  change _ <- _
  calc
    ⊨ v : t
    _ <- ∃ v', v ⇓ v' ∧ v' ∈ t
      := by rfl
    _ <- ∃ v', v = v' ∧ v' ∈ t
      := by restructuring
    _ <- v ∈ t
      := by restructuring

def semTy.add : Σ' (p : Prop), p -> ⊨ e + e' : t := by
  calculate fst as premise
  change _ <- _
  calc
    ⊨ e + e' : t
    _ <- ∃ v, e + e' ⇓ v ∧ v ∈ t
      := by rfl
    _ <- ∃ (v : Val) (n n' : ℤ), e ⇓ n ∧ e' ⇓ n' ∧ v = n + n' ∧ v ∈ t
      := by restructuring
    _ <- ∃ (n n' : ℤ), e ⇓ n ∧ e' ⇓ n' ∧ ↑(n + n') ∈ t
      := by restructuring
    _ <- ∃ (n n' : ℤ), e ⇓ n ∧ ↑n ∈ Ty.Int ∧ e' ⇓ n' ∧ ↑n' ∈ Ty.Int ∧ t = .Int
      := by restructuring
    _ <- (∃ (n : ℤ), e ⇓ ↑n ∧ ↑n ∈ Ty.Int) ∧ (∃ (n' : ℤ), e' ⇓ ↑n' ∧ ↑n' ∈ Ty.Int) ∧ t = .Int
      := by restructuring
    _ <- ⊨ e : .Int ∧ ⊨ e' : .Int ∧ t = .Int
      := by restructuring

def semTy.if_t : Σ' (p : Prop), p -> ⊨ if_ e then e₁ else e₂ : t := by
  calculate fst as premise
  change _ <- _
  calc
    ⊨ if_ e then e₁ else e₂ : t
    _ <- ∃ v, (if_ e then e₁ else e₂) ⇓ v ∧ v ∈ t
      := by rfl
    _ <- ∃ v, e ⇓ true ∧ e₁ ⇓ v ∧ v ∈ t
      := by restructuring [apply Eval.if_t]
    _ <- e ⇓ true ∧ ∃ v, e₁ ⇓ v ∧ v ∈ t
      := by simp only [exists_and_left]
    _ <- e ⇓ true ∧ ⊨ e₁ : t := by trivial

def semTy.if_f : Σ' (p : Prop), p -> ⊨ if_ e then e₁ else e₂ : t := by
  calculate fst as premise
  change _ <- _
  calc
    ⊨ if_ e then e₁ else e₂ : t
    _ <- ∃ v, (if_ e then e₁ else e₂) ⇓ v ∧ v ∈ t
      := by rfl
    _ <- ∃ v, e ⇓ false ∧ e₂ ⇓ v ∧ v ∈ t
      := by restructuring [apply Eval.if_f]
    _ <- e ⇓ false ∧ ∃ v, e₂ ⇓ v ∧ v ∈ t
      := by simp only [exists_and_left]
    _ <- e ⇓ false ∧ ⊨ e₂ : t := by trivial

#reduce semTy.val
#reduce semTy.add
#reduce semTy.if_t
#reduce semTy.if_f

end Calculations

end Calculator.Example.Rel
