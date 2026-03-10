import Calculator.Calculator
import Mathlib.Tactic.Common

namespace Calculator.Example.Rel

open Tactic.Calculation

section Syntax

-- instance : Coe Int Val where coe := Val.ofInt
-- instance : Coe Nat Val where coe n := Val.ofInt ↑n
-- instance : Coe Bool Val where coe := Val.ofBool
-- instance {n} : OfNat Val n where ofNat := ↑n

inductive Tm where
  | ofInt : Int -> Tm
  | ofBool : Bool -> Tm
  | add : Tm -> Tm -> Tm
  | if_ : Tm -> Tm -> Tm -> Tm

attribute [coe] Tm.ofInt
attribute [coe] Tm.ofBool

instance : Add Tm where add := .add
instance : Coe Int Tm where coe := .ofInt
instance : Coe Nat Tm where coe n := .ofInt ↑n
instance : Coe Bool Tm where coe := .ofBool
instance {n} : OfNat Tm n where ofNat := .ofInt ↑n

notation "if_ " c " then " x " else " y => Tm.if_ c x y

inductive IsVal : Tm -> Prop where
  | isInt : IsVal (.ofInt _)
  | isBool : IsVal (.ofBool _)

abbrev Val := { x : Tm // IsVal x }

instance : Coe Val Tm where coe v := v.val
instance : Coe Int Val where coe n := .mk n .isInt
instance : Coe Nat Val where coe n := .mk n .isInt
instance : Coe Bool Val where coe b := .mk b .isBool

end Syntax

section Semantics

inductive Eval : Tm -> Val -> Prop where
  | val : {v : Val}
    -> Eval v v
  | add : {e e' : Tm} -> {n n' : Int}
    -> Eval e n -> Eval e' n' -> Eval (e + e') (n + n')
  | if_t : {e e1 e2 : Tm} -> {v : Val}
    -> Eval e true -> Eval e1 v -> Eval (if_ e then e1 else e2) v
  | if_f : {e e1 e2 : Tm} -> {v : Val}
    -> Eval e false -> Eval e2 v -> Eval (if_ e then e1 else e2) v

scoped infix:60 " ⇓ " => Eval

@[simp, grind .] theorem Eval.rfl {T : Type} [Coe T Val] {v : T} : v ⇓ v := by apply Eval.val
@[simp, grind .] theorem Eval.rfl.val {v : Val} : v ⇓ v := by apply Eval.val
-- @[simp, grind .] theorem Eval.rfl.int {n : Int} : n ⇓ n := by apply Eval.val
-- @[simp, grind .] theorem Eval.rfl.nat {n : Nat} : n ⇓ n := by apply Eval.val

end Semantics

section Types

inductive Ty where
  | Int : Ty
  | Bool : Ty

inductive HasTy : (v : Tm) -> (t : Ty) -> Prop where
  | isInt : HasTy (.ofInt _) .Int
  | isBool : HasTy (.ofBool _) .Bool

instance : Membership Val Ty where
  mem t v := HasTy v t

abbrev TyRel := Tm -> Ty -> Prop

class Sound (rel : TyRel) where
  soundness : ∀ {e t}, rel e t -> ∃ v, e ⇓ v ∧ v ∈ t

end Types

section Implication

def imp (a b : Prop) : Prop := a -> b
def impR (a b : Prop) : Prop := b -> a

infix:25 " ==> " => imp
infix:25 "
  <==
" => impR

@[simp, refl] theorem rfl_impR (a) : a <== a := by
  unfold impR
  exact id

instance : IsTrans Prop impR where trans _ _ _ p q := p ∘ q
instance : Std.Refl impR where refl := rfl_impR
instance : IsPreorder Prop impR where

end Implication

section Calculations

-- @[delab app.Calculator.Example.Rel.Tm.ofVal]
-- def delabFoo : Delab := withAppArg delab

def semTy : TyRel := fun e t => ∃ v, e ⇓ v ∧ v ∈ t
scoped notation:50 "⊨ " e:50 " : " t:50 => semTy e t

macro "exists_mono" : tactic =>
  `(tactic| (repeat' apply Exists.imp; intro))

variable
  (v v' : Val)
  (e e' e₁ e₂ : Tm)
  (t t' : Ty)

def semTy.val : Σ' (p : Prop), p -> (⊨ v : t) := by
  calculate fst as premise
  change _ <== _
  calc
    ⊨ v : t
    _ <== ∃ v', v ⇓ v' ∧ v' ∈ t := by rfl
    _ <== ∃ v', v = v' ∧ v' ∈ t
      := by exists_mono; grind
    _ <== v ∈ t := by simp only [exists_eq_left']

#reduce semTy.val

theorem int_val {n : Int} : ↑n ∈ t ↔ t = Ty.Int := by
  constructor
  · rintro ⟨_⟩
    rfl
  · intro rfl
    tauto

def semTy.add : Σ' (p : Prop), p -> (⊨ e + e' : t) := by
  calculate fst as premise
  change _ <== _
  calc
    ⊨ e + e' : t
    _ <== ∃ v, e + e' ⇓ v ∧ v ∈ t := by rfl
    _ <== ∃ (v : Val) (n n' : ℤ), e ⇓ n ∧ e' ⇓ n' ∧ v = n + n' ∧ v ∈ t
      := by exists_mono; rintro ⟨n, n', p, q, rfl, s⟩
            constructor; apply Eval.add; repeat tauto
    _ <== ∃ (n n' : ℤ), e ⇓ n ∧ e' ⇓ n' ∧ ↑(n + n') ∈ t
      := by rintro ⟨n, n', p⟩; exists n+n', n, n'; simp_all only [and_self]
    _ <== ∃ (n n' : ℤ), e ⇓ n ∧ ↑n ∈ Ty.Int ∧ e' ⇓ n' ∧ ↑n' ∈ Ty.Int ∧ t = .Int
      := by exists_mono; rintro ⟨p, p', q, q', r⟩; rw [r]; tauto
    _ <== (∃ (n : ℤ), e ⇓ ↑n ∧ ↑n ∈ Ty.Int) ∧ (∃ (n' : ℤ), e' ⇓ ↑n' ∧ ↑n' ∈ Ty.Int) ∧ t = .Int
      := by tauto
    _ <== ⊨ e : .Int ∧ ⊨ e' : .Int ∧ t = Ty.Int
      := by simp_all [semTy]
            rintro ⟨p, q, r⟩
            simp_all only [and_true]
            rw [Subtype.exists'] at *
            constructor
            cases p
            constructor
    _ <== ?premise := by todo

#reduce semTy.add

end Calculations

end Calculator.Example.Rel
