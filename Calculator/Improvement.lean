import Calculator.Calculator
import Mathlib.Tactic.Common

open Tactic.Calculation

namespace Improvement

open Lean Elab

local syntax (name := tick) "✓" term:1000 : term

@[term_elab tick]
def elab_tick : Term.TermElab := fun stx _ => match stx with
  | `(✓ $t) => do
    return mkAnnotation `check (<- Term.elabTerm t none)
  | _ => throwUnsupportedSyntax

elab "cost(" t:term ")" : term => do
  let e <- Term.elabTerm t none
  let n <- IO.mkRef 0
  _ <- Meta.transform e
    (fun e => do
      if let some e' := annotation? `check e then
        n.modify Nat.succ
        return TransformStep.visit e'
      return .continue)
  let val <- n.get
  return mkNatLit val

syntax:25 term " ▹ " term : term
macro_rules | `($x ▹ $y) => `(cost($y) < cost($x))

def tm := 1 + ✓ (2 + 3)

#check ✓ 1 + (2 + ✓ 3) ▹ 1 + (2 + 3)

#print tm

end Improvement

namespace ImprovementAlt

open Lean Elab

variable
  {α β} [Inhabited α] [Inhabited β]

opaque tick (x : α) : α
notation "✓" t:1000 => tick t
notation "✓" => tick
axiom tick_elim (x : α) : tick x = x

-- inductive Impr : ∀ {T}, T -> T -> Prop where
--   | refl {a} : Impr a a
--   | elim {α} [Inhabited α] {a : α} : Impr a (✓ a)
--   | tick_cong {S T x y} {f : S -> T} : Impr x y -> Impr (f x) (f y)

-- attribute [refl] Impr.refl

-- def tm : Nat := 1 + ✓2

-- theorem eg : Impr (1 + 2) tm := by
--   rw [tm]
--   rw [tick_elim]

-- @[simp]
-- def rev' : List α -> List α -> List α := revCalc.fastrev

-- theorem eg2 : ∀ (xs : List α), Impr (rev' xs []) (rev xs) := by
--   intro xs
--   induction xs
--   case nil =>
--     rfl
--   case cons x xs ih =>
--     simp [<- revCalc.correct]
--     apply Impr.tick_cong
--     rfl

#check List.rec

inductive Impr : {T : Type u} -> T -> T -> Prop where
  | elim {α} [Inhabited α] {a : α}
    : Impr a (✓ a)
  | beta {α β : Type u} [Inhabited α] {C : α -> β} {V : α}
    : Impr (let x := V; C x) (let _ := V; C (✓ V))
  | cases {α M : Type u} [Inhabited M] {xs : List α} {f : M} {g : α -> List α -> M -> M}
    : Impr (✓ List.rec f g xs : M) (List.rec (✓ f) (✓ ∘ g) xs)
  | float {α M : Type u} [Inhabited M] {xs : List α} {f : M} {g : α -> List α -> M -> M}
    : Impr (List.rec f g (✓ xs) : M) (✓ List.rec f g xs)

abbrev Same {T : Type u} (a b : T) : Prop := Impr a b ∧ Impr b a

axiom tick_ind {M N : α} (C : α -> α)
  : Impr (✓ (C M)) M -> Same (✓ (C N)) N
  -> Impr N M

@[simp]
def app (xs ys : List a) : List a :=
  List.rec (fun ys => ys) (fun x _xs app_xs ys => x :: app_xs ys) xs ys

theorem eg : ∀ (xs ys zs : List a),
  Impr (app (app xs ys) zs) (app xs (app ys zs)) := by
  intro xs ys zs
  let C (u : List a) : List a
    := List.rec (app ys zs) (fun x _ _ => x :: u) xs
  apply tick_ind C


end ImprovementAlt
