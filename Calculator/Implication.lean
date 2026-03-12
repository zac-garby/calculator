import Mathlib.Tactic.Common

namespace Calculator.Syntax.Implication

@[simp]
def impR (a b : Prop) : Prop := b -> a

infix:25 "
  <-
" => impR

@[simp, refl] theorem rfl_impR (a) : a <- a := by
  unfold impR
  exact id

instance : IsTrans Prop impR where trans _ _ _ p q := p ∘ q
instance : Std.Refl impR where refl := rfl_impR
instance : IsPreorder Prop impR where

end Calculator.Syntax.Implication
