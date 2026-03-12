import Calculator.Calculator
import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

open Tactic.Calculation

inductive Tomato : Type where | it
  deriving Inhabited

inductive Mix : Set Type -> Type _ where
  | empty : Mix {}
  | add : {t : Type} -> t -> Mix s -> Mix (s.insert t)

def Tomatoes := Σ' (r : Set Type) (_ : Mix r), { Tomato } ⊆ r

def eg : Tomatoes := by
  constructor
  constructor
  case snd.fst => exact Mix.empty |>.add Tomato.it
  tauto
