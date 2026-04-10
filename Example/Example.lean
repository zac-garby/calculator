import Calculator.Calculator
import Mathlib.Tactic.Common
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Util.CompileInductive

open Tactic.Calculation
open List

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
  induction xs <;> intro ys
  case nil => calc
    rev [] ++ ys
    _ = ys
        := by rfl
    _ = fastrev [] ys
        := by give fastrev [] ys := ys
  case cons x xs ih => calc
    rev (x :: xs) ++ ys
    _ = rev xs ++ [x] ++ ys
        := by rfl
    _ = rev xs ++ ([x] ++ ys)
        := by simp only [List.append_assoc]
    _ = rev xs ++ x :: ys
        := by rfl
    _ = fastrev xs (x :: ys)
        := by rw [ih]
    _ = fastrev (x :: xs) ys
        := by give fastrev (x :: xs) ys := fastrev xs (x :: ys)

def fastrev {a} : List a -> List a := fun xs => revCalc.fastrev xs []

abbrev Sorted (xs : List Nat) := Pairwise (· ≤ ·) xs

structure SortSpec where
  ins : List Nat -> Nat -> List Nat
  sort : List Nat -> List Nat
  correct : ∀ xs, Sorted (sort xs) ∧ xs ~ (sort xs)

/-
def sortCalc : SortSpec := by
  calculate ins, sort
  give ins => apply List.rec
  give sort => apply List.rec
  intro xs
  induction xs
  case correct.nil => tauto
  case correct.cons x xs ih =>
    unroll sort
    let rec foo (xs : List Nat) (x : Nat) : List Nat := ?foo
    have h : ∀ n ns, Sorted ns
                  -> Sorted (ins ns n) ∧ (n :: ns) ~ (ins ns n) := ?q
    define sort (x :: xs) := foo (sort xs) x
    grind
-/

-- def sortCalc : SortSpec := by
--   calculate ins, sort
--   give ins => apply List.rec
--   give sort => apply List.rec
--   intro xs
--   induction xs
--   case correct.nil => tauto
--   case correct.cons x xs ih =>
--     unroll sort
--     have h : ∀ n ns, Sorted ns
--                   -> Sorted (ins ns n) ∧ (n :: ns) ~ (ins ns n) := ?q
--     define sort (x :: xs) := ins (sort xs) x
--     grind
--     · intro n ns
--       induction ns with
--       | nil =>
--         define ins [] n := [n]
--         grind
--       | cons u us ih_u =>
--         intro s
--         simp at s; rw [<- Sorted] at s
--         obtain ⟨h1, h2⟩ := s
--         obtain ⟨r1, r2⟩ := ih_u h2
--         constructor
--         cases decide (n <= u)
--         case true =>
--           define ins (u :: us) n := n :: u :: us
--           unroll ins
--           constructor
--           · grind
--           · constructor <;> grind
--         case false =>
--           define ins (u :: us) n := u :: ins us n
--           unroll ins
--           constructor
--           · grind
--           · grind

-- #print sortCalc

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
  case val n => calc
    exec c (eval (val n) :: s)
    _ = exec c (n :: s)
        := by rfl
    _ = exec (push n c) s
        := by give exec (push n c) s := exec c (n :: s)
    _ = exec (comp (val n) c) s
        := by give comp (val n) c := push n c
  case add x y ih_x ih_y => calc
    exec c (eval (add x y) :: s)
    _ = exec c ((eval x + eval y) :: s)
        := by rfl
    _ = exec (add c) (eval x :: eval y :: s)
        := by {
          give exec (add c) s by cases of s
          give exec (add c) (x :: xs) by cases of xs
          give h : exec (add c) (x :: y :: ys) := exec c ((x + y) :: ys)
          rw [h]
          exact []
          exact []
        }
    _ = exec (comp x (Code.add c)) (eval y :: s)
        := by simp only [ih_x]
    _ = exec (comp y (comp x (Code.add c))) s
        := by simp only [ih_y]
    _ = exec (comp (Exp.add x y) c) s
        := by give comp (Exp.add x y) c := comp y (comp x (Code.add c))

#print comp_calc

def eg : map (· + 1) ∘ map (· * 2) = map (· * 2 + 1) := by
  calc
    (map fun x ↦ x + 1) ∘ map fun x ↦ x * 2
    _ = map ((fun x ↦ x + 1) ∘ fun x ↦ x * 2)
        := by simp only [List.map_comp_map]
    _ = map fun x ↦ x * 2 + 1
        := by trivial

def seq (n : Nat) : List Nat := match n with
  | 0 => []
  | n+1 => 1 :: map .succ (seq n)


section Test

-- open Lean Elab Lean.PrettyPrinter Delaborator

-- syntax (name := myWith) "with " (ident " := " term),* "; " term : term
-- @[term_elab myWith]
-- def with_elab : Term.TermElab := fun stx ty => match stx with
--   | `(with $[$ns:ident := $vs:term],*; $body) => do
--     let stx <- ns.zip vs |>.foldlM (fun s (n, v) => `(let $n := $v; $(.mk s))) body
--     Term.elabTerm stx ty
--   | _ => throwUnsupportedSyntax

-- @[delab letE]
-- def delab_let : Delab := do
--   let e <- SubExpr.getExpr
--   inside_let e fun body vs => do vs.foldlM (fun s (n, v) => do
--     `(with $(mkIdent n) := $(<- delab v); $s)) (<- delab body)

end Test
