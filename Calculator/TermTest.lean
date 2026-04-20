import Mathlib.Tactic.Common
import Mathlib.Data.Vector.Basic

namespace Calculation.TermTest

open Lean

structure Env (t : Nat -> Type) (n m : Nat) where
  mk ::
  val : List.Vector (t m) n

attribute [coe] Env.val
attribute [coe] Env.mk

mutual
  inductive Tm : Nat -> Type where
    | bvar : Fin n -> Tm n
    | fvar : Name -> Tm n
    | pi : (ty : Tm n) -> Bind n -> Tm n
    | lam : (ty : Tm n) -> Bind n -> (bi : BinderInfo := .default) -> Tm n
    | letIn : (ty val : Tm n) -> Bind n -> (nondep : Bool := true) -> Tm n
    | app : Tm n -> Tm n -> Tm n
    | const : Name -> (levels : List Level := []) -> Tm n
    | lit : Literal -> Tm n

  inductive Bind : Nat -> Type where
    | bind : Name -> Tm (n + 1) -> Bind n
end

def Bind.name : Bind n -> Name
  | .bind n _ => n

def Bind.body : Bind n -> Tm (n + 1)
  | .bind _ b => b

def Env.get (env : Env t n m) (i : Fin n) : t m := env.val.get i

@[match_pattern]
def Env.nil : Env t 0 m := .mk .nil

@[match_pattern]
def Env.cons (x : t m) (xs : Env t n m) : Env t (n + 1) m :=
  .mk (List.Vector.cons x xs.val)

mutual
  def Tm.weaken : Tm n → Tm (n + 1)
    | .bvar i => .bvar i.castSucc
    | .fvar fv => .fvar fv
    | .pi ty b => .pi (Tm.weaken ty) (Bind.weaken b)
    | .lam ty b bi => .lam (Tm.weaken ty) (Bind.weaken b) bi
    | .letIn ty val b nondep => .letIn (Tm.weaken ty) (Tm.weaken val) (Bind.weaken b) nondep
    | .app x y => .app (Tm.weaken x) (Tm.weaken y)
    | .const n ls => .const n ls
    | .lit l => .lit l

  def Bind.weaken : Bind n → Bind (n + 1)
    | .bind name body => .bind name (Tm.weaken body)
end

def Env.shift (env : Env Tm n m) : Env Tm n (m + 1) :=
  .mk (env.val.map Tm.weaken)

def Env.extendBind (env : Env Tm n m) : Env Tm (n + 1) (m + 1) :=
  .cons (.bvar 0) env.shift

def Env.id (p : n <= m := by rfl) : Env Tm n m := match n with
  | 0 => .nil
  | .succ _ => .cons (.bvar (.mk 0 (Nat.zero_lt_of_lt p))) (Env.id (Nat.le_of_succ_le p))

def Env.apply (env : Env Tm n m) : Tm n → Tm m
  | .bvar i => env.get i
  | .fvar fv => .fvar fv
  | .pi ty (.bind name body) =>
      .pi (apply env ty) (.bind name (apply env.extendBind body))
  | .lam ty (.bind name body) bi =>
      .lam (apply env ty) (.bind name (apply env.extendBind body)) bi
  | .letIn ty val (.bind name body) nondep =>
      .letIn (apply env ty) (apply env val) (.bind name (apply env.extendBind body)) nondep
  | .app x y => .app (apply env x) (apply env y)
  | .const n ls => .const n ls
  | .lit l => .lit l

def Tm.sub (t : Tm n) (env : Env Tm n m) := env.apply t

def Bind.open : Bind n → Tm n
  | .bind name body => body.sub (.cons (.fvar name) .id)

#eval (.bind `x (.app (.bvar 0) (.bvar 1)) : Bind 1).open

-- Replace fvar `name` with bvar k, shifting bvars ≥ k up. k increases under each binder.
mutual
  def Tm.abstract (name : Name) (k : Fin (n + 1)) : Tm n → Tm (n + 1)
    | .fvar fv => if fv == name then .bvar k else .fvar fv
    | .bvar i => if i.val < k.val then .bvar i.castSucc else .bvar i.succ
    | .pi ty b => .pi (Tm.abstract name k ty) (Bind.abstract name k b)
    | .lam ty b bi => .lam (Tm.abstract name k ty) (Bind.abstract name k b) bi
    | .letIn ty val b nondep =>
        .letIn (Tm.abstract name k ty) (Tm.abstract name k val) (Bind.abstract name k b) nondep
    | .app x y => .app (Tm.abstract name k x) (Tm.abstract name k y)
    | .const c ls => .const c ls
    | .lit l => .lit l

  def Bind.abstract (name : Name) (k : Fin (n + 1)) : Bind n → Bind (n + 1)
    | .bind bname body => .bind bname (Tm.abstract name k.succ body)
end

def Tm.close (name : Name) (tm : Tm n) : Bind n :=
  .bind name (Tm.abstract name 0 tm)

structure Ctx (n : Nat) where
  decls : List LocalDecl
  bvars : List.Vector FVarId n
  deriving Inhabited

def Ctx.empty : Ctx 0 := { decls := [], bvars := default }

def Ctx.extend (ctx : Ctx n) (name : Name) (ty : Expr) : (Ctx (n + 1) × FVarId) :=
  let fv := FVarId.mk name
  ({ decls := (.cdecl 0 fv name ty .default .default) :: ctx.decls
     bvars := ctx.bvars.cons fv }, fv)

partial def Tm.reify (ctx : Ctx n := default) : Tm n → Expr
  | .bvar i => .bvar i
  | .fvar fv => .fvar (.mk fv)
  | .pi ty (.bind name body) =>
      let tyE := reify ctx ty
      let (ctx', _) := ctx.extend name tyE
      .forallE name tyE (reify ctx' body) .default
  | .lam ty (.bind name body) bi =>
      let tyE := reify ctx ty
      let (ctx', _) := ctx.extend name tyE
      .lam name tyE (reify ctx' body) bi
  | .letIn ty val (.bind name body) nondep =>
      let tyE := reify ctx ty
      let (ctx', _) := ctx.extend name tyE
      .letE name tyE (reify ctx val) (reify ctx' body) nondep
  | .app x y => .app (reify ctx x) (reify ctx y)
  | .const n ls => .const n ls
  | .lit l => .lit l

open Lean Elab Term Meta in
elab "tm[" t:term "]" : term => do
  let expTy ← elabTerm (← `(Tm 0)) none
  let tm ← elabTerm t expTy
  let tmVal ← unsafe Lean.Meta.evalExpr (Tm 0) expTy tm
  return tmVal.reify

#eval let u := tm[ .lam (.const ``Nat) (.bind `x (.bvar 0)) ]; u 5

#eval (.lam (.const ``List) (.bind `x (.bvar 0)) : Tm 0).reify

#eval (.letIn (.const ``Nat) (.lit (Literal.natVal 5)) (.bind `n (.bvar 0)) : Tm 0).reify

end Calculation.TermTest
