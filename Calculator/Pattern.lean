import Mathlib.Tactic.Common

namespace Tactic.Calculation

open Lean Meta Elab Term Mathlib.Tactic

/--
A pattern representation for a single argument.
-/
inductive ArgPatt where
  | var (name : Name)
  | ctor (ctorFn : Name) (ctorArgs : List ArgPatt)
  | bind (bindName bindVal : ArgPatt)
  deriving BEq, Hashable, Repr

def ArgPatt.isVar (p : ArgPatt) : Bool := match p with
  | var _ => true
  | _ => false

abbrev Patt := List ArgPatt

private def fmtPatt : (p : ArgPatt) -> Format
  | .var name => f!"{name.eraseMacroScopes}"
  | .ctor ct args =>
    let fmts := f!"{ct}" :: args.map (fmtPatt ·)
    f!"({Std.Format.joinSep fmts " "})"
  | .bind name val =>
    f!"({fmtPatt name} := {fmtPatt val})"

instance : ToFormat ArgPatt where
  format := fmtPatt

instance : ToFormat Patt where
  format p := Std.Format.joinSep (p.map format) " "

instance : ToMessageData ArgPatt := ⟨fun p => repr p⟩
instance : ToMessageData Patt := ⟨fun p => repr p⟩

abbrev NameMap a := Std.HashMap Name a

partial def unarrow (ty : Expr) : (List Expr × Expr) :=
  match ty with
  | Expr.forallE _ a b _ => let (xs, r) := unarrow b; (a :: xs, r)
  | _ => ([], ty)

partial def mkArgPatt (stx : Term) (typ? : Option Expr)
  : StateT (NameMap MVarId) Tactic.TacticM (ArgPatt × Expr) := withRef stx do
  let stx <- (liftMacroM <| expandMacros stx : Tactic.TacticM Syntax)
  match stx with
  | `($i:ident) => do
    let name := i.getId
    let mv <- mkFreshExprMVar typ?
    let hm <- get
    if name ∈ hm then
      throwErrorAt stx "Duplicate name in pattern: {name}"
    set <| hm.insert name mv.mvarId!
    return (.var name, mv)
  | `($f:term $args:term*) => do
    let arg_patts <- args.toList.mapM fun a => mkArgPatt a none
    let arg_tys <- arg_patts.mapM fun (_, e) => inferType e
    let ret_ty <- typ?.getDM (mkFreshExprMVar none)
    let fn <- elabTerm f (<- mkArrowN arg_tys.toArray ret_ty)
    let exp := mkAppN fn <| arg_patts.toArray.map (·.snd)
    let actual_ty <- inferType exp
    if !(<- isDefEq actual_ty ret_ty) then
      throwErrorAt stx "Pattern has wrong type: {actual_ty}, but expected {ret_ty}"
    let (ctor, _) := exp.getAppFnArgs
    return (.ctor ctor (arg_patts.map (·.fst)), exp)
  | `($f:term) => do
    let ret_ty <- typ?.getDM (mkFreshExprMVar none)
    let fn <- elabTerm f ret_ty
    let actual_ty <- inferType fn
    if !(<- isDefEq actual_ty ret_ty) then
      throwErrorAt stx "Pattern has wrong type: {actual_ty}, but expected {ret_ty}"
    let (ctor, _) := fn.getAppFnArgs
    return (.ctor ctor [], fn)

def mkPatt (args : List Term) (typs : List Expr)
  : Tactic.TacticM (Patt × NameMap MVarId) := do
  let m := (args.zipLeft typs).mapM fun (arg, typ?) => do
    let (q, _) <- mkArgPatt arg typ?
    return q
  m.run default

partial def Patt.matchPatt
  (ps qs : Patt)
  : StateT (NameMap Name) Tactic.TacticM Bool := do
  if ps.length ≠ qs.length then return false
  for (p, q) in ps.zip qs do
    match p, q with
    | .var pn, .var qn => do
      modify fun ns => ns.insert pn qn
    | .ctor pc (pargs : Patt), .ctor qc qargs => do
      if pc ≠ qc then return false
      if !(<- pargs.matchPatt qargs) then
        return false
    | .ctor pc [], .var qn =>
      if pc.eraseMacroScopes != qn.eraseMacroScopes then
        return false
    | .var pn, .ctor qc [] =>
      if pn.eraseMacroScopes != qc.eraseMacroScopes then
        return false
    | _, _ => return false
  return true

/--
Match a list of arguments (term syntax nodes) against a pattern, to extract a mapping
from names in the pattern `ps` to names in the arguments, and their types.
-/
partial def Patt.match (ps qs : Patt) (mvs : NameMap MVarId)
  : Tactic.TacticM (Option (NameMap (Name × Expr))) := do
  let (did?, names) <- (ps.matchPatt qs).run default
  if did? then
    let both <- names.toList.mapM fun (pn, qn) => do
      let mv := mvs.get! qn
      let ty <- mv.getType
      return (pn, qn, ty)
    return .some (.ofList both)
  else
    return none

structure ReplacementCtx where
  names : NameMap (Name × Expr)
  body : Term
  goal_name : TSyntax `ident
  goal_ty : Expr

abbrev Replacement := ReplacementCtx -> Tactic.TacticM (List MVarId)

def ReplacementCtx.fvarOf {m} [Monad m] [MonadNameGenerator m]
  (ctx : ReplacementCtx) (name : Name) (lctx : LocalContext)
  : m (FVarId × LocalContext) := do
  let fv <- mkFreshFVarId
  let (name', ty) := ctx.names.get! name
  let lctx' := lctx.mkLocalDecl fv name' ty
  return (fv, lctx')

structure Pattern where
  fname : Name
  fmv : MVarId
  endpointMv : MVarId
  ps : Patt
  repl : Replacement

instance : ToFormat Pattern where
  format p := f!"{p.fname} {p.ps}"

instance : BEq Pattern where
  beq p q := p.fname == q.fname
    && p.ps == q.ps
    && p.fmv == q.fmv
    && p.endpointMv == q.endpointMv

instance : Hashable Pattern where
  hash p := hash (p.fmv, p.fname, p.ps)

abbrev PatternMap := Std.HashSet Pattern

def PatternMap.find? (patts : PatternMap)
  (fmv : MVarId) (args : List Term) (typs : List Expr)
  : Tactic.TacticM (Option (Pattern × NameMap (Name × Expr))) := do
  let (qs, mvs) <- mkPatt args typs
  let patts := patts.filter fun p => p.fmv == fmv
  for patt in patts do
    if patt.ps.length ≠ qs.length then
      return none
    if let some names <- patt.ps.match qs mvs then
      return some (patt, names)
  if qs.all (·.isVar) then
    -- Finally, if we didn't find any explicit matches, then we can use
    -- a default pattern for a function.
    if <- fmv.isAssigned then
      return none
    let ty <- fmv.getType''
    let tag <- fmv.getTag
    let (args, retTy) := unarrow ty
    if args.length != mvs.size then
      return none
    let some names <- qs.match qs mvs
      | throwError "Internal: pattern {qs} didn't match against itself!"
    let pattern := {
      fname := tag, fmv := fmv, endpointMv := fmv, ps := qs
      repl := fun ctx => do
        let mut lctx <- getLCtx
        let mut fvs := #[]
        for (argty, q) in args.zip qs do
          let .var qv := q | unreachable!
          let fv <- mkFreshFVarId
          fvs := fvs.push (Expr.fvar fv)
          lctx := lctx.mkLocalDecl fv qv argty
        let fn <- withLCtx' lctx do
          let body <- Term.elabTermEnsuringType ctx.body retTy
          mkLambdaFVars fvs body
        fmv.assignIfDefEq fn
        return []
    }
    return some (pattern, names)
  return none

initialize
  patternsRef : IO.Ref PatternMap <- IO.mkRef {}

def findMatch? (fmv : MVarId) (args : List Term) (typs : List Expr)
  : Tactic.TacticM (Option (Pattern × NameMap (Name × Expr))) := do
  let patts <- patternsRef.get
  patts.find? fmv args typs

end Tactic.Calculation
