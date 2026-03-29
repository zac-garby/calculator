import Mathlib.Tactic.Common

namespace Tactic.Calculation

open Lean Meta Elab Term Mathlib.Tactic

partial def unarrow (ty : Expr) : (List Expr × Expr) := match ty.arrow? with
  | some (a, b) => let (xs, r) := unarrow b; (a :: xs, r)
  | none => ([], ty)

/--
A pattern representation for a single argument.
-/
inductive ArgPatt where
  | var (name : Name)
  | ctor (ctorFn : Name) (ctorArgs : List ArgPatt)
  | bind (bindName bindVal : ArgPatt)
  deriving Repr

private partial def argPattEq (p q : ArgPatt) : Bool := match p, q with
  | .var _a, .var _b => true
  | .ctor pc pargs, .ctor qc qargs
    => pc == qc && (pargs.zip qargs |>.all (Function.uncurry argPattEq))
  | .bind pn pv, .bind qn qv
    => argPattEq pn qn && argPattEq pv qv
  | _, _ => false

private def argPattHash (p : ArgPatt) : UInt64 := match p with
  | .var _ => hash "name"
  | .ctor n args => let args' := args.map argPattHash; hash (n, args')
  | .bind n v => hash (argPattHash n, argPattHash v)

instance : BEq ArgPatt where beq := argPattEq
instance : Hashable ArgPatt where hash := argPattHash

def ArgPatt.isVar (p : ArgPatt) : Bool := match p with
  | var _ => true
  | _ => false

/-- Replace all occurrences of `.var varName` with `replacement` in a pattern. -/
partial def ArgPatt.replace (varName : Name) (replacement : ArgPatt) : ArgPatt → ArgPatt
  | .var n => if n == varName then replacement else .var n
  | .ctor c args => .ctor c (args.map (ArgPatt.replace varName replacement))
  | .bind n v => .bind (ArgPatt.replace varName replacement n)
                       (ArgPatt.replace varName replacement v)

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

partial def mkArgPatt (stx : Term) (typ? : Option Expr)
  : StateT (NameMap MVarId) Tactic.TacticM (ArgPatt × Expr) := withRef stx do
  let stx <- (liftMacroM <| expandMacros stx : Tactic.TacticM Syntax)
  -- Named argument: (h := true) / (h := false) — branch selector syntax.
  -- namedArgument node layout: #[atom "(", ident, atom ":=", term, atom ")"]
  if stx.getKind == `Lean.Parser.Term.namedArgument then
    let name : TSyntax `ident := ⟨stx[1]!⟩
    let val : Term := ⟨stx[3]!⟩
    let (valPatt, valExpr) <- mkArgPatt val none
    return (.bind (.var name.getId) valPatt, valExpr)
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

mutual
partial def ArgPatt.match (p q : ArgPatt)
  : OptionT (StateM (NameMap Name)) Unit := do
  match p, q with
  | .var pn, .var qn =>
    modify fun ns => ns.insert pn qn
  | .ctor pc (pargs : Patt), .ctor qc qargs =>
    -- Either may be partially qualified; use suffix matching in both directions
    guard (pc == qc || qc.isSuffixOf pc || pc.isSuffixOf qc)
    pargs.matchPatt qargs
  | .ctor pc [], .var qn =>
    -- qn may be partially qualified (e.g. `Colour.Red`) while pc is fully qualified
    -- (e.g. `Tactic.Calculation.Colour.Red`). Use suffix matching.
    guard (qn.eraseMacroScopes.isSuffixOf pc.eraseMacroScopes)
  | .var pn, .ctor qc [] =>
    guard (pn.eraseMacroScopes.isSuffixOf qc.eraseMacroScopes)
  | .bind pn pv, .bind qn qv =>
    pn.match qn
    pv.match qv
  | _, _ => failure

partial def Patt.matchPatt (ps qs : Patt)
  : OptionT (StateM (NameMap Name)) Unit := do
  guard (ps.length == qs.length)
  _ <- ps.zipWithM (·.match) qs
end

/--
Match a list of arguments (term syntax nodes) against a pattern, to extract a mapping
from names in the pattern `ps` to names in the arguments, and their types.
-/
partial def Patt.match (ps qs : Patt) (mvs : NameMap MVarId)
  : Tactic.TacticM (Option (NameMap (Name × Expr))) := do
  if let (some (), names) := (ps.matchPatt qs).run default then
    let both <- names.toList.filterMapM fun (pn, qn) => do
      if let some mv := mvs.get? qn then
        let ty <- mv.getType
        return some (pn, qn, ty)
      else
        return none
    return .some (.ofList both)
  else
    return none

structure MatchCtx where
  ps : Patt
  names : NameMap (Name × Expr)
  body : Term
  goal_name : TSyntax `ident
  goal_ty : Expr

abbrev Refinement := MatchCtx -> Tactic.TacticM MVarId
abbrev Transformer := MatchCtx -> Term -> Tactic.TacticM Term

instance : Inhabited Transformer where
  default _ctx tm := return tm

def ReplacementCtx.fvarOf {m} [Monad m] [MonadNameGenerator m]
  (ctx : MatchCtx) (name : Name) (lctx : LocalContext)
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
  refine : Refinement
  transform : Transformer := default

instance : ToFormat Pattern where
  format p := f!"{p.fname} {p.ps}"

instance : BEq Pattern where
  beq p q := p.fname == q.fname
    && p.ps == q.ps
    && p.fmv == q.fmv
    && p.endpointMv == q.endpointMv

instance : Hashable Pattern where
  hash p := hash (p.fmv, p.fname, p.ps, p.endpointMv)

abbrev PatternMap := Std.HashSet Pattern

initialize
  patternsRef : IO.Ref PatternMap <- IO.mkRef {}

def PatternMap.insert (pattern : Pattern) : MetaM Unit := do
  patternsRef.modify fun (pm : Std.HashSet _) => pm.insert pattern
    -- Erase before insert so that re-elaboration (which resets mvar ID counters and
  -- may produce the same (fname, ps, fmv) triple) replaces the stale entry rather
  -- than leaving the old one with a dead endpointMv in the map.
  -- patternsRef.modify fun (pm : Std.HashSet _) =>
  --   (pm.erase pattern).insert pattern

private def refineTakeArgs
  (names : List Name)
  (goal : MVarId)
  : Refinement := fun _ctx => do
  let mut goal := goal
  for old in names do
    let (_fv, goal') <- goal.intro old
    -- Clear userName so the new mvar doesn't collide with the parent's userName
    -- in findCalcTarget lookups (MVarId.intro inherits the parent's userName).
    goal'.setUserName .anonymous
    goal := goal'
  return goal

-- let mut goal := goal
--   let tag <- goal.getTag
--   let (argTys, retTy) <- goal.getType <&> unarrow
--   let (args, argTys') := names.zipLeft' argTys
--   let retTy' <- mkArrowN argTys'.toArray retTy
--   let (fn, hole) <- goal.withContext <| do
--     let body <- mkFreshExprMVar retTy' (userName := tag.str "body")
--     let mut hole := body.mvarId!
--     let fvs <- args.mapM fun (name, ty) => do
--       let some ty := ty | throwError "Too many arguments given!"
--       let fv <- hole.withContext <|
--         mkFreshExprMVar ty (userName := name)
--       -- let hole' <- hole.define name ty fv
--       -- logInfo m!"hole' = {hole'}"
--       hole.modifyLCtx fun lctx => lctx.mkLocalDecl fv.fvarId! name ty
--       pure fv
--     -- for (name, fv) in names.zip fvs do
--     --   let (fv', hole') <- hole.let name fv
--     --   hole := hole'

--     -- let mut fvs' := #[]
--     --   fvs' := fvs'.push (.fvar fv')
--     -- logInfo m!"make fn from {fvs'} and {hole}"
--     let fn <- mkLambdaFVars fvs.toArray (.mvar hole)
--     logInfo m!"fn = {fn}"
--     logInfo s!"fn = {fn}"
--     return (fn, hole)
--   goal.assign fn
--   return hole
--   -- for old in names do
--   --   let (_fv, goal') <- goal.intro old
--   --   -- Clear userName so the new mvar doesn't collide with the parent's userName
--   --   -- in findCalcTarget lookups (MVarId.intro inherits the parent's userName).
--   --   let tag <- goal'.getTag
--   --   goal'.setUserName (tag ++ old)
--   --   do
--   --     logInfo m!"intro'd {old} in goal \
--   --     (= {Expr.mvar goal}) assigned?{<- goal.isAssigned}:\n{goal}\n  \
--   --     to goal' (= {Expr.mvar goal'}) assigned?{<- goal'.isAssigned}:\n{goal'}\n  \
--   --   we have fv: {_fv.name}"
--   --   goal := goal'
--   -- return goal

private def mkTakeArgsPattern (fmv : MVarId) (names? : Option (List Name) := none)
  : MetaM (Option Pattern) := do
  if <- fmv.isAssigned then
    return none
  let ty <- fmv.getType''
  let tag <- fmv.getTag
  let (args, _) := unarrow ty
  let un <- getUnusedUserName (.mkStr1 "x")
  let names := names?.getD <| args.mapIdx fun i _exp => un.appendIndexAfter i
  let qs := names.map (.var ·)
  let pattern : Pattern := {
    fname := tag, fmv := fmv, endpointMv := fmv, ps := qs
    refine := refineTakeArgs names fmv
  }
  return pattern

def PatternMap.find?
  (fmv : MVarId) (args : List Term) (typs : List Expr)
  : Tactic.TacticM (Option (Pattern × NameMap (Name × Expr))) := do
  let patts <- patternsRef.get
  let (qs, mvs) <- mkPatt args typs
  let patts := patts.filter fun p => p.fmv == fmv
  for patt in patts do
    if patt.ps.length == qs.length then
      if let some names <- patt.ps.match qs mvs then
        return some (patt, names)
        -- Skip stale entries whose endpoint has already been assigned or is no longer declared
    -- (mirrors the check in allPatterns, guards against leftover entries from prior elaborations)
    -- if !(<- patt.endpointMv.isDeclared) || (<- patt.endpointMv.isAssignedOrDelayedAssigned) then
    --   continue
    -- if let some names <- patt.ps.match qs mvs then
    --   return some (patt, names)
  if qs.all (·.isVar) then
    let some names <- qs.match qs mvs
      | throwError "Internal: pattern {qs} didn't match against itself!"
    if let some pattern <- mkTakeArgsPattern fmv names.keys then
      return some (pattern, names)
  return none

def allPatterns (fmv : MVarId) : Tactic.TacticM (List Pattern) := do
  let ps <- patternsRef.get
  let mut all := []
  for pattern in ps do
    if pattern.fmv != fmv then continue
    let endpoint := pattern.endpointMv
    if (<- endpoint.isDeclared) && !(<- endpoint.isAssignedOrDelayedAssigned) then
      all := all.concat pattern
  if all.isEmpty then
    if let some default <- mkTakeArgsPattern fmv then
      return [default]
  return all

def PatternMap.findMatch (fmv : MVarId) (args : List Term) (typs : List Expr)
  (pattRef? : Option Term := none)
  : Tactic.TacticM (Pattern × NameMap (Name × Expr)) := do
  if let some (pattern, names) <- find? fmv args typs then
    return (pattern, names)
  else
    if let some p := pattRef? then
      throwErrorAt p "No matching 'give' definition pattern found, \
        for pattern: {indentD p}\n\
        It may already have been assigned."
    else
      throwError "No matching 'give' definition pattern found."

def subSimul (names : NameMap Name) (lctx : LocalContext) : LocalContext :=
  let names := names.toList
  let decls := names.map fun (old, _) => lctx.findFromUserName? old
  (decls.zip names).foldl (init := lctx) fun lctx (decl, _old, new) =>
    match decl with
    | none => lctx
    | some decl =>
      let decl := decl.setUserName new
      { lctx with
        fvarIdToDecl := lctx.fvarIdToDecl.insert decl.fvarId decl,
        decls := lctx.decls.set decl.index decl }

end Tactic.Calculation
