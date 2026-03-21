import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive
import Calculator.Pattern

namespace Lean

def Name.recOf (name f : Name) := f ++ name

end Lean

namespace Tactic.Calculation

set_option linter.hashCommand false
set_option linter.style.setOption false
set_option pp.fieldNotation false

open Option List Lean
  Meta Elab Term Macro Qq
  Mathlib.Tactic Tactic
  PrettyPrinter.Delaborator SubExpr

macro "don't" "care" : term => `(panic! "found out the hard way that we do actually care")

elab "todo" : tactic => return ()
elab "todo" "[" term "]" : tactic => return ()
def no_proof := "todo"

def calc_name (name : Name) : Name
  := name
  where pre := Name.str .anonymous "ℂ"

def match_struct_fields (goal_type : Expr)
  : MetaM (Array Expr × Array (Name × Expr)) := do
  matchConstStructure goal_type.getAppFn
    (fun _ => do throwError "Target {<- ppExpr goal_type} is not a structure")
    fun ival us ctor => do
      let sinfo := getStructureInfo (<- getEnv) ival.name
      let fields := sinfo.fieldNames
      let mut type <- instantiateTypeLevelParams ctor.toConstantVal us
      let mut params : Array Expr := #[]
      for _ in *...ctor.numParams do
        let .forallE _ d b _ := type | throwError "Unexpected constructor type"
        let param <- mkFreshExprMVar d
        params := params.push param
        type := b.instantiate1 param
      let mut field_mvars := #[]
      for _ in fields do
        let .forallE arg_name d b bi := type | throwError "Unexpected constructor type"
        if bi.isImplicit then throwError "Unexpected implicit param {arg_name}"
        let mvar <- mkFreshExprMVar d
        field_mvars := field_mvars.push (arg_name, mvar)
        type := b.instantiate1 mvar
      if !(<- isDefEq type goal_type) then
        throwError "Oops, somehow constructed the wrong structure type {<- ppExpr type}"
      return (params, field_mvars)

def refold_def (fn within : Expr) : MetaM Expr := do
  Meta.transform within
    fun e => do
      let fn_args := (<- whnf fn).getAppArgs
      let rem := e.getAppNumArgs - fn_args.size
      let bs := e.getBoundedAppArgs rem
      let e_fn := e.getBoundedAppFn rem
      if <- isDefEq e_fn (<- whnf fn) then
        return .done (mkAppN fn bs)
      return .continue

-- finds 'name' in the local LCtx, so make sure you're in context
def unroll_def (name : Name) (target : Expr) : MetaM Expr := do
  let ctx <- getLCtx
  let (some decl) := ctx.findFromUserName? name | throwError m!"No assumption with name: {name}"
  let search_fn := decl.toExpr
  Meta.transform target fun e => do
    if e.getAppFn' != search_fn then return .continue
    let e' <- whnf e
    let back <- refold_def search_fn e'
    return .done back

elab (name := byDefTactic) "unroll" v:ident : tactic => Tactic.withMainContext do
  let target <- Tactic.getMainTarget
  let new <- unroll_def v.getId target
  let goal <- Tactic.getMainGoal
  let new_goal <- goal.replaceTargetDefEq new
  Tactic.replaceMainGoal [new_goal]

elab (name := refoldTactic) "refold" v:ident : tactic => Tactic.withMainContext do
  let target <- Tactic.getMainTarget
  let name := v.getId
  let ctx <- getLCtx
  let (some decl) := ctx.findFromUserName? name | throwError m!"No assumption with name: {name}"
  let search_fn := decl.toExpr
  let new <- refold_def search_fn target
  let goal <- Tactic.getMainGoal
  let new_goal <- goal.replaceTargetDefEq new
  Tactic.replaceMainGoal [new_goal]

def stx_from_names (names : List Name) : TSyntaxArray `ident
  := TSyntaxArray.mk <| .mk <| names.map fun n => mkIdent n

def get_rec_name (n : Name) : Name := .mkSimple s!"rec.{n}"

def desugar_clause_args (inp_ty : Expr) (con_args : List Name) (clause_args : List Expr)
  : MetaM (List Name)
  := do
  let rec_con_args <- rec_args (zip con_args clause_args)
  return con_args ++ rec_con_args
  where
    rec_args (cds : List (Name × Expr)) : MetaM (List Name) := match cds with
    | [] => pure []
    | (n, t) :: cds => do
      let ct <- inferType t
      if <- isDefEq ct inp_ty then
        return get_rec_name n :: (<- rec_args cds)
      else
        rec_args cds

def desugar_clause_def
  (clause_of : Name)
  (clause inp_ty : Expr)
  (con_args rest_args : List Name) -- the args for the recursor, but without the IH's
  (to_term : TSyntax `term)
  : TacticM Expr := do
  -- Look up the function mvar directly so we don't depend on it being in
  -- scope in the current goal's local context (sub-goals created by
  -- apply/refine don't inherit the calculate let-binding).
  let clause_ty <- inferType clause
  let (clause_args, _, _) <- forallMetaTelescopeReducing clause_ty
  let ns <- desugar_clause_args inp_ty con_args clause_args.toList
  let body_node : TSyntax `term <- `(fun $(stx_from_names (ns ++ rest_args))* => $to_term)
  let body_node_rw <- body_node.raw.rewriteBottomUpM fun
    | stx@`($f:ident $arg0:term $args:term*) => do
      if f.getId == clause_of then
        let `($arg_id:ident) := arg0
          | throwErrorAt arg0 "Can't make recursive call on non-variable-name argument"
        let arg_name := arg_id.getId
        let rec_name := get_rec_name arg_name
        `($(mkIdent rec_name) $args*)
      else
        return stx
    | s => pure s
  let body_fn <- Term.elabTerm body_node_rw (some clause_ty)
  return body_fn

/-- For each calc fvar (`let name := ?mv` in the main goal's lctx) that appears in `e`,
    add a corresponding let-binding to `clauseMv`'s local context.
    Returns the updated mvar and `e` with the outer fvars replaced by the new local ones.
    This keeps field names (like `ins`) visible by name in sub-goals rather than unfolding
    to the raw (possibly partially-assigned) mvar. -/
def liftCalcFvarsIntoClause (clauseMv : MVarId) (e : Expr)
    : TacticM (MVarId × Expr) :=
  Tactic.withMainContext do
    let lctx <- getLCtx
    let clauseDecl <- clauseMv.getDecl
    let calcBindings := lctx.decls.toList.filterMap fun d? => do
      let d <- d?
      guard d.isLet
      let val <- d.value?
      guard val.isMVar
      guard (e.containsFVar d.fvarId)
      -- Skip fvars already in the clause mvar's lctx — they're valid as-is.
      guard (! clauseDecl.lctx.contains d.fvarId)
      some d
    if calcBindings.isEmpty then return (clauseMv, e)
    let mut mv := clauseMv
    let mut oldFVars : Array Expr := #[]
    let mut newFVars : Array Expr := #[]
    for d in calcBindings do
      let some val := d.value? | continue
      -- Extend the clause mvar's local context directly. We avoid `define` + `intro1P`
      -- because `whnfD` reduces `let x := v; T` to `T` when x ∉ T, causing `intro1P`
      -- to introduce the wrong thing (the first ∀ of T instead of the let-binding).
      let decl <- mv.getDecl
      let newFVarId <- mkFreshFVarId
      let newLctx := decl.lctx.mkLetDecl newFVarId d.userName d.type val false
      let newMv <- mkFreshExprMVarAt newLctx decl.localInstances decl.type decl.kind (← mv.getTag)
      mv.assign newMv
      mv := newMv.mvarId!
      oldFVars := oldFVars.push (.fvar d.fvarId)
      newFVars := newFVars.push (.fvar newFVarId)
    return (mv, e.replaceFVars oldFVars newFVars)

partial def define_mv (bind_name : Name) (to_expr : Expr) : TacticM Unit :=
  go bind_name
where
  go (name : Name) : TacticM Unit := do
    let mctx <- getMCtx
    match mctx.findUserName? name with
    | none =>
      if name == bind_name then throwUnknownNameWithSuggestions bind_name
      else throwError m!"{bind_name} is already fully defined (no 'else' slot available)"
    | some mv => do
      if (<- mv.getTag) == name then do
        if <- mv.isAssigned then
          -- Redirect to the chained else-mvar introduced by 'define only'
          go (Name.str name "else")
        else
          let (mv', to_expr') <- liftCalcFvarsIntoClause mv to_expr
          mv'.withContext do mv'.assignIfDefEq to_expr'

def count_implicit_args (ty : Expr) : Nat := match ty with
  | .forallE _ _ b .implicit => 1 + count_implicit_args b
  | .lam _ _ b .implicit => 1 + count_implicit_args b
  | _ => 0

def count_args (ty : Expr) : Nat := match ty with
  | .forallE _ _ b _ => 1 + count_args b
  | .lam _ _ b _ => 1 + count_args b
  | _ => 0

partial def get_id (stx : Syntax) : Option Name := match stx.getKind with
  | `ident => pure stx.getId
  | ``Lean.Parser.Term.dotIdent => get_id stx[1]
  | ``Lean.Parser.Term.explicit => get_id stx[1]
  | ``Lean.Parser.Term.hole => some (.str .anonymous "_")
  | _ => none

def collect_ctor_pattern (stx : Syntax) : TermElabM (Syntax × Array Name) := do
  if let some _ := get_id stx then
    return (stx, #[])
  else if stx.getKind == ``Lean.Parser.Term.app then
    let (fn, #[], args, false) <- expandApp stx
      | throwErrorAt stx "Invalid constructor application here"
    let arg_names <- args.mapM fun
      | .stx s => match get_id s with
        | some name => pure name
        | none => throwErrorAt s "Unexpected non-ident constructor argument: {s.getKind}"
      | _ => unreachable!
    return (fn, arg_names)
  else
    throwErrorAt stx "Unexpected syntax in pattern: {stx.getKind.toString}"

def inhabit_mv (mv : MVarId) : MetaM Bool := do
  let ty <- mv.getType
  let inst_ty <- mkAppM ``Inhabited #[ty]
  if let some inst <- synthInstance? inst_ty then
    let e <- mkAppOptM ``Inhabited.default #[ty, inst]
    mv.assignIfDefEq e
    return true
  else
    return false

/-- Parse `rest` args into `(binder name, optional pattern)` pairs. -/
def parseRestArgs (rest : TSyntaxArray `term)
    : TacticM (List (Name × Option (TSyntax `term))) :=
  rest.toList.mapM fun s => do
    match s.raw with
    | `($i:ident) => pure (i.getId, none)
    | _ => return (← mkFreshUserName (.mkSimple "arg"), some ⟨s.raw⟩)

/-- Wrap `body` in `match` expressions for each pattern arg in `restInfo`.
    With `is_partial`, non-matching arms become `?holeId` (first pattern arg)
    or `don't care` (subsequent ones). -/
def wrapBodyInMatches
    (restInfo : List (Name × Option (TSyntax `term)))
    (is_partial : Bool)
    (firstPatName? : Option Name)
    (holeId : Ident)
    (body : TSyntax `term)
    : TacticM (TSyntax `term) :=
  restInfo.foldrM (fun (name, pat?) acc => do
    match pat? with
    | none => pure acc
    | some pat =>
      let nameId : Ident := mkIdent name
      if is_partial then
        let elseArm : TSyntax `term <-
          if firstPatName? == some name then `(?$holeId:ident)
          else `(don't care)
        `(match $nameId:ident with | $pat:term => $acc | _ => $elseArm)
      else
        `(match $nameId:ident with | $pat:term => $acc))
  body

/--
Provides a (partial) definition of a function being calculated.

* `define foo (.con x y) a b = ...` provides a definition for the `.con` constructor
  case of the function `foo`.

  There must be a metavariable named `foo.con`, typically arising
  from `refine foo => apply MyType.rec`.

* `define only ...` does the same thing, but doesn't automatically close the current
  goal.

* `define total ...` don't allow partial pattern matching on subsequent (non-recursive)
  arguments.
-/
elab (name := defineTactic)
  "define" only:("only")? tot:("total")? p:term " := " to_term:term : tactic
  => do
  let main_goal <- Tactic.withMainContext Tactic.getMainGoal
  let mctx <- Tactic.withMainContext getMCtx
  let is_only := only.isSome
  let is_partial := !tot.isSome
  match p with
  | `($f:ident) => do
    let (some mv) := mctx.findUserName? f.getId
      | throwErrorAt f "The name {f.getId} is undefined"
    let mv_ty <- mv.getType''
    let to_expr <- Term.elabTerm to_term (some mv_ty)
    define_mv f.getId to_expr
  | `($f:ident $pat:term $rest*) => do
    let (some search_fn_mv) := mctx.findUserName? f.getId
      | throwErrorAt f "The name {f.getId} is undefined"
    let some (inp_ty, _) := (<- search_fn_mv.getType'').arrow?
      | throwErrorAt f "Unexpected argument in definition of non-function {f}"
    -- Expand the constructor pattern to get constructor name and arg names.
    let pat <- liftMacroM <| expandMacros pat
    let (con_stx, con_arg_names) <- collect_ctor_pattern pat
    let con <- Term.elabTerm con_stx (some inp_ty)
    let (con_fn, _) := con.getAppFnArgs
    let con_arg_names := con_arg_names.drop (count_implicit_args (<- inferType con))
    let clause_name <- match con_fn with
    | .str _ con_name => pure (Name.str f.getId con_name)
    | _ => throwErrorAt pat "Expected a constructor, but got {con_fn}"
    let some clause_expr := (<- getMCtx).findUserName? clause_name |> (·.map (Expr.mvar ·))
      | throwErrorAt f "Unknown defining clause for {f}, for pattern: {pat}"
    let restInfo <- parseRestArgs rest
    let rest_names := restInfo.map (·.fst)
    -- Whether any rest arg uses a pattern (vs plain ident).
    let hasPatternArgs := restInfo.any (·.snd.isSome)
    -- First pattern arg's else arm gets a named hole; subsequent ones use `don't care`.
    let firstPatName? := restInfo.findSome? fun (n, p?) => if p?.isSome then some n else none
    let else_clause_name := Name.str clause_name "else"
    -- Use a fresh uniquely-named hole for the outermost else arm in 'define only'.
    -- We name it so we can look it up in the mctx by userName after elaboration.
    let hole_user_name <- if /- is_only && -/ hasPatternArgs
        then mkFreshUserName `else
        else pure .anonymous
    let holeId : Ident := mkIdent hole_user_name
    -- Wrap to_term in match expressions for all pattern args.
    let to_term' <- wrapBodyInMatches restInfo is_partial firstPatName? holeId to_term
    -- Capture outer lctx (before lambda binders are added by desugar_clause_def).
    let outer_lctx <- Tactic.withMainContext getLCtx
    -- construct a new function, 'fn', to define as the body
    let fn <- Tactic.withMainContext <| desugar_clause_def
      f.getId clause_expr inp_ty
      con_arg_names.toList rest_names to_term'
    -- When 'define partial is used with pattern args, post-process fn to replace
    -- the named hole ?holeName with `(else_mv arg₁ arg₂ ...)`.
    -- We do this inside Meta.transform so the lambda binders are fresh FVars that
    -- get re-abstracted to de Bruijn by the transform — no dangling FVar refs.
    let fn' <- if is_partial && hasPatternArgs then Tactic.withMainContext do
      let mctx <- getMCtx
      let some hole_mv_id := mctx.findUserName? hole_user_name
        | throwError m!"internal: 'define' hole mvar not found named '{hole_user_name}'"
      -- If the hole is inhabited, then we just use the default value for it, since it
      -- doesn't matter anyway.
      if <- inhabit_mv hole_mv_id then
        return fn
      -- Collect clause arg types for matching against lambda binder FVars.
      let clause_ty <- inferType clause_expr
      let mut clause_arg_types : Array Expr := #[]
      let mut peel_ty := clause_ty
      while peel_ty.isForall do
        let .forallE _ arg_ty body _ := peel_ty | break
        clause_arg_types := clause_arg_types.push arg_ty
        peel_ty := body
      -- Create else_mv so it exists as a mvar ref in the resulting fn'.
      let else_mv <- mkFreshExprMVar clause_ty (userName := else_clause_name)
      -- Replace the hole with (else_mv binder_fvar_c binder_fvar_arg ...).
      -- Meta.transform opens each lambda with fresh FVars, then re-abstracts them
      -- to .bvar N — so the result is a closed de Bruijn expression.
      Tactic.appendGoals [hole_mv_id]
      Meta.transform fn (fun e => do
        if let .mvar mv := e then
          if mv == hole_mv_id then
            let lctx <- getLCtx
            -- Lambda binder FVars = those in current lctx not in the outer (main goal) lctx.
            let binders := (lctx.decls.toList.filterMap fun d? =>
              d?.filter fun d => !outer_lctx.contains d.fvarId).toArray
            let mut used := Array.replicate binders.size false
            let mut apply_fvars : Array Expr := #[]
            for arg_ty in clause_arg_types do
              let mut found : Option (Nat × Expr) := none
              for i in [:binders.size] do
                if !used[i]! then
                  let d_ty <- inferType binders[i]!.toExpr
                  if <- isDefEq d_ty arg_ty then
                    found := some (i, binders[i]!.toExpr)
                    break
              match found with
              | some (i, e) =>
                apply_fvars := apply_fvars.push e
                used := used.set! i true
              | none =>
                throwError m!"Internal: no binder FVar of type {<- ppExpr arg_ty} for else-arm"
            return .done (mkAppN else_mv apply_fvars)
        return .continue)
    else pure fn
    define_mv clause_name fn'
    if !is_only then
      main_goal.withContext do
        Tactic.evalTactic (<- `(tactic| try rfl))
  | _ => throwUnsupportedSyntax

declare_syntax_cat give_mode
syntax "as"  ident+ : give_mode
syntax "as?" ident* : give_mode

declare_syntax_cat give_by
syntax "recursion" : give_by
syntax "cases" : give_by -- Still use recursor, probably
syntax "if " Parser.Term.matchDiscr : give_by
syntax "intro " ident* : give_by

/--
Refine a metavariable by applying a tactic.

Typically used in calculations, for instance:

  ```lean
  calculate comp
  give comp => apply Exp.rec
  ```

`calculate comp` introduces a metavar named `comp`, which is then refined
into a recursive definition with a new metavar for each constructor's case.
-/
syntax (name := giveTactic)
  "give" ident binderIdent* (give_mode)? " => " tacticSeq : tactic
@[inherit_doc giveTactic] syntax (name := giveAskTactic)
  "give?" ident : tactic
@[inherit_doc giveTactic] syntax (name := giveDefTactic)
  "give" term " := " term : tactic
@[inherit_doc giveTactic] syntax (name := giveByTactic)
  "give" term " by " give_by : tactic

#allow_unused_tactic! giveTactic
#allow_unused_tactic! giveAskTactic
#allow_unused_tactic! giveDefTactic
#allow_unused_tactic! giveByTactic

/- Should support:
 * define f x y := body
  -> give f => intros x y; exact body
 * define f (.ctor a b) x y := body
  ->

Maybe we need extra metadata, so like
 * by_recursion f
  -> give f => apply <Type>.rec
    but also, registers the patterns somewhere: e.g.
    f [] ⋯ := body
     => f.nil ⋯ := body
    f (a :: as) ⋯ := body
     => f.cons a as f.as ⋯ := body [f as ⋯ -> f.as ⋯]
 * by_condition f x y z => h : c
  -> give f => refine fun x y z => if h : c then blank else blank
     registers patterns:
     f x y z (h = true) := body
      => f x y z
     f x y z (h = false) := body
  (h : c is a matchDiscr parser type)

Example

* calculate f   (f : Nat -> List Nat -> Nat -> List Nat)
  - Patterns: [f * * *]
  by_recursion f n xs at xs
  - Patterns: [f * [] *, f * (* :: *) *]
  by_condition f n [] m => h : n = m
  - Patterns: [
      f * [] * (* := true),
      f * [] * (* := false),
      f * (* :: *) *
    ]
  define f x [] y (h := true) := ...
  - Patterns: [
      f * [] * (* := false),
      f * (* :: *) *
    ]
-/

private def elabGiveExact
  (v : Name) (val : Expr)
  : TacticM Unit := do
  let mctx <- getMCtx
  let some mv := mctx.findUserName? v
    | throwError "Unknown goal called '{v}'"
  -- If the named mv isn't a goal already, then make it one
  let goals <- Tactic.getGoals
  let already_goal <- goals.anyM (fun g => do return (<- g.getTag) = v)
  if !already_goal then
    Tactic.appendGoals [mv]
  -- Then, evaluate the tactic over it, finding it in the goals list
  let goals <- Tactic.getGoals
  let some goal <- goals.findM? fun goal => do return v = (<- goal.getTag)
    | unreachable!
  let actualTy <- inferType val
  let goalTy <- goal.getType
  if !(<- isDefEq actualTy goalTy) then
    throwTacticEx `give goal m!"Wrong type given for {v}. \
    expected: {indentD goalTy}\n\
    but got {indentD actualTy}"
  if <- goal.isAssigned then
    throwError "Already assigned the calculation target '{v}'"
  goal.assignIfDefEq val
  Tactic.evalTactic (<- `(tactic| try refold $(mkIdent v)))

private def showLCtx (lctx : Option LocalContext := none) : MetaM Format := do
  let lctx := lctx.getD (<- getLCtx)
  let msg := Std.Format.join <| intersperse f!"\n  "
    (<- lctx.decls.toList.flatMap (·.toList) |>.mapM fun d =>
      return f!"* ({d.fvarId.name}) {d.userName} : {<- ppExpr d.type}")
  return f!"lctx:\n  \
  {msg}"

private def elabGiveDef (p to_term : Term) : TacticM Unit
  := Tactic.withMainContext do
  let mctx <- getMCtx
  match p with
  | `($f:ident) => do
    let (some mv) := mctx.findUserName? f.getId
      | throwErrorAt f "No calculation target found: '{f.getId}'"
    let mv_ty <- mv.getType''
    let to_expr <- Term.elabTerm to_term (some mv_ty)
    -- define_mv f.getId to_expr
    elabGiveExact f.getId to_expr
  | `($f:ident $rest*) => do
    let (some mv) := mctx.findUserName? f.getId
      | throwErrorAt f "No calculation target found: '{f.getId}'"
    let mv_ty <- mv.getType''
    let (args, _) := unarrow mv_ty
    let (qs, _mvs) <- mkPatt rest.toList args
    let (pattern, names) <- findMatch mv rest.toList args (pattRef? := p)
    let ctx := {names, body := to_term, goal_name := f, goal_ty := mv_ty, ps := qs}
    withRef to_term <| do
      let hole <- pattern.refine ctx
      hole.withContext do
        let to_term' <- pattern.transform ctx to_term
        -- Rename the local variables according to the names
        -- given in the pattern.
        let mut tempLCtx <- getLCtx
        tempLCtx := subSimul (names.map fun _ (old, _) => old) tempLCtx
        for (old, new, _ty) in ctx.names do
          tempLCtx := tempLCtx.renameUserName (old.recOf f.getId) (new.recOf f.getId)
        let val <- withLCtx' tempLCtx do
          Tactic.elabTermEnsuringType to_term' (<- hole.getType)
        hole.assignIfDefEq val
  | _ => do
    throwUnsupportedSyntax

private def elabGive
  (v : TSyntax `ident) (args : TSyntaxArray `Lean.binderIdent)
  (asIds : TSyntaxArray `ident)
  (tac : TSyntax `Lean.Parser.Tactic.tacticSeq)
  (keepGoals : Bool := false)
  (mv? : Option MVarId := none)
  : TacticM (List MVarId) := do
  let id := calc_name v.getId
  let ids := asIds.toList.map (·.getId)
  let goals <- Tactic.getGoals
  let mut already_goal := true
  let some mv <- if let some mv := mv? then do
      -- If the given mv isn't a goal already, then make it one
      let already <- goals.anyM (fun g => return g == mv)
      if !already then
        Tactic.appendGoals [mv]
        already_goal := true
      pure (some mv)
    else
      -- If no mv is given explicitly, we just find one with the username
      goals.findM? fun goal => do return (<- goal.getTag) == id
    | throwErrorAt v "Unknown goal called '{id}'"
  -- Then, evaluate the tactic over it, finding it in the goals list
  let goal <- Tactic.renameInaccessibles mv args
  let res <- Tactic.evalTacticAt tac goal
  if ids.length > res.length then
    throwErrorAt asIds[res.length]!
      "Too many 'as' names given! the tactic generated {res.length} goals"
  for (i, r) in ids.zip res do
    r.setUserName i
  for r in res do
    r.setKind .syntheticOpaque
  -- If we produce exactly one goal, and it has the same name as the original
  -- mvar which giving, then it should remain a visible goal.
  if keepGoals then
    Tactic.appendGoals res
  else if let [mv] := res then
    if already_goal && (<- mv.getTag) = id then
      Tactic.appendGoals [mv]
  Tactic.evalTactic (<- `(tactic| try refold $v))
  return res

private def transformRecursion (pre : Patt := []) (ctx : MatchCtx) (body : Term)
  : TacticM Term := do
  let body <- body.raw.rewriteBottomUpM fun
  | stx@`($f:ident $args:term*) => do
    let numPre := pre.length
    for (pre, p) in args.toList.zip (ctx.ps.take numPre) do
      let (r, _) <- mkArgPatt pre none |>.run' default
      if r != p then
        throwErrorAt stx "Can't make recursive call at {stx}\n\
        Wrong index (i.e. non-recursive) arguments\n\
        Expected: {f} {Std.format (ctx.ps.take numPre : Patt)} ..."
    let (arg0 :: args) := args.drop numPre |>.toList
      | throwErrorAt stx "Can't make recursive call at {stx}\n\
      Not enough arguments"
    if f.getId = ctx.goal_name.getId then
      let `($arg_id:ident) := arg0
        | throwErrorAt arg0 "Can't make recursive call on {arg0}"
      let arg_name := arg_id.getId
      let some (old_name, new_name, _) := ctx.names.toList
        |>.find? (fun (_, n, _) => n == arg_name)
        | throwErrorAt arg0 "Can't make recursive call on {arg0}"
      let old_rec_name := old_name.recOf f.getId
      let new_rec_name := new_name.recOf f.getId
      if let some _recur := (<- getLCtx).findFromUserName? old_rec_name then
        let s <- `($(mkIdent new_rec_name) $(args.toArray)*)
        return s
      else
        throwErrorAt stx "Can't make recursive call in non-recursive case\n\
        (Expecting in-scope {new_rec_name})"
    else
      return stx
  | s => pure s
  return .mk body

private def refineRecursion
  (goal_args : Array (Expr × Name)) (goal : MVarId)
  : Refinement := fun _ctx => goal.withContext do
  let mut goal := goal
  for (_ty, old) in goal_args do
    let (_fv, goal') <- goal.intro old
    goal := goal'
  return goal

def elabGiveBy (v : Ident) (b : TSyntax `give_by)
  (mv? : Option MVarId := none) (prePatt? : Option Pattern := none)
  : TacticM Unit
  := do
  let mctx <- getMCtx
  let id := v.getId
  let some rootMv := mctx.findUserName? id
    | throwErrorAt v "Unknown goal called '{id}'"
  let mv := mv?.getD rootMv
  let mv_ty <- mv.getType''
  let (args, _retTy) := unarrow mv_ty
  let some (_, motive) := mv_ty.arrow?
    | throwErrorAt v "Cannot refine {v}, of type {mv_ty}, by recursion, \
      (it is not a function type)"
  match b with
  | `(give_by| recursion) => do
    let (inp_ty :: rest_args) := args
      | throwErrorAt b "Cannot refine {v}, of type {mv_ty}, by recursion"
    matchConstInduct (inp_ty.getAppFn)
      (fun _ => throwErrorAt v "Cannot refine {v}, of input type {inp_ty}, \
        by recursion (it is not an inductive type)")
      <| fun ival us => do
      let rec_name := mkRecName ival.name
      let goal_names <- ival.ctors.mapM fun ctor => do
        getUnusedUserName (ctor.replacePrefix ival.name id)
      let goals <- elabGive v #[] (keepGoals := true) (mv? := mv?)
        (goal_names.toArray.map mkIdent)
        (<- `(tacticSeq| apply $(mkIdent rec_name)))
      assert! goals.length == goal_names.length
      -- Register the new patterns
      for (goal, ctor) in goals.zip ival.ctors do
        let env <- getEnv
        let some ctor_val := env.find? ctor
          | throwError "Internal: couldn't find ctor {ctor} in environment"
        let ctor_ty := ctor_val.instantiateTypeLevelParams us
        let (cargs, _bs, r) <- forallMetaTelescope ctor_ty
        if !(<- isDefEq r inp_ty) then
          throwError f!"The constructor {ctor} yields {r}, not {inp_ty}"
        -- Drop the parameter arguments, these don't go into the recursor ops
        let cargs := cargs.drop ival.numParams
        let mut goal_args := #[]
        let mut ctor_patt_args := []
        for carg in cargs do
          let mv := carg.mvarId!
          let cty <- mv.getType
          let tag <- mv.getTag
          let fresh <- mkFreshUserName tag
          goal_args := goal_args.push (<- mv.getType, fresh)
          -- Here, the goal args are just the visible constructor args, so we
          -- add them to the pattern.
          ctor_patt_args := ctor_patt_args.concat (.var fresh)
          -- Then, find the recursive arguments
          if <- isDefEq cty inp_ty then
            let recName := fresh.recOf id
            goal_args := goal_args.push (motive, recName)
        let ctor_patt := ArgPatt.ctor ctor ctor_patt_args
        -- And finally, the remaining arguments from the motive
        let names <- rest_args.mapM fun _ => mkFreshBinderName
        let rest_named := rest_args.zip names
        goal_args := goal_args ++ rest_named
        let rest_patts := rest_named.map fun (_, name) => ArgPatt.var name
        let mut pattern : Pattern := {
          fname := id, fmv := rootMv, endpointMv := goal
          ps := ctor_patt :: rest_patts
          refine := refineRecursion goal_args goal,
          transform := transformRecursion
        }
        if let some prePatt := prePatt? then
          pattern := { pattern with
            ps := prePatt.ps ++ pattern.ps
            transform ctx
              := prePatt.transform ctx
              >=> transformRecursion prePatt.ps ctx
          }
        patternsRef.modify fun ps => ps.insert pattern
    return ()
  | _ => throwUnsupportedSyntax

syntax (name := blankHole) "blank" ident : term

def elabGivePattBy
  (p : Term) (f : Ident) (rest : TSyntaxArray `term) (b : TSyntax `give_by)
  : TacticM Unit := Tactic.withMainContext do
  let mctx <- getMCtx
  let (some mv) := mctx.findUserName? f.getId
    | throwErrorAt f "No calculation target found: '{f.getId}'"
  let mv_ty <- mv.getType''
  let (args, _) := unarrow mv_ty
  let (qs, _mvs) <- mkPatt rest.toList args
  let (pattern, names) <- findMatch mv rest.toList args (pattRef? := p)
  let tag <- mkFreshUserName (f.getId.str "body")
  let body <- `(blank $(mkIdent tag))
  let hole <- pattern.refine {
    names, body, goal_name := f, goal_ty := mv_ty, ps := qs
  }
  hole.withContext do
    let mut tempLCtx <- getLCtx
    tempLCtx := subSimul (names.map fun _ (new, _) => new) tempLCtx
    withLCtx' tempLCtx do
      elabGiveBy f b (prePatt? := pattern) (mv? := hole)
  return ()

def elabGiveAsk (v : TSyntax `ident) : TacticM Unit
  := Tactic.withMainContext do
  let some mv := (<- getMCtx).findUserName? v.getId
    | throwErrorAt v "No calculation target found named '{v.getId}'"
  let ps <- patternsRef.get
  let mut fmt : MessageData := m!"Available 'give' patterns for {v}:"
  let mut any := false
  for pattern in ps do
    if pattern.fmv != mv then continue
    let endpoint := pattern.endpointMv
    if (<- endpoint.isDeclared)
        && !(<- endpoint.isAssignedOrDelayedAssigned) then
      fmt := fmt ++ indentD (format pattern)
      any := true
  if any then
    logInfo fmt
  else
    logInfo m!"No available 'give' patterns for {v}"

elab_rules : tactic
  | `(tactic| give $v:ident $args:binderIdent* $mode:give_mode => $tac) =>
    match mode with
    | `(give_mode| as $vs:ident*) =>
        discard <| elabGive v args vs tac
    | `(give_mode| as? $vs:ident*) => Tactic.withMainContext do
        let res <- elabGive v args vs tac
        let names <- res.mapM fun mv => mv.getTag <&> (·.toString)
        logInfoAt mode m!"Generated {res.length} goals: {String.intercalate ", " names}\n\
        To rename them, use:\n  give {v} as x y z ... => {tac}"
    | _ => throwUnsupportedSyntax
  | `(tactic| give $v:ident $args:binderIdent* => $tac) =>
    discard <| elabGive v args #[] tac
  | `(tactic| give $p:term := $to_term:term) => do
    elabGiveDef p to_term
  | `(tactic| give $v:ident by $b:give_by) => do
    elabGiveBy v b
  | `(tactic| give $p:term by $b:give_by) =>
    if let `($f:ident $rest*) := p then
      elabGivePattBy p f rest b
    else throwUnsupportedSyntax
  | `(tactic| give? $v:ident) =>
    elabGiveAsk v

#allow_unused_tactic! defineTactic

def intro_let_in_main_goal (name : Name) (ty val : Expr) (isDef : Bool := true)
  : TacticM FVarId := do
  let mut main_mv <- Tactic.getMainGoal
  if isDef then
    main_mv <- main_mv.define name ty val
  else
    main_mv <- main_mv.assert name ty val
  let (fv, new_main) <- main_mv.intro1P
  Tactic.replaceMainGoal [new_main]
  return fv

def calc_intro_other (as_name : Name) (field_ty : Expr)
  : TacticM (Expr × FVarId) := do
  let field_body <- Tactic.withMainContext do
    mkFreshExprMVar (some field_ty) (kind := .syntheticOpaque)
  field_body.mvarId!.setUserName (calc_name as_name)
  let fv <- intro_let_in_main_goal as_name field_ty (.mvar (field_body.mvarId!))
  Tactic.appendGoals [field_body.mvarId!]
  return (field_body, fv)

def calc_intro_for (field_name : Name) (fields : Array (Name × Expr)) (as_name : Name := field_name)
    : TacticM (Expr × FVarId)
  := do
  let some (_, field) := fields.find? fun (n, _) => n = field_name
    | throwUnknownNameWithSuggestions field_name (extraMsg :=
      m!", could be any of {fields.map (·.fst)}")
  let field_ty <- inferType field >>= instantiateMVars
  calc_intro_other as_name field_ty

declare_syntax_cat calc_name
syntax ident : calc_name
syntax ident "as" ident : calc_name

elab (name := collectTac)
  "collect " body:tacticSeq : tactic =>
  Tactic.withMainContext do
  patternsRef.set {}
  -- let target <- Tactic.getMainTarget
  Tactic.evalTactic body
  -- Unsure if I still need this...
  -- let mctx <- getMCtx
  -- for (mv, decl) in mctx.decls do
  --   if !decl.userName.isAnonymous &&
  --      !(<- mv.isAssignedOrDelayedAssigned) then
  --     Tactic.pushGoal mv

/--
Introduce a calculation for the current goal.

 * `calculate x, y, z` introduces calculation targets for fields `x` `y` and `z`,
   if the current goal is a structure with such named fields.

 * `calculate x as foo` lets us locally alias these calculation target names. Useful
   with products, e.g. `calculate fst as my_function`.

 * `calculate ⊢ as foo`, a special case where the goal isn't a structure, and instead
   we simply make the entire goal into a calculation target named `foo`.
-/
elab (name := calculateTactic) "calculate " vs:calc_name,* : tactic => Tactic.withMainContext do
  -- look at main goal, get its fields
  let main_goal <- Tactic.getMainGoal
  let main_type <- main_goal.getType''
  let (_, spec_fields) <- match_struct_fields main_type
  if vs.getElems.size == 0 then
    logWarning f!"Use `calculate` followed by any of {spec_fields.toList.map fun (n, _) => n}"
  -- for each ident 'v' listed:
  let vals <- vs.getElems.mapM fun s => withRef s do
    match s with
    | `(calc_name| $v:ident) =>
      let field_name := v.getId
      let val <- calc_intro_for field_name spec_fields
      return (field_name, field_name, val, s)
    | `(calc_name| $v:ident as $r:ident) =>
      let field_name := v.getId
      let as_name := r.getId
      let val <- calc_intro_for field_name spec_fields (as_name := as_name)
      return (field_name, as_name, val, s)
    | _ => throwUnsupportedSyntax
  -- split the main goal into its constructor fields, and set each one to the corresponding
  -- recursor binding from above
  let main_mv <- Tactic.getMainGoal
  let field_mvs <- main_mv.constructor
  for fmv in field_mvs do
    fmv.setKind .syntheticOpaque
  Tactic.pushGoals field_mvs
  for (field_name, as_name, (mv_val, _fv), stx) in vals do
    let some field_mv <- field_mvs.findM? fun u => u.getTag <&> (· == field_name)
      | throwErrorAt stx "bug: unknown field name: {field_name}"
    field_mv.assign mv_val
    field_mv.setUserName (calc_name as_name)

@[inherit_doc calculateTactic]
elab (name := calculateGoal) "calculate" "⊢" "as" r:ident : tactic => Tactic.withMainContext do
  let main_goal <- Tactic.getMainGoal
  main_goal.setUserName r.getId

#allow_unused_tactic! calculateGoal

macro "exists_mono" : tactic =>
  `(tactic| (repeat' apply Exists.imp; intro))

private partial def splitHyp (fv : FVarId) : TacticM Unit :=
  Tactic.withMainContext do
    let goal <- Tactic.getMainGoal
    let checkpoint <- Meta.saveState
    try
      let subgoals <- goal.cases fv
      if let #[sg] := subgoals then
        Tactic.replaceMainGoal [sg.mvarId]
        for fieldExpr in sg.fields do
          if let some fieldFV := fieldExpr.fvarId? then
            splitHyp fieldFV
      else
        failure
    catch | _ => do
      checkpoint.restore

elab "unpkg" "[" fv:ident "]" : tactic => Tactic.withMainContext do
  let fvar <- getFVarFromUserName fv.getId
  splitHyp fvar.fvarId!

elab "unpkg" : tactic => Tactic.withMainContext do
  let un <- mkFreshUserName (.mkSimple "it")
  let mv <- Tactic.getMainGoal
  let (fv, mv') <- mv.intro un
  Tactic.replaceMainGoal [mv']
  splitHyp fv

local infixl: 50 " <;> " => Tactic.andThenOnSubgoals

open Tactic

def restructureCore (tacs : TSyntaxArray `tactic) : TacticM Unit := do
  _ <- tryTactic (evalTactic (<- `(tactic| contradiction)))
  _ <- tryTactic (evalTactic (<- `(tactic| assumption)))
  iterateUntilFailure do
    let gs <- getUnsolvedGoals
    allGoals <|
      liftMetaTactic (fun m => do pure [(<- m.intros!).2]) <;>
      Tauto.distribNot <;>
      liftMetaTactic (MVarId.casesMatching casesMatch
        (recursive := true) (throwOnNoMatch := false)) <;>
      (do _ <- tryTactic (evalTactic (<- `(tactic| contradiction)))) <;>
      liftMetaTactic (fun m => do pure [(<- m.intros!).2]) <;>
      liftMetaTactic (constructorMatching · ctorMatch
        (recursive := true) (throwOnNoMatch := false)) <;>
      do _ <- tryTactic (evalTactic (<- `(tactic| assumption)))
    allGoals <| for tac in tacs do
      _ <- tryTactic (evalTactic tac)
    let gs' <- getUnsolvedGoals
    if gs == gs' then failure
    pure ()
  where
    casesMatch (e : Q(Prop)) : MetaM Bool := match e with
    | ~q(_ ∧ _) => pure true
    | ~q(_ ∨ _) => pure true
    | ~q(Exists _) => pure true
    | ~q(False) => pure true
    | _ => pure false
    ctorMatch (e : Q(Prop)) : MetaM Bool := match e with
    | ~q(_ ∧ _) => pure true
    | ~q(_ ↔ _) => pure true
    | ~q(True) => pure true
    | _ => pure false

def restructure (tacs : TSyntaxArray `tactic) : TacticM Unit := focus do
  _ <- tryTactic (evalTactic (<- `(tactic| unpkg)))
  restructureCore tacs
  allGoals <| iterateUntilFailure do
    let gs <- getUnsolvedGoals
    for tac in tacs do
      _ <- tryTactic (evalTactic tac)
    _ <- tryTactic
      <|  evalTactic (<- `(tactic| rfl))
      <|> evalTactic (<- `(tactic| solve_by_elim))
      <|> liftMetaTactic (constructorMatching · ctorMatch)
    let gs' <- getUnsolvedGoals
    if gs == gs' then failure
    pure ()
  where
    ctorMatch (e : Q(Prop)) : MetaM Bool := match e with
    | ~q(_ ∧ _) => pure true
    | ~q(_ ↔ _) => pure true
    | ~q(Exists _) => pure true
    | ~q(True) => pure true
    | _ => pure false

elab "restructuring" "[" tacs:tactic* "]" : tactic => restructure tacs
elab "restructuring" : tactic => restructure #[]

/-
Things that would be good, then:

  * `define f (.ctor a b c) := ...` automatically refines/gives the function as a .rec instance
    -> `f = .rec P Q R`
  * `define f n m | m < 0 := ...` automatically
    - If before: `f = .rec () g`
    -> then: `f =
-/

inductive Colour where
  | Red
  | Blue
  | Green

compile_inductive% Colour

-- set_option pp.mvars.delayed true

elab "mv_info" v:ident : tactic => withMainContext do
  let mctx <- getMCtx
  let some mv := mctx.findUserName? v.getId
    | throwError "unknown mvar"
  let decl := mctx.getDecl mv
  logInfo m!"found decl for {v.getId}
  name: {mv.name}
  type: {<- mv.getType}
  expr: {Expr.mvar mv}
  synthetic? {decl.kind.isSyntheticOpaque}
  readonly? {<- mv.isReadOnly}
  declared? {<- mv.isDeclared}
  delayed?  {<- mv.isDelayedAssigned}
  assigned? {<- mv.isAssigned}"

structure Eg where
  f : Nat -> Nat
  g : Colour -> Int
  correct : ∀ n, f n <= n

@[term_elab blankHole]
def elabQ : TermElab := fun stx typ? => match stx with
  | `(blank $v:ident) => do
    tryPostponeIfNoneOrMVar typ?
    let mv_expr <- mkFreshExprMVar typ?
    let mv := mv_expr.mvarId!
    mv.setTag v.getId
    return mv_expr
  | _ => throwUnsupportedSyntax

def test_def : Nat := by
  let f : List Nat -> Nat -> Nat := ?f
  give f by recursion
  give f (u :: us) head := u + f us head
  give f [] n := n
  let g : Nat -> Nat -> Nat -> Nat := ?g
  give g n by recursion
  give g x Nat.zero n := x
  give g x (Nat.succ m) n := g x m n
  exact g 10 10 10

-- def eg :
--     Σ' f : List Nat -> Nat -> List Nat,
--     f [] 5 = [5]
--   := by
--   collect
--     calculate fst as f
--     -- give f (y :: ys) n a true := n
--     give f => apply List.rec
--     give f.nil as f.cond.true f.cond.false =>
--       refine fun n => if h : n = 5 then blank else blank
--     unfold f
--     simp
--     -- define2 f x y z (h := true) := [5]
--     give f.cond.true => exact fun n h => [5]
--     rfl
--   give f.cond.false => exact fun n h => []
--   give f.cons => exact fun n ns «f.ns» m => []

-- def eg2 : Eg := by
--   calculate f, g
--   give f => apply Nat.rec
--   give g => apply Colour.rec
--   give f.zero => exact 0
--   have p : f 0 = 0 := by
--     trivial
--   have r : f 5 = 0 := by
--     give f.succ as f.a f.b => refine fun n nf => if h : n = 4 then ?_ else ?_
--     give f.a => exact 0
--     reduce
--     rfl
--   give f.b => exact n
--   give g.Red => exact 10
--   have q : g .Red = 10 := by
--     reduce
--     rfl
--   give g.Blue => exact 15
--   give g.Green => exact 20
--   case correct =>
--     intro n
--     induction n
--     all_goals grind

-- def eg3 : Eg := by
--   calculate f, g
--   give f => apply Nat.rec
--   define f .zero := 0
--   -- give f.zero => exact 0
--   have p : f 0 = 0 := by
--     trivial
--   have r : f 5 = 0 := by
--     give f.succ as f.a f.b => refine fun n nf => if n = 4 then ?_ else ?_
--     -- unfold f
--     -- rw [Nat.rec_eq_recCompiled]
--     -- unfold Nat.recCompiled
--     -- simp
--     give f.a => exact 0
--     rfl
--   give g => intro c; exact 0
--   case correct =>
--     give f.b => exact n
--     intro n
--     induction n
--     all_goals grind

-- @[simp]
-- def rev {a} : List a → List a
--   | [] => []
--   | x :: xs => rev xs ++ [x]

-- structure RevSpec a : Type where
--   fastrev : List a -> List a -> List a
--   correct : ∀ xs ys, rev xs ++ ys = fastrev xs ys

-- def revCalc {a} : RevSpec a := by
--   calculate fastrev
--   give fastrev by recursion
--   intro xs
--   (induction xs) <;> intro ys
--   case nil => calc
--     rev [] ++ ys
--     _ = ys
--         := by rfl
--     _ = fastrev [] ys
--         := by define fastrev [] ys := ys
--   case cons x xs ih => calc
--     rev (x :: xs) ++ ys
--     _ = rev xs ++ [x] ++ ys
--         := by rfl
--     _ = rev xs ++ ([x] ++ ys)
--         := by simp only [List.append_assoc]
--     _ = fastrev xs ([x] ++ ys)
--         := by rw [ih]
--     _ = fastrev xs (x :: ys)
--         := by rfl
--     _ = fastrev (x :: xs) ys
--         := by define fastrev (x :: xs) ys := fastrev xs (x :: ys)

-- def fastrev {a} : List a -> List a := fun xs => revCalc.fastrev xs []

end Tactic.Calculation
