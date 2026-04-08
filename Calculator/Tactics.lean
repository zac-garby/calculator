import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive
import Calculator.Pattern


namespace Lean

def Name.recOf (name f : Name) := f ++ name
def Name.target (name : Name) : Name := .mkStr1 "target" ++ name

def LocalContext.eraseUserName (lctx : LocalContext) (name : Name) :=
  if let some fv := lctx.findFromUserName? name then
    lctx.erase fv.fvarId
  else
    lctx

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

def applyNames
  (lctx : LocalContext) (names : Tactic.Calculation.NameMap Name)
  (f? : Option Name)
  : LocalContext := Id.run do
  let mut names := names
  if let some f := f? then
    for decl in lctx do
      if let some suff := f.isPrefixOf? decl.userName then
        let new := f ++ names.getD suff suff
        names := names.insert decl.userName new
  Tactic.Calculation.subSimul names lctx

/--
Find a calculation target. This is a metavariable with the given name, but it
prioritises those which are not yet assigned if there are duplicate names.
-/
def findCalcTarget? (name : Name) : MetaM (Option MVarId) := do
  let mctx <- getMCtx
  for (mv, decl) in mctx.decls do
    if decl.userName = name.target then
      return some mv
  return mctx.findUserName? name.target

def findCalcTarget (name : Name) (stxRef : Option Syntax := none)
  : MetaM MVarId := do
  match (<- findCalcTarget? name), stxRef with
  | none, some ref => throwErrorAt ref "No calculation target found named '{name}'"
  | none, none => throwError "No calculation target found named '{name}'"
  | some mv, _ => return mv

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
      else throwError m!"{bind_name} is already fully defined"
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
scoped syntax "recursion" : give_by
scoped syntax "cases" "of" term : give_by
scoped syntax "if " Parser.Term.matchDiscr : give_by
-- scoped syntax "intro " ident* : give_by
scoped syntax "aux " term : give_by

private def giveByHelp := [
  "recursion",
  "cases of x",
  "if P",
  "if h : P",
  -- "intro x y z ⋯",
  "aux f x y z ⋯"
]

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
@[inherit_doc giveTactic] syntax (name := giveDefHypTactic)
  "give" ident " : " term " := " term : tactic
@[inherit_doc giveTactic] syntax (name := giveByTactic)
  "give" term " by " give_by : tactic

#allow_unused_tactic! giveTactic
#allow_unused_tactic! giveAskTactic
#allow_unused_tactic! giveDefTactic
#allow_unused_tactic! giveDefHypTactic
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
  -- let mctx <- getMCtx
  let mv <- findCalcTarget v
  -- let some mv := mctx.findUserName? v
  --   | throwError "Unknown goal called '{v}'"
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

def ArgPatt.toTerm (p : ArgPatt) : Option Term := match p with
  | .var n => mkIdent n
  | .ctor c args => Syntax.mkApp
    (mkIdent c)
    (args.filterMap (·.toTerm) |>.toArray)
  | _ => none

private def elabGiveDef
  (p to_term : Term) (hypName? : Option Name := none)
  : TacticM Unit
  := Tactic.withMainContext do
  match p with
  | `($f:ident) => do
    let mv <- findCalcTarget f.getId f
    let mv_ty <- mv.getType''
    let to_expr <- mv.withContext <|
      Term.elabTerm to_term (some mv_ty)
    define_mv f.getId.target to_expr
  | `($f:ident $rest*) => do
    let mv <- findCalcTarget f.getId f
    let mv_ty <- mv.getType''
    let (args, _) := unarrow mv_ty
    let (qs, _mvs) <- mkPatt rest.toList args
    let (pattern, names) <- PatternMap.findMatch mv rest.toList args (pattRef? := p)
    let ctx := {names, body := to_term, goal_name := f, goal_ty := mv_ty, ps := qs}
    let hole <- pattern.refine ctx
    let hole_ty <- hole.getType
    -- Rename the local variables according to the names
    -- given in the pattern.
    let tempLCtx := applyNames (<- hole.withContext getLCtx)
      (names.map fun _ (old, _) => old)
      (f? := f.getId)
    -- hole.modifyLCtx fun lctx => applyNames lctx
    --   (names.map fun _ (old, _) => old)
    --   (f? := f.getId)
    let body <- withRef to_term <| withLCtx' tempLCtx do
      let to_term' <- pattern.transform ctx to_term
      let body <- Tactic.elabTermEnsuringType to_term' hole_ty
      hole.assignIfDefEq body
      pure body
      -- let mvs <- Tactic.evalTacticAt (<- `(tactic| exact $to_term')) hole
      -- unless mvs.isEmpty do
      --   throwError "Unexpected: 'give' assignment produced new metavariables!"
    -- Now we've given our definition, if we are supposed to introduce a hypothesis
    -- for it, do that now.
    if let some hypName := hypName? then
      let prop <- hole.withContext do
        let propLCtx <- getLCtx
        let fvs <- pattern.foralls.mapM fun (name, _ty) => do
          let some decl := propLCtx.findFromUserName? name
            | throwError "Internal: {name} doesn't exist in the local context, \
            when forming a 'give' hypothesis"
          let fv := decl.fvarId
          pure (.fvar fv)
        let fnApp <- withLCtx' tempLCtx do
          let realArgs := qs.filterMap (·.toTerm)
          let tm <- `(term| $f $(realArgs.toArray)*)
          Tactic.elabTerm tm hole_ty
        let (_, fvst) <- fnApp.collectFVars.run {}
        let some fnFv := (<- getLCtx).findFromUserName? f.getId
          | throwError "Can't find target function {f.getId} in local contxt"
        let fvs := fvst.fvarIds
          |>.filter (fun fv => fv != fnFv.fvarId)
          |>.map (.fvar ·)
          |>.append fvs
        let concl <- mkEq fnApp body
        let prop <- mkForallFVars fvs concl (usedOnly := true)
        pure prop
      let proof <- mkFreshExprMVar prop
      let goal <- Tactic.getMainGoal
      let (_hypFvs, goal') <- goal.assertHypotheses #[{
        userName := hypName
        type := prop
        value := proof
      }]
      Tactic.replaceMainGoal [goal']
      Tactic.appendGoals [proof.mvarId!]
  | _ => do
    throwUnsupportedSyntax

/--
Like `elabGiveDef`, but also introduces a universally-quantified hypothesis.
`give h : f m .zero := 0` defines the clause AND adds `h : ∀ m, f m 0 = 0`.
-/
private def elabGiveDefHyp (hypName : Ident) (p to_term : Term) : TacticM Unit
    := Tactic.withMainContext do
  let `($_f:ident $_rest*) := p
    | throwErrorAt p "'give {hypName} :' requires a pattern like 'f args...'"
  elabGiveDef p to_term (hypName? := hypName.getId)
  -- logInfo m!"give hyp at {f} {rest}"
  -- let mv <- findCalcTarget f.getId f
  -- let mv_ty <- mv.getType''
  -- let (args, _) := unarrow mv_ty
  -- let (qs, mvs) <- mkPatt rest.toList args
  -- let mut forallFvs := #[]
  -- for q in qs do
  --   match q with
  --   | .var qn =>
  --     let qty <- mvs[qn]!.getType
  --     let fv <- mkFreshExprMVar qty (userName := qn)
  --     forallFvs := forallFvs.push fv
  --   | .ctor c cargs => pure ()
  --   | .bind a b => pure ()
  -- let prop <- mkForallFVars' forallFvs (<- Term.elabTerm (<- `(term| top)) none)
  -- logInfo m!"prop = {prop}"
  -------
  -- let (pattern, names) <- PatternMap.findMatch mv rest.toList args
  -- -- Build the hypothesis in the main goal's context so `f` refers to its let-fvar
  -- Tactic.withMainContext do
  --   -- Find the fvar for `f` in the current lctx (it's a let-binding := ?target.f)
  --   let lctx <- getLCtx
  --   let some fDecl := lctx.findFromUserName? f.getId
  --     | throwErrorAt f "'{f.getId}' not found in local context"
  --   let fFVar := Expr.fvar fDecl.fvarId
  --   -- Get the hole (now assigned) to find its lctx (for .bind / if-branch hypotheses)
  --   let ctx' := { names, body := to_term, goal_name := f, goal_ty := mv_ty, ps := pattern.ps }
  --   let hole <- pattern.refine ctx'
  --   let holeLCtx <- hole.withContext getLCtx
  --   let rhs <- instantiateMVars (.mvar hole)
  --   -- All building is done in the hole's lctx so hole fvars (m, n, h) are in scope.
  --   -- The hole inherits all let-bindings from parent goals, so fFVar is also valid here.
  --   let (hyp_ty, hyp_val) <- withLCtx' holeLCtx do
  --     let mut allFvDecls  : Array (FVarId × Name × Expr) := #[]
  --     let mut argExprs    : Array Expr := #[]
  --     let mut preconds    : Array Expr := #[]
  --     for (pat, _) in pattern.ps.zip args do
  --       match <- buildHypArg pat names holeLCtx with
  --       | .arg expr decls => allFvDecls := allFvDecls ++ decls; argExprs := argExprs.push expr
  --       | .pre cond =>
  --         -- inferType uses holeLCtx, so the condition type references hole fvars correctly
  --         preconds := preconds.push (<- inferType cond)
  --     -- lhs = f applied to all arg exprs (all using hole fvars)
  --     let lhs := mkAppN fFVar argExprs
  --     let fvarExprs := allFvDecls.map fun (fvId, _, _) => Expr.fvar fvId
  --     let eqTy  <- mkEq lhs rhs
  --     -- Fold preconditions as implications: pre₁ → pre₂ → ... → lhs = rhs
  --     let body  := preconds.foldr (fun pre acc => .forallE `_ pre acc .default) eqTy
  --     let ty    <- mkForallFVars fvarExprs body
  --     -- Proof: fun fvars => fun _ : pre₁ => ... => rfl
  --     let refl  <- mkEqRefl lhs
  --     let proof := preconds.foldr (fun pre acc => .lam `_ pre acc .default) refl
  --     let val   <- mkLambdaFVars fvarExprs proof
  --     return (ty, val)
  --   -- Inject into the first unassigned non-target goal (the spec/proof goal)
  --   let goals <- Tactic.getGoals
  --   let some specGoal <- goals.findM? fun (g : MVarId) => do
  --       if <- g.isAssigned then return false
  --       let tag <- g.getTag
  --       return !tag.toString.startsWith "target"
  --     | return ()  -- no suitable goal; silently skip
  --   let specGoal' <- specGoal.assert hypName.getId hyp_ty hyp_val
  --   let (_, new_spec) <- specGoal'.intro1P
  --   let goals' <- goals.mapM fun g => if g == specGoal then pure new_spec else pure g
  --   Tactic.setGoals goals'

private def elabGive
  (v : TSyntax `ident) (args : TSyntaxArray `Lean.binderIdent)
  (asIds : TSyntaxArray `ident)
  (tac : TSyntax `Lean.Parser.Tactic.tacticSeq)
  (keepGoals : Bool := false)
  (mv? : Option MVarId := none)
  : TacticM (List MVarId) := do
  let id := v.getId
  let ids := asIds.toList.map (·.getId)
  let goals <- Tactic.getGoals
  let mut already_goal := true
  -- TODO: Is this logic correct? That it requires it to be a *goal*,
  -- as opposed to the other give elaborators which use findCalcTarget
  let mv <- if let some mv := mv? then do
      pure mv
    else
      -- If no mv is given explicitly, we just find one with the username
      findCalcTarget id v
  -- If the given mv isn't a goal already, then make it one
  let already <- goals.anyM (fun g => return g == mv)
  if !already then
    Tactic.appendGoals [mv]
    already_goal := true
  -- Then, evaluate the tactic over it, finding it in the goals list
  let goal <- Tactic.renameInaccessibles mv args
  let res <- Tactic.evalTacticAt tac goal
  if ids.length > res.length then
    throwErrorAt asIds[res.length]!
      "Too many 'as' names given! the tactic generated {res.length} goals"
  for (i, r) in ids.zip res do
    r.setUserName i.target
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
    if args.isEmpty then
      return stx
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
      let some (_, new_name, _) := ctx.names.toList
        |>.find? (fun (_, n, _) => n == arg_name)
        | throwErrorAt arg0 "Can't make recursive call on {arg0}"
      let new_rec_name := new_name.recOf f.getId
      if (<- getLCtx).usesUserName new_rec_name then
        `($(mkIdent new_rec_name) $(args.toArray)*)
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

private def applyPrePatt
  (prePatt? : Option Pattern) (pattern : Pattern) : Pattern :=
  if let some prePatt := prePatt? then
    { pattern with
      ps := prePatt.ps ++ pattern.ps
      foralls := prePatt.foralls ++ pattern.foralls
      transform ctx :=
        prePatt.transform ctx >=> pattern.transform ctx }
  else
    pattern

private def buildRecPattern
  (id : Name) (rootMv : MVarId) (inp_ty motive : Expr) (us : List Level)
  (rest_args : List Expr) (ival : InductiveVal) (ctor : Name) (goal : MVarId)
  (prePatt? : Option Pattern := none)
  : MetaM Pattern := do
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
  let mut ih_args := #[]
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
    -- Then, find the recursive arguments (IHs come after all ctor args
    -- in Lean's recursor, so we collect them separately)
    if <- isDefEq cty inp_ty then
      let recName := fresh.recOf id
      ih_args := ih_args.push (motive, recName)
  goal_args := goal_args ++ ih_args
  let ctor_patt := ArgPatt.ctor ctor ctor_patt_args
  -- And finally, the remaining arguments from the motive
  let names <- rest_args.mapM fun _ => mkFreshBinderName
  let rest_named := rest_args.zip names
  goal_args := goal_args ++ rest_named
  let rest_patts := rest_named.map fun (_, name) => ArgPatt.var name
  return {
    fname := id, fmv := rootMv, endpointMv := goal
    ps := ctor_patt :: rest_patts
    refine := refineRecursion goal_args goal
    transform := transformRecursion
      (pre := prePatt?.map (·.ps) |>.getD [])
    foralls := goal_args.map (·.swap)
  }

def elabGiveBy (v : Ident) (b : TSyntax `give_by)
  (mv? : Option MVarId := none) (prePatt? : Option Pattern := none)
  (rootMv? : Option MVarId := none)
  : TacticM Unit := do
  let vId := v.getId
  let rootMv <- rootMv?.getDM (findCalcTarget vId v)
  let holeMv := mv?.getD rootMv
  let holeTy <- holeMv.getType''
  let (args, _retTy) := unarrow holeTy
  match b with
  | `(give_by| recursion) => do
    let some (_, motive) := holeTy.arrow?
      | throwErrorAt v "Cannot refine {v}, of type {holeTy}, by recursion \
        (it is not a function type)"
    let (inp_ty :: rest_args) := args
      | throwErrorAt b "Cannot refine {v}, of type {holeTy}, by recursion"
    matchConstInduct (inp_ty.getAppFn)
      (fun _ => throwErrorAt v "Cannot refine {v}, of input type {inp_ty}, \
        by recursion (it is not an inductive type)")
      <| fun ival us => do
      let rec_name := mkRecName ival.name
      let goal_names <- ival.ctors.mapM fun ctor =>
        getUnusedUserName (ctor.replacePrefix ival.name vId)
      let goals <- elabGive v #[] (keepGoals := true) (mv? := mv?)
        (goal_names.toArray.map mkIdent)
        (<- `(tacticSeq| apply $(mkIdent rec_name)))
      assert! goals.length == goal_names.length
      for (goal, ctor) in goals.zip ival.ctors do
        let pattern <- buildRecPattern vId rootMv inp_ty motive
          us rest_args ival ctor goal prePatt?
        let pattern := applyPrePatt prePatt? pattern
        PatternMap.insert pattern
  | `(give_by| cases of $argTerm:term) => do
    let `($argId:ident) := argTerm
      | throwErrorAt argTerm "Expected an identifier after 'cases of'"
    let argName := argId.getId
    -- getLCtx returns the renamed context (due to withLCtx' in elabGivePattBy)
    let renamedLCtx <- getLCtx
    let some argDecl := renamedLCtx.findFromUserName? argName
      | throwErrorAt argTerm "'{argName}' not found in context. \
          Use 'give {v} patt by cases of {argName}' after a pattern that binds {argName}."
    let argFVarId := argDecl.fvarId
    -- Get the original (pre-rename) name of this fvar from the hole's stored lctx.
    -- prePatt.ps uses these original names, not the user-renamed ones.
    let origArgName : Name <- holeMv.withContext do
      let some decl := (← getLCtx).find? argFVarId
        | throwError "Internal: arg fvar '{argName}' not in hole's lctx"
      return decl.userName
    let argTy <- whnf (<- inferType (.fvar argFVarId))
    matchConstInduct argTy.getAppFn
      (fun _ => throwErrorAt argTerm
        "Cannot case-split on '{argName}': type {argTy} is not an inductive type")
      <| fun ival _us => do
    -- Apply cases directly via MVarId.cases using the fvarId
    -- (bypasses the name-lookup issue in the renamed lctx)
    let casesSubgoals <- holeMv.cases argFVarId
    -- Name the goals after constructors (like elabGive does)
    for subgoal in casesSubgoals do
      let some ctorName := subgoal.ctorName
        | continue  -- skip catch-all
      let goalName <- getUnusedUserName (ctorName.replacePrefix ival.name vId)
      subgoal.mvarId.setUserName goalName
      subgoal.mvarId.setKind .syntheticOpaque
    -- Build a Pattern for each constructor case
    for subgoal in casesSubgoals do
      let some ctorName := subgoal.ctorName | continue
      -- fields are the new constructor arg fvars introduced in this subgoal
      let fieldNames <- subgoal.fields.toList.mapM fun fieldExpr =>
        subgoal.mvarId.withContext do
          let some decl := (← getLCtx).find? fieldExpr.fvarId!
            | throwError "Internal: case field fvar not found"
          return decl.userName
      let ctorPatt := ArgPatt.ctor ctorName (fieldNames.map ArgPatt.var)
      -- Replace the split variable's position in prePatt.ps with ctorPatt.
      -- This handles both top-level and nested positions (e.g. chained splits).
      let ps := match prePatt? with
        | none => [ctorPatt]
        | some prePatt => prePatt.ps.map (ArgPatt.replace origArgName ctorPatt)
      let transform : Transformer := prePatt?.map (·.transform) |>.getD default
      let pattern : Pattern := {
        fname := vId, fmv := rootMv, endpointMv := subgoal.mvarId
        ps
        refine := fun _ => return subgoal.mvarId
        transform
      }
      PatternMap.insert pattern
    -- Expose the new goals to the proof state
    Tactic.appendGoals (casesSubgoals.toList.map (·.mvarId))
  | `(give_by| if $discr:matchDiscr) => do
    let (h, prop) <- match discr with
    | `(matchDiscr| $h : $prop) =>
      let inf := h.raw.getInfo?.getD .none
      pure (.mk <| Syntax.node1 inf `Lean.binderIdent h, prop)
    | `(matchDiscr| $prop:term) =>
      pure (<- `(binderIdent| _), prop)
    | _ => throwUnsupportedSyntax
    -- Generate names for the two branches: f.pos and f.neg
    let holeName <- holeMv.getTag
    let posName <- getUnusedUserName (holeName.str "yes")
    let negName <- getUnusedUserName (holeName.str "no")
    let hypName <- match h with
      | `(binderIdent| $i:ident) => pure i.getId
      | `(binderIdent| _) => pure `h
      | _ => throwUnsupportedSyntax
    -- Save current goals, focus on holeMv, apply the if-split
    let prevGoals <- Tactic.getGoals
    let inGoals <- prevGoals.anyM (fun g => return g == holeMv)
    if !inGoals then Tactic.setGoals (holeMv :: prevGoals)
    let body_term <- `(if $h : $prop then ?_ else ?_)
    let (body, branches) <- Tactic.elabTermWithHoles body_term holeTy vId
    holeMv.assignIfDefEq body
    match branches with
    | [posMv, negMv] =>
      -- Name the branches so findCalcTarget can find them later.
      posMv.setUserName posName
      negMv.setUserName negName
      let holeCtx <- holeMv.withContext getLCtx
      posMv.modifyLCtx fun lctx =>
        holeCtx.addDecl (lctx.findFromUserName? hypName |>.get!)
      negMv.modifyLCtx fun lctx =>
        holeCtx.addDecl (lctx.findFromUserName? hypName |>.get!)
      posMv.setKind .syntheticOpaque
      negMv.setKind .syntheticOpaque
      let transform := prePatt?.map (·.transform) |>.getD default
      PatternMap.insert <| applyPrePatt prePatt? {
        fname := vId, fmv := rootMv, endpointMv := posMv
        ps := [.bind (.var hypName) (.ctor ``true [])]
        refine := fun _ => return posMv, transform
        foralls := #[]
      }
      PatternMap.insert <| applyPrePatt prePatt? {
        fname := vId, fmv := rootMv, endpointMv := negMv
        ps := [.bind (.var hypName) (.ctor ``false [])]
        refine := fun _ => return negMv, transform
        foralls := #[]
      }
      -- Expose both branches as goals
      Tactic.appendGoals [posMv, negMv]
    | _ =>
      throwError "give by if: expected 2 goals from if-split, got {branches.length}"
  | `(give_by| aux ($_auxFn:ident : $auxTy:term) $_auxArgs:term*) => do
    logErrorAt auxTy "Auxiliary function type annotations are not yet supported."
  | `(give_by| aux $auxId:ident $auxArgs:term*) => do
    let auxName := auxId.getId
    let args <- auxArgs.mapM (Tactic.elabTerm · none)
    let argTys <- args.mapM (inferType ·)
    let auxTy <- mkArrowN argTys holeTy
    let auxFn <- mkFreshExprMVar auxTy (userName := auxName.target)
    let auxApp <- Term.ensureHasType holeTy (mkAppN auxFn args)
    let auxMv := auxFn.mvarId!
    -- Remove from the new hole's local context the variables which are used
    -- in arguments to the new function.
    auxMv.modifyLCtx fun lctx => lctx.foldl (init := lctx) fun lctx decl =>
      if auxApp.hasAnyFVar (· == decl.fvarId) then lctx.erase decl.fvarId
      else lctx
    -- Build a proper closed lambda for rootMv by abstracting the prePatt fvars.
    -- This avoids the display issue where `rev := fun xs ↦ ?rev` instead of
    -- `rev := fun xs ↦ ?fastrev xs []`, which happens because MVarId.intro stores
    -- `rootMv := fun xs => Expr.mvar holeMv` with xs only accessible via holeMv's
    -- local context (which is erased from auxMv's context).
    let prePattVarNames := (prePatt?.map (·.ps) |>.getD []).filterMap fun
      | .var n => some n | _ => none
    let prePattFVars <- prePattVarNames.mapM fun n => do
      let some decl := (← getLCtx).findFromUserName? n
        | throwError "Internal: pattern var '{n}' not found in aux context"
      return decl.fvarId
    let lambda <- mkLambdaFVars (prePattFVars.map .fvar).toArray auxApp
    -- Use rootMv? (the pre-refineTakeArgs mvar) to assign the closed lambda.
    -- rootMv from findUserName? may be the inner mvar (after intro), which has wrong type.
    let trueRootMv := rootMv?.getD rootMv
    trueRootMv.eraseAssignment
    trueRootMv.assign lambda
    Tactic.appendGoals [auxMv]
  | _ => throwUnsupportedSyntax

syntax (name := blankHole) "blank" ident : term

def elabGivePattBy
  (p : Term) (f : Ident) (rest : TSyntaxArray `term) (b : TSyntax `give_by)
  : TacticM Unit := Tactic.withMainContext do
  let mv <- findCalcTarget f.getId f
  let mv_ty <- mv.getType''
  let (args, _) := unarrow mv_ty
  let (qs, _mvs) <- mkPatt rest.toList args
  let (pattern, names) <- PatternMap.findMatch mv rest.toList args (pattRef? := p)
  let tag <- mkFreshUserName (f.getId.str "body")
  let body <- `(blank $(mkIdent tag))
  let hole <- pattern.refine {
    names, body, goal_name := f, goal_ty := mv_ty, ps := qs
  }
  let lctx <- hole.withContext getLCtx
  let tempLCtx :=
    applyNames lctx (names.map fun _ (old, _) => old) f.getId
  -- hole.modifyLCtx <| fun lctx =>
  withLCtx' tempLCtx do
    elabGiveBy f b (prePatt? := pattern) (mv? := hole) (rootMv? := mv)
  return ()

def elabGiveAsk (v : TSyntax `ident) : TacticM Unit
  := Tactic.withMainContext do
  let mv <- findCalcTarget v.getId v
  let patts <- allPatterns mv
  if !patts.isEmpty then
    let mut fmt : MessageData := m!"Available 'give' patterns for {v}:"
    for patt in patts do
      fmt := fmt ++ indentD (format patt)
    fmt := fmt ++ m!"\n\nOr, use: 'give {v} by ...'"
    for help in giveByHelp do
      fmt := fmt ++ indentD m!"... {help}"
    fmt := fmt ++ "\n"
    logInfo fmt
  else
    logInfo m!"No available 'give' patterns for {v}"

private def tryClose (f : TacticM a) : TacticM Unit := do
  let main_goal <- getMainGoal
  discard <| f
  main_goal.withContext do
    discard <| tryTactic main_goal.applyRfl

elab_rules : tactic
  | `(tactic| give $v:ident $args:binderIdent* $mode:give_mode => $tac) =>
    tryClose <| match mode with
    | `(give_mode| as $vs:ident*) =>
        discard <| elabGive v args vs tac (keepGoals := true)
    | `(give_mode| as? $vs:ident*) => Tactic.withMainContext do
        let res <- elabGive v args vs tac (keepGoals := true)
        let names <- res.mapM fun mv => mv.getTag <&> (·.toString)
        logInfoAt mode m!"Generated {res.length} goals: {String.intercalate ", " names}\n\
        To rename them, use:\n  give {v} as x y z ... => {tac}"
    | _ => throwUnsupportedSyntax
  | `(tactic| give $v:ident $args:binderIdent* => $tac) =>
    tryClose <| elabGive v args #[] tac (keepGoals := true)
  | `(tactic| give $h:ident : $p:term := $to_term:term) => do
    tryClose <| elabGiveDefHyp h p to_term
  | `(tactic| give $p:term := $to_term:term) => do
    tryClose <| elabGiveDef p to_term
  | `(tactic| give $v:ident by $b:give_by) => do
    tryClose <| elabGiveBy v b
  | `(tactic| give $p:term by $b:give_by) =>
    if let `($f:ident $rest*) := p then
      tryClose <| elabGivePattBy p f rest b
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
  field_body.mvarId!.setUserName as_name.target
  let fv <- intro_let_in_main_goal as_name field_ty (.mvar (field_body.mvarId!))
  -- field_body was created before 'as_name' was introduced into the main goal's lctx,
  -- so its lctx doesn't yet contain the let binding for the function being calculated.
  -- Extend it now so that inner goals derived from field_body (e.g. the branches of
  -- 'give f n by if h : ...') can reference 'as_name' and prove properties like
  -- 'f 10 = 0' before the negative branch is filled in.
  let extLCtx <- Tactic.withMainContext getLCtx
  field_body.mvarId!.modifyLCtx fun _ => extLCtx
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
    let possible := spec_fields.toList.map (m!"{·.fst}")
    logWarning m!"Possible calculation targets:\
    {indentD <| MessageData.joinSep possible ", "}\n"
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
    field_mv.setUserName as_name
  for (_, as_name, _) in vals do
    Tactic.evalTactic (<- `(tactic| refold $(mkIdent as_name)))

/- TODO:
Support this more generally, so we could write:

  calculate f : Int -> Int, foo, bar

then foo and bar are fields from the goal type, but f is a new thing,
equivalent to writing:

  let f : Int -> Int := ?f
-/
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

-- TODO: May not need this anymore.
-- TODO: Or, keep it, and auto-instantiate remaining with 'default'
elab (name := collectTac)
  "collect " body:tacticSeq : tactic =>
  Tactic.withMainContext do
  -- patternsRef.set {}
  -- let target <- Tactic.getMainTarget
  Tactic.evalTactic body
  -- Unsure if I still need this...
  -- let mctx <- getMCtx
  -- for (mv, decl) in mctx.decls do
  --   if !decl.userName.isAnonymous &&
  --      !(<- mv.isAssignedOrDelayedAssigned) then
  --     Tactic.pushGoal mv

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
  for (mv, decl) in mctx.decls do
    if decl.userName = v.getId then
      logInfo m!"found decl for {v.getId}
    name: {mv.name}
    type: {<- mv.getType}
    expr: {Expr.mvar mv}
    synthetic? {decl.kind.isSyntheticOpaque}
    readonly? {<- mv.isReadOnly}
    declared? {<- mv.isDeclared}
    delayed?  {<- mv.isDelayedAssigned}
    assigned? {<- mv.isAssigned}
    lctx: {<- mv.withContext showLCtx}"

elab "dbg_reduce" t:term : tactic => withMainContext do
  let exp <- withoutErrToSorry <| Term.elabTerm t none
  let exp' <- reduce exp
  logInfo m!"{exp}\n --> {exp'}"

@[term_elab blankHole]
def elabQ : TermElab := fun stx typ? => match stx with
  | `(blank $v:ident) => do
    tryPostponeIfNoneOrMVar typ?
    let mv_expr <- mkFreshExprMVar typ?
    let mv := mv_expr.mvarId!
    mv.setTag v.getId
    return mv_expr
  | _ => throwUnsupportedSyntax

structure Eg where
  f : Nat -> Nat
  g : Colour -> Int
  correct : ∀ n, f n <= n

def test_def : Eg := by
  calculate f, g
  give g c by cases of c
  give g Colour.Red := 1
  give g Colour.Blue := 2
  give g Colour.Green := 3
  give f n := n
  grind

set_option pp.rawOnError true

structure EgIf where
  f : Nat -> Nat
  correct : ∀ n, f n ≤ n + 1


def test_if : EgIf := by
  calculate f
  -- TODO: for tomorrow, we should be able to prove things about the positive
  -- case before defining the negative one.
  give f n by if n > 5
  give f n (h := true) := n
  -- have h : f 10 = 0 := by
  --   rfl
  give f v (h := false) := v
  grind

def test_if2
  : Σ' f : Nat -> Nat -> Nat, ∀ n, f 0 n = 0 := by
  calculate fst as f
  give f by recursion
  give h : f .zero m := 0
  give h1 : f (.succ n) u := u
  -- Prove the actual theorem
  intro n
  apply h n
  -- Prove the given hypotheses
  all_goals { intros; trivial }

set_option pp.mvars.delayed true

def test_if3
  : Σ' f : Nat -> Nat -> Nat, ∀ l, f l 0 = 0 := by
  calculate fst as f
  give f n by recursion
  -- `give h0 :` defines the zero case AND introduces h0 : ∀ m, f m 0 = 0
  give h0 : f m .zero := 0 * m

  give f m (.succ v) by if h : v = 3

  -- should be: p : ∀ m, n,  f m (.succ n)
  give h1 : f m (.succ n) (h := true) := m
  -- have p : ∀ m n, ∀ (h : n = 3), f m (.succ n) = m := fun m n h => ?b
  give f m (.succ n) (h := false) := n
  -- when we 'give', we could automatically try to close associated hypotheses
  intro l
  -- simp only [Nat.zero_mul] at h0
  -- apply h0 l
  -- grind

def test_aux_def : List Nat := by
  let rev : List Nat -> List Nat := ?target.rev
  -- give rev as fastrev =>
  --   refine fun xs => (?fastrev : List Nat -> List Nat -> List Nat) xs []
  give rev xs by aux fastrev xs ([] : List Nat)
  give fastrev by recursion
  give fastrev [] ys := ys
  give fastrev (x :: xs) ys := fastrev xs (x :: ys)
  exact []

def eg :
    Σ' f : List Nat -> Nat -> List Nat,
    f [] 5 = [5]
  := by
  collect
    calculate fst as f
    -- give f (y :: ys) n a true := n
    give f => apply List.rec
    -- give f.nil n by if n = 5
    -- give f.nil as f.cond.true f.cond.false =>
    --   refine fun n => if h : n = 5 then ?x else ?y
    give f.nil as f.nil' => refine fun n => blank u
    give f.nil' as f.cond.true f.cond.false => refine fun n => if n == 5 then ?x else ?y
    unfold f
    simp only [BEq.rfl]
    give f.cond.true := [5]
  give f.cond.false := []
  give f.cons => exact fun n ns «f.ns» m => []

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

@[simp]
private def rev {a} : List a → List a
  | [] => []
  | x :: xs => rev xs ++ [x]

private structure RevSpec a : Type where
  fastrev : List a -> List a -> List a
  correct : ∀ xs ys, rev xs ++ ys = fastrev xs ys

def revCalc {a} : RevSpec a := by
  calculate fastrev
  give fastrev by recursion
  intro xs
  (induction xs) <;> intro ys
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
    _ = fastrev xs ([x] ++ ys)
        := by rw [ih]
    _ = fastrev xs (x :: ys)
        := by rfl
    _ = fastrev (x :: xs) ys
        := by give fastrev (x :: xs) ys := fastrev xs (x :: ys)

def fastrev {a} : List a -> List a := fun xs => revCalc.fastrev xs []

-- inductive Exp' : Type
--   | val : Nat -> Exp'
--   | add : Exp' -> Exp' -> Exp'
--   deriving BEq

-- @[simp]
-- def eval' : Exp' -> Nat
--   | .val n => n
--   | .add x y => eval' x + eval' y

-- inductive Code' where
--   | push : ℕ → Code' → Code'
--   | add : Code' → Code'

-- abbrev Stack' := List Nat

-- compile_inductive% Exp'
-- compile_inductive% Code'
-- open Exp' Code'

-- structure CompSpec' where
--   comp : Exp' -> Code' -> Code'
--   exec : Code' -> Stack' -> Stack'
--   correct : ∀ e c s, exec c (eval' e :: s) = exec (comp e c) s

-- def comp_calc' : CompSpec' := by
--   calculate comp, exec
--   give comp by recursion
--   give exec by recursion
--   intro e
--   (induction e) <;> intros c s
--   case val n =>
--     calc
--       exec c (eval' (Exp'.val n) :: s)
--       _ = exec c (n :: s) := by rfl
--       _ = exec (Code'.push n c) s
--         := by give exec (Code'.push n c) s := exec c (n :: s)
--       _ = exec (comp (Exp'.val n) c) s
--         := by give comp (Exp'.val n) c := Code'.push n c
--   case add x y ih_x ih_y =>
--     calc
--       exec c (eval' (Exp'.add x y) :: s)
--       _ = exec c ((eval' x + eval' y) :: s) := by rfl
--       _ = let u_1 := eval' y; let u := eval' x;
--           exec c ((u + u_1) :: s) := by rfl
--       _ = let u_1 := eval' y; let u := eval' x;
--           exec (Code'.add c) (u :: u_1 :: s)
--           := by define exec (Code'.add c) (u :: u_1 :: s) := exec c ((u + u_1) :: s)
--       _ = exec (Code'.add c) (eval' x :: eval' y :: s) := by rfl
--       _ = exec (comp x (Code'.add c)) (eval' y :: s)
--           := by simp only [ih_x]
--       _ = exec (comp y (comp x (Code'.add c))) s
--           := by simp only [ih_y]
--       _ = exec (comp (Exp'.add x y) c) s
--           := by give comp (Exp'.add x y) c := comp y (comp x (Code'.add c))

-- #print comp_calc'

-- -- Test: give by cases of
-- def comp_calc'' : CompSpec' := by
--   calculate comp, exec
--   give comp by recursion
--   give exec by recursion
--   -- Case-split the stack argument of exec.add, then fill the real case
--   give exec (Code'.add c) s by cases of s
--   give exec (Code'.add c) (u :: s) by cases of s
--   give exec (Code'.add c) (u :: u_1 :: s) := exec c ((u + u_1) :: s)
--   give comp (Exp'.val n) c := Code'.push n c
--   give comp (Exp'.add x y) c := comp y (comp x (Code'.add c))
--   give exec (Code'.push n c) s := exec c (n :: s)
--   -- Fill unused exec.add cases (nil and singleton stack)
--   all_goals (try exact default)
--   -- Correctness proof
--   intro e
--   (induction e) <;> intros c s
--   case val n => rfl
--   case add x y ih_x ih_y =>
--     calc
--       exec c (eval' (Exp'.add x y) :: s)
--       _ = exec c ((eval' x + eval' y) :: s) := by rfl
--       _ = let u_1 := eval' y; let u := eval' x; exec c ((u + u_1) :: s) := by rfl
--       _ = let u_1 := eval' y; let u := eval' x;
--           exec (Code'.add c) (u :: u_1 :: s) := by rfl
--       _ = exec (Code'.add c) (eval' x :: eval' y :: s) := by rfl
--       _ = exec (comp x (Code'.add c)) (eval' y :: s) := by simp only [ih_x]
--       _ = exec (comp y (comp x (Code'.add c))) s := by simp only [ih_y]
--       _ = exec (comp (Exp'.add x y) c) s := by rfl

-- #print comp_calc''

end Tactic.Calculation
