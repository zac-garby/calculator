import Mathlib.Tactic.Common

namespace Tactic.Calculation

set_option linter.hashCommand false
set_option linter.style.setOption false
set_option pp.fieldNotation false

open Option List
open Lean Meta Elab Term Macro Mathlib.Tactic Qq

macro "don't" "care" : term => `(panic! "found out the hard way that we do actually care")

elab "todo" : tactic => return ()
elab "todo" "[" term "]" : tactic => return ()
def no_proof := "todo"

def match_struct_fields (goal_type : Expr)
  : MetaM (Array Expr × Array (Name × Expr)) := do
  matchConstStructure goal_type.getAppFn
    (fun _ => do throwError "target {<- ppExpr goal_type} is not a structure")
    fun ival us ctor => do
      let sinfo := getStructureInfo (<- getEnv) ival.name
      let fields := sinfo.fieldNames
      let mut type <- instantiateTypeLevelParams ctor.toConstantVal us
      let mut params : Array Expr := #[]
      for _ in *...ctor.numParams do
        let .forallE _ d b _ := type | throwError "unexpected constructor type"
        let param <- mkFreshExprMVar d
        params := params.push param
        type := b.instantiate1 param
      let mut field_mvars := #[]
      for _ in fields do
        let .forallE arg_name d b bi := type | throwError "unexpected constructor type"
        if bi.isImplicit then throwError "unexpected implicit param {arg_name}"
        let mvar <- mkFreshExprMVar d
        field_mvars := field_mvars.push (arg_name, mvar)
        type := b.instantiate1 mvar
      if !(<- isDefEq type goal_type) then
        throwError "oops, somehow constructed the wrong structure type {<- ppExpr type}"
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
  let (some decl) := ctx.findFromUserName? name | throwError m!"no assumption with name: {name}"
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
  let (some decl) := ctx.findFromUserName? name | throwError m!"no assumption with name: {name}"
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
  : Tactic.TacticM Expr := do
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
          | throwErrorAt arg0 "can't make recursive call on non-variable-name argument"
        let arg_name := arg_id.getId
        let rec_name := get_rec_name arg_name
        `($(mkIdent rec_name) $args*)
      else
        return stx
    | s => pure s
  let body_fn <- elabTerm body_node_rw (some clause_ty)
  return body_fn

/-- For each calc fvar (`let name := ?mv` in the main goal's lctx) that appears in `e`,
    add a corresponding let-binding to `clauseMv`'s local context.
    Returns the updated mvar and `e` with the outer fvars replaced by the new local ones.
    This keeps field names (like `ins`) visible by name in sub-goals rather than unfolding
    to the raw (possibly partially-assigned) mvar. -/
def liftCalcFvarsIntoClause (clauseMv : MVarId) (e : Expr)
    : Tactic.TacticM (MVarId × Expr) :=
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

partial def define_mv (bind_name : Name) (to_expr : Expr) : Tactic.TacticM Unit :=
  go bind_name
where
  go (name : Name) : Tactic.TacticM Unit := do
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
      | throwErrorAt stx "invalid constructor application here"
    let arg_names <- args.mapM fun
      | .stx s => match get_id s with
        | some name => pure name
        | none => throwErrorAt s "unexpected non-ident constructor argument: {s.getKind}"
      | _ => unreachable!
    return (fn, arg_names)
  else
    throwErrorAt stx "unexpected syntax in pattern: {stx.getKind.toString}"

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
    : Tactic.TacticM (List (Name × Option (TSyntax `term))) :=
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
    : Tactic.TacticM (TSyntax `term) :=
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
      | throwErrorAt f "the name {f.getId} is undefined"
    let mv_ty <- mv.getType''
    let to_expr <- elabTerm to_term (some mv_ty)
    define_mv f.getId to_expr
  | `($f:ident $pat:term $rest*) => do
    let (some search_fn_mv) := mctx.findUserName? f.getId
      | throwErrorAt f "the name {f.getId} is undefined"
    let some (inp_ty, _) := (<- search_fn_mv.getType'').arrow?
      | throwErrorAt f "unexpected argument in definition of non-function {f}"
    -- Expand the constructor pattern to get constructor name and arg names.
    let pat <- liftMacroM <| expandMacros pat
    let (con_stx, con_arg_names) <- collect_ctor_pattern pat
    let con <- elabTerm con_stx (some inp_ty)
    let (con_fn, _) := con.getAppFnArgs
    let con_arg_names := con_arg_names.drop (count_implicit_args (<- inferType con))
    let clause_name <- match con_fn with
    | .str _ con_name => pure (Name.str f.getId con_name)
    | _ => throwErrorAt pat "expected a constructor, but got {con_fn}"
    let some clause_expr := (<- getMCtx).findUserName? clause_name |> (·.map (Expr.mvar ·))
      | throwErrorAt f "unknown defining clause for {f}, for pattern: {pat}"
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
                throwError m!"internal: no binder FVar of type {<- ppExpr arg_ty} for else-arm"
            return .done (mkAppN else_mv apply_fvars)
        return .continue)
    else pure fn
    define_mv clause_name fn'
    if !is_only then
      main_goal.withContext do
        Tactic.evalTactic (<- `(tactic| try rfl))
  | _ => throwUnsupportedSyntax

#allow_unused_tactic! defineTactic

def intro_let_in_main_goal (name : Name) (ty val : Expr) (isDef : Bool := true)
  : Tactic.TacticM FVarId := do
  let mut main_mv <- Tactic.getMainGoal
  if isDef then
    main_mv <- main_mv.define name ty val
  else
    main_mv <- main_mv.assert name ty val
  let (fv, new_main) <- main_mv.intro1P
  Tactic.replaceMainGoal [new_main]
  return fv

def calc_intro_other (as_name : Name) (field_ty : Expr)
  : Tactic.TacticM (Expr × FVarId) := do
  let field_body <- Tactic.withMainContext <| mkFreshExprMVar (some field_ty)
  field_body.mvarId!.setUserName as_name
  let fv <- intro_let_in_main_goal as_name field_ty (.mvar (field_body.mvarId!))
  Tactic.appendGoals [field_body.mvarId!]
  return (field_body, fv)

def calc_intro_for (field_name : Name) (fields : Array (Name × Expr)) (as_name : Name := field_name)
    : Tactic.TacticM (Expr × FVarId)
  := do
  let some (_, field) := fields.find? fun (n, _) => n = field_name
    | throwUnknownNameWithSuggestions field_name (extraMsg :=
      m!", could be any of {fields.map (·.fst)}")
  let field_ty <- inferType field >>= instantiateMVars
  calc_intro_other as_name field_ty

/--
Refine some metavariables by applying a tactic.

Typically used in calculations, for instance:

  ```lean
  calculate comp
  given_by comp => apply Exp.rec
  ```

`calculate comp` introduces a metavar named `comp`, which is then refined
into a recursive definition with a new metavar for each constructor's case.
-/
elab "given_by " vs:ident,* " => " tac:tacticSeq : tactic => Tactic.withMainContext do
  let ids <- vs.getElems.mapM fun v => do
    let id := v.getId
    if (<- getMCtx).findUserName? id |>.isNone then
      throwErrorAt v "unknown goal called '{id}'"
    pure id
  let goals <- Tactic.getGoals
  let goals' <- goals.flatMapM fun goal => do
    let decl <- goal.getDecl
    if ids.elem decl.userName then
      Tactic.evalTacticAt tac goal
    else
      pure [goal]
  Tactic.setGoals goals'
  for v in vs.getElems do
    Tactic.evalTactic (<- `(tactic| try refold $v))

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
    logWarning f!"use `calculate` followed by any of {spec_fields.toList.map fun (n, _) => n}"
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
  Tactic.pushGoals field_mvs
  for (field_name, as_name, (mv_val, _fv), stx) in vals do
    let some field_mv <- field_mvs.findM? fun u => u.getTag <&> (· == field_name)
      | throwErrorAt stx "bug: unknown field name: {field_name}"
    field_mv.assign mv_val
    field_mv.setUserName as_name

@[inherit_doc calculateTactic]
elab (name := calculateGoal) "calculate" "⊢" "as" r:ident : tactic => Tactic.withMainContext do
  let main_goal <- Tactic.getMainGoal
  main_goal.setUserName r.getId

#allow_unused_tactic! calculateGoal

macro "exists_mono" : tactic =>
  `(tactic| (repeat' apply Exists.imp; intro))

private partial def splitHyp (fv : FVarId) : Tactic.TacticM Unit :=
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

end Tactic.Calculation
