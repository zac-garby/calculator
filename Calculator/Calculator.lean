import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

open Nat
open Option
open List
open Lean Meta Elab Term Macro Command

namespace Tactic
namespace Calculation

set_option linter.style.multiGoal false
set_option linter.style.longLine false
set_option linter.hashCommand false

elab (name := defineTactic) "define" v:ident args:ident* ":=" to_term:term : tactic => do
  let bind_name := v.getId
  let body_node: TSyntax `term <- `(fun $args* => $to_term)
  let mctx <- getMCtx
  match mctx.findUserName? bind_name with
  | none => throwUnknownNameWithSuggestions bind_name
  | some mv => do
    if (<- mv.getTag) == bind_name then do
      let mv_ty <- mv.getType'
      let to_expr <- elabTerm body_node (some mv_ty)
      if <- mv.isAssigned then
        if !(<- isDefEq (.mvar mv) to_expr) then
          throwError m!"cannot re-define {<- mv.getTag} as {to_expr}\n  (already assigned to {Expr.mvar mv})"
      else
        mv.assignIfDefEq to_expr
      Tactic.evalTactic (<- `(tactic| try rfl))

#allow_unused_tactic! defineTactic

def of_inductive_ty (ty : Expr) : MetaM (Name × List (Name × Expr)) := do
  let ty <- whnf ty
  match ty.getAppFn with
  | .const name us => match (<- getEnv).find? name with
    | some (.inductInfo i) =>
      let ctors <- i.ctors.mapM fun ctor => do
        let cinfo <- getConstInfo ctor
        match ctor.componentsRev with
        | fn_name :: _ => return (fn_name, cinfo.type.instantiateLevelParams i.levelParams us)
        | [] => throwError f!"can't figure out name for constructor: {ctor}"
      return (name, ctors)
    | _ => throwError "not an inductive type"
  | _ => throwError "not a known constant type"

def match_struct_fields (goal_type : Expr) : TermElabM (Array Expr × Array (Name × Expr)) := do
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

elab (name := calculateTactic) "calculate " vs:ident,* : tactic => Tactic.withMainContext do
  -- look at main goal, get its fields
  let main_goal <- Tactic.getMainGoal
  let main_type <- main_goal.getType''
  let (_, spec_fields) <- match_struct_fields main_type
  if vs.getElems.size == 0 then
    logWarning f!"use `calculate` followed by any of {spec_fields.toList.map fun (n, _) => n}"
  -- for each ident 'v' listed:
  let fvs <- vs.getElems.mapM fun s => do
    let field_name := s.getId
    -- find the constructor they're asking for, split into input and motive
    let (field_ty, inp_ty, mot_ty) <- match spec_fields.find? (fun (n, _) => n = field_name) with
      | none => throwUnknownNameWithSuggestions field_name
      | some (_, field) => do
        let field_type <- inferType field
        match field_type.arrow? with
        | none => throwError m!"cannot calculate non-arrow-type of '{field_name}'"
        | some t => pure (field_type, t)
    -- find the recursor
    let (inp_ty_name, ctors) <- of_inductive_ty inp_ty
    let recursor <- mkConstWithFreshMVarLevels (.str inp_ty_name "rec")
    let rec_ty <- inferType recursor
    -- make the motive (a const function)
    let motive_stx <- `(fun x => $(<- mot_ty.toSyntax))
    let motive <- elabTerm motive_stx none
    -- instantiate the recursor's implicit parameters to new mvars
    -- until we get to the motive. then assign this to our motive, defined above
    let mut (ms, bs, r) <- forallMetaTelescopeReducing rec_ty (some 1)
    while bs.back!.isImplicit do
      let mv := ms.back!.mvarId!
      let (ms', bs', r') <- forallMetaTelescopeReducing r (some 1)
      unless ms'.size == 1 do
        throwError f!"wrong type!"
      if (<- mv.getTag).eqStr "motive" then
        mv.assignIfDefEq motive
      if bs'.back!.isExplicit then break
      (ms, bs, r) := (ms ++ ms', bs ++ bs', r')
    -- get explicit_rec_ty, the recursor type with only explicit (algebra) arguments remaining.
    -- make new mvars for these algebras, and give them useful usernames
    let explicit_rec_ty <- instantiateExprMVars r
    let (algebra_mv_exps, _, concl_ty) <- forallMetaTelescopeReducing explicit_rec_ty (some ctors.length)
    for (exp, ctor, _) in zip algebra_mv_exps.toList ctors do
      let mv := exp.mvarId!
      mv.setUserName (ctor.updatePrefix field_name)
      Tactic.appendGoals [mv]
    if !(<- isDefEq concl_ty field_ty) then
      throwError m!"that's weird, the recursor's conclusion is the wrong type\n{concl_ty}\n  vs\n{field_ty}"
    let final_ty <- instantiateExprMVars concl_ty
    -- add a 'let ... = ...' for this constructor to the main goal, and then intro it as a hypothesis
    let field_body := mkAppN recursor (ms ++ algebra_mv_exps)
    let mut main_mv <- Tactic.getMainGoal
    main_mv <- main_mv.define field_name final_ty field_body
    let (fv, new_main) <- main_mv.intro1P
    Tactic.replaceMainGoal [new_main]
    return (field_name, fv)
  -- split the main goal into its constructor fields, and set each one to the corresponding
  -- recursor binding from above
  let main_mv <- Tactic.getMainGoal
  let new_mvs <- main_mv.constructor
  Tactic.pushGoals new_mvs
  fvs.forM fun (field_name, fv) => do
    new_mvs.forM fun mv => do
      if (<- mv.getTag) == field_name then
        mv.assign (.fvar fv)

def rev {a} : List a → List a
  | [] => []
  | x :: xs => rev xs ++ [x]

structure RevSpec (a : Type) : Type where
  aux : List a -> List a -> List a
  correct : ∀ xs ys, aux xs ys = rev xs ++ ys

def correct {a} : RevSpec a := by
  calculate aux
  intro xs
  induction xs
  case nil =>
    intro ys
    dsimp [rev]
    define aux.nil ys := ys
  case cons x xs ih =>
    intro ys
    dsimp [rev]
    rw [List.append_assoc]
    define aux.cons x xs aux_xs ys := aux_xs (x :: ys)
    dsimp
    rw [ih]

inductive Exp : Type
  | val : Nat -> Exp
  | add : Exp -> Exp -> Exp
  deriving BEq

compile_inductive% Exp

def eval : Exp -> Nat
  | .val n => n
  | .add x y => eval x + eval y

inductive Code where
  | push : Nat -> Code -> Code
  | add : Code -> Code
  | halt : Code

compile_inductive% Code

abbrev Stack := List Nat

structure CompSpec where
  comp : Exp -> Code -> Code
  exec : Code -> Stack -> Stack
  correct : ∀ e c s, exec c (eval e :: s) = exec (comp e c) s

-- def comp_calc : CompSpec := by
--   calculate comp, exec

end Calculation
end Tactic
