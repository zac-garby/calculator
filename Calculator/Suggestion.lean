import Mathlib.Tactic.Common
import ProofWidgets.Data.Html

namespace Tactic.Calculation

open Lean Meta ProofWidgets.Jsx ProofWidgets Server.Snapshots Server

structure CalcParams extends SelectInsertParams where
  isFirst : Bool
  indent : Nat
  deriving SelectInsertParamsClass, RpcEncodable

structure Suggestion where
  hint : String
  info? : Option Html := none
  new_lhs? : Option Expr := none
  new_rhs? : Option Expr := none
  proof? : Option String := none
  custom_button? : Option Html := none

instance : BEq Suggestion where
  beq s1 s2 := false -- s1.hint = s2.hint

abbrev CalcSuggester
  := Widget.InteractiveGoal -> FileWorker.EditableDocument
  -> CalcParams -> (lhs rhs : Expr)
  -> MetaM (Array Suggestion)

initialize suggester_ext : SimplePersistentEnvExtension Name NameSet
  <- registerSimplePersistentEnvExtension {
      name := `suggester_ext
      addImportedFn := mkStateFromImportedEntries (·.insert) .empty
      addEntryFn := (·.insert)
    }

initialize registerBuiltinAttribute {
  name := `suggest
  descr := "register a calculation suggestion function"
  add := fun name stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    ensureAttrDeclIsPublic `suggest name kind
    setEnv (suggester_ext.addEntry (<- getEnv) name)
}

def all_suggestions : CalcSuggester := fun doc params goal lhs rhs => do
  let env <- getEnv
  let sugg_names := suggester_ext.getState env
  sugg_names.foldlM (init := #[]) fun acc n => do
    let some f_info := env.find? n | throwError "couldn't find suggester: {n}"
    let f <- unsafe evalExpr CalcSuggester (f_info.type) (mkConst n)
    let suggs <- f doc params goal lhs rhs
    pure (acc.mergeUnsortedDedup suggs)
    -- pure (suggs ++ acc)

end Tactic.Calculation
