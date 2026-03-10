import Mathlib.Tactic.Common
import ProofWidgets.Data.Html

namespace Tactic.Calculation

open Lean Meta ProofWidgets Server.Snapshots Server

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
  beq s1 s2
    := s1.new_lhs? == s2.new_lhs?
    && s1.new_rhs? == s2.new_rhs?
    && s1.proof? == s2.proof?

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

end Tactic.Calculation
