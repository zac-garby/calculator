import Mathlib.Tactic.Common
import ProofWidgets.Data.Html

namespace Tactic.Calculation

open Lean Meta ProofWidgets.Jsx ProofWidgets Server.Snapshots Server

structure Suggestion where
  hint : String
  info? : Option Html := none
  newLhs? : Option Expr := none
  proofStr? : Option String := none

abbrev CalcSuggester
  := (goal : Widget.InteractiveGoal) -> (lhs rhs : Expr)
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
