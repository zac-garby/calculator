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

def all_suggestions : CalcSuggester := fun goal lhs rhs => do
  let env <- getEnv
  let sugg_names := suggester_ext.getState env
  sugg_names.foldlM (init := #[]) fun acc n => do
    let some f_info := env.find? n | throwError "couldn't find suggester: {n}"
    let f <- unsafe evalExpr CalcSuggester (f_info.type) (mkConst n)
    let suggs <- f goal lhs rhs
    pure (suggs ++ acc)

end Tactic.Calculation
