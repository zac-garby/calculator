import Mathlib.Tactic.Common
import ProofWidgets.Data.Html

namespace Tactic.Calculation

open Lean Meta ProofWidgets Server.Snapshots Server

structure CalcParams extends SelectInsertParams where
  isFirst : Bool
  indent : Nat
  deriving SelectInsertParamsClass, RpcEncodable

/-- What a suggestion does: replace the current calc step with a sequence of steps.

    The chain is: `lhs → intermediate₁ → intermediate₂ → … → original_rhs`
    - `intermediates` holds the (rhs, proof) pairs for every step *except* the last.
    - `finalProof` is the proof of the last step (from the last intermediate, or from
      `lhs` if `intermediates` is empty, to the original goal rhs).
    - `finalProof = none` means remove the step entirely (lhs ≡ rhs definitionally).
-/
structure SuggestionSpec where
  hint : String
  /-- Intermediate steps. Each `(e, p)` means `_ rel e := by p`. -/
  intermediates : Array (Expr × TSyntax `tactic)
  /-- Proof of the final step to the original rhs. `none` = remove this step. -/
  finalProof : Option (TSyntax `tactic) := none
  /-- Optional extra display info shown in the widget next to the button. -/
  info? : Option ProofWidgets.Html := none
  /-- Escape hatch: if set, used as the button directly (bypasses auto-generation). -/
  custom_button? : Option ProofWidgets.Html := none
  /-- Higher precedence is shown first -/
  precedence : Int := 0

instance : BEq SuggestionSpec where
  beq s1 s2 :=
    s1.intermediates.size == s2.intermediates.size
    && (s1.intermediates.zip s2.intermediates).all
      (fun ((e1, p1), (e2, p2)) => e1 == e2 && p1.raw == p2.raw)
    && (s1.finalProof.map (·.raw)) == (s2.finalProof.map (·.raw))
    && s1.finalProof.isSome == s2.finalProof.isSome

private def SuggestionSpec.ble (s1 s2 : SuggestionSpec) : Bool :=
  s1.precedence > s2.precedence
  || (s1.precedence == s2.precedence && (
    if s1.intermediates.size == s2.intermediates.size then
      s1.finalProof.isNone
    else
      s1.intermediates.size < s2.intermediates.size
  ))

instance : LE SuggestionSpec where le s1 s2 := s1.ble s2

instance : DecidableLE SuggestionSpec := fun s1 s2 =>
  if h : s1.ble s2 then isTrue h else isFalse h

abbrev CalcSuggester
  := Widget.InteractiveGoal -> FileWorker.EditableDocument
  -> CalcParams -> (lhs rhs : Expr)
  -> MetaM (Array SuggestionSpec)

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
