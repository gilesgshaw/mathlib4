import Lean.Elab.InheritDoc
import Mathlib.Tactic.MinImports -- for `getDeclName`; see TODO

/-!
# Constructive linter

A linter which ensures that no axioms are used (e.g. `Classical.choice`) which
are not compatible with the general use of Lean as a programming language.

-/

/-
# TODO

Get `getDeclName` upstreamed from `Mathlib.Tactic.MinImports`, and possibly more robust?

Consider that other linters seem to have done some of the following, which may be applicable:
* don't bother reporting if `(←get).messages.hasErrors`
* or instead refer to `(←get).messages.reportedPlusUnreported.isEmpty`
* behave differently if `warningAsError` is true

-/

namespace Lean.Linter

/--
The `constructive` linter ensures that no axioms are used (e.g. `Classical.choice`) which
are not compatible with the general use of Lean as a programming language.
-/
register_option linter.constructive : Bool := {
  defValue := false
  descr    := "enable the constructive linter"
}

/- Note: we only consider non-`unsafe` axioms, since the linter ignores `unsafe` declarations -/
@[inline] private def ConstructiveLinter.allowed_axioms : Std.HashSet Name := {

  /- The axioms of the constructive type theory used in Lean -/
  ``Quot.sound,
  ``propext,

  /- We currently do not allow these axioms -/
  -- ``Lean.ofReduceNat,
  -- ``Lean.trustCompiler,
  -- ``Lean.ofReduceBool,

  /- The use of this axiom will already ensure a warning is emmited -/
  ``sorryAx
}

@[inherit_doc linter.constructive]
def constructiveLinter : Linter where run stx := do
  unless getLinterValue linter.constructive (←getLinterOptions) do return
  let declName ← Mathlib.Command.MinImports.getDeclName stx
  let some declInfo := (←getEnv).find? declName | return
  if declInfo.isUnsafe then return
  let axs := (←collectAxioms declName).toList.filter (· ∉ ConstructiveLinter.allowed_axioms)
  if axs.isEmpty then return
  logLint linter.constructive stx <|
    "This declaration uses disallowed axioms:\n  " ++
      .joinSep (axs.map .ofConstName) ", "

initialize addLinter constructiveLinter

end Lean.Linter
