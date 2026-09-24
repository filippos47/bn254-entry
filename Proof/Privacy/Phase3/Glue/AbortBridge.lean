/-
Phase 3 glue: **the bridge from P4's restated abort bound to `AbortBound`.**

`Glue.AbortBound.perQuery` takes an existential finite site type. `Lazy.AbortPerQuery'` (P4,
`Lazy/AbortReduction.lean`) is the same statement at the site type `Lazy.AbortSite`. The lazy
development imports `Glue.Assembly`, so `Assembly` cannot name `Lazy.AbortSite` itself; this module
closes the gap.

* `AbortBound.of_perQuery'`: `Lazy.AbortPerQuery' H I^U → AbortBound hybrids`.
* `AbortBound.of_keyAveraged`: for the opened hybrids of P1b and P4 (`openedHybrid`,
  `idealUniformHybrid`), `Lazy.KeyAveragedFailBound → AbortBound hybrids`, through P4's
  `abortBound_perQuery'_of`.

This is a chain-end module: it imports the lazy development, which imports `Glue.Assembly`, so it
sits outside the `Proof.Privacy.Phase3.Glue` root. `Glue.Final` imports it, and `Proof.Privacy`
reaches it through `Glue.Final`.
-/

import Proof.Privacy.Phase3.Glue.Assembly
import Proof.Privacy.Phase3.Lazy.AbortPerQuery

namespace Kriterion.ArgoMAC.Phase3.Glue

/-- P4's per-abort-site statement is `AbortBound`, at the site type `Lazy.AbortSite`. -/
theorem AbortBound.of_perQuery' {hybrids : Hybrids}
    (bound : Lazy.AbortPerQuery' hybrids.opened hybrids.idealUniform) : AbortBound hybrids :=
  ⟨fun field group adversary parameter scalar small => by
    obtain ⟨count, nonneg, total, le⟩ := bound field group adversary parameter scalar small
    exact ⟨Lazy.AbortSite, inferInstance, count, nonneg, total, le⟩⟩

/-- **`H_abort` from the key-averaged failure bound**, for the opened hybrids. -/
theorem AbortBound.of_keyAveraged {hybrids : Hybrids}
    (opened : @Hybrids.opened hybrids =
      (Kriterion.ArgoMAC.Security.Phase3.openedHybrid : HybridGame))
    (idealUniform : @Hybrids.idealUniform hybrids = (Lazy.idealUniformHybrid : HybridGame))
    (bound : Lazy.KeyAveragedFailBound) : AbortBound hybrids := by
  apply AbortBound.of_perQuery'
  rw [opened, idealUniform]
  exact Lazy.abortBound_perQuery'_of bound

end Kriterion.ArgoMAC.Phase3.Glue
