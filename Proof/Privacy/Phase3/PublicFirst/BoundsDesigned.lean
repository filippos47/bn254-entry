/-
**Phase 3, P1k — the bounds for P1j's `designedShadow`.**

`designedShadow scalar := planBShadow scalar designedOff` (`LiftTV.lean`): on the curve it is P1i's
shadow, off the curve the pads at a uniform coin and system A, with **no** reveal flag. So:

* `offRevealBound_designedOff` — the designed off-curve part never reveals (mass `0`);
* **`designedShadow_revealBound`** — `RevealBound (designedShadow scalar) scalar (364/(r − 1))`,
  real, by transport of `revealBound_planBShadow` (no re-proof);
* `designedBounds_of_perPair` — `DesignedBounds` from its per-pair half alone.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsEnc
import Proof.Privacy.Phase3.PublicFirst.LiftTV

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source)
open scoped ENNReal

noncomputable section

section Designed

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
variable [FieldCertificate] [GroupCertificate]

/-- **The designed off-curve part never reveals.** -/
theorem offRevealBound_designedOff (ρ : ℝ≥0∞) : OffRevealBound designedOff ρ := by
  intro source input
  refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun o => ?_)) zero_le
  by_cases member : o ∈ (offOutcome designedOff source input).support
  · unfold offOutcome at member
    obtain ⟨coin, _, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    obtain ⟨shadowed, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rest
    rcases shadowed with _ | result
    · simp [revealWeight]
    · have noReveal : ¬ designedOff.revealOff source input coin result.2 := fun h => h
      simp [revealWeight, noReveal]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul]

/-- **(B2) for the designed shadow**, at the honest constant `364/(r − 1)`. -/
theorem designedShadow_revealBound (scalar : NonZeroScalar) :
    RevealBound (designedShadow scalar) scalar
      (ENNReal.ofReal Kriterion.ArgoMAC.Phase3.Glue.exceptionalError) :=
  revealBound_planBShadow scalar designedOff (offRevealBound_designedOff _)

end Designed

/-- **`DesignedBounds` from its per-pair half**: the reveal half is real. -/
theorem designedBounds_of_perPair
    (perPair : ∀ (field : FieldCertificate) (group : @GroupCertificate field)
      (scalar : NonZeroScalar),
      (letI := field
       letI := group
       letI : Fintype FixedIndex := Fintype.ofFinite FixedIndex
       letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
       letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
       letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
       PerPairBound (designedShadow scalar) scalar (4 / 2 ^ 128))) :
    DesignedBounds := by
  intro field group scalar
  refine ⟨perPair field group scalar, ?_⟩
  have reveal := @designedShadow_revealBound (Classical.decEq _) (Classical.decEq _) field group
    scalar
  convert reveal using 1

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
