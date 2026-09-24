/-
**Phase 3, P1m — `PerPairBound (designedShadow scalar) scalar (4/2^128)` and `DesignedBounds`.**

The three conjuncts, each at `4/2^128`:

* fixed key — `designed_fixed_onCurve` (on the curve), `designed_fixed_off` (off it);
* EncPRF — `designedShadow_encBound`;
* hash — `designedShadow_hashBound`.

`designedBounds` closes `DesignedBounds` through `designedBounds_of_perPair` (its reveal half is
`designedShadow_revealBound`).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedOffKey
import Proof.Privacy.Phase3.PublicFirst.BoundsDesigned

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open scoped ENNReal

noncomputable section

section PerPair

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex] [FieldCertificate]
  [GroupCertificate]

/-- **(B1) for the designed shadow, at `4/2^128`.** -/
theorem designedShadow_perPair (scalar : NonZeroScalar) :
    PerPairBound (designedShadow scalar) scalar (4 / 2 ^ 128) := by
  intro pub input
  refine ⟨fun i x y => ?_, fun j x y => designedShadow_encBound scalar pub input j x y,
    fun k => designedShadow_hashBound scalar pub input k⟩
  cases output : Scheme.scheme.function scalar input with
  | none => exact designed_fixed_off scalar pub input output i x y
  | some target => exact designed_fixed_onCurve scalar pub input target output i x y

end PerPair

/-- **`DesignedBounds`, real.** -/
theorem designedBounds : DesignedBounds :=
  designedBounds_of_perPair fun field group scalar =>
    @designedShadow_perPair (Classical.decEq _) (Classical.decEq _) field group scalar

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
