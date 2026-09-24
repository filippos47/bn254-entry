/-
**Phase 3, P1m — (B1): the hash conjunct of `PerPairBound (designedShadow scalar) scalar
(4/2^128)`.**

* On the curve (`hash_onCurve_le`, `BoundsHash.lean`): a key is the opening's bridge input
  (`≤ 2/p`: the bridge value is affine in one uniform mask coordinate, two bridge preimages per key)
  or a limb input of a switch at its one-hot label (`≤ 1/2^128`: fold-label entropy).
* Off the curve (`offHash_le`, `BoundsFixedOff.lean`): a key is a limb input of a system-A switch at
  its one-hot label (`≤ 1/2^128`).
* **`designedShadow_hashBound`** — the hash conjunct, `≤ 4/2^128` on and off the curve.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedOff

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
variable [FieldCertificate] [GroupCertificate]
variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]

/-- **The hash conjunct of `PerPairBound (designedShadow scalar) scalar (4/2^128)`.** -/
theorem designedShadow_hashBound (scalar : NonZeroScalar) (pub : PubPart) (input : AffineInput)
    (k : BaseField) :
    (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.hashIn k} ≤
      4 / 2 ^ 128 := by
  refine keyedPoints_le_of_source _ _ _ _ _ _ fun source => ?_
  cases output : Scheme.scheme.function scalar input with
  | none => exact le_trans (offHash_le scalar source input k) delta_le_four
  | some target => exact hash_onCurve_le scalar designedOff source input target k

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
