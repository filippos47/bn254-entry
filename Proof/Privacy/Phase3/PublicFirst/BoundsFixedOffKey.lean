/-
**Phase 3, P1m — (B1) the fixed-key conjunct off the curve.**

Off the curve only system A's folds are asked (`off_fixed`): a level-1 fold input is the source's
own label (`offCurveIn_le`, uniform over the key: `hotCurve_key_le`), a fold input of a level `≥ 2`
carries fresh fold material (`offLevelIn_le`), an output is a fresh lazy answer (`offOut_le`), and
every other index is untouched (`offHotAbsent_le`, `offGadget_le`):

* `designed_fixed_off` — off the curve, `Pr[x ∈ fixedIn_i] + Pr[y ∈ fixedOut_i] ≤ 4/2^128`.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedKey

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open scoped ENNReal

noncomputable section

section Conjunct

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **The input half off the curve**: `≤ 2/2^128`. -/
theorem designed_fixedIn_off (scalar : NonZeroScalar) (pub : PubPart) (input : AffineInput)
    (offCurve : Scheme.scheme.function scalar input = none) (i : FixedIndex) (x : Block) :
    (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.fixedIn i x} ≤
      2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [keyedPoints_measure_eq, offCurve]
  cases i with
  | hot lane c f e h =>
    by_cases present : (lane = .curveX ∨ lane = .curveY) ∧ 1 ≤ f.val ∧ f.val < chunkWidth c ∧
        e.val < 2 ^ f.val
    · obtain ⟨curve, one, small, lt⟩ := present
      by_cases first : f.val = 1
      · obtain ⟨κ, labelsEq⟩ := curve_labels curve
        exact le_trans (ENNReal.tsum_le_tsum fun key => mul_le_mul' le_rfl
          (offCurveIn_le scalar (joinSource pub key) input lane κ labelsEq c f e h x first))
          (le_trans (hotCurve_key_le pub input κ c x) delta_le_two)
      · exact tsum_le_of_support _ _ _ fun key _ => le_trans
          (offLevelIn_le scalar (joinSource pub key) input lane curve c f e h x (by omega) small
            lt) delta_le_two
    · exact tsum_le_of_support _ _ _ fun key _ => le_trans
        (offHotAbsent_le scalar (joinSource pub key) input lane c f e h x present) zero_le
  | gadget d κ pos b =>
    exact tsum_le_of_support _ _ _ fun key _ => le_trans
      (offGadget_le scalar (joinSource pub key) input d κ pos b x) zero_le

/-- **The output half off the curve**: `≤ 1/2^128 ≤ 2/2^128`. -/
theorem designed_fixedOut_off (scalar : NonZeroScalar) (pub : PubPart) (input : AffineInput)
    (offCurve : Scheme.scheme.function scalar input = none) (i : FixedIndex) (y : Block) :
    (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.fixedOut i y} ≤
      2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  refine keyedPoints_le_of_source _ _ _ _ _ _ fun source => ?_
  rw [offCurve]
  exact le_trans (offOut_le scalar source input i y) delta_le_two

/-- **The fixed-key conjunct of `PerPairBound (designedShadow scalar) scalar (4/2^128)`, off the
curve.** -/
theorem designed_fixed_off (scalar : NonZeroScalar) (pub : PubPart) (input : AffineInput)
    (offCurve : Scheme.scheme.function scalar input = none) (i : FixedIndex) (x y : Block) :
    (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.fixedIn i x} +
      (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.fixedOut i y} ≤
        4 / 2 ^ 128 := by
  rw [← two_inv_add_two_inv]
  exact add_le_add (designed_fixedIn_off scalar pub input offCurve i x)
    (designed_fixedOut_off scalar pub input offCurve i y)

end Conjunct

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
