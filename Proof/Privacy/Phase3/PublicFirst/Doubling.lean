/-
**Phase 3, P1e — a sharper doubling bound: the offsets' hit mass under the good-tail law.**

A plain union bound charges the good-tail restriction as a distance (`91/#Point`) on top of the
uniform-tail clamp. The corrected middle game of `G1U → HW` must also flag the **collision
extension** of the exceptional event (root `PublicFirst` §4), so it needs room below
`exceptionalError = 364/(r−1)`, and the additive charge leaves only `≈ 2^-500`.

Here the restriction is charged **multiplicatively** instead: conditioning the uniform tail on the
good tails costs a factor `1/Pr[good] ≤ 1/(1 − 91/#Point)` (`goodTails_mass_mul_le`,
`good_mass_ge`), so for any per-digit target sets `A d`

  `Pr_good[∃ d, K_d ∈ A d] · (1 − 91/#Point) ≤ (Σ_d |A d|) / #Point`   (`goodTails_hit_mul_le`)

with `K = clampOffsets radixMap tail` the construction's offsets. At singletons (the doubling event,
`K_d = T_d`) this is `≈ 91/#Point` (`doubling_mass_mul_le`). The reveal bound
(`BoundsRevealBound`) uses it at two targets per digit (both exceptional kinds), `≈ 182/#Point`: half
of `exceptionalError`, leaving the other half for the collision extension (whose targets are the
`≤ 2^{|S|}` inputs agreeing with `u` off the collision set `S`).
-/

import Proof.Privacy.Phase3.OpeningBound

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.Phase3 (GoodTails)
open scoped ENNReal

noncomputable section

theorem mass_add_not {X : Type} (law : PMF X) (event : X → Prop) :
    law.toOuterMeasure {x | event x} + law.toOuterMeasure {x | ¬ event x} = 1 := by
  classical
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add, ← law.tsum_coe]
  refine tsum_congr fun x => ?_
  by_cases hit : event x <;> simp [hit, Set.indicator]

variable [FieldCertificate] [GroupCertificate]

/-- **Conditioning on the good tails costs the factor `1/Pr[good]`.** -/
theorem goodTails_mass_mul_le (event : Set (Fin 90 → Point)) :
    (PMF.uniformOfFintype GoodTails).toOuterMeasure {tail | tail.1 ∈ event}
        * (PMF.uniformOfFintype (Fin 90 → Point)).toOuterMeasure {tail | GoodTail radixMap tail}
      ≤ (PMF.uniformOfFintype (Fin 90 → Point)).toOuterMeasure event := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  have sameCard : Fintype.card {tail : Fin 90 → Point | GoodTail radixMap tail}
      = Fintype.card GoodTails := Fintype.card_congr (Equiv.refl _)
  have goodPos : (Fintype.card GoodTails : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card GoodTails := Fintype.card_pos
    exact_mod_cast this.ne'
  have smaller : Fintype.card {tail : GoodTails | tail.1 ∈ event} ≤ Fintype.card event :=
    Fintype.card_le_of_injective (fun tail => ⟨tail.1.1, tail.2⟩) (by
      intro first second same
      simp only [Subtype.mk.injEq] at same
      exact Subtype.ext (Subtype.ext same))
  rw [sameCard, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
    ← mul_assoc ((Fintype.card GoodTails : ℝ≥0∞)⁻¹), ENNReal.inv_mul_cancel goodPos
      (ENNReal.natCast_ne_top _), one_mul]
  exact mul_le_mul' (Nat.cast_le.mpr smaller) le_rfl

/-- **The good tails have mass at least `1 − 91/#Point`** under the uniform tail. -/
theorem good_mass_ge :
    1 - 91 * (Fintype.card Point : ℝ≥0∞)⁻¹
      ≤ (PMF.uniformOfFintype (Fin 90 → Point)).toOuterMeasure {tail | GoodTail radixMap tail} := by
  have total := mass_add_not (PMF.uniformOfFintype (Fin 90 → Point)) (GoodTail radixMap)
  have bad := notGood_mass_le
  calc 1 - 91 * (Fintype.card Point : ℝ≥0∞)⁻¹
      ≤ 1 - (PMF.uniformOfFintype (Fin 90 → Point)).toOuterMeasure
          {tail | ¬ GoodTail radixMap tail} := tsub_le_tsub_left bad 1
    _ = _ := by
      rw [← total]
      exact ENNReal.add_sub_cancel_right (ne_top_of_le_ne_top ENNReal.one_ne_top
        (total ▸ le_add_self))

theorem clampPoints_zero {G : Type} [AddCommGroup G] (f : G →+ G) {n : ℕ} (tail : Fin n → G) :
    clampPoints f 0 tail = clampOffsets f tail := by
  simp only [clampPoints, clampOffsets, zero_sub]

/-- The uniform-tail offsets hit per-digit target sets with mass `≤ Σ |A d| / #Point`. -/
theorem uniform_hit_le (targets : Fin 91 → Finset Point) :
    (PMF.uniformOfFintype (Fin 90 → Point)).toOuterMeasure
        {tail | ∃ digit, clampOffsets radixMap tail digit ∈ targets digit}
      ≤ ((∑ digit, (targets digit).card : ℕ) : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  classical
  have cover : {tail : Fin 90 → Point | ∃ digit, clampOffsets radixMap tail digit ∈ targets digit}
      ⊆ ⋃ digit, ⋃ point ∈ targets digit,
          {tail | clampPoints radixMap 0 tail digit = point} := by
    rintro tail ⟨digit, member⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, clampPoints_zero]
    exact ⟨digit, _, member, rfl⟩
  refine le_trans (MeasureTheory.measure_mono cover) ?_
  refine le_trans (MeasureTheory.measure_iUnion_fintype_le _ _) ?_
  have each : ∀ digit : Fin 91,
      (PMF.uniformOfFintype (Fin 90 → Point)).toOuterMeasure
          (⋃ point ∈ targets digit, {tail | clampPoints radixMap 0 tail digit = point})
        ≤ (targets digit).card * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
    intro digit
    refine le_trans (MeasureTheory.measure_biUnion_finset_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun point _ =>
      clamp_hit_le (n := 89) radixMap radixMap_injective 0 digit point) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  refine le_trans (Finset.sum_le_sum fun digit _ => each digit) ?_
  rw [← Finset.sum_mul]
  push_cast
  exact le_rfl

/-- **The sharper hit bound under the construction's offset law.** -/
theorem goodTails_hit_mul_le (targets : Fin 91 → Finset Point) :
    (PMF.uniformOfFintype GoodTails).toOuterMeasure
        {tail | ∃ digit, clampOffsets radixMap tail.1 digit ∈ targets digit}
        * (1 - 91 * (Fintype.card Point : ℝ≥0∞)⁻¹)
      ≤ ((∑ digit, (targets digit).card : ℕ) : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ :=
  le_trans (mul_le_mul' le_rfl good_mass_ge)
    (le_trans (goodTails_mass_mul_le
      {tail | ∃ digit, clampOffsets radixMap tail digit ∈ targets digit})
      (uniform_hit_le targets))

/-- **The doubling mass, sharply**: `Pr[∃ d, T_d = K_d] · (1 − 91/#Point) ≤ 91/#Point`. -/
theorem doubling_mass_mul_le (multiples : Fin 91 → Point) :
    (PMF.uniformOfFintype GoodTails).toOuterMeasure
        {tail | ∃ digit, multiples digit = clampOffsets radixMap tail.1 digit}
        * (1 - 91 * (Fintype.card Point : ℝ≥0∞)⁻¹)
      ≤ 91 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  classical
  have same : {tail : GoodTails | ∃ digit, multiples digit = clampOffsets radixMap tail.1 digit}
      = {tail | ∃ digit, clampOffsets radixMap tail.1 digit ∈ ({multiples digit} : Finset Point)} := by
    ext tail
    simp only [Set.mem_setOf_eq, Finset.mem_singleton]
    exact exists_congr fun digit => eq_comm
  rw [same]
  refine le_trans (goodTails_hit_mul_le fun digit => {multiples digit}) (le_of_eq ?_)
  simp

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
