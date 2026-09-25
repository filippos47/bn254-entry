/-
**The total cutoff mass and `SamplerCutoff`.**

The sources, with `ρ_F`, `ρ_λ ≤ 2^-500` the field-cell and randomiser cutoffs (`fieldAbort_le`,
`lambdaAbort_le`), `ρ_x ≤ 2^-170` the curve-`x` cutoff (`curveXAbort_le`) and
`ρ_t ≤ 2^-138` the designated preimage's `t` sampler (`BigInt.samplerAbort_le`):

`34,297 ρ_F + (90 ρ_x + 1/#A) + 91 · 2 ρ_λ + 91 ρ_F + ρ_t
  ≤ 2^16 · 2^-500 + (2^7 · 2^-170 + 2^-131) + 2^8 · 2^-500 + 2^7 · 2^-500 + 2^-138 ≤ 2^-128`

(`cells ≤ 2^-129`, `tail ≤ 2^-130`, `lambdas ≤ 2^-131`, `free ≤ 2^-132`, `t ≤ 2^-132`). Every
numeric step is exponent arithmetic on powers of two (`CutoffNat`, `CutoffPow`): the draw counts
are bounded by powers of two (`34,297 ≤ 2^16`, `182 ≤ 2^8`, `91 ≤ 2^7`, `90 ≤ 2^7`) and the
curve-`x` rejection ratio by `5/8` (`5^3 ≤ 2^7`), so no large numeral is formed.
-/

import Proof.Simulator.Cutoff
import Proof.Simulator.CutoffNat
import Proof.Simulator.CutoffPow

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

theorem scalar_large : 3 * 2 ^ 252 + 1 ≤ scalarFieldModulus := Nat.le_of_ble_eq_true rfl

section Numbers

variable [FieldCertificate] [GroupCertificate]

/-- `#A ≥ 3 · 2^252`. -/
theorem affineCount_large : 3 * 2 ^ 252 ≤ affineCount :=
  Nat.le_of_add_le_add_right (Nat.le_trans scalar_large scalar_le_affineCount)

omit [FieldCertificate] [GroupCertificate] in
/-- The accepted and the rejected draws partition the draws. -/
theorem acceptedSet_add_rejectedCount (width : Nat) (accept : Nat → Bool) :
    (acceptedSet width accept).card + rejectedCount width accept = 2 ^ width := by
  have split := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 ^ width))))
    (fun value : Fin (2 ^ width) => accept value.val = true)
  rw [Finset.card_univ, Fintype.card_fin] at split
  unfold rejectedCount acceptedSet
  simp only [Bool.not_eq_true] at split
  exact split

/-- The curve-`x` sampler rejects at most `5 · 2^251` draws: `#A ≥ r − 1` and each accepted `x`
carries at most two offsets. -/
theorem rejectedCount_curveX : rejectedCount fieldWidth curveXAccept ≤ 5 * 2 ^ 251 := by
  have split := acceptedSet_add_rejectedCount fieldWidth curveXAccept
  have lower := affineCount_le
  rw [show acceptedX = acceptedSet fieldWidth curveXAccept from rfl] at lower
  have large := affineCount_large
  have first : (2 : Nat) ^ fieldWidth = 8 * 2 ^ 251 := by
    show (2 : Nat) ^ (3 + 251) = 8 * 2 ^ 251
    rewrite [Nat.pow_add]
    rfl
  have second : (2 : Nat) ^ 252 = 2 * 2 ^ 251 := by
    rewrite [show 252 = 1 + 251 from rfl, Nat.pow_add]
    rfl
  omega

/-- **The curve-`x` sampler aborts with probability below `2^-170`.** -/
theorem curveXAbort_le :
    rejectLaw fieldWidth curveXAccept attempts none ≤ ((2 : ENNReal) ^ 170)⁻¹ :=
  (rejectLaw_none_le fieldWidth _ attempts _ rejectedCount_curveX).trans
    (ratio_pow_le _ fieldWidth attempts 170 fiveEighths_nat)

/-- One over the number of affine offsets is below `2^-131`. -/
theorem affineCount_inv_le : (affineCount : ENNReal)⁻¹ ≤ ((2 : ENNReal) ^ 131)⁻¹ := by
  refine inv_le_of_pow_le _ _ (Nat.le_trans ?_ affineCount_large)
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by decide : 131 ≤ 252))
    (Nat.le_mul_of_pos_left _ (by decide))

/-- **The total cutoff mass is below `2^-128`.** -/
theorem cutoffMass_le :
    (fieldCellCount * rejectLaw fieldWidth (fun value => decide (value < pNat)) attempts none + 0) +
      ((90 * rejectLaw fieldWidth curveXAccept attempts none + (affineCount : ENNReal)⁻¹) +
        ((digitCount : ENNReal) * (((2 : Nat) : ENNReal) *
            rejectLaw fieldWidth (fun value => decide (1 ≤ value ∧ value < pNat)) attempts none) +
          (((digitCount * 1 : Nat) : ENNReal) *
              rejectLaw fieldWidth (fun value => decide (value < pNat)) attempts none +
            ((2 : ENNReal) ^ 138)⁻¹)) + 0) ≤
      ((2 : ENNReal) ^ 128)⁻¹ := by
  have cells : (fieldCellCount : ENNReal) *
      rejectLaw fieldWidth (fun value => decide (value < pNat)) attempts none ≤
      ((2 : ENNReal) ^ 129)⁻¹ :=
    (mul_le_mul' le_rfl fieldAbort_le).trans (mul_inv_pow_le _ 500 129
      (count_le _ 16 129 500 (by rw [fieldCellCount_eq]; exact Nat.le_of_ble_eq_true rfl)
        (by decide)))
  have points : ((90 : Nat) : ENNReal) * rejectLaw fieldWidth curveXAccept attempts none ≤
      ((2 : ENNReal) ^ 131)⁻¹ :=
    (mul_le_mul' le_rfl curveXAbort_le).trans
      (mul_inv_pow_le 90 170 131 (count_le _ 7 131 170 (by decide) (by decide)))
  rw [Nat.cast_ofNat] at points
  have tailPart : 90 * rejectLaw fieldWidth curveXAccept attempts none +
      (affineCount : ENNReal)⁻¹ ≤ ((2 : ENNReal) ^ 130)⁻¹ := by
    rw [← inv_pow_add_self 130 131 rfl]
    exact add_le_add points affineCount_inv_le
  have lambdas : (digitCount : ENNReal) * (((2 : Nat) : ENNReal) *
      rejectLaw fieldWidth (fun value => decide (1 ≤ value ∧ value < pNat)) attempts none) ≤
      ((2 : ENNReal) ^ 131)⁻¹ := by
    rw [← mul_assoc, ← Nat.cast_mul]
    exact (mul_le_mul' le_rfl lambdaAbort_le).trans (mul_inv_pow_le _ 500 131
      (count_le _ 8 131 500 (by unfold digitCount; decide) (by decide)))
  have free : (((digitCount * 1 : Nat) : ENNReal)) *
      rejectLaw fieldWidth (fun value => decide (value < pNat)) attempts none ≤
      ((2 : ENNReal) ^ 132)⁻¹ :=
    (mul_le_mul' le_rfl fieldAbort_le).trans (mul_inv_pow_le _ 500 132
      (count_le _ 7 132 500 (by unfold digitCount; decide) (by decide)))
  have preimage : ((2 : ENNReal) ^ 138)⁻¹ ≤ ((2 : ENNReal) ^ 132)⁻¹ :=
    ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ one_le_two (by decide))
  refine (add_le_add (add_le_add cells le_rfl) (add_le_add (add_le_add tailPart
    (add_le_add lambdas (add_le_add free preimage))) le_rfl)).trans (le_of_eq ?_)
  rw [add_zero, add_zero, inv_pow_add_self 131 132 rfl, inv_pow_add_self 130 131 rfl,
    inv_pow_add_self 129 130 rfl, inv_pow_add_self 128 129 rfl]

end Numbers

/-! ### The cutoff -/

/-- **`SamplerCutoff`**: the machine's bounded samplers are within `2^-128` of the exact ones in
the abstract ideal game. -/
theorem samplerCutoff : SamplerCutoff := by
  intro field group adversary parameter scalar
  have lift := AbortClose.optionProduct digitCount (fun _ => pairLaw)
    (fun _ => (PMF.uniformOfFintype (NonZeroBase × NonZeroBase)).map some) (fun _ => pair_close)
  rw [optionProduct_uniform] at lift
  have finite : ((2 : ENNReal) ^ 128)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (two_pow_ne_zero 128)
  have bound := @game_close field group (Classical.decEq _) (Classical.decEq _) _ _ _ _ _
    boundedSamplers idealSamplers source_close tail_close lift free_close
    (fun vector => (preimage_close vector).mono
      (BigInt.samplerAbort_le (vectorEnc vector) (vectorEnc_lt vector)))
    (ne_top_of_le_ne_top finite cutoffMass_le) adversary parameter scalar
  refine bound.trans ((ENNReal.toReal_mono finite cutoffMass_le).trans (le_of_eq ?_))
  unfold machineCutoffError
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, one_div]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
