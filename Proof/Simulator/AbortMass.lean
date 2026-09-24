/-
The abort mass of bounded rejection, exactly, and its value for the machine's field samplers.

`rejectLaw_none`: `count` attempts at `width`-bit draws abort with probability
`(#rejected / 2^width) ^ count`. For the field cells and the designated vector's non-collector
coordinates (`width = 254`, accept `< p`), `fieldAbort_le`: the abort mass is below `2^-500`; for
the randomisers (accept `1 ≤ · < p`), `lambdaAbort_le`: also below `2^-500`. The preimage
sampler's abort mass (`≤ 2^-138`) is `BigInt.samplerAbort_le` (`BigIntAccept.lean`).
-/

import Proof.Simulator.Sampling

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography

/-- The number of rejected `width`-bit draws. -/
def rejectedCount (width : Nat) (accept : Nat → Bool) : Nat :=
  (Finset.univ.filter fun value : Fin (2 ^ width) => accept value.val = false).card

/-- **The abort mass of bounded rejection.** -/
theorem rejectLaw_none (width : Nat) (accept : Nat → Bool) (count : Nat) :
    rejectLaw width accept count none =
      ((rejectedCount width accept : ENNReal) / 2 ^ width) ^ count := by
  induction count with
  | zero => simp [rejectLaw]
  | succ count ih =>
      rw [rejectLaw, PMF.bind_apply, tsum_fintype, pow_succ]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
      have each : ∀ value : Fin (2 ^ width),
          (if accept value.val then PMF.pure (some value.val) else rejectLaw width accept count) none =
            if accept value.val = false then rejectLaw width accept count none else 0 := by
        intro value
        cases accept value.val <;> simp
      simp only [each, ih, mul_ite, mul_zero]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, rejectedCount]
      rw [ENNReal.div_eq_inv_mul]
      push_cast
      ring

/-- The field sampler rejects exactly the draws `≥ p`. -/
theorem rejectedCount_field : rejectedCount 254 (fun value => decide (value < pNat)) = 2 ^ 254 - pNat := by
  have small : pNat < 2 ^ 254 := by unfold pNat; norm_num
  unfold rejectedCount
  have same : (Finset.univ.filter fun value : Fin (2 ^ 254) =>
      decide (value.val < pNat) = false) = Finset.Ici ⟨pNat, small⟩ := by
    ext value
    simp [Fin.le_def]
  rw [same, Fin.card_Ici]

theorem fieldAbort_nat : (2 ^ 254 - pNat) ^ 256 * 2 ^ 500 ≤ (2 ^ 254) ^ 256 :=
  Nat.le_of_ble_eq_true rfl

/-- **The field sampler aborts with probability below `2^-500`.** -/
theorem fieldAbort_le :
    rejectLaw fieldWidth (fun value => decide (value < pNat)) attempts none ≤ (2 ^ 500 : ENNReal)⁻¹ := by
  rw [show fieldWidth = 254 from rfl, show attempts = 256 from rfl, rejectLaw_none,
    rejectedCount_field, div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv]
  have base : ((2 : ENNReal) ^ 254) ^ 256 ≠ 0 := by positivity
  have finite : ((2 : ENNReal) ^ 254) ^ 256 ≠ ⊤ := by
    exact ENNReal.pow_ne_top (ENNReal.pow_ne_top (by norm_num))
  rw [ENNReal.div_le_iff base finite, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le
    (Or.inl (by positivity)) (Or.inl (ENNReal.pow_ne_top (by norm_num)))]
  have cast := fieldAbort_nat
  exact_mod_cast cast

/-- Fewer rejections, smaller abort mass. -/
theorem rejectLaw_none_le (width : Nat) (accept : Nat → Bool) (count bound : Nat)
    (fewer : rejectedCount width accept ≤ bound) :
    rejectLaw width accept count none ≤ ((bound : ENNReal) / 2 ^ width) ^ count := by
  rw [rejectLaw_none]
  gcongr

/-- The randomiser sampler rejects `0` and the draws `≥ p`. -/
theorem rejectedCount_lambda :
    rejectedCount 254 (fun value => decide (1 ≤ value ∧ value < pNat)) ≤ 2 ^ 254 - pNat + 1 := by
  have small : pNat < 2 ^ 254 := by unfold pNat; norm_num
  unfold rejectedCount
  have sub : (Finset.univ.filter fun value : Fin (2 ^ 254) =>
      decide (1 ≤ value.val ∧ value.val < pNat) = false) ⊆
        insert ⟨0, by positivity⟩ (Finset.Ici ⟨pNat, small⟩) := by
    intro value member
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_false_iff_not, not_and,
      not_lt] at member
    simp only [Finset.mem_insert, Finset.mem_Ici, Fin.le_def, Fin.ext_iff]
    by_cases zero : value.val = 0
    · exact Or.inl zero
    · exact Or.inr (member (by omega))
  refine (Finset.card_le_card sub).trans ((Finset.card_insert_le _ _).trans ?_)
  rw [Fin.card_Ici]

theorem lambdaAbort_nat : (2 ^ 254 - pNat + 1) ^ 256 * 2 ^ 500 ≤ (2 ^ 254) ^ 256 :=
  Nat.le_of_ble_eq_true rfl

/-- **Every randomiser draw aborts with probability below `2^-500`.** -/
theorem lambdaAbort_le :
    rejectLaw fieldWidth (fun value => decide (1 ≤ value ∧ value < pNat)) attempts none ≤
      (2 ^ 500 : ENNReal)⁻¹ := by
  refine (rejectLaw_none_le 254 _ 256 _ rejectedCount_lambda).trans ?_
  rw [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv]
  have base : ((2 : ENNReal) ^ 254) ^ 256 ≠ 0 := by positivity
  have finite : ((2 : ENNReal) ^ 254) ^ 256 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.pow_ne_top (by norm_num))
  rw [ENNReal.div_le_iff base finite, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le
    (Or.inl (by positivity)) (Or.inl (ENNReal.pow_ne_top (by norm_num)))]
  exact_mod_cast lambdaAbort_nat

/-! ### Off the cutoff, bounded rejection is uniform on the accepted draws -/

/-- One more attempt: the mass of a kept draw `v`. -/
theorem rejectLaw_some_succ (width : Nat) (accept : Nat → Bool) (count value : Nat) :
    rejectLaw width accept (count + 1) (some value) =
      (if accept value ∧ value < 2 ^ width then ((2 ^ width : ℕ) : ENNReal)⁻¹ else 0) +
        ((rejectedCount width accept : ENNReal) / 2 ^ width) *
          rejectLaw width accept count (some value) := by
  rw [rejectLaw, PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  have each : ∀ draw : Fin (2 ^ width),
      (if accept draw.val then PMF.pure (some draw.val) else rejectLaw width accept count)
          (some value) =
        (if accept draw.val ∧ draw.val = value then 1 else 0) +
          (if accept draw.val = false then rejectLaw width accept count (some value) else 0) := by
    intro draw
    by_cases accepted : accept draw.val = true
    · simp [accepted, PMF.pure_apply, eq_comm]
    · simp [accepted]
  simp only [each, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  congr 1
  · by_cases good : accept value = true ∧ value < 2 ^ width
    · rw [if_pos good, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
      have single : (Finset.univ.filter fun draw : Fin (2 ^ width) =>
          accept draw.val = true ∧ draw.val = value) = {⟨value, good.2⟩} := by
        ext draw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
        constructor
        · exact fun both => both.2
        · intro same; exact ⟨same ▸ good.1, same⟩
      rw [single, Finset.card_singleton, one_nsmul]
    · rw [if_neg good]
      apply Finset.sum_eq_zero
      intro draw _
      rw [if_neg]
      rintro ⟨accepted, same⟩
      exact good ⟨same ▸ accepted, same ▸ draw.isLt⟩
  · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, rejectedCount, ENNReal.div_eq_inv_mul]
    push_cast
    ring

/-- **Uniform on the accepted draws**: every accepted draw has the same mass. -/
theorem rejectLaw_uniform (width : Nat) (accept : Nat → Bool) (count first second : Nat)
    (firstGood : accept first = true ∧ first < 2 ^ width)
    (secondGood : accept second = true ∧ second < 2 ^ width) :
    rejectLaw width accept count (some first) = rejectLaw width accept count (some second) := by
  induction count with
  | zero => simp [rejectLaw]
  | succ count ih => rw [rejectLaw_some_succ, rejectLaw_some_succ, if_pos firstGood,
      if_pos secondGood, ih]

/-- **No mass off the accepted draws.** -/
theorem rejectLaw_off (width : Nat) (accept : Nat → Bool) (count value : Nat)
    (bad : ¬ (accept value = true ∧ value < 2 ^ width)) :
    rejectLaw width accept count (some value) = 0 := by
  induction count with
  | zero => simp [rejectLaw]
  | succ count ih => rw [rejectLaw_some_succ, if_neg bad, ih, mul_zero, add_zero]

end Kriterion.ArgoMAC.PlanB.SimMachine
