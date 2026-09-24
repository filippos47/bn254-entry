/-
Powers of two in `ENNReal`: the three generic conversions the cutoff mass needs, stated on
variables so that no numeral is ever cast or evaluated.
-/

import Mathlib.Data.ENNReal.Inv

namespace Kriterion.ArgoMAC.PlanB.SimMachine

theorem two_pow_ne_zero (k : Nat) : (2 : ENNReal) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero

theorem two_pow_ne_top (k : Nat) : (2 : ENNReal) ^ k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top

/-- `a · 2^-k ≤ 2^-m` from `a · 2^m ≤ 2^k`. -/
theorem mul_inv_pow_le (a k m : Nat) (le : a * 2 ^ m ≤ 2 ^ k) :
    (a : ENNReal) * ((2 : ENNReal) ^ k)⁻¹ ≤ ((2 : ENNReal) ^ m)⁻¹ := by
  rw [← div_eq_mul_inv, ENNReal.div_le_iff (two_pow_ne_zero k) (two_pow_ne_top k),
    ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl (two_pow_ne_zero m))
    (Or.inl (two_pow_ne_top m))]
  have cast : ((a * 2 ^ m : Nat) : ENNReal) ≤ ((2 ^ k : Nat) : ENNReal) := Nat.cast_le.mpr le
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat] at cast
  exact cast

/-- `(a / 2^w)^n ≤ 2^-k` from `a^n · 2^k ≤ (2^w)^n`. -/
theorem ratio_pow_le (a w n k : Nat) (le : a ^ n * 2 ^ k ≤ (2 ^ w) ^ n) :
    ((a : ENNReal) / 2 ^ w) ^ n ≤ ((2 : ENNReal) ^ k)⁻¹ := by
  rw [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv]
  have base : ((2 : ENNReal) ^ w) ^ n ≠ 0 := pow_ne_zero _ (two_pow_ne_zero w)
  have finite : ((2 : ENNReal) ^ w) ^ n ≠ ⊤ := ENNReal.pow_ne_top (two_pow_ne_top w)
  rw [ENNReal.div_le_iff base finite, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le
    (Or.inl (two_pow_ne_zero k)) (Or.inl (two_pow_ne_top k))]
  have cast : ((a ^ n * 2 ^ k : Nat) : ENNReal) ≤ (((2 ^ w) ^ n : Nat) : ENNReal) :=
    Nat.cast_le.mpr le
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat] at cast
  exact cast

/-- `a⁻¹ ≤ 2^-n` from `2^n ≤ a`. -/
theorem inv_le_of_pow_le (a n : Nat) (le : 2 ^ n ≤ a) :
    (a : ENNReal)⁻¹ ≤ ((2 : ENNReal) ^ n)⁻¹ := by
  rw [ENNReal.inv_le_inv]
  have cast : ((2 ^ n : Nat) : ENNReal) ≤ (a : ENNReal) := Nat.cast_le.mpr le
  rw [Nat.cast_pow, Nat.cast_ofNat] at cast
  exact cast

/-- Two halves. -/
theorem inv_pow_add_self (n m : Nat) (succ : m = n + 1) :
    ((2 : ENNReal) ^ m)⁻¹ + ((2 : ENNReal) ^ m)⁻¹ = ((2 : ENNReal) ^ n)⁻¹ := by
  subst succ
  rw [← two_mul, pow_succ, ENNReal.mul_inv (Or.inl (two_pow_ne_zero n)) (Or.inl (two_pow_ne_top n)),
    mul_left_comm, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]

end Kriterion.ArgoMAC.PlanB.SimMachine
