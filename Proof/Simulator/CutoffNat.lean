/-
The natural-number facts behind the cutoff mass, by exponent arithmetic only (core `Nat`
lemmas; no large numeral is ever formed or evaluated, and no inequality between powers is
closed by evaluation).
-/

namespace Kriterion.ArgoMAC.PlanB.SimMachine

/-- A count below `2^c` times `2^m` is below `2^k` when `c + m ≤ k`. -/
theorem count_le (a c m k : Nat) (count : a ≤ 2 ^ c) (exponents : c + m ≤ k) :
    a * 2 ^ m ≤ 2 ^ k := by
  have step : 2 ^ c * 2 ^ m ≤ 2 ^ k := by
    rewrite [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) exponents
  exact Nat.le_trans (Nat.mul_le_mul_right _ count) step

/-- `(5 · 2^251)^256 · 2^170 ≤ (2^254)^256`, from `5^3 ≤ 2^7`. -/
theorem fiveEighths_nat : (5 * 2 ^ 251) ^ 256 * 2 ^ 170 ≤ (2 ^ 254) ^ 256 := by
  have cube : (5 ^ 3) ^ 85 ≤ (2 ^ 7) ^ 85 := Nat.pow_le_pow_left (by decide) 85
  have five : 5 * (5 ^ 3) ^ 85 ≤ 2 ^ 3 * (2 ^ 7) ^ 85 := Nat.mul_le_mul (by decide) cube
  have left : (5 * 2 ^ 251) ^ 256 * 2 ^ 170 =
      (5 * (5 ^ 3) ^ 85) * (2 ^ (251 * 256) * 2 ^ 170) := by
    rewrite [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_assoc]
    rewrite [show 256 = 1 + 3 * 85 from rfl, Nat.pow_add, Nat.pow_one]
    rfl
  have right : (2 ^ 254) ^ 256 = (2 ^ 3 * (2 ^ 7) ^ 85) * (2 ^ (251 * 256) * 2 ^ 170) := by
    rewrite [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
    rfl
  rewrite [left, right]
  exact Nat.mul_le_mul_right _ five

end Kriterion.ArgoMAC.PlanB.SimMachine
