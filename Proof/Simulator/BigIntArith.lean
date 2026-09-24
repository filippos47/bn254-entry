/-
**The natural-number facts behind the machine big-integer routines** (task T9a).

* `limb`, `div_limb`: base-`2^256` limbs;
* `hiWord_eq`: the high word of `x · p` from the four `128`-bit half products (`mulHi`);
* `hensel_step`: one Hensel exact-division limb — the quotient limb and the next borrow, in the
  closed form `borrow Q r i = (p · (Q mod 2^(256 i)) + r) / 2^(256 i)`;
* `horner_step`: one field-Horner step from the top limb;
* `mac_step`: one multiply-accumulate limb of `E ↦ p · E + y`, with the closed-form carry;
* `hornerValue_eq`: the Horner passes compute `E₀ · p^n + Σ_e Y_e p^e`;
* `encNat_lt`: `Σ_e Y_e p^e < p^n` for digits below `p`.

Every power of two stays symbolic; the only evaluated numerals are `p`, `p⁻¹ mod 2^256` and
their products (`pinv_spec`, 512-bit).
-/

import Construction.Simulator.BigInt

namespace Kriterion.ArgoMAC.PlanB.SimMachine

namespace BigInt

/-! ### Limbs -/

/-- Limb `index` of `value` in base `2^256`. -/
def limb (value index : Nat) : Nat := value / 2 ^ (256 * index) % 2 ^ 256

theorem limb_lt (value index : Nat) : limb value index < 2 ^ 256 :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem pow_limb_succ (index : Nat) : 2 ^ (256 * (index + 1)) = 2 ^ (256 * index) * 2 ^ 256 := by
  rw [Nat.mul_succ, Nat.pow_add]

/-- The value above limb `index` shifted down, plus the limb. -/
theorem div_limb (value index : Nat) :
    value / 2 ^ (256 * index) = value / 2 ^ (256 * (index + 1)) * 2 ^ 256 + limb value index := by
  rw [pow_limb_succ, ← Nat.div_div_eq_div_mul, limb, Nat.div_add_mod']

/-! ### The modulus -/

theorem pNat_lt_254 : pNat < 2 ^ 254 := by decide +kernel
theorem pNat_pos : 0 < pNat := by decide +kernel
theorem pNat_lt_word : pNat < 2 ^ 256 := lt_trans pNat_lt_254 (Nat.pow_lt_pow_right (by decide) (by decide))

/-- **`p⁻¹ mod 2^256`.** -/
theorem pinv_spec : pNat * pinvNat % 2 ^ 256 = 1 := by decide +kernel

theorem c256_lt_p : c256 < pNat := Nat.mod_lt _ pNat_pos
theorem pLow_lt : pLow < 2 ^ 128 := Nat.mod_lt _ (Nat.two_pow_pos _)
theorem pHigh_lt : pHigh < 2 ^ 126 := by
  unfold pHigh
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
  exact pNat_lt_254
theorem pNat_split : pNat = pLow + 2 ^ 128 * pHigh := (Nat.mod_add_div pNat _).symm
theorem mask128_eq : mask128 = 2 ^ 128 - 1 := rfl

/-! ### The high word -/

/-- **The high word of `x · p`** from the half products `A = x₀ p₀`, `B = x₀ p₁`, `C = x₁ p₀`,
`D = x₁ p₁` (`x = x₀ + 2^128 x₁`), exactly as `mulHi` sums them. -/
theorem hiWord_eq (x : Nat) (small : x < 2 ^ 256) :
    x % 2 ^ 128 * pHigh % 2 ^ 256 / 2 ^ 128 + x / 2 ^ 128 * pLow % 2 ^ 256 / 2 ^ 128 +
        (x % 2 ^ 128 * pLow % 2 ^ 256 / 2 ^ 128 + x % 2 ^ 128 * pHigh % 2 ^ 128 +
          x / 2 ^ 128 * pLow % 2 ^ 128) % 2 ^ 256 / 2 ^ 128 +
        x / 2 ^ 128 * pHigh =
      x * pNat / 2 ^ 256 := by
  have low : x % 2 ^ 128 < 2 ^ 128 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have high : x / 2 ^ 128 < 2 ^ 128 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]; exact small
  have key : x * pNat = x % 2 ^ 128 * pLow + 2 ^ 128 * (x % 2 ^ 128 * pHigh) +
      2 ^ 128 * (x / 2 ^ 128 * pLow) + 2 ^ 256 * (x / 2 ^ 128 * pHigh) := by
    conv_lhs => rw [← Nat.mod_add_div x (2 ^ 128), pNat_split]
    ring
  have boundA : x % 2 ^ 128 * pLow < 2 ^ 256 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' low pLow_lt) (by rw [← Nat.pow_add])
  have boundB : x % 2 ^ 128 * pHigh < 2 ^ 254 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' low pHigh_lt) (by rw [← Nat.pow_add])
  have boundC : x / 2 ^ 128 * pLow < 2 ^ 256 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' high pLow_lt) (by rw [← Nat.pow_add])
  have boundD : x / 2 ^ 128 * pHigh < 2 ^ 254 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' high pHigh_lt) (by rw [← Nat.pow_add])
  generalize x % 2 ^ 128 * pLow = A at *
  generalize x % 2 ^ 128 * pHigh = B at *
  generalize x / 2 ^ 128 * pLow = C at *
  generalize x / 2 ^ 128 * pHigh = D at *
  generalize x * pNat = product at *
  omega

/-! ### Hensel exact division -/

/-- The Hensel borrow after `index` limbs of the exact quotient `Q = (V − r) / p`. -/
def borrow (quotient remainder index : Nat) : Nat :=
  (pNat * (quotient % 2 ^ (256 * index)) + remainder) / 2 ^ (256 * index)

theorem borrow_zero (quotient remainder : Nat) : borrow quotient remainder 0 = remainder := by
  simp [borrow, Nat.mod_one]

theorem borrow_lt (quotient remainder index : Nat) (small : remainder < pNat) :
    borrow quotient remainder index < pNat := by
  unfold borrow
  have positive := Nat.two_pow_pos (256 * index)
  rw [Nat.div_lt_iff_lt_mul positive]
  have below := Nat.mod_lt quotient positive
  calc pNat * (quotient % 2 ^ (256 * index)) + remainder
      < pNat * (quotient % 2 ^ (256 * index)) + pNat := by omega
    _ = pNat * (quotient % 2 ^ (256 * index) + 1) := by ring
    _ ≤ pNat * 2 ^ (256 * index) := Nat.mul_le_mul_left _ below

/-- `(a + M · z) / M = z` for `a < M`. -/
theorem add_mul_div_of_lt {a M z : Nat} (small : a < M) : (a + M * z) / M = z := by
  have positive : 0 < M := lt_of_le_of_lt (Nat.zero_le _) small
  rw [Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt small, Nat.zero_add]

/-- The next borrow from the current one and the quotient limb. -/
theorem borrow_succ (quotient remainder index : Nat) :
    borrow quotient remainder (index + 1) =
      (borrow quotient remainder index + pNat * limb quotient index) / 2 ^ 256 := by
  unfold borrow limb
  have positive : 0 < 2 ^ (256 * index) := Nat.two_pow_pos _
  rw [pow_limb_succ, Nat.mod_mul, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [show pNat * (quotient % 2 ^ (256 * index) +
      2 ^ (256 * index) * (quotient / 2 ^ (256 * index) % 2 ^ 256)) + remainder =
      pNat * (quotient % 2 ^ (256 * index)) + remainder +
        2 ^ (256 * index) * (pNat * (quotient / 2 ^ (256 * index) % 2 ^ 256)) by ring,
    Nat.add_mul_div_left _ _ positive]

/-- The borrow and the quotient limb reproduce the limb of `V = p Q + r`. -/
theorem borrow_digit (value quotient remainder index : Nat)
    (exact : pNat * quotient + remainder = value) :
    (borrow quotient remainder index + pNat * limb quotient index) % 2 ^ 256 = limb value index := by
  unfold borrow limb
  have positive : 0 < 2 ^ (256 * index) := Nat.two_pow_pos _
  have split : value = pNat * (quotient % 2 ^ (256 * index)) + remainder +
      2 ^ (256 * index) * (pNat * (quotient / 2 ^ (256 * index))) := by
    rw [← exact]
    conv_lhs => rw [← Nat.mod_add_div quotient (2 ^ (256 * index))]
    ring
  have upper : pNat * (quotient / 2 ^ (256 * index)) =
      pNat * (quotient / 2 ^ (256 * index) % 2 ^ 256) +
        2 ^ 256 * (pNat * (quotient / 2 ^ (256 * index) / 2 ^ 256)) := by
    conv_lhs => rw [← Nat.mod_add_div (quotient / 2 ^ (256 * index)) (2 ^ 256)]
    ring
  rw [split, Nat.add_mul_div_left _ _ positive, upper, ← Nat.add_assoc, Nat.add_mul_mod_self_left]

/-- **One Hensel limb.** With `b = borrow Q r i` and `v = limb V i` (`V = p Q + r`): the
quotient limb is `(v − b) · p⁻¹ mod 2^256`, and the next borrow is the high word of its product
with `p` plus the subtraction's borrow bit. -/
theorem hensel_step (value quotient remainder index : Nat)
    (exact : pNat * quotient + remainder = value) (small : remainder < pNat) :
    (limb value index + (2 ^ 256 - borrow quotient remainder index)) * pinvNat % 2 ^ 256 =
        limb quotient index ∧
      limb quotient index * pNat / 2 ^ 256 +
          (if limb value index < borrow quotient remainder index then 1 else 0) =
        borrow quotient remainder (index + 1) := by
  have bSmall : borrow quotient remainder index < 2 ^ 256 :=
    lt_trans (borrow_lt quotient remainder index small) pNat_lt_word
  have qSmall := limb_lt quotient index
  have digit := borrow_digit value quotient remainder index exact
  refine ⟨?_, ?_⟩
  · have congruent : (limb value index + (2 ^ 256 - borrow quotient remainder index)) % 2 ^ 256 =
        pNat * limb quotient index % 2 ^ 256 := by
      generalize pNat * limb quotient index = product at *
      omega
    rw [Nat.mul_mod, congruent, ← Nat.mul_mod,
      show pNat * limb quotient index * pinvNat = limb quotient index * (pNat * pinvNat) by ring,
      Nat.mul_mod, pinv_spec, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt qSmall]
  · rw [borrow_succ, Nat.mul_comm (limb quotient index) pNat]
    generalize pNat * limb quotient index = product at *
    split_ifs <;> omega

/-! ### Field Horner from the top limb -/

/-- **One field-Horner step**: `((V / 2^(256 (i+1))) mod p) · (2^256 mod p) + limb_i ≡ V / 2^(256 i)`. -/
theorem horner_step (value index : Nat) :
    (value / 2 ^ (256 * (index + 1)) % pNat * c256 % pNat + limb value index) % pNat =
      value / 2 ^ (256 * index) % pNat := by
  rw [div_limb value index]
  unfold c256
  rw [← Nat.mul_mod, Nat.mod_add_mod]

/-- Above the top limb nothing is left. -/
theorem div_top (value count : Nat) (small : value < 2 ^ (256 * count)) :
    value / 2 ^ (256 * count) = 0 := Nat.div_eq_of_lt small

/-! ### Multiply-accumulate -/

/-- **One multiply-accumulate limb** of `E ↦ p · E + y`, carry `c = borrow E y j` (the same
closed form as the Hensel borrow): the new limb is `(e · p + c) mod 2^256`, the next carry the high
word of `e · p` plus the addition's carry bit. -/
theorem mac_step (value digit index : Nat) (small : digit < pNat) :
    (limb value index * pNat + borrow value digit index) % 2 ^ 256 =
        limb (pNat * value + digit) index ∧
      limb value index * pNat / 2 ^ 256 +
          (if (limb value index * pNat + borrow value digit index) % 2 ^ 256 <
            borrow value digit index then 1 else 0) =
        borrow value digit (index + 1) := by
  have cSmall : borrow value digit index < 2 ^ 256 :=
    lt_trans (borrow_lt value digit index small) pNat_lt_word
  have digitIs := borrow_digit (pNat * value + digit) value digit index rfl
  have next := borrow_succ value digit index
  rw [Nat.mul_comm (limb value index) pNat]
  generalize pNat * limb value index = product at *
  refine ⟨by omega, ?_⟩
  rw [next]
  split_ifs <;> omega

/-! ### Horner passes -/

/-- The value after `step` Horner passes `E ← p · E + Y_{n−1−step}` from `E = start`. -/
def hornerValue (start : Nat) (digits : Nat → Nat) (count : Nat) : Nat → Nat
  | 0 => start
  | step + 1 => pNat * hornerValue start digits count step + digits (count - 1 - step)

/-- The little-endian base-`p` encoding `Σ_{e<n} Y_e p^e`. -/
def encNat (digits : Nat → Nat) (count : Nat) : Nat :=
  ∑ e ∈ Finset.range count, digits e * pNat ^ e

theorem hornerValue_partial (start : Nat) (digits : Nat → Nat) (count : Nat) :
    ∀ step, step ≤ count → hornerValue start digits count step =
      start * pNat ^ step + ∑ e ∈ Finset.range step, digits (count - step + e) * pNat ^ e
  | 0, _ => by simp [hornerValue]
  | step + 1, bound => by
      rw [hornerValue, hornerValue_partial start digits count step (by omega),
        Finset.sum_range_succ']
      have shifted : pNat * ∑ e ∈ Finset.range step, digits (count - step + e) * pNat ^ e =
          ∑ e ∈ Finset.range step, digits (count - (step + 1) + (e + 1)) * pNat ^ (e + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [show count - (step + 1) + (e + 1) = count - step + e by omega, pow_succ]
        ring
      rw [show count - (step + 1) + 0 = count - 1 - step by omega, ← shifted, pow_succ]
      ring

/-- **The Horner passes compute `E₀ · p^n + Σ_e Y_e p^e`.** -/
theorem hornerValue_eq (start : Nat) (digits : Nat → Nat) (count : Nat) :
    hornerValue start digits count count = start * pNat ^ count + encNat digits count := by
  rw [hornerValue_partial start digits count count le_rfl, encNat]
  simp

/-- Digits below `p` encode below `p^n`. -/
theorem encNat_lt (digits : Nat → Nat) :
    ∀ count, (∀ e, e < count → digits e < pNat) → encNat digits count < pNat ^ count
  | 0, _ => by simp [encNat]
  | count + 1, below => by
      have previous := encNat_lt digits count fun e bound => below e (by omega)
      have top : digits count + 1 ≤ pNat := below count (by omega)
      rw [encNat, Finset.sum_range_succ, ← encNat, pow_succ]
      calc encNat digits count + digits count * pNat ^ count
          < pNat ^ count + digits count * pNat ^ count := by omega
        _ = (digits count + 1) * pNat ^ count := by ring
        _ ≤ pNat * pNat ^ count := Nat.mul_le_mul_right _ top
        _ = pNat ^ count * pNat := by ring

/-- The iterated quotients: `V / p^e / p = V / p^(e+1)`. -/
theorem div_pow_succ (value digit : Nat) : value / pNat ^ digit / pNat = value / pNat ^ (digit + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

/-! ### Mixed radix: limbs of a limb sum -/

/-- The value of `count` base-`2^256` limbs. -/
def limbSum (limbs : Nat → Nat) (count : Nat) : Nat :=
  ∑ index ∈ Finset.range count, limbs index * 2 ^ (256 * index)

theorem limbSum_lt (limbs : Nat → Nat) (small : ∀ index, limbs index < 2 ^ 256) :
    ∀ count, limbSum limbs count < 2 ^ (256 * count)
  | 0 => by simp [limbSum]
  | count + 1 => by
      have previous := limbSum_lt limbs small count
      rw [limbSum, Finset.sum_range_succ, ← limbSum, pow_limb_succ]
      have top : limbs count + 1 ≤ 2 ^ 256 := small count
      calc limbSum limbs count + limbs count * 2 ^ (256 * count)
          < 2 ^ (256 * count) + limbs count * 2 ^ (256 * count) := by omega
        _ = (limbs count + 1) * 2 ^ (256 * count) := by ring
        _ ≤ 2 ^ 256 * 2 ^ (256 * count) := Nat.mul_le_mul_right _ top
        _ = 2 ^ (256 * count) * 2 ^ 256 := by ring

/-- **The limbs of a limb sum are the limbs** (each below `2^256`). -/
theorem limb_limbSum (limbs : Nat → Nat) (small : ∀ index, limbs index < 2 ^ 256) :
    ∀ count index, index < count → limb (limbSum limbs count) index = limbs index
  | 0, _, bound => absurd bound (Nat.not_lt_zero _)
  | count + 1, index, bound => by
      rw [limbSum, Finset.sum_range_succ, ← limbSum]
      have below := limbSum_lt limbs small count
      unfold limb
      by_cases top : index = count
      · subst top
        rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt below, Nat.zero_add,
          Nat.mod_eq_of_lt (small index)]
      · have inner : index < count := by omega
        have split : limbs count * 2 ^ (256 * count) =
            2 ^ (256 * index) * (2 ^ 256 * (limbs count * 2 ^ (256 * (count - index - 1)))) := by
          rw [show 256 * count = 256 * index + (256 + 256 * (count - index - 1)) by omega,
            Nat.pow_add, Nat.pow_add]
          ring
        rw [split, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_left]
        exact limb_limbSum limbs small count index inner

end BigInt

end Kriterion.ArgoMAC.PlanB.SimMachine
