/-
This file defines the Plan B chunk word: the `chunkJoinBits`-bit packing of one chunk's
`elementCount` published `scale-hot` join values.

The plan source is `2026-09-17-planB.md`, section D.5 "Packing, in
full". The x coordinate's `elementCountX` values occupy slots `0 .. elementCountX - 1` and the
y coordinate's `elementCountY` values slots `elementCountX .. elementCount - 1`; each slot is
`coordinateBits` wide, and no slot carries into the next because the modulus is below
`2 ^ coordinateBits`.

Interleaving the two coordinates per chunk is what makes the published unit a single word:
`elementCount * coordinateBits = 163,068` value bits, and four zero bits above the last slot round
the word up to `chunkJoinBits = 8 * chunkJoinBytes`.

Rule N: `256 ^ chunkJoinBytes = 2 ^ chunkJoinBits` is proved symbolically; no numeral of that
size is ever evaluated.
-/

import Construction.PGS.Sampler

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-! ### The natural-number digit lemma -/

/-- A little-endian base-`2 ^ width` digit sum. -/
private def packNat (width : Nat) (digit : Nat → Nat) (count : Nat) : Nat :=
  ∑ slot ∈ Finset.range count, digit slot * 2 ^ (width * slot)

/-- A `count`-digit sum stays below `2 ^ (width * count)`: no slot carries into the next. -/
private theorem packNat_lt (width : Nat) (digit : Nat → Nat)
    (bound : ∀ slot, digit slot < 2 ^ width) :
    ∀ count, packNat width digit count < 2 ^ (width * count) := by
  intro count
  induction count with
  | zero => simp [packNat]
  | succ n ih =>
    have expand : (2 : Nat) ^ (width * (n + 1)) = 2 ^ width * 2 ^ (width * n) := by
      rw [Nat.mul_succ, pow_add, Nat.mul_comm]
    have step : (digit n + 1) * 2 ^ (width * n) ≤ 2 ^ width * 2 ^ (width * n) :=
      Nat.mul_le_mul_right _ (bound n)
    rw [Nat.succ_mul] at step
    rw [packNat, Finset.sum_range_succ, ← packNat, expand]
    omega

/-- Digit extraction: shifting by `width * slot` and reducing modulo `2 ^ width` recovers the
digit at that slot. -/
private theorem packNat_digit (width : Nat) (digit : Nat → Nat)
    (bound : ∀ slot, digit slot < 2 ^ width) :
    ∀ count slot, slot < count →
      packNat width digit count / 2 ^ (width * slot) % 2 ^ width = digit slot := by
  intro count
  induction count with
  | zero => intro slot inRange; exact absurd inRange (by omega)
  | succ n ih =>
    intro slot inRange
    rw [packNat, Finset.sum_range_succ, ← packNat]
    rcases Nat.lt_or_ge slot n with below | above
    · obtain ⟨gap, hgap⟩ : ∃ gap, n = slot + 1 + gap := ⟨n - slot - 1, by omega⟩
      have expo : (2 : Nat) ^ (width * n)
          = 2 ^ (width * slot) * (2 ^ (width * gap) * 2 ^ width) := by
        rw [hgap]
        rw [Nat.mul_add, Nat.mul_add, pow_add, pow_add, Nat.mul_one]
        ring
      have regroup : digit n * (2 ^ (width * slot) * (2 ^ (width * gap) * 2 ^ width))
          = 2 ^ (width * slot) * (digit n * 2 ^ (width * gap) * 2 ^ width) := by ring
      rw [expo, regroup, Nat.add_mul_div_left _ _ (Nat.two_pow_pos (width * slot)),
        Nat.add_mul_mod_self_right]
      exact ih slot below
    · have same : slot = n := by omega
      subst same
      rw [Nat.mul_comm (digit slot) (2 ^ (width * slot)),
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos (width * slot)),
        Nat.div_eq_of_lt (packNat_lt width digit bound slot), Nat.zero_add,
        Nat.mod_eq_of_lt (bound slot)]

/-! ### The chunk word -/

/-- `chunkJoinBits = coordinateBits * elementCount + 4`: the value slots, a structural product of
two small numerals, and the four zero bits that round the word up to whole bytes. -/
theorem chunkJoinBits_eq_product : chunkJoinBits = coordinateBits * elementCount + 4 := by
  unfold chunkJoinBits coordinateBits elementCount
  norm_num

/-- The value slots fit the word. -/
theorem slots_le_chunkJoinBits : coordinateBits * elementCount ≤ chunkJoinBits := by
  rw [chunkJoinBits_eq_product]
  omega

/-- `256 ^ chunkJoinBytes = 2 ^ chunkJoinBits`.

Rule N: `256 = 2 ^ 8` and `chunkJoinBits = 8 * chunkJoinBytes`, so this is `pow_mul`; the
`163072`-bit numeral is never formed. -/
theorem pow_width : (256 : Nat) ^ chunkJoinBytes = 2 ^ chunkJoinBits := by
  rw [chunkJoinBits_eq, pow_mul]
  norm_num

/-- Every field element fits its `coordinateBits`-wide slot. -/
theorem val_lt_slot (value : BaseField) : value.val < 2 ^ coordinateBits := by
  unfold coordinateBits
  exact lt_trans (ZMod.val_lt value) baseFieldModulus_lt

/-- **The chunk word.** The `elementCount` join values of one chunk, little-endian, one
`coordinateBits`-wide slot each. -/
def pack (values : Fin elementCount → BaseField) : BitVec chunkJoinBits :=
  BitVec.ofNat chunkJoinBits
    (∑ element : Fin elementCount, (values element).val * 2 ^ (coordinateBits * element.val))

/-- **Reading one slot back.** -/
def unpack (word : BitVec chunkJoinBits) (element : Fin elementCount) : BaseField :=
  (((word >>> (coordinateBits * element.val)).setWidth coordinateBits).toNat : BaseField)

/-- The packing round-trips: no slot carries into the next, because the modulus is below
`2 ^ coordinateBits`. -/
theorem unpack_pack (values : Fin elementCount → BaseField) (element : Fin elementCount) :
    unpack (pack values) element = values element := by

  set digit : Nat → Nat := fun slot =>
    if inRange : slot < elementCount then (values ⟨slot, inRange⟩).val else 0 with hdigit
  have bound : ∀ slot, digit slot < 2 ^ coordinateBits := by
    intro slot
    rw [hdigit]
    by_cases inRange : slot < elementCount
    · simpa [inRange] using val_lt_slot (values ⟨slot, inRange⟩)
    · simp only [inRange, dif_neg, not_false_eq_true]
      exact Nat.two_pow_pos coordinateBits
  have sumEq : (∑ slot : Fin elementCount,
        (values slot).val * 2 ^ (coordinateBits * slot.val))
      = packNat coordinateBits digit elementCount := by
    rw [packNat, ← Fin.sum_univ_eq_sum_range
      (fun slot => digit slot * 2 ^ (coordinateBits * slot)) elementCount]
    refine Finset.sum_congr rfl ?_
    intro slot _
    rw [hdigit]
    simp [slot.isLt]
  have small : packNat coordinateBits digit elementCount < 2 ^ chunkJoinBits :=
    lt_of_lt_of_le (packNat_lt coordinateBits digit bound elementCount)
      (Nat.pow_le_pow_right (by norm_num) slots_le_chunkJoinBits)
  have toNatEq : (pack values).toNat = packNat coordinateBits digit elementCount := by
    rw [pack, sumEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  rw [unpack, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, toNatEq,
    Nat.shiftRight_eq_div_pow,
    packNat_digit coordinateBits digit bound elementCount element.val element.isLt, hdigit]
  simp only [element.isLt, dif_pos]
  exact ZMod.natCast_zmod_val (values element)

/-- The round trip, as a function equation: this is the form the pipeline rewrites with. -/
theorem unpack_pack_eq (values : Fin elementCount → BaseField) :
    unpack (pack values) = values :=
  funext fun element => unpack_pack values element

end Kriterion.ArgoMAC.PlanB
