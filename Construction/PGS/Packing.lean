/-
This file defines the Plan B chunk word: the `chunkJoinBits`-bit packing of one chunk's
`elementCount` published `scale-hot` join values, as one little-endian base-`p` number
(`p ^ 642 < 2 ^ 162816`, `20,352` bytes). The generic base-`p` cell packing of the
curve-and-rows word and the bit packing of the gadget word follow it. The historical slot
description below is kept for the slot lemmas that the bit packing reuses.

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
def packNat (width : Nat) (digit : Nat → Nat) (count : Nat) : Nat :=
  ∑ slot ∈ Finset.range count, digit slot * 2 ^ (width * slot)

/-- A `count`-digit sum stays below `2 ^ (width * count)`: no slot carries into the next. -/
theorem packNat_lt (width : Nat) (digit : Nat → Nat)
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
theorem packNat_digit (width : Nat) (digit : Nat → Nat)
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

/-! ### The base-`b` digit lemma -/

/-- A little-endian base-`b` digit sum. -/
def packBase (base : Nat) (digit : Nat → Nat) (count : Nat) : Nat :=
  ∑ slot ∈ Finset.range count, digit slot * base ^ slot

/-- A `count`-digit sum stays below `base ^ count`. -/
theorem packBase_lt (base : Nat) (digit : Nat → Nat) (bound : ∀ slot, digit slot < base) :
    ∀ count, packBase base digit count < base ^ count := by
  intro count
  induction count with
  | zero => simp [packBase]
  | succ n ih =>
    have step : (digit n + 1) * base ^ n ≤ base * base ^ n :=
      Nat.mul_le_mul_right _ (bound n)
    rw [Nat.succ_mul] at step
    rw [packBase, Finset.sum_range_succ, ← packBase, pow_succ, Nat.mul_comm (base ^ n) base]
    omega

/-- Digit extraction in base `base`. -/
theorem packBase_digit (base : Nat) (digit : Nat → Nat) (bound : ∀ slot, digit slot < base) :
    ∀ count slot, slot < count → packBase base digit count / base ^ slot % base = digit slot := by
  have basePos : 0 < base := lt_of_le_of_lt (Nat.zero_le _) (bound 0)
  intro count
  induction count with
  | zero => intro slot inRange; exact absurd inRange (by omega)
  | succ n ih =>
    intro slot inRange
    rw [packBase, Finset.sum_range_succ, ← packBase]
    rcases Nat.lt_or_ge slot n with below | above
    · obtain ⟨gap, hgap⟩ : ∃ gap, n = slot + 1 + gap := ⟨n - slot - 1, by omega⟩
      have regroup : digit n * base ^ n = base ^ slot * (digit n * base ^ gap * base) := by
        rw [hgap, pow_add, pow_add, pow_one]; ring
      rw [regroup, Nat.add_mul_div_left _ _ (Nat.pow_pos (n := slot) basePos),
        Nat.add_mul_mod_self_right]
      exact ih slot below
    · have same : slot = n := by omega
      subst same
      rw [Nat.mul_comm (digit slot) (base ^ slot),
        Nat.add_mul_div_left _ _ (Nat.pow_pos (n := slot) basePos),
        Nat.div_eq_of_lt (packBase_lt base digit bound slot), Nat.zero_add,
        Nat.mod_eq_of_lt (bound slot)]

/-! ### The chunk word -/

/-- `p ^ 642` fits the chunk word: the base-`p` number of the `642` join values never overflows. -/
theorem modulus_pow_lt_chunkJoinBits :
    BN254.baseFieldModulus ^ elementCount < 2 ^ chunkJoinBits := by
  unfold elementCount chunkJoinBits
  decide +kernel

/-- `256 ^ chunkJoinBytes = 2 ^ chunkJoinBits`.

Rule N: `256 = 2 ^ 8` and `chunkJoinBits = 8 * chunkJoinBytes`, so this is `pow_mul`; the
`162816`-bit numeral is never formed. -/
theorem pow_width : (256 : Nat) ^ chunkJoinBytes = 2 ^ chunkJoinBits := by
  rw [chunkJoinBits_eq, pow_mul]
  norm_num

/-- Every field element fits its `coordinateBits`-wide slot. -/
theorem val_lt_slot (value : BaseField) : value.val < 2 ^ coordinateBits := by
  unfold coordinateBits
  exact lt_trans (ZMod.val_lt value) baseFieldModulus_lt

/-- The base-`p` number of the `642` join values of one chunk. -/
def packWord (values : Fin elementCount → BaseField) : Nat :=
  ∑ element : Fin elementCount, (values element).val * BN254.baseFieldModulus ^ element.val

private theorem packWord_eq_packBase (values : Fin elementCount → BaseField) :
    packWord values = packBase BN254.baseFieldModulus (fun slot =>
      if inRange : slot < elementCount then (values ⟨slot, inRange⟩).val else 0) elementCount := by
  rw [packWord, packBase, ← Fin.sum_univ_eq_sum_range
    (fun slot => (if inRange : slot < elementCount then (values ⟨slot, inRange⟩).val else 0) *
      BN254.baseFieldModulus ^ slot) elementCount]
  refine Finset.sum_congr rfl ?_
  intro slot _
  simp [slot.isLt]

private theorem packWord_digit_bound (values : Fin elementCount → BaseField) :
    ∀ slot, (if inRange : slot < elementCount then (values ⟨slot, inRange⟩).val else 0) <
      BN254.baseFieldModulus := by
  intro slot
  by_cases inRange : slot < elementCount
  · simpa [inRange] using ZMod.val_lt (values ⟨slot, inRange⟩)
  · simp only [inRange, dif_neg, not_false_eq_true]
    exact Nat.pos_of_ne_zero (NeZero.ne _)

/-- The base-`p` number stays below `p ^ 642`. -/
theorem packWord_lt_pow (values : Fin elementCount → BaseField) :
    packWord values < BN254.baseFieldModulus ^ elementCount := by
  rw [packWord_eq_packBase]
  exact packBase_lt _ _ (packWord_digit_bound values) elementCount

/-- The base-`p` number fits the chunk word. -/
theorem packWord_lt (values : Fin elementCount → BaseField) :
    packWord values < 2 ^ chunkJoinBits :=
  lt_trans (packWord_lt_pow values) modulus_pow_lt_chunkJoinBits

/-- **The chunk word.** The `elementCount` join values of one chunk as one little-endian base-`p`
number. -/
def pack (values : Fin elementCount → BaseField) : BitVec chunkJoinBits :=
  BitVec.ofNat chunkJoinBits (packWord values)

/-- **Reading one value back**: base-`p` digit `element` of the word. -/
def unpack (word : BitVec chunkJoinBits) (element : Fin elementCount) : BaseField :=
  ((word.toNat / BN254.baseFieldModulus ^ element.val % BN254.baseFieldModulus : Nat) : BaseField)

theorem pack_toNat (values : Fin elementCount → BaseField) :
    (pack values).toNat = packWord values := by
  rw [pack, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (packWord_lt values)]

/-- The packing round-trips. -/
theorem unpack_pack (values : Fin elementCount → BaseField) (element : Fin elementCount) :
    unpack (pack values) element = values element := by
  rw [unpack, pack_toNat, packWord_eq_packBase,
    packBase_digit _ _ (packWord_digit_bound values) elementCount element.val element.isLt]
  simp only [element.isLt, dif_pos]
  exact ZMod.natCast_zmod_val (values element)

/-- The round trip, as a function equation: this is the form the pipeline rewrites with. -/
theorem unpack_pack_eq (values : Fin elementCount → BaseField) :
    unpack (pack values) = values :=
  funext fun element => unpack_pack values element

/-! ### Generic base-`p` cell packing

The curve-and-rows word packs `count` canonical field elements as one little-endian base-`p`
number. -/

/-- `count` field elements as one little-endian base-`p` number. -/
def packBaseCells (count : Nat) (values : Fin count → BaseField) : Nat :=
  ∑ element : Fin count, (values element).val * BN254.baseFieldModulus ^ element.val

/-- Reading base-`p` digit `element` back as a field element. -/
def unpackBaseCells (count : Nat) (word : Nat) (element : Fin count) : BaseField :=
  ((word / BN254.baseFieldModulus ^ element.val % BN254.baseFieldModulus : Nat) : BaseField)

private theorem packBaseCells_eq_packBase (count : Nat) (values : Fin count → BaseField) :
    packBaseCells count values = packBase BN254.baseFieldModulus (fun slot =>
      if inRange : slot < count then (values ⟨slot, inRange⟩).val else 0) count := by
  rw [packBaseCells, packBase, ← Fin.sum_univ_eq_sum_range
    (fun slot => (if inRange : slot < count then (values ⟨slot, inRange⟩).val else 0) *
      BN254.baseFieldModulus ^ slot) count]
  refine Finset.sum_congr rfl ?_
  intro slot _
  simp [slot.isLt]

private theorem packBaseCells_digit_bound (count : Nat) (values : Fin count → BaseField) :
    ∀ slot, (if inRange : slot < count then (values ⟨slot, inRange⟩).val else 0) <
      BN254.baseFieldModulus := by
  intro slot
  by_cases inRange : slot < count
  · simpa [inRange] using ZMod.val_lt (values ⟨slot, inRange⟩)
  · simp only [inRange, dif_neg, not_false_eq_true]
    exact Nat.pos_of_ne_zero (NeZero.ne _)

/-- The base-`p` number stays below `p ^ count`. -/
theorem packBaseCells_lt_pow (count : Nat) (values : Fin count → BaseField) :
    packBaseCells count values < BN254.baseFieldModulus ^ count := by
  rw [packBaseCells_eq_packBase]
  exact packBase_lt _ _ (packBaseCells_digit_bound count values) count

/-- The base-`p` cell packing round-trips. -/
theorem unpackBaseCells_packBaseCells (count : Nat) (values : Fin count → BaseField) :
    unpackBaseCells count (packBaseCells count values) = values := by
  funext element
  rw [unpackBaseCells, packBaseCells_eq_packBase,
    packBase_digit _ _ (packBaseCells_digit_bound count values) count element.val element.isLt]
  simp only [element.isLt, dif_pos]
  exact ZMod.natCast_zmod_val (values element)

/-! ### Generic bit-field packing (the gadget word) -/

/-- `count` bit vectors of `width` bits, little-endian, no padding between them. -/
def packBitsNat (width count : Nat) (values : Fin count → BitVec width) : Nat :=
  ∑ element : Fin count, (values element).toNat * 2 ^ (width * element.val)

/-- Reading one bit field back. -/
def unpackBits (width count : Nat) (word : Nat) (element : Fin count) : BitVec width :=
  BitVec.ofNat width (word / 2 ^ (width * element.val) % 2 ^ width)

private theorem packBitsNat_eq_packNat (width count : Nat) (values : Fin count → BitVec width) :
    packBitsNat width count values = packNat width (fun slot =>
      if inRange : slot < count then (values ⟨slot, inRange⟩).toNat else 0) count := by
  rw [packBitsNat, packNat, ← Fin.sum_univ_eq_sum_range
    (fun slot => (if inRange : slot < count then (values ⟨slot, inRange⟩).toNat else 0) *
      2 ^ (width * slot)) count]
  refine Finset.sum_congr rfl ?_
  intro slot _
  simp [slot.isLt]

private theorem packBits_digit_bound (width count : Nat) (values : Fin count → BitVec width) :
    ∀ slot, (if inRange : slot < count then (values ⟨slot, inRange⟩).toNat else 0) <
      2 ^ width := by
  intro slot
  by_cases inRange : slot < count
  · simpa [inRange] using (values ⟨slot, inRange⟩).isLt
  · simp only [inRange, dif_neg, not_false_eq_true]
    exact Nat.two_pow_pos width

theorem packBitsNat_lt (width count : Nat) (values : Fin count → BitVec width) :
    packBitsNat width count values < 2 ^ (width * count) := by
  rw [packBitsNat_eq_packNat]
  exact packNat_lt width _ (packBits_digit_bound width count values) count

theorem unpackBits_packBitsNat (width count : Nat) (values : Fin count → BitVec width) :
    unpackBits width count (packBitsNat width count values) = values := by
  funext element
  rw [unpackBits, packBitsNat_eq_packNat,
    packNat_digit width _ (packBits_digit_bound width count values) count element.val
      element.isLt]
  simp only [element.isLt, dif_pos]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (values element).isLt]

end Kriterion.ArgoMAC.PlanB
