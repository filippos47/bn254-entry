/-
This file defines the frozen Plan B parameters of the projectivized garbling scheme.
The plan source is `2026-09-17-planB.md`, sections D.1 and D.5; the phase-4 profile is
`A1-batched-sampler-design.md`, sections 0 and 2; the phase-5 widths are `P5-brief.md` §5b.

**The query-gated profile.** The pinned challenge bounds the oracle queries of garbling
(`≤ 1,759,967`) and evaluation (`≤ 1,055,879`). The `scale-hot` layer draws one switch mask
*vector* per (lane, chunk, switch) from `limbCount lane` hash queries (`731` per switch of the
four lanes together), so the chunks can be wide: the profile is **ragged-first, then wide, then
narrow**, widths `[2, 5 × 48, 4 × 3]`. Chunk `0` is `firstChunkBits = 2` bits wide, chunks
`1 .. 48` are `chunkBits = 5` bits wide (the widest, so every switch index is below
`2 ^ chunkBits`), and chunks `49 .. 51` are `narrowChunkBits = 4` bits wide, `chunkCount = 52`
chunks in all. The sign row (`Construction/ArgoMAC/Biquadratic.lean`) leaves seven elements per
digit, `642` in all, so a switch costs `641` hash queries and the chunks can be this wide.
Garbling then makes `1,123,253` queries and evaluation `1,042,077`, both below
their gates (`Programs.garbleBudget_eq` and `Programs.evaluateBudget_eq` in
`Construction/OraclePrograms.lean` count every term). Keeping chunk `0` at width `2` keeps its
four candidate switches, which the privacy proof's chunk-zero analysis reads.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import ScalarMultiplication

namespace Kriterion.ArgoMAC.PlanB

/-- The number of chunks one 254-bit coordinate is cut into. -/
def chunkCount : Nat := 52

/-- The width of the wide chunks `1 .. wideChunkCount`, the widest of all chunks: every switch
index of every chunk is below `2 ^ chunkBits`, and every fold level below `chunkBits`. -/
def chunkBits : Nat := 5

/-- The width of the narrow chunks after the wide ones, chunks `wideChunkCount + 1 .. 51`. -/
def narrowChunkBits : Nat := 4

/-- The width of the first chunk, chunk `0`: `254 - 48 * 5 - 3 * 4`. -/
def firstChunkBits : Nat := 2

/-- The number of wide (`chunkBits`-bit) chunks, chunks `1 .. 48`. -/
def wideChunkCount : Nat := 48

/-- The number of narrow (`narrowChunkBits`-bit) chunks, chunks `49 .. 51`. -/
def narrowChunkCount : Nat := 3

/-- The number of paid `bin-to-hot` fold steps of one coordinate:
`254 - chunkCount = (2 - 1) + 48 * (5 - 1) + 3 * (4 - 1)`. -/
def foldStepCount : Nat := 202

/-- The number of x-type elements: `91 * 4 + 3`. -/
def elementCountX : Nat := 367

/-- The number of y-type elements: `91 * 3 + 2`. -/
def elementCountY : Nat := 275

/-- The x-type elements of the point rows, delivered by switch system B: `91 * 4`. -/
def pointElementCountX : Nat := 364

/-- The y-type elements of the point rows, delivered by switch system B: `91 * 3`. -/
def pointElementCountY : Nat := 273

/-- The x-type elements of the curve check, delivered by switch system A. -/
def curveElementCountX : Nat := 3

/-- The y-type elements of the curve check, delivered by switch system A. -/
def curveElementCountY : Nat := 2

/-- The total number of IT-GS elements `S`. -/
def elementCount : Nat := 642

/-- The width in bits of one chunk's published `scale-hot` join word: the `642 * 254 = 163,068`
value bits and four zero bits, so that the word fills whole bytes. -/
def chunkJoinBits : Nat := 163072

/-- The width in bytes of one chunk's published `scale-hot` join word. -/
def chunkJoinBytes : Nat := 20384

/-- The number of bits of one coordinate. -/
def coordinateBits : Nat := 254

/-- The number of recoded digits, one per output MAC. -/
def digitCount : Nat := 91

/-- A coordinate of the affine input. Each one carries its own switch system. -/
inductive Coord
  | x
  | y
deriving DecidableEq

instance : Fintype Coord := ⟨{.x, .y}, fun value => by cases value <;> simp⟩

theorem card_coord : Fintype.card Coord = 2 := rfl

/-- A *lane*: one switch system on one coordinate.

Plan B runs **two** switch systems per coordinate, not one. System A (`curveX`, `curveY`) is
keyed on the raw 508 Lamport labels and delivers the five curve-check elements; its output is
the bridge key `t`. System B (`pointX`, `pointY`) is keyed on the *EncPRF-whitened* labels,
whose one-time pads are derived from `t`, and delivers the 637 point-row elements. An
evaluator who cannot produce `t` -- an off-curve input -- holds only garbage labels for system
B and can compute none of the point rows. The lane is part of every `bin-to-hot` index and of
every `scale-hot` hash input, so the two systems never share a gate. -/
inductive Lane
  | curveX
  | curveY
  | pointX
  | pointY
deriving DecidableEq

instance : Fintype Lane :=
  ⟨{.curveX, .curveY, .pointX, .pointY}, fun value => by cases value <;> simp⟩

theorem card_lane : Fintype.card Lane = 4 := rfl

/-- The coordinate a lane reads. -/
def Lane.coord : Lane → Coord
  | .curveX => .x
  | .curveY => .y
  | .pointX => .x
  | .pointY => .y

/-- The number of element slots each lane's switch system delivers: the length of one switch
mask vector of that lane. It is reducible, so `Fin (laneCount .pointX)` and
`Fin pointElementCountX` are the same type to every tactic, not only to the kernel. -/
abbrev laneCount : Lane → Nat
  | .curveX => curveElementCountX
  | .curveY => curveElementCountY
  | .pointX => pointElementCountX
  | .pointY => pointElementCountY

/-- The width of chunk `c`, as a total function of a natural number.
Chunk `0` is `firstChunkBits` wide, chunks `1 .. wideChunkCount` are `chunkBits` wide, and every
later chunk is `narrowChunkBits` wide. -/
def chunkWidthNat (c : Nat) : Nat :=
  if c = 0 then firstChunkBits else if c ≤ wideChunkCount then chunkBits else narrowChunkBits

/-- The width `b_c` of chunk `c`. -/
def chunkWidth (c : Fin chunkCount) : Nat := chunkWidthNat c.val

/-- The offset of chunk `c`'s fold joins inside the coordinate's flat
`Vector Block foldStepCount`. -/
def foldBase (c : Fin chunkCount) : Nat :=
  ∑ i ∈ Finset.range c.val, (chunkWidthNat i - 1)

theorem elementCount_eq : elementCount = elementCountX + elementCountY := by
  rfl

theorem elementCountX_eq : elementCountX = pointElementCountX + curveElementCountX := by
  rfl

theorem elementCountY_eq : elementCountY = pointElementCountY + curveElementCountY := by
  rfl

theorem chunkJoinBits_eq : chunkJoinBits = 8 * chunkJoinBytes := by
  rfl

theorem chunkBits_pos : 0 < chunkBits := by unfold chunkBits; omega

theorem chunkCount_pos : 0 < chunkCount := by unfold chunkCount; omega

theorem twoPowChunkBits_pos : 0 < 2 ^ chunkBits := Nat.two_pow_pos chunkBits

theorem chunkWidthNat_pos (c : Nat) : 0 < chunkWidthNat c := by
  unfold chunkWidthNat firstChunkBits chunkBits narrowChunkBits
  split_ifs <;> omega

theorem chunkWidthNat_le (c : Nat) : chunkWidthNat c ≤ chunkBits := by
  unfold chunkWidthNat firstChunkBits chunkBits narrowChunkBits
  split_ifs <;> omega

theorem chunkWidth_pos (c : Fin chunkCount) : 0 < chunkWidth c :=
  chunkWidthNat_pos c.val

theorem chunkWidth_le (c : Fin chunkCount) : chunkWidth c ≤ chunkBits :=
  chunkWidthNat_le c.val

/-- Chunk `0` is `firstChunkBits` wide. -/
theorem chunkWidthNat_zero : chunkWidthNat 0 = firstChunkBits := by
  unfold chunkWidthNat
  rw [if_pos rfl]

/-- Chunks `1 .. wideChunkCount` are `chunkBits` wide. -/
theorem chunkWidthNat_of_le_wide (c : Nat) (after : c ≠ 0) (wide : c ≤ wideChunkCount) :
    chunkWidthNat c = chunkBits := by
  unfold chunkWidthNat
  rw [if_neg after, if_pos wide]

/-- Every chunk after the wide ones is `narrowChunkBits` wide. -/
theorem chunkWidthNat_of_wide_lt (c : Nat) (narrow : wideChunkCount < c) :
    chunkWidthNat c = narrowChunkBits := by
  unfold chunkWidthNat
  rw [if_neg (show c ≠ 0 by omega), if_neg (show ¬ c ≤ wideChunkCount by omega)]

/-- The chunk count is the ragged chunk `0`, the wide chunks and the narrow chunks. -/
theorem chunkCount_eq : chunkCount = wideChunkCount + 1 + narrowChunkCount := rfl

/-- A sum over the first `count + 1 ≤ wideChunkCount + 1` chunks: the ragged chunk `0` and
`count` wide chunks. It is proved by induction on the number of chunks, never by evaluating the
sum (Rule O). -/
theorem sum_range_chunkWidthNat_wide (g : Nat → Nat) (count : Nat)
    (small : count ≤ wideChunkCount) :
    (∑ i ∈ Finset.range (count + 1), g (chunkWidthNat i))
      = count * g chunkBits + g firstChunkBits := by
  induction count with
  | zero => simp [chunkWidthNat_zero]
  | succ count ih =>
      rw [Finset.sum_range_succ, ih (by omega),
        chunkWidthNat_of_le_wide (count + 1) (Nat.succ_ne_zero _) small, Nat.succ_mul]
      omega

/-- A sum over the first `wideChunkCount + 1 + extra` chunks: the ragged chunk `0`, all the wide
chunks and `extra` narrow chunks, by induction on `extra`. -/
theorem sum_range_chunkWidthNat_narrow (g : Nat → Nat) (extra : Nat) :
    (∑ i ∈ Finset.range (wideChunkCount + 1 + extra), g (chunkWidthNat i))
      = extra * g narrowChunkBits + wideChunkCount * g chunkBits + g firstChunkBits := by
  induction extra with
  | zero =>
      rw [Nat.add_zero, sum_range_chunkWidthNat_wide g wideChunkCount le_rfl, Nat.zero_mul,
        Nat.zero_add]
  | succ extra ih =>
      rw [show wideChunkCount + 1 + (extra + 1) = wideChunkCount + 1 + extra + 1 by omega,
        Finset.sum_range_succ, ih,
        chunkWidthNat_of_wide_lt (wideChunkCount + 1 + extra) (by omega), Nat.succ_mul]
      omega

/-- A sum over all chunks: the narrow chunks, the wide chunks and the ragged first one. -/
theorem sum_chunkWidth (g : Nat → Nat) :
    (∑ c : Fin chunkCount, g (chunkWidth c))
      = narrowChunkCount * g narrowChunkBits + wideChunkCount * g chunkBits + g firstChunkBits := by
  have toRange : (∑ c : Fin chunkCount, g (chunkWidth c))
      = ∑ i ∈ Finset.range chunkCount, g (chunkWidthNat i) :=
    Fin.sum_univ_eq_sum_range (fun i => g (chunkWidthNat i)) chunkCount
  rw [toRange, chunkCount_eq, sum_range_chunkWidthNat_narrow]

/-- A sum over the chunks after chunk `0`: the wide and the narrow ones. -/
theorem sum_range_chunkWidthNat_succ (g : Nat → Nat) :
    (∑ i ∈ Finset.range (chunkCount - 1), g (chunkWidthNat (i + 1)))
      = narrowChunkCount * g narrowChunkBits + wideChunkCount * g chunkBits := by
  have whole := Finset.sum_range_succ' (fun i => g (chunkWidthNat i)) (chunkCount - 1)
  beta_reduce at whole
  rw [show chunkCount - 1 + 1 = wideChunkCount + 1 + narrowChunkCount from rfl,
    sum_range_chunkWidthNat_narrow, chunkWidthNat_zero] at whole
  omega

/-- The chunk widths of one coordinate add up to its 254 bits. -/
theorem chunkWidth_sum : (∑ c : Fin chunkCount, chunkWidth c) = coordinateBits := by
  have split := sum_chunkWidth id
  simp only [id] at split
  rw [split]
  rfl

/-- The paid fold steps of one coordinate add up to `foldStepCount`. -/
theorem foldStep_sum : (∑ c : Fin chunkCount, (chunkWidth c - 1)) = foldStepCount := by
  rw [sum_chunkWidth (fun width => width - 1)]
  rfl

/-- A prefix sum of the chunk widths in closed form: `0` before chunk `0`, then the ragged chunk
`0` and `c - 1` wide chunks up to chunk `wideChunkCount`, then all of them and `c - 1 -
wideChunkCount` narrow chunks. -/
theorem sum_range_chunkWidthNat_prefix (g : Nat → Nat) (c : Nat) :
    (∑ i ∈ Finset.range c, g (chunkWidthNat i))
      = if c = 0 then 0
        else if c ≤ wideChunkCount + 1 then (c - 1) * g chunkBits + g firstChunkBits
        else (c - 1 - wideChunkCount) * g narrowChunkBits + wideChunkCount * g chunkBits
          + g firstChunkBits := by
  split
  · next zero => rw [zero, Finset.sum_range_zero]
  · next nonzero =>
      split
      · next wide =>
          obtain ⟨count, hcount⟩ : ∃ count, c = count + 1 := ⟨c - 1, by omega⟩
          rw [hcount, sum_range_chunkWidthNat_wide g count (by omega), Nat.add_sub_cancel]
      · next narrow =>
          obtain ⟨extra, hextra⟩ : ∃ extra, c = wideChunkCount + 1 + extra :=
            ⟨c - 1 - wideChunkCount, by omega⟩
          rw [hextra, sum_range_chunkWidthNat_narrow g extra,
            show wideChunkCount + 1 + extra - 1 - wideChunkCount = extra by omega]

/-- The fold bases in closed form: chunk `0` starts at `0`; a wide chunk `c` starts after the
first chunk's `firstChunkBits - 1` joins and `c - 1` wide chunks of `chunkBits - 1` joins; a
narrow chunk `c` after all of those and `c - 1 - wideChunkCount` narrow chunks of
`narrowChunkBits - 1` joins. -/
theorem foldBase_eq (c : Fin chunkCount) :
    foldBase c
      = if c.val = 0 then 0
        else if c.val ≤ wideChunkCount then (c.val - 1) * (chunkBits - 1) + (firstChunkBits - 1)
        else (c.val - 1 - wideChunkCount) * (narrowChunkBits - 1)
          + wideChunkCount * (chunkBits - 1) + (firstChunkBits - 1) := by
  unfold foldBase
  rw [sum_range_chunkWidthNat_prefix (fun width => width - 1)]
  unfold chunkBits narrowChunkBits firstChunkBits wideChunkCount
  split_ifs <;> omega

/-- The fold joins of every chunk fit inside the flat `foldStepCount`-block vector. -/
theorem foldBase_add_le (c : Fin chunkCount) :
    foldBase c + (chunkWidth c - 1) ≤ foldStepCount := by
  rw [foldBase_eq]
  have bound := c.isLt
  change _ + (chunkWidthNat c.val - 1) ≤ foldStepCount
  unfold chunkWidthNat
  unfold chunkCount at bound
  unfold chunkBits narrowChunkBits firstChunkBits wideChunkCount foldStepCount
  split_ifs <;> omega

theorem foldBase_zero : foldBase ⟨0, chunkCount_pos⟩ = 0 := by
  rw [foldBase_eq, if_pos rfl]

/-! ### Chunking a coordinate

The construction cuts the 254 bits of a coordinate into `chunkCount` chunks: chunk `0` carries
the ragged `firstChunkBits` low bits, chunks `1 .. wideChunkCount` are `chunkBits` wide and the
later ones `narrowChunkBits` wide (`chunkWidthNat`). These are the plan's `chunkOf` (section D.9)
and the chunk value the switch system's evaluator holds in the clear. Both are total functions of
the whole coordinate word; nothing here mentions a tape. -/

/-- The bit offset of chunk `c` inside the coordinate: `0` for chunk `0`,
`firstChunkBits + chunkBits * (c - 1)` for a wide chunk, and
`firstChunkBits + chunkBits * wideChunkCount + narrowChunkBits * (c - 1 - wideChunkCount)` for a
narrow one. -/
def chunkOffset (c : Fin chunkCount) : Nat :=
  if c.val = 0 then 0
  else if c.val ≤ wideChunkCount then firstChunkBits + chunkBits * (c.val - 1)
  else firstChunkBits + chunkBits * wideChunkCount + narrowChunkBits * (c.val - 1 - wideChunkCount)

/-- The offset of chunk `c` is the sum of the widths of the chunks before it. -/
theorem chunkOffset_eq_sum (c : Fin chunkCount) :
    chunkOffset c = ∑ i ∈ Finset.range c.val, chunkWidthNat i := by
  have prefixSum := sum_range_chunkWidthNat_prefix id c.val
  simp only [id] at prefixSum
  rw [prefixSum]
  unfold chunkOffset chunkBits narrowChunkBits firstChunkBits wideChunkCount
  split_ifs <;> omega

/-- Every chunk lies inside the coordinate. -/
theorem chunkOffset_add_width_le (c : Fin chunkCount) :
    chunkOffset c + chunkWidth c ≤ coordinateBits := by
  have bound := c.isLt
  change chunkOffset c + chunkWidthNat c.val ≤ coordinateBits
  unfold chunkOffset chunkWidthNat
  unfold chunkCount at bound
  unfold chunkBits narrowChunkBits firstChunkBits wideChunkCount coordinateBits
  split_ifs <;> omega

/-- Chunk `c` of a natural number, as the switch index of that chunk's `scale-hot` system. -/
def chunkOfNat (bits : Nat) (c : Fin chunkCount) : Fin (2 ^ chunkWidth c) :=
  ⟨bits >>> chunkOffset c % 2 ^ chunkWidth c, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Chunk `c` of a coordinate word, as a switch index. -/
def chunkOf (bits : BitVec coordinateBits) (c : Fin chunkCount) : Fin (2 ^ chunkWidth c) :=
  chunkOfNat bits.toNat c

/-- Chunk `c` of a coordinate word, as a bit vector of that chunk's width. -/
def chunkValue (bits : BitVec coordinateBits) (c : Fin chunkCount) : BitVec (chunkWidth c) :=
  BitVec.ofNat (chunkWidth c) (bits.toNat >>> chunkOffset c)

/-- The two readings of a chunk agree. -/
theorem chunkValue_toNat (bits : BitVec coordinateBits) (c : Fin chunkCount) :
    (chunkValue bits c).toNat = (chunkOf bits c).val := by
  rw [chunkValue, BitVec.toNat_ofNat]
  rfl

/-- The canonical little-endian 254-bit encoding of a coordinate. This is definitionally the
baseline's `Kriterion.ArgoMAC.coordinateBits`. -/
def coordWord (value : BN254.BaseField) : BitVec coordinateBits :=
  BitVec.ofNat coordinateBits value.val

/-- The modulus fits in 254 bits, so the canonical encoding loses nothing. -/
theorem baseFieldModulus_lt_two_pow : BN254.baseFieldModulus < 2 ^ coordinateBits := by
  unfold BN254.baseFieldModulus coordinateBits
  norm_num

theorem coordWord_toNat (value : BN254.BaseField) : (coordWord value).toNat = value.val := by
  rw [coordWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_trans (ZMod.val_lt value) baseFieldModulus_lt_two_pow

end Kriterion.ArgoMAC.PlanB
