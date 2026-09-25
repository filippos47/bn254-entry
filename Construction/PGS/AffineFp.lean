/-
This file assembles the Plan B chunked affine encoding over `F_p`: one lane's whole
switch system, garbler and evaluator side.

The plan source is `2026-09-17-planB.md`, sections D.2--D.4 and Task 14;
the internal Python reference implementation is `pgs.py` (`coordinate_mask_pass`,
`scale_joins_from_slopes`, `coordinate_garble`, `coordinate_evaluate`).

Plan D.4's ordering is what the split into `offsets` and `garbleCoord` buys:

1. sample every switch mask vector `Y_{c,j}` from the hash oracle,
2. compute `O[e] = sum_c sum_j iota(j) * Y_{c,j}[e]` -- this is `offsets`, and it does **not**
   mention the slopes,
3. the row layer computes the slopes from `O` (the element offset is `b_e := O[e]`, the
   output-mask absorption that costs 0 bytes),
4. `s_c := (a_e * 2 ^ chunkOffset c)_e` -- this is `chunkScalar`,
5. publish `J_c = sum_j Y_{c,j} + s_c` -- this is `scaleJoins`.

The coordinate's `Σ_c (b_c - 1) = 1 + 32 * 4 + 23 * 3 = 198` fold joins are flattened into one
`Vector Block foldStepCount`. The ragged first chunk pays `firstChunkBits - 1 = 1` step and
lands at slot `0`; every wide chunk `1 ≤ c ≤ 32` pays `chunkBits - 1 = 4` steps at slots
`1 + 4 * (c - 1) .. 4 * c`, and every narrow chunk `c ≥ 33` pays `narrowChunkBits - 1 = 3` steps
at slots `129 + 3 * (c - 33) .. 128 + 3 * (c - 32)`. `hotSlice` reads the flat vector back, and
`hotSlice_flattenHot` says the round trip is the identity.
-/

import Construction.PGS.ScaleHot

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

variable {count : Nat}

/-! ### Chunk-local views of the coordinate's bits -/

/-- The position inside the coordinate of bit `position` of chunk `c`. -/
def chunkBitIndex (c : Fin chunkCount) (position : Fin (chunkWidth c)) : Fin coordinateBits :=
  ⟨chunkOffset c + position.val, by
    have inside := chunkOffset_add_width_le c
    have small := position.isLt
    omega⟩

/-- The garbler's label pairs of chunk `c`. -/
def chunkKey (bitKey : Fin coordinateBits → Block × Block) (c : Fin chunkCount) :
    Fin (chunkWidth c) → Block × Block :=
  fun position => bitKey (chunkBitIndex c position)

/-- The evaluator's held labels of chunk `c`. -/
def chunkLabels (labels : Fin coordinateBits → Block) (c : Fin chunkCount) :
    Fin (chunkWidth c) → Block :=
  fun position => labels (chunkBitIndex c position)

/-! ### The flat layout of the fold joins -/

/-- The number of flat fold-join slots owned by chunk `0` and the wide chunks. -/
def wideSlotCount : Nat := (firstChunkBits - 1) + wideChunkCount * (chunkBits - 1)

/-- The chunk a flat fold-join slot belongs to. Chunk `0` owns the first
`firstChunkBits - 1` slots; after them every wide chunk owns `chunkBits - 1` consecutive slots,
and after the `wideSlotCount` slots of those, every narrow chunk owns `narrowChunkBits - 1`. -/
def slotChunk (slot : Fin foldStepCount) : Fin chunkCount :=
  if slot.val < firstChunkBits - 1 then ⟨0, chunkCount_pos⟩
  else if slot.val < wideSlotCount then
    ⟨(slot.val - (firstChunkBits - 1)) / (chunkBits - 1) + 1, by
      have bound := slot.isLt
      unfold foldStepCount at bound
      unfold chunkBits firstChunkBits chunkCount
      omega⟩
  else ⟨(slot.val - wideSlotCount) / (narrowChunkBits - 1) + wideChunkCount + 1, by
    have bound := slot.isLt
    unfold foldStepCount at bound
    unfold wideSlotCount narrowChunkBits chunkBits firstChunkBits wideChunkCount chunkCount
    omega⟩

/-- The position of a flat fold-join slot inside its chunk. -/
def slotOffset (slot : Fin foldStepCount) : Nat :=
  if slot.val < firstChunkBits - 1 then slot.val
  else if slot.val < wideSlotCount then (slot.val - (firstChunkBits - 1)) % (chunkBits - 1)
  else (slot.val - wideSlotCount) % (narrowChunkBits - 1)

/-- The chunk of a flat fold-join slot, as a number: the three ranges of `slotChunk`. -/
theorem slotChunk_val (slot : Fin foldStepCount) :
    (slotChunk slot).val =
      if slot.val < firstChunkBits - 1 then 0
      else if slot.val < wideSlotCount then (slot.val - (firstChunkBits - 1)) / (chunkBits - 1) + 1
      else (slot.val - wideSlotCount) / (narrowChunkBits - 1) + wideChunkCount + 1 := by
  unfold slotChunk
  split_ifs <;> rfl

/-- **A flat fold-join slot is its chunk's base plus its offset**, and the offset is a paid step
of that chunk. Every range of the three-range layout is split in the hypotheses only, so the
proof is `omega` on each case. -/
theorem slot_eq_foldBase_add (slot : Fin foldStepCount) :
    slot.val = foldBase (slotChunk slot) + slotOffset slot ∧
      slotOffset slot < chunkWidth (slotChunk slot) - 1 := by
  have bound := slot.isLt
  have chunkVal := slotChunk_val slot
  have offsetVal : slotOffset slot =
      if slot.val < firstChunkBits - 1 then slot.val
      else if slot.val < wideSlotCount then (slot.val - (firstChunkBits - 1)) % (chunkBits - 1)
      else (slot.val - wideSlotCount) % (narrowChunkBits - 1) := rfl
  have baseVal := foldBase_eq (slotChunk slot)
  have widthVal : chunkWidth (slotChunk slot) = chunkWidthNat (slotChunk slot).val := rfl
  generalize slotOffset slot = position at offsetVal ⊢
  generalize foldBase (slotChunk slot) = base at baseVal ⊢
  generalize chunkWidth (slotChunk slot) = width at widthVal ⊢
  generalize (slotChunk slot).val = c at chunkVal baseVal widthVal
  unfold chunkWidthNat at widthVal
  unfold foldStepCount at bound
  unfold wideSlotCount at chunkVal offsetVal
  unfold chunkBits narrowChunkBits firstChunkBits wideChunkCount
    at chunkVal offsetVal baseVal widthVal
  split_ifs at chunkVal offsetVal baseVal widthVal <;> omega

/-- A flat slot is determined by its chunk and its offset. -/
theorem slot_ext_of_eq {slot slot' : Fin foldStepCount} (chunk : slotChunk slot = slotChunk slot')
    (offset : slotOffset slot = slotOffset slot') : slot = slot' := by
  apply Fin.ext
  rw [(slot_eq_foldBase_add slot).1, (slot_eq_foldBase_add slot').1, chunk, offset]

/-- The flat slot of fold step `position` of chunk `c`. -/
def flatSlot (c : Fin chunkCount) (position : Fin (chunkWidth c - 1)) : Fin foldStepCount :=
  ⟨foldBase c + position.val, by
    have inside := foldBase_add_le c
    have small := position.isLt
    omega⟩

/-- Any flat slot whose value is `foldBase c + position` belongs to chunk `c`. -/
theorem slotChunk_eq (slot : Fin foldStepCount) (c : Fin chunkCount) (position : Nat)
    (small : position < chunkWidth c - 1) (value : slot.val = foldBase c + position) :
    slotChunk slot = c := by
  have chunks := c.isLt
  rw [foldBase_eq] at value
  change position < chunkWidthNat c.val - 1 at small
  unfold chunkWidthNat at small
  unfold slotChunk
  unfold chunkCount at chunks
  unfold narrowChunkBits chunkBits firstChunkBits wideChunkCount at value small
  unfold wideSlotCount narrowChunkBits chunkBits firstChunkBits wideChunkCount
  split
  · apply Fin.ext
    show 0 = c.val
    split_ifs at value small <;> omega
  · split
    · apply Fin.ext
      show (slot.val - (2 - 1)) / (5 - 1) + 1 = c.val
      split_ifs at value small <;> omega
    · apply Fin.ext
      show (slot.val - ((2 - 1) + 48 * (5 - 1))) / (4 - 1) + 48 + 1 = c.val
      split_ifs at value small <;> omega

/-- ... at position `position` inside it. -/
theorem slotOffset_eq (slot : Fin foldStepCount) (c : Fin chunkCount) (position : Nat)
    (small : position < chunkWidth c - 1) (value : slot.val = foldBase c + position) :
    slotOffset slot = position := by
  have chunks := c.isLt
  rw [foldBase_eq] at value
  change position < chunkWidthNat c.val - 1 at small
  unfold chunkWidthNat at small
  unfold slotOffset
  unfold chunkCount at chunks
  unfold narrowChunkBits chunkBits firstChunkBits wideChunkCount at value small
  unfold wideSlotCount narrowChunkBits chunkBits firstChunkBits wideChunkCount
  split_ifs at value small ⊢ <;> omega

/-- Flatten one block per (chunk, fold step) into the coordinate's published join vector. -/
def flattenHot (blockAt : Fin chunkCount → Nat → Block) : Vector Block foldStepCount :=
  Vector.ofFn fun slot => blockAt (slotChunk slot) (slotOffset slot)

/-- Read chunk `c`'s fold joins back out of the flat vector. -/
def hotSlice (joins : Vector Block foldStepCount) (c : Fin chunkCount) :
    Vector Block (chunkWidth c - 1) :=
  Vector.ofFn fun position => joins.get (flatSlot c position)

/-- Flattening and slicing are inverse. -/
theorem hotSlice_flattenHot (blockAt : Fin chunkCount → Nat → Block) (c : Fin chunkCount)
    (position : Nat) (inRange : position < chunkWidth c - 1) :
    (hotSlice (flattenHot blockAt) c)[position] = blockAt c position := by
  have slice : (hotSlice (flattenHot blockAt) c)[position]
      = (flattenHot blockAt).get (flatSlot c ⟨position, inRange⟩) := by
    simp only [hotSlice]
    exact Vector.getElem_ofFn inRange
  rw [slice]
  have flat : (flattenHot blockAt).get (flatSlot c ⟨position, inRange⟩)
      = blockAt (slotChunk (flatSlot c ⟨position, inRange⟩))
          (slotOffset (flatSlot c ⟨position, inRange⟩)) := by
    simp only [flattenHot]
    exact Vector.getElem_ofFn (flatSlot c ⟨position, inRange⟩).isLt
  rw [flat, slotChunk_eq _ c position inRange rfl, slotOffset_eq _ c position inRange rfl]

/-! ### One lane, garbler side -/

/-- `bin-to-hot` for chunk `c`: the one-hot masks and this chunk's fold joins. -/
def garbleChunk (oracle : PermutationOracle FixedIndex Block) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBits → Block × Block) (c : Fin chunkCount) :
    HotLabels (chunkWidth c) × Vector Block (chunkWidth c - 1) :=
  garbleHot oracle lane c (chunkWidth c) delta fun position => (chunkKey bitKey c position).1

/-- The block published at fold step `position` of chunk `c`. -/
def chunkJoinBlock (oracle : PermutationOracle FixedIndex Block) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBits → Block × Block) (c : Fin chunkCount) (position : Nat) :
    Block :=
  if inRange : position < chunkWidth c - 1 then
    (garbleChunk oracle lane delta bitKey c).2.get ⟨position, inRange⟩
  else 0

/-- The coordinate's `foldStepCount` published fold-join blocks. -/
def hotJoins (oracle : PermutationOracle FixedIndex Block) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBits → Block × Block) : Vector Block foldStepCount :=
  flattenHot (chunkJoinBlock oracle lane delta bitKey)

/-- The round trip: chunk `c` reads back exactly its own fold joins. -/
theorem hotSlice_hotJoins (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (delta : Block) (bitKey : Fin coordinateBits → Block × Block) (c : Fin chunkCount) :
    hotSlice (hotJoins oracle lane delta bitKey) c
      = (garbleChunk oracle lane delta bitKey c).2 := by
  refine Vector.ext ?_
  intro position inRange
  rw [hotJoins, hotSlice_flattenHot _ c position inRange, chunkJoinBlock, dif_pos inRange]
  rfl

/-- **Step (4) of plan D.4.** The scalar of chunk `c`: the element's slope, weighted by this
chunk's place value `2 ^ chunkOffset c`. -/
def chunkScalar (slopes : Fin count → BaseField) (c : Fin chunkCount) : Fin count → BaseField :=
  fun element => slopes element * (2 : BaseField) ^ chunkOffset c

/-- **Step (5) of plan D.4.** The `chunkCount` published `scale-hot` joins of one lane. -/
def scaleJoins (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (lane : Lane) (delta : Block) (bitKey : Fin coordinateBits → Block × Block)
    (slopes : Fin (laneCount lane) → BaseField) :
    Fin chunkCount → Fin (laneCount lane) → BaseField :=
  fun c =>
    garbleScale hashOracle lane c (chunkWidth c) (garbleChunk oracle lane delta bitKey c).1
      (chunkScalar slopes c)

/-- **`Garb`/`Enc` for one lane.** The published fold joins and the `chunkCount` published
`scale-hot` joins. -/
def garbleCoord (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (lane : Lane) (delta : Block) (bitKey : Fin coordinateBits → Block × Block)
    (slopes : Fin (laneCount lane) → BaseField) :
    Vector Block foldStepCount × (Fin chunkCount → Fin (laneCount lane) → BaseField) :=
  (hotJoins oracle lane delta bitKey, scaleJoins oracle hashOracle lane delta bitKey slopes)

/-- **Step (2) of plan D.4: mask absorption, 0 bytes.** The element offsets
`O[e] = sum_c sum_j iota(j) * Y_{c,j}[e]`.

`offsets` depends only on `(oracle, hashOracle, lane, delta, bitKey)` -- never on the slopes --
which is what lets the row layer take `b_e := O[e]` as the IT-GS element offset and then derive
the slopes from it in one pass. -/
def offsets (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (lane : Lane) (delta : Block) (bitKey : Fin coordinateBits → Block × Block) :
    Fin (laneCount lane) → BaseField :=
  fun element =>
    ∑ c : Fin chunkCount,
      outputMask hashOracle lane c (chunkWidth c) (garbleChunk oracle lane delta bitKey c).1
        element

/-! ### One lane, evaluator side -/

/-- **`Eval` for one lane.** Per chunk: rebuild the one-hot labels from the published fold
joins, fold them against the chunk index (Lemma 6.1), then sum over the 52 chunks. -/
def evalCoord (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (bits : BitVec coordinateBits) (labels : Fin coordinateBits → Block) :
    Fin (laneCount lane) → BaseField :=
  fun element =>
    ∑ c : Fin chunkCount,
      evalScale hashOracle lane c (chunkWidth c)
        (evalHot oracle lane c (chunkWidth c) (hotSlice joins c) (chunkLabels labels c)
          (chunkValue bits c))
        (chunkOf bits c) (scale c) element

end Kriterion.ArgoMAC.PlanB
