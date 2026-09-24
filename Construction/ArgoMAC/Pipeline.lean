/-
This file connects `C_1`, `C_23` and `C_45` over the projectivized garbling scheme.
The active paper shows this pipeline at `fig:garbled_c_with_cm_opt`.

Plan B replaces the 733 `DigitAdaptor` tables by chunked switch systems, and Task 19a runs
**two** of them per coordinate:

* **system A** (lanes `curveX`, `curveY`) is keyed on the *raw* 508 Lamport labels and delivers
  the five curve-check elements. Its output is the bridge key `t`, which the check publishes
  as `t + mask * (x^3 + 3 - y^2)`: exactly `t` on the curve, uniform off it.
* **system B** (lanes `pointX`, `pointY`) is keyed on the *EncPRF-whitened* labels, whose
  one-time pads come from `t` through `EncPRF.whiteningKeys`. It delivers the `728 = 91 * 8`
  point-row elements. An evaluator who cannot produce `t` holds garbage labels for system B
  and can compute none of the point rows -- that is the gating the curve check is for.

The whitening is `EncPRF.whitenAt`, the *correlation-preserving* half of the EncPRF gate: one
pad per (coordinate, position), applied to both labels of the pair, so the free-XOR relation
the `bin-to-hot` fold needs survives the gate. The exception gadget keeps reading the
bit-dependent `EncPRF.transformMac` labels, unchanged from the baseline.

`garble` runs plan D.4's five-step order once per system:

1. sample every switch mask vector from the hash oracle -- implicit in `offsets`; the vector of
   one (lane, chunk, switch) is the base-`p` digits of `limbCount lane` hash limbs asked at the
   switch's one-hot label (`PlanB.switchMask`),
2. compute the element offsets `O[e]` (`curveXK`/`curveYK`, `pointXK`/`pointYK`); they do
   **not** mention the slopes,
3. derive the slopes from the offsets (`curveSlopes`, `pointSlopes`),
4. weight them per chunk (`chunkScalar`, inside `garbleCoord`),
5. publish the joins (`garbleCoord`), the eleven row constants and the three curve constants,
   each with its element offsets absorbed.

The four lanes' `733` joins of one chunk are still interleaved into a single
`chunkJoinBits`-wide word (two zero bits round it up to whole bytes), so the chunk stays the
byte-aligned publication unit.
The plan source is `2026-09-17-planB.md`, sections D.3--D.6 and
Tasks 19 and 19a.
-/

import Construction.ArgoMAC.CurveMembership
import Construction.ArgoMAC.EncPRF
import Construction.ArgoMAC.FieldMacToECMac
import Construction.PGS.AffineFp

set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Pipeline

open BN254 Cryptography
open Kriterion.ArgoMAC.PlanB hiding coordinateBits

/-! ### The free-XOR input keys -/

/-- The label pair of each bit of one coordinate. -/
def bitKeyOf (key : InputMacKey) : Coord → Fin coordinateBitCount → Block × Block
  | .x => fun position => ((key.x.get position).falseLabel, (key.x.get position).trueLabel)
  | .y => fun position => ((key.y.get position).falseLabel, (key.y.get position).trueLabel)

/-- The labels the evaluator holds for one coordinate. -/
def macLabels (mac : InputMac) : Coord → Fin coordinateBitCount → Block
  | .x => fun position => mac.x.get position
  | .y => fun position => mac.y.get position

/-- The cleartext bits of one coordinate. -/
def coordBits (input : BitInput) : Coord → BitVec coordinateBitCount
  | .x => input.xBits
  | .y => input.yBits

/-- The free-XOR relation the switch systems need: the two labels of a bit differ by that
coordinate's global offset. -/
def CorrelatedKey (key : InputMacKey) (delta : Coord → Block) : Prop :=
  ∀ (coord : Coord) (position : Fin coordinateBitCount),
    (bitKeyOf key coord position).2 = (bitKeyOf key coord position).1 ^^^ delta coord

/-- The canonical coordinate word of an affine input. -/
theorem coordBits_ofAffine (input : AffineInput) (coord : Coord) :
    coordBits (BitInput.ofAffine input) coord
      = coordWord (match coord with | .x => input.x | .y => input.y) := by
  cases coord <;> rfl

/-- The evaluator's held labels are the garbler's label pairs selected by the cleartext bits. -/
theorem macLabels_encode (key : InputMacKey) (input : BitInput) (coord : Coord) :
    macLabels (key.encode input) coord
      = selectBits (bitKeyOf key coord) (coordBits input coord) := by
  funext position
  cases coord
  · show (encodeCoordinate key.x input.xBits).get position
        = selectBits (bitKeyOf key .x) input.xBits position
    unfold encodeCoordinate
    rw [Vector.get_eq_getElem, Vector.getElem_ofFn position.isLt]
    rfl
  · show (encodeCoordinate key.y input.yBits).get position
        = selectBits (bitKeyOf key .y) input.yBits position
    unfold encodeCoordinate
    rw [Vector.get_eq_getElem, Vector.getElem_ofFn position.isLt]
    rfl

/-! ### The EncPRF gate, on the system-B side

System B reads the whitened label family. `EncPRF.whitenAt` applies one pad per (coordinate,
position) to *both* labels, so the free-XOR offset is untouched and the whitened key is again
a `CorrelatedKey` with the same `delta`. Everything the gate hides -- the labels themselves --
is hidden exactly as before. -/

/-- The label family system B is keyed on. -/
def whitenedKey (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (bridgeKey : BaseField) (key : InputMacKey) : InputMacKey :=
  EncPRF.whitenKey encPRFOracle (EncPRF.whiteningKeys hashOracle bridgeKey) key

/-- The whitening keeps the free-XOR relation. -/
theorem whitenedKey_correlated
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (bridgeKey : BaseField) (key : InputMacKey)
    (delta : Coord → Block) (correlated : CorrelatedKey key delta) :
    CorrelatedKey (whitenedKey encPRFOracle hashOracle bridgeKey key) delta := by
  intro coord position
  have source := correlated coord position
  cases coord <;>
    · simp only [bitKeyOf, whitenedKey, EncPRF.whitenKey, EncPRF.whitenCoordinateKey,
        Vector.get_eq_getElem, Vector.getElem_ofFn] at source ⊢
      rw [source, EncPRF.whitenAt_xor]

/-! ### The element slots

`Construction/PGS/Elements.lean` maps each digit slot and curve slot to its lane's element
index. Here is the inverse, which is what lets the garbler assemble one slope vector per
lane. -/

/-- The x-type element slot inside a digit. -/
def xElementOfSlot : Nat → XElement
  | 0 => .rowX_x7
  | 1 => .rowX_x9
  | 2 => .rowY_mixed
  | 3 => .rowY_cubic
  | _ => .rowZ_x9

/-- The y-type element slot inside a digit. -/
def yElementOfSlot : Nat → YElement
  | 0 => .rowX_y10
  | 1 => .rowY_y8
  | _ => .rowY_y10

/-- The x-type curve element slot. -/
def curveXElementOfSlot : Nat → CurveXElement
  | 0 => .x3
  | 1 => .x5
  | _ => .x7

/-- The y-type curve element slot. -/
def curveYElementOfSlot : Nat → CurveYElement
  | 0 => .y4
  | _ => .y6

/-- The `pointX` lane's element vector, assembled from the 91 per-digit families. -/
def pointXAssemble (point : Fin digitCount → Biquadratic.Values)
    (element : Fin pointElementCountX) : BaseField :=
  point ⟨element.val / xSlotsPerDigit, by
    have bound := element.isLt
    unfold pointElementCountX at bound
    unfold xSlotsPerDigit digitCount
    omega⟩
    (.inl (xElementOfSlot (element.val % xSlotsPerDigit)))

/-- The `pointY` lane's element vector. -/
def pointYAssemble (point : Fin digitCount → Biquadratic.Values)
    (element : Fin pointElementCountY) : BaseField :=
  point ⟨element.val / ySlotsPerDigit, by
    have bound := element.isLt
    unfold pointElementCountY at bound
    unfold ySlotsPerDigit digitCount
    omega⟩
    (.inr (yElementOfSlot (element.val % ySlotsPerDigit)))

/-- The `curveX` lane's element vector. -/
def curveXAssemble (curve : CurveMembership.Values) (element : Fin curveElementCountX) :
    BaseField :=
  curve (.inl (curveXElementOfSlot element.val))

/-- The `curveY` lane's element vector. -/
def curveYAssemble (curve : CurveMembership.Values) (element : Fin curveElementCountY) :
    BaseField :=
  curve (.inr (curveYElementOfSlot element.val))

theorem pointXAssemble_digit (point : Fin digitCount → Biquadratic.Values)
    (digit : Fin digitCount) (element : XElement) :
    pointXAssemble point (xElementIndex digit element) = point digit (.inl element) := by
  have slot : element.slot.val < xSlotsPerDigit := element.slot.isLt
  have value : (xElementIndex digit element).val
      = xSlotsPerDigit * digit.val + element.slot.val := rfl
  rw [pointXAssemble]
  have quotient : (xElementIndex digit element).val / xSlotsPerDigit = digit.val := by
    rw [value]; unfold xSlotsPerDigit at slot ⊢; omega
  have remainder : (xElementIndex digit element).val % xSlotsPerDigit = element.slot.val := by
    rw [value]; unfold xSlotsPerDigit at slot ⊢; omega
  rw [remainder, show (⟨(xElementIndex digit element).val / xSlotsPerDigit, by
    have bound := (xElementIndex digit element).isLt
    unfold pointElementCountX at bound
    unfold xSlotsPerDigit digitCount
    omega⟩ : Fin digitCount) = digit from Fin.ext quotient]
  cases element <;> rfl

theorem pointYAssemble_digit (point : Fin digitCount → Biquadratic.Values)
    (digit : Fin digitCount) (element : YElement) :
    pointYAssemble point (yElementIndex digit element) = point digit (.inr element) := by
  have slot : element.slot.val < ySlotsPerDigit := element.slot.isLt
  have value : (yElementIndex digit element).val
      = ySlotsPerDigit * digit.val + element.slot.val := rfl
  rw [pointYAssemble]
  have quotient : (yElementIndex digit element).val / ySlotsPerDigit = digit.val := by
    rw [value]; unfold ySlotsPerDigit at slot ⊢; omega
  have remainder : (yElementIndex digit element).val % ySlotsPerDigit = element.slot.val := by
    rw [value]; unfold ySlotsPerDigit at slot ⊢; omega
  rw [remainder, show (⟨(yElementIndex digit element).val / ySlotsPerDigit, by
    have bound := (yElementIndex digit element).isLt
    unfold pointElementCountY at bound
    unfold ySlotsPerDigit digitCount
    omega⟩ : Fin digitCount) = digit from Fin.ext quotient]
  cases element <;> rfl

theorem curveXAssemble_slot (curve : CurveMembership.Values) (element : CurveXElement) :
    curveXAssemble curve (curveXElementIndex element) = curve (.inl element) := by
  cases element <;> rfl

theorem curveYAssemble_slot (curve : CurveMembership.Values) (element : CurveYElement) :
    curveYAssemble curve (curveYElementIndex element) = curve (.inr element) := by
  cases element <;> rfl

/-- The per-digit view of the two point lanes' element vectors. -/
def digitValues (xValues : Fin pointElementCountX → BaseField)
    (yValues : Fin pointElementCountY → BaseField) (digit : Fin digitCount) :
    Biquadratic.Values
  | .inl element => xValues (xElementIndex digit element)
  | .inr element => yValues (yElementIndex digit element)

/-- The curve check's view of the two curve lanes' element vectors. -/
def curveValues (xValues : Fin curveElementCountX → BaseField)
    (yValues : Fin curveElementCountY → BaseField) : CurveMembership.Values
  | .inl element => xValues (curveXElementIndex element)
  | .inr element => yValues (curveYElementIndex element)

/-! ### The chunk word

One chunk publishes a single `chunkJoinBits`-wide word carrying all four lanes' joins: the
`pointX` lane's `455` values in slots `0 .. 454`, the `curveX` lane's `3` in slots
`455 .. 457`, the `pointY` lane's `273` in slots `458 .. 730` and the `curveY` lane's `2` in
slots `731, 732`, then two zero bits. Interleaving the lanes per chunk is what makes the *chunk*
the byte-aligned unit. -/

/-- Interleave the two coordinates' joins of one chunk. -/
def interleave (xJoin : Fin elementCountX → BaseField) (yJoin : Fin elementCountY → BaseField)
    (element : Fin elementCount) : BaseField :=
  if low : element.val < elementCountX then xJoin ⟨element.val, low⟩
  else yJoin ⟨element.val - elementCountX, by
    have bound := element.isLt
    unfold elementCount at bound
    unfold elementCountX at low ⊢
    unfold elementCountY
    omega⟩

/-- Read the x coordinate's joins back out of one chunk word. -/
def xPart (values : Fin elementCount → BaseField) (element : Fin elementCountX) : BaseField :=
  values ⟨element.val, by
    have bound := element.isLt
    unfold elementCountX at bound
    unfold elementCount
    omega⟩

/-- Read the y coordinate's joins back out of one chunk word. -/
def yPart (values : Fin elementCount → BaseField) (element : Fin elementCountY) : BaseField :=
  values ⟨elementCountX + element.val, by
    have bound := element.isLt
    unfold elementCountY at bound
    unfold elementCount elementCountX
    omega⟩

theorem xPart_interleave (xJoin : Fin elementCountX → BaseField)
    (yJoin : Fin elementCountY → BaseField) : xPart (interleave xJoin yJoin) = xJoin := by
  funext element
  rw [xPart, interleave, dif_pos element.isLt]

theorem yPart_interleave (xJoin : Fin elementCountX → BaseField)
    (yJoin : Fin elementCountY → BaseField) : yPart (interleave xJoin yJoin) = yJoin := by
  funext element
  have outside : ¬ elementCountX + element.val < elementCountX := by omega
  rw [yPart, interleave, dif_neg outside]
  exact congrArg yJoin (Fin.ext (by simp))

/-- Split one coordinate's element vector into its point lane and its curve lane. -/
def xSplit (pointJoin : Fin pointElementCountX → BaseField)
    (curveJoin : Fin curveElementCountX → BaseField) (element : Fin elementCountX) : BaseField :=
  if low : element.val < pointElementCountX then pointJoin ⟨element.val, low⟩
  else curveJoin ⟨element.val - pointElementCountX, by
    have bound := element.isLt
    unfold elementCountX at bound
    unfold pointElementCountX at low ⊢
    unfold curveElementCountX
    omega⟩

/-- The same split on the y coordinate. -/
def ySplit (pointJoin : Fin pointElementCountY → BaseField)
    (curveJoin : Fin curveElementCountY → BaseField) (element : Fin elementCountY) : BaseField :=
  if low : element.val < pointElementCountY then pointJoin ⟨element.val, low⟩
  else curveJoin ⟨element.val - pointElementCountY, by
    have bound := element.isLt
    unfold elementCountY at bound
    unfold pointElementCountY at low ⊢
    unfold curveElementCountY
    omega⟩

/-- Read the `pointX` lane out of one coordinate's element vector. -/
def xPointPart (values : Fin elementCountX → BaseField) (element : Fin pointElementCountX) :
    BaseField :=
  values ⟨element.val, by
    have bound := element.isLt
    unfold pointElementCountX at bound
    unfold elementCountX
    omega⟩

/-- Read the `curveX` lane out of one coordinate's element vector. -/
def xCurvePart (values : Fin elementCountX → BaseField) (element : Fin curveElementCountX) :
    BaseField :=
  values ⟨pointElementCountX + element.val, by
    have bound := element.isLt
    unfold curveElementCountX at bound
    unfold elementCountX pointElementCountX
    omega⟩

/-- Read the `pointY` lane out of one coordinate's element vector. -/
def yPointPart (values : Fin elementCountY → BaseField) (element : Fin pointElementCountY) :
    BaseField :=
  values ⟨element.val, by
    have bound := element.isLt
    unfold pointElementCountY at bound
    unfold elementCountY
    omega⟩

/-- Read the `curveY` lane out of one coordinate's element vector. -/
def yCurvePart (values : Fin elementCountY → BaseField) (element : Fin curveElementCountY) :
    BaseField :=
  values ⟨pointElementCountY + element.val, by
    have bound := element.isLt
    unfold curveElementCountY at bound
    unfold elementCountY pointElementCountY
    omega⟩

theorem xPointPart_xSplit (pointJoin : Fin pointElementCountX → BaseField)
    (curveJoin : Fin curveElementCountX → BaseField) :
    xPointPart (xSplit pointJoin curveJoin) = pointJoin := by
  funext element
  rw [xPointPart, xSplit, dif_pos element.isLt]

theorem xCurvePart_xSplit (pointJoin : Fin pointElementCountX → BaseField)
    (curveJoin : Fin curveElementCountX → BaseField) :
    xCurvePart (xSplit pointJoin curveJoin) = curveJoin := by
  funext element
  have outside : ¬ pointElementCountX + element.val < pointElementCountX := by omega
  rw [xCurvePart, xSplit, dif_neg outside]
  exact congrArg curveJoin (Fin.ext (by simp))

theorem yPointPart_ySplit (pointJoin : Fin pointElementCountY → BaseField)
    (curveJoin : Fin curveElementCountY → BaseField) :
    yPointPart (ySplit pointJoin curveJoin) = pointJoin := by
  funext element
  rw [yPointPart, ySplit, dif_pos element.isLt]

theorem yCurvePart_ySplit (pointJoin : Fin pointElementCountY → BaseField)
    (curveJoin : Fin curveElementCountY → BaseField) :
    yCurvePart (ySplit pointJoin curveJoin) = curveJoin := by
  funext element
  have outside : ¬ pointElementCountY + element.val < pointElementCountY := by omega
  rw [yCurvePart, ySplit, dif_neg outside]
  exact congrArg curveJoin (Fin.ext (by simp))

/-- All four lanes' joins of one chunk, in one word. -/
def assembleWord (pointX : Fin pointElementCountX → BaseField)
    (curveX : Fin curveElementCountX → BaseField)
    (pointY : Fin pointElementCountY → BaseField)
    (curveY : Fin curveElementCountY → BaseField) : Fin elementCount → BaseField :=
  interleave (xSplit pointX curveX) (ySplit pointY curveY)

/-- Read the `pointX` lane out of a chunk word. -/
def readPointX (values : Fin elementCount → BaseField) : Fin pointElementCountX → BaseField :=
  xPointPart (xPart values)

/-- Read the `curveX` lane out of a chunk word. -/
def readCurveX (values : Fin elementCount → BaseField) : Fin curveElementCountX → BaseField :=
  xCurvePart (xPart values)

/-- Read the `pointY` lane out of a chunk word. -/
def readPointY (values : Fin elementCount → BaseField) : Fin pointElementCountY → BaseField :=
  yPointPart (yPart values)

/-- Read the `curveY` lane out of a chunk word. -/
def readCurveY (values : Fin elementCount → BaseField) : Fin curveElementCountY → BaseField :=
  yCurvePart (yPart values)

theorem readPointX_assembleWord (pointX curveX pointY curveY) :
    readPointX (assembleWord pointX curveX pointY curveY) = pointX := by
  rw [readPointX, assembleWord, xPart_interleave, xPointPart_xSplit]

theorem readCurveX_assembleWord (pointX curveX pointY curveY) :
    readCurveX (assembleWord pointX curveX pointY curveY) = curveX := by
  rw [readCurveX, assembleWord, xPart_interleave, xCurvePart_xSplit]

theorem readPointY_assembleWord (pointX curveX pointY curveY) :
    readPointY (assembleWord pointX curveX pointY curveY) = pointY := by
  rw [readPointY, assembleWord, yPart_interleave, yPointPart_ySplit]

theorem readCurveY_assembleWord (pointX curveX pointY curveY) :
    readCurveY (assembleWord pointX curveX pointY curveY) = curveY := by
  rw [readCurveY, assembleWord, yPart_interleave, yCurvePart_ySplit]

/-! ### The gadget permutations -/

/-- The gadget coordinate, as a `Coord`. -/
def gadgetCoord : EncPRF.Coordinate → Coord
  | .x => .x
  | .y => .y

/-- The exception gadget reads one dedicated permutation per (digit, coordinate, label
position). Nothing is tweaked and nothing is shared, so every gadget index carries exactly one
construction query. -/
def gadgetPermutations (oracle : PermutationOracle FixedIndex Block) :
    FieldMacToECMac.GadgetPermutations :=
  fun output coordinate position =>
    oracle.permutation (.gadget output (gadgetCoord coordinate) position)

/-! ### System A, in plan D.4's order -/

/-- **Step 2.** The `curveX` lane's element offsets `O[e]`, from the tape alone. -/
def curveXK (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (delta : Coord → Block) (key : InputMacKey) : Fin curveElementCountX → BaseField :=
  offsets oracle hashOracle .curveX (delta .x) (bitKeyOf key .x)

/-- **Step 2.** The `curveY` lane's element offsets. -/
def curveYK (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (delta : Coord → Block) (key : InputMacKey) : Fin curveElementCountY → BaseField :=
  offsets oracle hashOracle .curveY (delta .y) (bitKeyOf key .y)

/-- The curve check's element offsets. -/
def curveK (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (delta : Coord → Block) (key : InputMacKey) : CurveMembership.Values :=
  curveValues (curveXK oracle hashOracle delta key) (curveYK oracle hashOracle delta key)

/-- **Step 3.** The five slopes of the curve check, derived from its element offsets. -/
def curveSlopes (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (delta : Coord → Block) (key : InputMacKey) (curveR1 curveR2 : BaseField) :
    CurveMembership.Values :=
  CurveMembership.slopes curveR1 curveR2 (curveK oracle hashOracle delta key)

/-- **Steps 4 and 5.** The `curveX` lane's published fold joins and chunk joins. -/
def curveXGarbled (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (delta : Coord → Block) (key : InputMacKey) (curveR1 curveR2 : BaseField) :
    Vector Block foldStepCount × (Fin chunkCount → Fin curveElementCountX → BaseField) :=
  garbleCoord oracle hashOracle .curveX (delta .x) (bitKeyOf key .x)
    (curveXAssemble (curveSlopes oracle hashOracle delta key curveR1 curveR2))

/-- **Steps 4 and 5.** The `curveY` lane's published fold joins and chunk joins. -/
def curveYGarbled (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (delta : Coord → Block) (key : InputMacKey) (curveR1 curveR2 : BaseField) :
    Vector Block foldStepCount × (Fin chunkCount → Fin curveElementCountY → BaseField) :=
  garbleCoord oracle hashOracle .curveY (delta .y) (bitKeyOf key .y)
    (curveYAssemble (curveSlopes oracle hashOracle delta key curveR1 curveR2))

/-! ### System B, in plan D.4's order

Every definition below takes the *whitened* key, not the raw one: system B's gates are keyed
on the labels the EncPRF gate produces from the bridge key. -/

/-- **Step 2.** The `pointX` lane's element offsets `O[e]`. -/
def pointXK (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (delta : Coord → Block) (whitened : InputMacKey) : Fin pointElementCountX → BaseField :=
  offsets oracle hashOracle .pointX (delta .x) (bitKeyOf whitened .x)

/-- **Step 2.** The `pointY` lane's element offsets. -/
def pointYK (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (delta : Coord → Block) (whitened : InputMacKey) : Fin pointElementCountY → BaseField :=
  offsets oracle hashOracle .pointY (delta .y) (bitKeyOf whitened .y)

/-- The per-digit element offsets: the row layer's `K`. -/
def digitK (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (delta : Coord → Block) (whitened : InputMacKey) : FieldMacToECMac.DigitValues :=
  fun digit =>
    digitValues (pointXK oracle hashOracle delta whitened)
      (pointYK oracle hashOracle delta whitened) digit

/-- **Step 3.** The eight slopes of each digit, derived from the element offsets. -/
def pointSlopes (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (delta : Coord → Block) (whitened : InputMacKey) (randomness : FieldMacToECMac.Randomness) :
    Fin digitCount → Biquadratic.Values :=
  fun digit =>
    Biquadratic.slopes (randomness.get digit).x (randomness.get digit).y (randomness.get digit).z
      (digitK oracle hashOracle delta whitened digit)

/-- **Steps 4 and 5.** The `pointX` lane's published fold joins and chunk joins. -/
def pointXGarbled (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (delta : Coord → Block) (whitened : InputMacKey) (randomness : FieldMacToECMac.Randomness) :
    Vector Block foldStepCount × (Fin chunkCount → Fin pointElementCountX → BaseField) :=
  garbleCoord oracle hashOracle .pointX (delta .x) (bitKeyOf whitened .x)
    (pointXAssemble (pointSlopes oracle hashOracle delta whitened randomness))

/-- **Steps 4 and 5.** The `pointY` lane's published fold joins and chunk joins. -/
def pointYGarbled (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (delta : Coord → Block) (whitened : InputMacKey) (randomness : FieldMacToECMac.Randomness) :
    Vector Block foldStepCount × (Fin chunkCount → Fin pointElementCountY → BaseField) :=
  garbleCoord oracle hashOracle .pointY (delta .y) (bitKeyOf whitened .y)
    (pointYAssemble (pointSlopes oracle hashOracle delta whitened randomness))

/-- The point layer's published table: the eleven row constants of each digit and the gadget
entries. The gadget keeps reading the bit-dependent `EncPRF.transformKey` labels. -/
def pointGarble (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness)
    (exceptionPad : FieldMacToECMac.ExceptionPad)
    (bridgeKey : BaseField)
    (fixedKeyOracle : PermutationOracle FixedIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (delta : Coord → Block) (inputKey : InputMacKey) :
    FieldMacToECMac.Table :=
  FieldMacToECMac.garble outputKeys
    (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness) pointRandomness
    (digitK fixedKeyOracle hashOracle delta
      (whitenedKey encPRFOracle hashOracle bridgeKey inputKey))
    (EncPRF.transformKey encPRFOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey)
    (gadgetPermutations fixedKeyOracle) exceptionPad

/-- The point layer's view of a published value. -/
def pointTable (table : Public) : FieldMacToECMac.Table := (table.rows, table.exception)

/-- **Step 6.** The complete public value. -/
def garble (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness)
    (exceptionPad : FieldMacToECMac.ExceptionPad)
    (bridgeKey : BaseField) (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
    (fixedKeyOracle : PermutationOracle FixedIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (delta : Coord → Block) (inputKey : InputMacKey) :
    Public :=
  { curve := CurveMembership.garble bridgeKey curveMask.value curveR1 curveR2
      (curveK fixedKeyOracle hashOracle delta inputKey)
    rows := (pointGarble outputKeys pointRandomness exceptionPad bridgeKey fixedKeyOracle
      encPRFOracle hashOracle delta inputKey).1
    exception := (pointGarble outputKeys pointRandomness exceptionPad bridgeKey fixedKeyOracle
      encPRFOracle hashOracle delta inputKey).2
    curveXHot := (curveXGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).1
    curveYHot := (curveYGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).1
    pointXHot := (pointXGarbled fixedKeyOracle hashOracle delta
      (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).1
    pointYHot := (pointYGarbled fixedKeyOracle hashOracle delta
      (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).1
    scale := Vector.ofFn fun chunk => pack (assembleWord
      ((pointXGarbled fixedKeyOracle hashOracle delta
        (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).2 chunk)
      ((curveXGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).2 chunk)
      ((pointYGarbled fixedKeyOracle hashOracle delta
        (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).2 chunk)
      ((curveYGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).2 chunk)) }

/-! ### The evaluator -/

/-- The `curveX` lane's element values, off the raw labels. -/
def curveXValues (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (table : Public) (input : BitInput) (inputMac : InputMac) :
    Fin curveElementCountX → BaseField :=
  evalCoord oracle hashOracle .curveX table.curveXHot
    (fun chunk => readCurveX (unpack (table.scale.get chunk)))
    (coordBits input .x) (macLabels inputMac .x)

/-- The `curveY` lane's element values, off the raw labels. -/
def curveYValues (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (table : Public) (input : BitInput) (inputMac : InputMac) :
    Fin curveElementCountY → BaseField :=
  evalCoord oracle hashOracle .curveY table.curveYHot
    (fun chunk => readCurveY (unpack (table.scale.get chunk)))
    (coordBits input .y) (macLabels inputMac .y)

/-- The `pointX` lane's element values, off the whitened labels. -/
def pointXValues (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (table : Public) (input : BitInput) (whitenedMac : InputMac) :
    Fin pointElementCountX → BaseField :=
  evalCoord oracle hashOracle .pointX table.pointXHot
    (fun chunk => readPointX (unpack (table.scale.get chunk)))
    (coordBits input .x) (macLabels whitenedMac .x)

/-- The `pointY` lane's element values, off the whitened labels. -/
def pointYValues (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (table : Public) (input : BitInput) (whitenedMac : InputMac) :
    Fin pointElementCountY → BaseField :=
  evalCoord oracle hashOracle .pointY table.pointYHot
    (fun chunk => readPointY (unpack (table.scale.get chunk)))
    (coordBits input .y) (macLabels whitenedMac .y)

/-- The pipeline evaluator: curve check first, then the EncPRF gate, then the point rows. -/
def evaluate [FieldCertificate]
    (fixedKeyOracle : PermutationOracle FixedIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (table : Public)
    (input : BitInput) (inputMac : InputMac) : Option FieldMacToECMac.Result :=
  let affineInput := input.toAffine
  match decodePoint affineInput with
  | none => none
  | some _ =>
      let bridgeKey := CurveMembership.evaluate table.curve affineInput
        (curveValues (curveXValues fixedKeyOracle hashOracle table input inputMac)
          (curveYValues fixedKeyOracle hashOracle table input inputMac))
      let keys := EncPRF.whiteningKeys hashOracle bridgeKey
      let whitenedMac := EncPRF.whitenMac encPRFOracle keys inputMac
      let pointInputMac := EncPRF.transformMac encPRFOracle keys input inputMac
      some (FieldMacToECMac.evaluate (pointTable table)
        (digitValues (pointXValues fixedKeyOracle hashOracle table input whitenedMac)
          (pointYValues fixedKeyOracle hashOracle table input whitenedMac))
        (gadgetPermutations fixedKeyOracle) affineInput pointInputMac)

/-! ### Delivery

`Construction` may not import `Proof`, so the row-layer theorem below takes the projectivized
garbling scheme's end-to-end delivery fact as a hypothesis. It is exactly
`evalCoord_garbleCoord` of `Proof/Correctness/PGS/AffineFp.lean`, which holds for every tape,
every lane, every offset and every slope vector; Task 20 discharges it. -/

/-- The switch systems deliver `slope * coordinate + offset` for every element of every lane,
for every fixed-key oracle and every hash oracle. -/
def Delivers (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle) :
    Prop :=
  ∀ (lane : Lane) (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block),
    (∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta) →
      ∀ (slopes : Fin (laneCount lane) → BaseField) (value : BaseField)
        (element : Fin (laneCount lane)),
        evalCoord oracle hashOracle lane
            (garbleCoord oracle hashOracle lane delta bitKey slopes).1
            (garbleCoord oracle hashOracle lane delta bitKey slopes).2
            (coordWord value) (selectBits bitKey (coordWord value)) element
          = slopes element * value + offsets oracle hashOracle lane delta bitKey element

/-! ### One construction query per gate

The index builder `hotIndexNat` of `Construction/PGS/Index.lean` clamps its `Nat` arguments
with `%`, so "the clamp is the identity" is a property of the call sites. These are the call
sites the pipeline wires, and the clamps are the identity at every one of them; the builder is
therefore injective there, which is what makes each `bin-to-hot` index carry exactly one
construction query (plan D.6, budget term `T2 = 0`). The lane is part of the index, so the two
switch systems of one coordinate never share a gate either.

The `scale-hot` switch masks are hash queries, not fixed-key gates: their inputs are the
`PlanB.scaleInput` values, whose mixed-radix tag carries the lane, the chunk, the switch and the
limb, so they are pairwise distinct as well (`scaleInput_injective`, proved with the sampler
facts). -/

/-- Every switch of every chunk is inside the `chunkBits`-wide switch radix. -/
theorem switch_lt_twoPowChunkBits (chunk : Fin chunkCount) (switch : Fin (2 ^ chunkWidth chunk)) :
    switch.val < 2 ^ chunkBits :=
  lt_of_lt_of_le switch.isLt (Nat.pow_le_pow_right (by omega) (chunkWidth_le chunk))

/-- Every fold step of every chunk is inside the `hot` index's step range. -/
theorem fold_lt_chunkBits (chunk : Fin chunkCount) (step : Nat)
    (inChunk : step < chunkWidth chunk) : step < chunkBits :=
  lt_of_lt_of_le inChunk (chunkWidth_le chunk)

/-- Every one-hot entry of every fold level is inside the `hot` index's entry range. -/
theorem entry_lt_twoPowChunkBits (chunk : Fin chunkCount) (step entry : Nat)
    (inChunk : step < chunkWidth chunk) (inLevel : entry < 2 ^ step) :
    entry < 2 ^ chunkBits :=
  lt_of_lt_of_le inLevel
    (Nat.pow_le_pow_right (by omega) (le_of_lt (fold_lt_chunkBits chunk step inChunk)))

/-- The `bin-to-hot` gates of one lane are pairwise distinct. -/
theorem hotIndexNat_injective (lane : Lane) (chunk chunk' : Fin chunkCount)
    (fold entry fold' entry' : Nat) (half half' : Bool) (foldRange : fold < chunkBits)
    (entryRange : entry < 2 ^ chunkBits) (foldRange' : fold' < chunkBits)
    (entryRange' : entry' < 2 ^ chunkBits)
    (equal : hotIndexNat lane chunk fold entry half
      = hotIndexNat lane chunk' fold' entry' half') :
    chunk = chunk' ∧ fold = fold' ∧ entry = entry' ∧ half = half' := by
  rw [hotIndexNat_eq lane chunk fold entry half foldRange entryRange,
    hotIndexNat_eq lane chunk' fold' entry' half' foldRange' entryRange'] at equal
  simp only [FixedIndex.hot.injEq, Fin.mk.injEq] at equal
  exact ⟨equal.2.1, equal.2.2.1, equal.2.2.2.1, equal.2.2.2.2⟩

/-- Distinct lanes never share a `bin-to-hot` gate. -/
theorem hotIndexNat_lane (lane lane' : Lane) (chunk chunk' : Fin chunkCount)
    (fold entry fold' entry' : Nat) (half half' : Bool) (foldRange : fold < chunkBits)
    (entryRange : entry < 2 ^ chunkBits) (foldRange' : fold' < chunkBits)
    (entryRange' : entry' < 2 ^ chunkBits)
    (equal : hotIndexNat lane chunk fold entry half
      = hotIndexNat lane' chunk' fold' entry' half') :
    lane = lane' := by
  rw [hotIndexNat_eq lane chunk fold entry half foldRange entryRange,
    hotIndexNat_eq lane' chunk' fold' entry' half' foldRange' entryRange'] at equal
  simp only [FixedIndex.hot.injEq] at equal
  exact equal.1

/-- The gadget family is disjoint from the `bin-to-hot` family. -/
theorem gadget_ne_hot (digit : Fin digitCount) (coord : Coord) (lane : Lane)
    (position : Fin PlanB.coordinateBits) (chunk : Fin chunkCount) (fold : Fin chunkBits)
    (entry : Fin (2 ^ chunkBits)) (half : Bool) :
    (FixedIndex.gadget digit coord position) ≠ FixedIndex.hot lane chunk fold entry half :=
  fun equal => by cases equal

section Encoded

variable (outputKeys : FieldMacToECMac.OutputKeys)
  (pointRandomness : FieldMacToECMac.Randomness)
  (exceptionPad : FieldMacToECMac.ExceptionPad)
  (bridgeKey : BaseField) (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
  (fixedKeyOracle : PermutationOracle FixedIndex Block)
  (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
  (hashOracle : EncPRF.HashOracle) (delta : Coord → Block) (inputKey : InputMacKey)

/-- The published chunk words read back as the `pointX` lane's own chunk joins. -/
theorem scale_pointX :
    (fun chunk => readPointX (unpack ((garble outputKeys pointRandomness exceptionPad bridgeKey
        curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey).scale.get
        chunk)))
      = (pointXGarbled fixedKeyOracle hashOracle delta
          (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).2 := by
  funext chunk
  have word : (garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1 curveR2
        fixedKeyOracle encPRFOracle hashOracle delta inputKey).scale.get chunk
      = pack (assembleWord
          ((pointXGarbled fixedKeyOracle hashOracle delta
            (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).2 chunk)
          ((curveXGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).2 chunk)
          ((pointYGarbled fixedKeyOracle hashOracle delta
            (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).2 chunk)
          ((curveYGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).2 chunk)) := by
    simp only [garble, Vector.get_ofFn]
  rw [word, unpack_pack_eq, readPointX_assembleWord]

/-- The published chunk words read back as the `curveX` lane's own chunk joins. -/
theorem scale_curveX :
    (fun chunk => readCurveX (unpack ((garble outputKeys pointRandomness exceptionPad bridgeKey
        curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey).scale.get
        chunk)))
      = (curveXGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).2 := by
  funext chunk
  have word : (garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1 curveR2
        fixedKeyOracle encPRFOracle hashOracle delta inputKey).scale.get chunk
      = pack (assembleWord
          ((pointXGarbled fixedKeyOracle hashOracle delta
            (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).2 chunk)
          ((curveXGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).2 chunk)
          ((pointYGarbled fixedKeyOracle hashOracle delta
            (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).2 chunk)
          ((curveYGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).2 chunk)) := by
    simp only [garble, Vector.get_ofFn]
  rw [word, unpack_pack_eq, readCurveX_assembleWord]

/-- The published chunk words read back as the `pointY` lane's own chunk joins. -/
theorem scale_pointY :
    (fun chunk => readPointY (unpack ((garble outputKeys pointRandomness exceptionPad bridgeKey
        curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey).scale.get
        chunk)))
      = (pointYGarbled fixedKeyOracle hashOracle delta
          (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).2 := by
  funext chunk
  have word : (garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1 curveR2
        fixedKeyOracle encPRFOracle hashOracle delta inputKey).scale.get chunk
      = pack (assembleWord
          ((pointXGarbled fixedKeyOracle hashOracle delta
            (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).2 chunk)
          ((curveXGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).2 chunk)
          ((pointYGarbled fixedKeyOracle hashOracle delta
            (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).2 chunk)
          ((curveYGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).2 chunk)) := by
    simp only [garble, Vector.get_ofFn]
  rw [word, unpack_pack_eq, readPointY_assembleWord]

/-- The published chunk words read back as the `curveY` lane's own chunk joins. -/
theorem scale_curveY :
    (fun chunk => readCurveY (unpack ((garble outputKeys pointRandomness exceptionPad bridgeKey
        curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey).scale.get
        chunk)))
      = (curveYGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).2 := by
  funext chunk
  have word : (garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1 curveR2
        fixedKeyOracle encPRFOracle hashOracle delta inputKey).scale.get chunk
      = pack (assembleWord
          ((pointXGarbled fixedKeyOracle hashOracle delta
            (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).2 chunk)
          ((curveXGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).2 chunk)
          ((pointYGarbled fixedKeyOracle hashOracle delta
            (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).2 chunk)
          ((curveYGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).2 chunk)) := by
    simp only [garble, Vector.get_ofFn]
  rw [word, unpack_pack_eq, readCurveY_assembleWord]

/-- **System A, x lane.** Every curve x-element value the evaluator recovers off the raw
labels is the element's slope times the coordinate, offset by the garbler's output mask. -/
theorem curveXValues_garble (correlated : CorrelatedKey inputKey delta)
    (delivers : Delivers fixedKeyOracle hashOracle) (input : AffineInput)
    (element : Fin curveElementCountX) :
    curveXValues fixedKeyOracle hashOracle (garble outputKeys pointRandomness exceptionPad bridgeKey
        curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey)
        (BitInput.ofAffine input) (inputKey.encode (BitInput.ofAffine input)) element
      = curveXAssemble
            (curveSlopes fixedKeyOracle hashOracle delta inputKey curveR1 curveR2) element
          * input.x
        + curveXK fixedKeyOracle hashOracle delta inputKey element := by
  rw [curveXValues, scale_curveX outputKeys pointRandomness exceptionPad bridgeKey curveMask
    curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey, macLabels_encode]
  have hot : (garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1 curveR2
      fixedKeyOracle encPRFOracle hashOracle delta inputKey).curveXHot
      = (curveXGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).1 := rfl
  rw [hot, curveXGarbled, coordBits_ofAffine]
  exact delivers .curveX (delta .x) (bitKeyOf inputKey .x) (fun position => correlated .x position)
    (curveXAssemble (curveSlopes fixedKeyOracle hashOracle delta inputKey curveR1 curveR2))
    input.x element

/-- **System A, y lane.** -/
theorem curveYValues_garble (correlated : CorrelatedKey inputKey delta)
    (delivers : Delivers fixedKeyOracle hashOracle) (input : AffineInput)
    (element : Fin curveElementCountY) :
    curveYValues fixedKeyOracle hashOracle (garble outputKeys pointRandomness exceptionPad bridgeKey
        curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey)
        (BitInput.ofAffine input) (inputKey.encode (BitInput.ofAffine input)) element
      = curveYAssemble
            (curveSlopes fixedKeyOracle hashOracle delta inputKey curveR1 curveR2) element
          * input.y
        + curveYK fixedKeyOracle hashOracle delta inputKey element := by
  rw [curveYValues, scale_curveY outputKeys pointRandomness exceptionPad bridgeKey curveMask
    curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey, macLabels_encode]
  have hot : (garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1 curveR2
      fixedKeyOracle encPRFOracle hashOracle delta inputKey).curveYHot
      = (curveYGarbled fixedKeyOracle hashOracle delta inputKey curveR1 curveR2).1 := rfl
  rw [hot, curveYGarbled, coordBits_ofAffine]
  exact delivers .curveY (delta .y) (bitKeyOf inputKey .y) (fun position => correlated .y position)
    (curveYAssemble (curveSlopes fixedKeyOracle hashOracle delta inputKey curveR1 curveR2))
    input.y element

/-- The curve check sees exactly the five values its algebra expects. -/
theorem curveValues_garble (correlated : CorrelatedKey inputKey delta)
    (delivers : Delivers fixedKeyOracle hashOracle) (input : AffineInput) :
    curveValues
        (curveXValues fixedKeyOracle hashOracle
          (garble outputKeys pointRandomness exceptionPad bridgeKey
          curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey)
          (BitInput.ofAffine input) (inputKey.encode (BitInput.ofAffine input)))
        (curveYValues fixedKeyOracle hashOracle
          (garble outputKeys pointRandomness exceptionPad bridgeKey
          curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey)
          (BitInput.ofAffine input) (inputKey.encode (BitInput.ofAffine input)))
      = CurveMembership.delivered curveR1 curveR2 (curveK fixedKeyOracle hashOracle delta inputKey)
          input := by
  funext element
  cases element with
  | inl slot =>
      show curveXValues _ _ _ _ _ (curveXElementIndex slot) = _
      rw [curveXValues_garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1
        curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey correlated delivers input,
        curveXAssemble_slot]
      rfl
  | inr slot =>
      show curveYValues _ _ _ _ _ (curveYElementIndex slot) = _
      rw [curveYValues_garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1
        curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey correlated delivers input,
        curveYAssemble_slot]
      rfl

/-- **System B, x lane.** The same delivery, off the EncPRF-whitened labels. -/
theorem pointXValues_garble (correlated : CorrelatedKey inputKey delta)
    (delivers : Delivers fixedKeyOracle hashOracle) (input : AffineInput)
    (element : Fin pointElementCountX) :
    pointXValues fixedKeyOracle hashOracle (garble outputKeys pointRandomness exceptionPad bridgeKey
        curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey)
        (BitInput.ofAffine input)
        ((whitenedKey encPRFOracle hashOracle bridgeKey inputKey).encode
          (BitInput.ofAffine input)) element
      = pointXAssemble (pointSlopes fixedKeyOracle hashOracle delta
            (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness) element
          * input.x
        + pointXK fixedKeyOracle hashOracle delta
            (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) element := by
  rw [pointXValues, scale_pointX outputKeys pointRandomness exceptionPad bridgeKey curveMask
    curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey, macLabels_encode]
  have hot : (garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1 curveR2
      fixedKeyOracle encPRFOracle hashOracle delta inputKey).pointXHot
      = (pointXGarbled fixedKeyOracle hashOracle delta
          (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).1 := rfl
  rw [hot, pointXGarbled, coordBits_ofAffine]
  exact delivers .pointX (delta .x)
    (bitKeyOf (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) .x)
    (fun position => whitenedKey_correlated encPRFOracle hashOracle bridgeKey inputKey delta
      correlated .x position)
    (pointXAssemble (pointSlopes fixedKeyOracle hashOracle delta
      (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness)) input.x element

/-- **System B, y lane.** -/
theorem pointYValues_garble (correlated : CorrelatedKey inputKey delta)
    (delivers : Delivers fixedKeyOracle hashOracle) (input : AffineInput)
    (element : Fin pointElementCountY) :
    pointYValues fixedKeyOracle hashOracle (garble outputKeys pointRandomness exceptionPad bridgeKey
        curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey)
        (BitInput.ofAffine input)
        ((whitenedKey encPRFOracle hashOracle bridgeKey inputKey).encode
          (BitInput.ofAffine input)) element
      = pointYAssemble (pointSlopes fixedKeyOracle hashOracle delta
            (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness) element
          * input.y
        + pointYK fixedKeyOracle hashOracle delta
            (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) element := by
  rw [pointYValues, scale_pointY outputKeys pointRandomness exceptionPad bridgeKey curveMask
    curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey, macLabels_encode]
  have hot : (garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1 curveR2
      fixedKeyOracle encPRFOracle hashOracle delta inputKey).pointYHot
      = (pointYGarbled fixedKeyOracle hashOracle delta
          (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness).1 := rfl
  rw [hot, pointYGarbled, coordBits_ofAffine]
  exact delivers .pointY (delta .y)
    (bitKeyOf (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) .y)
    (fun position => whitenedKey_correlated encPRFOracle hashOracle bridgeKey inputKey delta
      correlated .y position)
    (pointYAssemble (pointSlopes fixedKeyOracle hashOracle delta
      (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) pointRandomness)) input.y element

/-- Each digit's row sees exactly the eight values its algebra expects. -/
theorem digitValues_garble (correlated : CorrelatedKey inputKey delta)
    (delivers : Delivers fixedKeyOracle hashOracle) (input : AffineInput) :
    digitValues
        (pointXValues fixedKeyOracle hashOracle
          (garble outputKeys pointRandomness exceptionPad bridgeKey
          curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey)
          (BitInput.ofAffine input)
          ((whitenedKey encPRFOracle hashOracle bridgeKey inputKey).encode
            (BitInput.ofAffine input)))
        (pointYValues fixedKeyOracle hashOracle
          (garble outputKeys pointRandomness exceptionPad bridgeKey
          curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey)
          (BitInput.ofAffine input)
          ((whitenedKey encPRFOracle hashOracle bridgeKey inputKey).encode
            (BitInput.ofAffine input)))
      = FieldMacToECMac.delivered pointRandomness
          (digitK fixedKeyOracle hashOracle delta
            (whitenedKey encPRFOracle hashOracle bridgeKey inputKey)) input := by
  funext digit element
  cases element with
  | inl slot =>
      show pointXValues _ _ _ _ _ (xElementIndex digit slot) = _
      rw [pointXValues_garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1
        curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey correlated delivers input,
        pointXAssemble_digit]
      rfl
  | inr slot =>
      show pointYValues _ _ _ _ _ (yElementIndex digit slot) = _
      rw [pointYValues_garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1
        curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey correlated delivers input,
        pointYAssemble_digit]
      rfl

/-- **Correct labels evaluate the whole pipeline.** -/
theorem evaluateEncoded [FieldCertificate] (correlated : CorrelatedKey inputKey delta)
    (delivers : Delivers fixedKeyOracle hashOracle)
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point) :
    evaluate fixedKeyOracle encPRFOracle hashOracle
        (garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1 curveR2
          fixedKeyOracle encPRFOracle hashOracle delta inputKey)
        (BitInput.ofAffine input) (inputKey.encode (BitInput.ofAffine input)) =
      some (FieldMacToECMac.expectedResult outputKeys
        (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness) pointRandomness
        (digitK fixedKeyOracle hashOracle delta
          (whitenedKey encPRFOracle hashOracle bridgeKey inputKey))
        (EncPRF.transformKey encPRFOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey)
        (gadgetPermutations fixedKeyOracle) exceptionPad input) := by
  have inputOnCurve : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
  simp only [evaluate, BitInput.toAffineOfAffine, decoded]
  rw [curveValues_garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1
    curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey correlated delivers input]
  have curveValue : CurveMembership.evaluate
      (garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1 curveR2
        fixedKeyOracle encPRFOracle hashOracle delta inputKey).curve input
      (CurveMembership.delivered curveR1 curveR2 (curveK fixedKeyOracle hashOracle delta inputKey)
        input)
      = bridgeKey := by
    show CurveMembership.evaluate (CurveMembership.garble bridgeKey curveMask.value curveR1
      curveR2 (curveK fixedKeyOracle hashOracle delta inputKey)) input _ = bridgeKey
    exact CurveMembership.evaluateEncodedOnCurve bridgeKey curveMask.value curveR1 curveR2
      (curveK fixedKeyOracle hashOracle delta inputKey) input inputOnCurve
  rw [curveValue, EncPRF.whitenEncode,
    show EncPRF.whitenKey encPRFOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey
      = whitenedKey encPRFOracle hashOracle bridgeKey inputKey from rfl,
    digitValues_garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1
      curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey correlated delivers input,
    EncPRF.transformEncode]
  rw [show pointTable (garble outputKeys pointRandomness exceptionPad bridgeKey curveMask
      curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle delta inputKey)
      = pointGarble outputKeys pointRandomness exceptionPad bridgeKey fixedKeyOracle
        encPRFOracle hashOracle delta inputKey from rfl,
    pointGarble, InputMacKey.encodeOfAffine,
    FieldMacToECMac.evaluateEncoded (onCurve := inputOnCurve)]
  exact FieldMacToECMac.rowsForOutputKeysSparse outputKeys pointRandomness

end Encoded

end Kriterion.ArgoMAC.Pipeline
