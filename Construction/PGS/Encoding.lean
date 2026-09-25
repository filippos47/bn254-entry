/-
This file defines the Plan B byte layout and proves the ciphertext-size theorem.

The plan source is `2026-09-17-planB.md`, section D.5 and Task 11.
`Public` carries no `Option` tag, so every inhabitant encodes to exactly
`ciphertextBytesConstant = 1100521` bytes and the theorem is independent of `garble`.

| Field       | Encoding                                | Formula        | Bytes   |
|-------------|-----------------------------------------|----------------|---------|
| `curve`, `rows` | `fieldsWord`: 911 cells, one base-`p` number | `⌈log₂ p ^ 911 / 8⌉` | 28,879 |
| `exception` | `gadget`: 1092 cells at 3 bits          | `410`          | 410     |
| `curveXHot` | `Vector block 202`                      | `202 * 16`     | 3,232   |
| `curveYHot` | `Vector block 202`                      | `202 * 16`     | 3,232   |
| `pointXHot` | `Vector block 202`                      | `202 * 16`     | 3,232   |
| `pointYHot` | `Vector block 202`                      | `202 * 16`     | 3,232   |
| `scale`     | `Vector chunkWord 52`                   | `52 * 20352`   | 1,058,304 |
| **total**   |                                         |                | **1,100,521** |

The curve constant and the row constants are canonical field elements, so they share one
base-`p` number of `911` digits: `p ^ 911 < 2 ^ 231,027 ≤ 2 ^ (8 * 28,879)`.

A chunk word is the `642` join values as one base-`p` number, below `p ^ 642 < 2 ^ 162,810`.
Rule N: the only fact about the `162816`-bit word is `pow_width`, proved symbolically in
`Construction/PGS/Packing.lean`; the numeral itself is never formed.
-/

import Construction.ArgoMAC.Public
import Encoding

namespace Kriterion.ArgoMAC.PlanB.Wire

open BN254 Cryptography

/-- A correlation block, `16` bytes. -/
private def block : Encoding Block :=
  (Encoding.natural 16).map
    (fun value => ⟨value.toNat, by
      have expand : (256 : Nat) ^ 16 = 2 ^ 128 := by norm_num
      rw [expand]; exact value.isLt⟩)
    (fun value => BitVec.ofNat 128 value.val)
    (fun value => by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt value.isLt])

/-- One chunk's `scale-hot` join word, `chunkJoinBytes` bytes. -/
private def chunkWord : Encoding (BitVec chunkJoinBits) :=
  (Encoding.natural chunkJoinBytes).map
    (fun value => ⟨value.toNat, by rw [pow_width]; exact value.isLt⟩)
    (fun value => BitVec.ofNat chunkJoinBits value.val)
    (fun value => by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt value.isLt])

/-- The gadget cells: `91 · 12 = 1092` three-bit codes. -/
def gadgetCellsCount : Nat := 1092

/-- The gadget word's bytes: `1092 · 3 = 3276` bits and four zero bits. -/
def gadgetBytes : Nat := 410

theorem gadget_pow : (256 : Nat) ^ gadgetBytes = 2 ^ (8 * gadgetBytes) := by
  rw [pow_mul]
  norm_num

theorem gadgetBits_le : 3 * gadgetCellsCount ≤ 8 * gadgetBytes := by
  unfold gadgetCellsCount gadgetBytes
  norm_num

/-- Cell `index` of the gadget: slot `index % 12` of digit `index / 12`. -/
def gadgetCell (value : Vector Exception.Entry digitCount) (index : Fin gadgetCellsCount) :
    BitVec 3 :=
  (value.get ⟨index.val / 12, by
      have := index.isLt; unfold gadgetCellsCount at this; unfold digitCount; omega⟩).get
    ⟨index.val % 12, Nat.mod_lt _ (by decide)⟩

/-- Reading the gadget back from its cells. -/
def gadgetOf (cells : Fin gadgetCellsCount → BitVec 3) : Vector Exception.Entry digitCount :=
  Vector.ofFn fun digit => Vector.ofFn fun slot => cells ⟨12 * digit.val + slot.val, by
    have := digit.isLt; have := slot.isLt
    unfold gadgetCellsCount; unfold digitCount at *; omega⟩

theorem gadgetOf_gadgetCell (value : Vector Exception.Entry digitCount) :
    gadgetOf (gadgetCell value) = value := by
  refine Vector.ext fun digit digitSmall => ?_
  refine Vector.ext fun slot slotSmall => ?_
  unfold gadgetOf gadgetCell
  simp only [Vector.getElem_ofFn, Vector.get_eq_getElem]
  have quotient : (12 * digit + slot) / 12 = digit := by omega
  have remainder : (12 * digit + slot) % 12 = slot := by omega
  simp only [quotient, remainder]

/-- The whole gadget, `1092` three-bit cells in one `410`-byte word. -/
private def gadget : Encoding (Vector Exception.Entry digitCount) :=
  (Encoding.natural gadgetBytes).map
    (fun value => ⟨packBitsNat 3 gadgetCellsCount (gadgetCell value), by
      rw [gadget_pow]
      exact lt_of_lt_of_le (packBitsNat_lt _ _ _)
        (Nat.pow_le_pow_right (by norm_num) gadgetBits_le)⟩)
    (fun word => gadgetOf (unpackBits 3 gadgetCellsCount word.val))
    (fun value => by
      simp only [unpackBits_packBitsNat]
      exact gadgetOf_gadgetCell value)

/-- The number of field cells of the curve-and-rows word: `1 + 91 * 10`. -/
def fieldCellsCount : Nat := 911

/-- The curve-and-rows word's bytes: `p ^ 911 < 2 ^ 231027 ≤ 2 ^ (8 * 28879)`. -/
def fieldsBytes : Nat := 28879

/-- `p ^ 911` fits the curve-and-rows word: its base-`p` number never overflows. -/
theorem fields_modulus_lt : BN254.baseFieldModulus ^ fieldCellsCount < 256 ^ fieldsBytes := by
  unfold fieldCellsCount fieldsBytes
  decide +kernel

/-- The index of cell `j` of digit `d`'s row constants. -/
def rowCellIndex (digit : Fin digitCount) (field : Fin 10) : Fin fieldCellsCount :=
  ⟨1 + 10 * digit.val + field.val, by
    have := digit.isLt; have := field.isLt
    unfold fieldCellsCount; unfold digitCount at *; omega⟩

/-- The cell `index` of the curve-and-rows word: the curve constant, then each digit's ten row
constants. -/
def fieldsCell (value : BaseField × Vector RowGamma digitCount)
    (index : Fin fieldCellsCount) : BaseField :=
  if index.val = 0 then value.1
  else (value.2.get ⟨(index.val - 1) / 10, by
      have := index.isLt; unfold fieldCellsCount at this; unfold digitCount; omega⟩).cell
    ((index.val - 1) % 10)

/-- Reading the curve and the rows back from the cells. -/
def fieldsOf (cells : Fin fieldCellsCount → BaseField) :
    BaseField × Vector RowGamma digitCount :=
  (cells ⟨0, by decide⟩,
    Vector.ofFn fun digit =>
      ⟨cells (rowCellIndex digit 0), cells (rowCellIndex digit 1), cells (rowCellIndex digit 2),
        cells (rowCellIndex digit 3), cells (rowCellIndex digit 4), cells (rowCellIndex digit 5),
        cells (rowCellIndex digit 6), cells (rowCellIndex digit 7), cells (rowCellIndex digit 8),
        cells (rowCellIndex digit 9)⟩)

theorem fieldsCell_row (value : BaseField × Vector RowGamma digitCount)
    (digit : Fin digitCount) (field : Fin 10) :
    fieldsCell value (rowCellIndex digit field) = (value.2.get digit).cell field.val := by
  have fieldSmall := field.isLt
  unfold fieldsCell rowCellIndex
  simp only
  rw [if_neg (by omega)]
  have quotient : (1 + 10 * digit.val + field.val - 1) / 10 = digit.val := by omega
  have remainder : (1 + 10 * digit.val + field.val - 1) % 10 = field.val := by omega
  simp only [quotient, remainder]

theorem fieldsOf_fieldsCell (value : BaseField × Vector RowGamma digitCount) :
    fieldsOf (fieldsCell value) = value := by
  obtain ⟨c0, rows⟩ := value
  unfold fieldsOf
  simp only [fieldsCell_row]
  refine Prod.ext ?_ ?_
  · rfl
  · refine Vector.ext fun digit small => ?_
    rw [Vector.getElem_ofFn]
    exact RowGamma.eta_cell (rows.get ⟨digit, small⟩)

/-- The curve-and-rows word: `911` canonical field elements as one base-`p` number, `28879`
bytes. -/
private def fieldsWord :
    Encoding (BaseField × Vector RowGamma digitCount) :=
  (Encoding.natural fieldsBytes).map
    (fun value => ⟨packBaseCells fieldCellsCount (fieldsCell value),
      lt_trans (packBaseCells_lt_pow _ _) fields_modulus_lt⟩)
    (fun word => fieldsOf (unpackBaseCells fieldCellsCount word.val))
    (fun value => by
      simp only [unpackBaseCells_packBaseCells]
      exact fieldsOf_fieldsCell value)

/-- One coordinate's `bin-to-hot` fold joins. -/
private def hotVector : Encoding (Vector Block foldStepCount) := block.vector foldStepCount

/-- The `52` chunk words. -/
private def scaleVector : Encoding (Vector (BitVec chunkJoinBits) chunkCount) :=
  chunkWord.vector chunkCount

/-- The complete public encoding. Every field is fixed-width. -/
def encoding : Encoding Public :=
  (fieldsWord.pair (gadget.pair
    (hotVector.pair (hotVector.pair (hotVector.pair (hotVector.pair scaleVector)))))).map
    (fun value => ((value.curve, value.rows), value.exception, value.curveXHot, value.curveYHot,
      value.pointXHot, value.pointYHot, value.scale))
    (fun value => ⟨value.1.1, value.1.2, value.2.1, value.2.2.1, value.2.2.2.1,
      value.2.2.2.2.1, value.2.2.2.2.2.1, value.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-! ### Sizes

`Encoding.natural chunkJoinBytes` is a `20352`-fold structural recursion, so nothing may force
a concrete chunk-word encoding: any defeq check that reaches `List.length` of one exhausts the
kernel's stack. `SizedBy` keeps every such check at the `Encoding` level, where the comparison
is a single delta step, and the concrete byte counts only ever meet as `Nat` arithmetic. -/

/-- `encoding` emits exactly `size` bytes for every value. -/
private def SizedBy {alpha : Type} (encoding : Encoding alpha) (size : Nat) : Prop :=
  ∀ value, (encoding.encode value).length = size

private theorem sizedBy_pair {alpha beta : Type} {first : Encoding alpha} {second : Encoding beta}
    {left right : Nat} (hfirst : SizedBy first left) (hsecond : SizedBy second right) :
    SizedBy (first.pair second) (left + right) := by
  intro value
  show ((first.encode value.1) ++ (second.encode value.2)).length = left + right
  rw [List.length_append, hfirst, hsecond]

private theorem sizedBy_map {alpha beta : Type} {base : Encoding alpha} {size : Nat}
    (hbase : SizedBy base size) (encode : beta → alpha) (decode : alpha → beta)
    (inverse : ∀ value, decode (encode value) = value) :
    SizedBy (base.map encode decode inverse) size :=
  fun value => hbase (encode value)

private theorem sizedBy_vector {alpha : Type} {base : Encoding alpha} {size : Nat}
    (hbase : SizedBy base size) (count : Nat) : SizedBy (base.vector count) (count * size) :=
  fun value => Encoding.vector_length base size count value (fun _ => hbase _)

private theorem sizedBy_natural (width : Nat) : SizedBy (Encoding.natural width) width :=
  fun value => Encoding.natural_length width value

private theorem sizedBy_byte : SizedBy Encoding.byte 1 := fun _ => rfl

private theorem block_sized : SizedBy block 16 := sizedBy_map (sizedBy_natural 16) _ _ _

private theorem chunkWord_sized : SizedBy chunkWord chunkJoinBytes :=
  sizedBy_map (sizedBy_natural chunkJoinBytes) _ _ _

private theorem gadget_sized : SizedBy gadget gadgetBytes :=
  sizedBy_map (sizedBy_natural gadgetBytes) _ _ _

private theorem fieldsWord_sized : SizedBy fieldsWord fieldsBytes :=
  sizedBy_map (sizedBy_natural fieldsBytes) _ _ _

private theorem hotVector_sized : SizedBy hotVector 3232 :=
  sizedBy_vector block_sized foldStepCount

private theorem scaleVector_sized : SizedBy scaleVector 1058304 :=
  sizedBy_vector chunkWord_sized chunkCount

/-- The complete layout: `28879 + 410 + 4 * 3232 + 1058304`. -/
private theorem encoding_sized : SizedBy encoding ciphertextBytesConstant :=
  sizedBy_map (sizedBy_pair fieldsWord_sized
    (sizedBy_pair gadget_sized (sizedBy_pair hotVector_sized
      (sizedBy_pair hotVector_sized (sizedBy_pair hotVector_sized
        (sizedBy_pair hotVector_sized scaleVector_sized)))))) _ _ _

/-- The byte table of plan D.5 with Task 19a's four fold-join vectors, as an arithmetic
identity. -/
theorem byteArithmetic :
    28879 + (91 * 12 * 3 + 4) / 8 + 4 * (202 * 16) + 52 * 20352 = 1100521 := by
  norm_num

/-- **Every** public value encodes to exactly `ciphertextBytesConstant` bytes.
There are no `Option` tags in `Public`, so this does not mention `garble`. -/
theorem encoding_length (value : Public) :
    (encoding.encode value).length = ciphertextBytesConstant :=
  encoding_sized value

/-- The construction-facing corollary: the Plan B ciphertext is `1100521` bytes for every
garbling, whatever the tape, because it is `1100521` bytes for every inhabitant of `Public`. -/
theorem garble_length (value : Public) :
    (encoding.encode value).length = 1100521 :=
  encoding_length value

end Kriterion.ArgoMAC.PlanB.Wire
