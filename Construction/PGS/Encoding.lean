/-
This file defines the Plan B byte layout and proves the ciphertext-size theorem.

The plan source is `2026-09-17-planB.md`, section D.5 and Task 11.
`Public` carries no `Option` tag, so every inhabitant encodes to exactly
`ciphertextBytesConstant = 1103204` bytes and the theorem is independent of `garble`.

| Field       | Encoding                                | Formula        | Bytes   |
|-------------|-----------------------------------------|----------------|---------|
| `curve`     | `3 * field`                             | `3 * 32`       | 96      |
| `rows`      | `Vector rowGamma 91`                    | `91 * 320`     | 29,120  |
| `exception` | `Vector entry 91`                       | `91 * 12`      | 1,092   |
| `curveXHot` | `Vector block 202`                      | `202 * 16`     | 3,232   |
| `curveYHot` | `Vector block 202`                      | `202 * 16`     | 3,232   |
| `pointXHot` | `Vector block 202`                      | `202 * 16`     | 3,232   |
| `pointYHot` | `Vector block 202`                      | `202 * 16`     | 3,232   |
| `scale`     | `Vector chunkWord 52`                   | `52 * 20384`   | 1,059,968 |
| **total**   |                                         |                | **1,103,204** |

A chunk word carries `642 * 254 = 163,068` value bits and four zero bits.
Rule N: the only fact about the `163072`-bit word is `pow_width`, proved symbolically in
`Construction/PGS/Packing.lean`; the numeral itself is never formed.
-/

import Construction.ArgoMAC.Public
import Encoding

namespace Kriterion.ArgoMAC.PlanB.Wire

open BN254 Cryptography

/-- A field element, `32` bytes, no tag. -/
private def field : Encoding BaseField :=
  (Encoding.natural 32).map
    (fun value => ⟨value.val, lt_trans value.val_lt (by decide)⟩)
    (fun value => value.val)
    (fun value => ZMod.natCast_zmod_val value)

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

/-- One gadget byte. -/
private def gadgetByte : Encoding (BitVec 8) :=
  Encoding.byte.map
    (fun value : BitVec 8 => ⟨value.toNat, value.isLt⟩)
    (fun value => BitVec.ofNat 8 value.val)
    (fun value => by simp)

/-- One digit's gadget entry, `12` bytes. -/
private def entry : Encoding Exception.Entry := gadgetByte.vector 12

/-- The whole gadget, `91 * 12 = 1092` bytes. -/
private def gadget : Encoding (Vector Exception.Entry digitCount) := entry.vector digitCount

/-- One digit's ten published row constants, `10 * 32 = 320` bytes. -/
private def rowGamma : Encoding RowGamma :=
  (field.pair (field.pair (field.pair (field.pair (field.pair (field.pair (field.pair
    (field.pair (field.pair field))))))))).map
    (fun value => (value.xC0, value.xC1, value.xC2, value.xC4, value.yC0, value.yC2,
      value.yC4, value.yC5, value.zC0, value.zC1))
    (fun ⟨xC0, xC1, xC2, xC4, yC0, yC2, yC4, yC5, zC0, zC1⟩ =>
      ⟨xC0, xC1, xC2, xC4, yC0, yC2, yC4, yC5, zC0, zC1⟩)
    (fun _ => rfl)

/-- The curve-membership check, `3 * 32 = 96` bytes. -/
private def curveTriple : Encoding (BaseField × BaseField × BaseField) :=
  field.pair (field.pair field)

/-- All `91` digits' row constants. -/
private def rowVector : Encoding (Vector RowGamma digitCount) := rowGamma.vector digitCount

/-- One coordinate's `bin-to-hot` fold joins. -/
private def hotVector : Encoding (Vector Block foldStepCount) := block.vector foldStepCount

/-- The `52` chunk words. -/
private def scaleVector : Encoding (Vector (BitVec chunkJoinBits) chunkCount) :=
  chunkWord.vector chunkCount

/-- The complete public encoding. Every field is fixed-width. -/
def encoding : Encoding Public :=
  (curveTriple.pair (rowVector.pair (gadget.pair
    (hotVector.pair (hotVector.pair (hotVector.pair (hotVector.pair scaleVector))))))).map
    (fun value => (value.curve, value.rows, value.exception, value.curveXHot, value.curveYHot,
      value.pointXHot, value.pointYHot, value.scale))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2.1,
      value.2.2.2.2.2.1, value.2.2.2.2.2.2.1, value.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-! ### Sizes

`Encoding.natural chunkJoinBytes` is a `23273`-fold structural recursion, so nothing may force
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

private theorem field_sized : SizedBy field 32 := sizedBy_map (sizedBy_natural 32) _ _ _

private theorem block_sized : SizedBy block 16 := sizedBy_map (sizedBy_natural 16) _ _ _

private theorem chunkWord_sized : SizedBy chunkWord chunkJoinBytes :=
  sizedBy_map (sizedBy_natural chunkJoinBytes) _ _ _

private theorem gadgetByte_sized : SizedBy gadgetByte 1 := sizedBy_map sizedBy_byte _ _ _

private theorem entry_sized : SizedBy entry 12 := sizedBy_vector gadgetByte_sized 12

private theorem gadget_sized : SizedBy gadget 1092 := sizedBy_vector entry_sized digitCount

private theorem rowGamma_sized : SizedBy rowGamma 320 :=
  sizedBy_map (sizedBy_pair field_sized (sizedBy_pair field_sized (sizedBy_pair field_sized
    (sizedBy_pair field_sized (sizedBy_pair field_sized (sizedBy_pair field_sized
      (sizedBy_pair field_sized (sizedBy_pair field_sized (sizedBy_pair field_sized
        field_sized))))))))) _ _ _

private theorem curveTriple_sized : SizedBy curveTriple 96 :=
  sizedBy_pair field_sized (sizedBy_pair field_sized field_sized)

private theorem rowVector_sized : SizedBy rowVector 29120 :=
  sizedBy_vector rowGamma_sized digitCount

private theorem hotVector_sized : SizedBy hotVector 3232 :=
  sizedBy_vector block_sized foldStepCount

private theorem scaleVector_sized : SizedBy scaleVector 1059968 :=
  sizedBy_vector chunkWord_sized chunkCount

/-- The complete layout: `96 + 29120 + 1092 + 4 * 3232 + 1059968`. -/
private theorem encoding_sized : SizedBy encoding ciphertextBytesConstant :=
  sizedBy_map (sizedBy_pair curveTriple_sized (sizedBy_pair rowVector_sized
    (sizedBy_pair gadget_sized (sizedBy_pair hotVector_sized
      (sizedBy_pair hotVector_sized (sizedBy_pair hotVector_sized
        (sizedBy_pair hotVector_sized scaleVector_sized))))))) _ _ _

/-- The byte table of plan D.5 with Task 19a's four fold-join vectors, as an arithmetic
identity. -/
theorem byteArithmetic :
    3 * 32 + 91 * (10 * 32) + 91 * 12 + 4 * (202 * 16) + 52 * 20384 = 1103204 := by
  norm_num

/-- **Every** public value encodes to exactly `ciphertextBytesConstant` bytes.
There are no `Option` tags in `Public`, so this does not mention `garble`. -/
theorem encoding_length (value : Public) :
    (encoding.encode value).length = ciphertextBytesConstant :=
  encoding_sized value

/-- The construction-facing corollary: the Plan B ciphertext is `1103204` bytes for every
garbling, whatever the tape, because it is `1103204` bytes for every inhabitant of `Public`. -/
theorem garble_length (value : Public) :
    (encoding.encode value).length = 1103204 :=
  encoding_length value

end Kriterion.ArgoMAC.PlanB.Wire
