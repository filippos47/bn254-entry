/-
**The bits of the Plan B wire encoding.**

`wire_bits`: the flattened byte bits of `Wire.encoding.encode value` are, in order, the curve
constant and the `91 × 10` row constants (one base-`p` word), the `1092` three-bit gadget cells and
four zero bits, the four fold-join vectors (`128`), and the `52` chunk words (each one base-`p`
word). Every statement is symbolic in the counts; no encoding of a concrete width is ever
unfolded.
-/

import Proof.Simulator.Stage1Bits
import Proof.Simulator.CutoffSource

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Kriterion.ArgoMAC.Phase3.Glue

/-- The byte bits of a flattened list of byte lists. -/
theorem byteBits_flatten (lists : List (List (Fin 256))) :
    byteBits lists.flatten = (lists.map byteBits).flatten := by
  induction lists with
  | nil => rfl
  | cons first rest ih => rw [List.flatten_cons, byteBits_append, ih, List.map_cons, List.flatten_cons]

/-- An encoding's bytes, behind a regular (non-projection) head: the kernel compares
`encodeOf E x` with `encodeOf E y` by comparing `x` with `y`, and never unfolds `E` (the
encodings of large widths must never be unfolded). -/
def encodeOf {α : Type} (encoding : Encoding α) (value : α) : List (Fin 256) := encoding.encode value

theorem encode_eq {α : Type} (encoding : Encoding α) (value : α) :
    encoding.encode value = encodeOf encoding value := rfl

theorem encodeOf_map {α β : Type} (encoding : Encoding α) (encode : β → α) (decode : α → β)
    (inverse : ∀ value, decode (encode value) = value) (value : β) :
    encodeOf (encoding.map encode decode inverse) value = encodeOf encoding (encode value) := rfl

theorem encodeOf_pair {α β : Type} (first : Encoding α) (second : Encoding β) (left : α)
    (right : β) :
    encodeOf (first.pair second) (left, right) = encodeOf first left ++ encodeOf second right := rfl

/-- The byte bits of a vector encoding. -/
theorem byteBits_vector {α : Type} (encoding : Encoding α) (count : Nat) (values : Vector α count) :
    byteBits (encodeOf (encoding.vector count) values) =
      (List.ofFn fun index : Fin count => byteBits (encodeOf encoding values[index.val])).flatten := by
  unfold encodeOf
  rw [vector_encode, byteBits_flatten, List.map_ofFn]
  rfl


/-! ### The chunk word -/

/-- A little-endian digit sum of `count` digits of `width` bits. -/
def digitSum (width count : Nat) (digit : Fin count → Nat) : Nat :=
  ∑ slot : Fin count, digit slot * 2 ^ (width * slot.val)

theorem digitSum_succ (width count : Nat) (digit : Fin (count + 1) → Nat) :
    digitSum width (count + 1) digit =
      digit 0 + 2 ^ width * digitSum width count fun slot => digit slot.succ := by
  unfold digitSum
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun slot _ => ?_
    rw [Fin.val_succ, Nat.mul_succ, pow_add]
    ring

theorem digitSum_lt (width : Nat) : ∀ (count : Nat) (digit : Fin count → Nat),
    (∀ slot, digit slot < 2 ^ width) → digitSum width count digit < 2 ^ (width * count)
  | 0, _, _ => by simp [digitSum]
  | count + 1, digit, small => by
      rw [digitSum_succ]
      have rest := digitSum_lt width count (fun slot => digit slot.succ) (fun slot => small _)
      have head := small 0
      rw [Nat.mul_succ, pow_add]
      calc digit 0 + 2 ^ width * digitSum width count (fun slot => digit slot.succ)
          < 2 ^ width + 2 ^ width * digitSum width count (fun slot => digit slot.succ) := by omega
        _ = 2 ^ width * (digitSum width count (fun slot => digit slot.succ) + 1) := by ring
        _ ≤ 2 ^ width * 2 ^ (width * count) := Nat.mul_le_mul_left _ rest
        _ = 2 ^ (width * count) * 2 ^ width := Nat.mul_comm _ _

/-- **The bits of a digit sum are its digits' bits.** -/
theorem digitSum_bits (width : Nat) : ∀ (count : Nat) (digit : Fin count → Nat),
    (∀ slot, digit slot < 2 ^ width) →
      lsbs (width * count) (digitSum width count digit) =
        (List.ofFn fun slot : Fin count => lsbs width (digit slot)).flatten
  | 0, _, _ => by simp [lsbs]
  | count + 1, digit, small => by
      rw [Nat.mul_succ, Nat.add_comm, lsbs_add, List.ofFn_succ, List.flatten_cons]
      have head := small 0
      have split := digitSum_succ width count digit
      congr 1
      · rw [← lsbs_mod, split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt head]
      · rw [split, Nat.add_mul_div_left _ _ (Nat.two_pow_pos width), Nat.div_eq_of_lt head,
          Nat.zero_add]
        exact digitSum_bits width count (fun slot => digit slot.succ) (fun slot => small _)

end Kriterion.ArgoMAC.PlanB.SimMachine

namespace Kriterion.ArgoMAC.PlanB.Wire

open BN254 Cryptography Kriterion.GarbledCircuit Kriterion.ArgoMAC.PlanB.SimMachine
open private fieldsWord block chunkWord gadget hotVector scaleVector
  from Construction.PGS.Encoding

section Fields

variable [FieldCertificate]

theorem fieldsWord_natural
    (value : BaseField × Vector RowGamma digitCount) :
    byteBits (encodeOf fieldsWord value) =
      lsbs (8 * fieldsBytes) (packBaseCells fieldCellsCount (fieldsCell value)) := by
  unfold fieldsWord
  rw [encodeOf_map]
  unfold encodeOf
  rw [natural_byteBits]

theorem block_bits (value : Block) : byteBits (encodeOf block value) = lsbs 128 value.toNat :=
  natural_byteBits 16 _

theorem gadget_natural (value : Vector Exception.Entry digitCount) :
    byteBits (encodeOf gadget value) =
      lsbs (8 * gadgetBytes) (packBitsNat 3 gadgetCellsCount (gadgetCell value)) := by
  unfold gadget
  rw [encodeOf_map]
  unfold encodeOf
  rw [natural_byteBits]

/-- **The gadget word** reads as its `1092` three-bit cells, then four zero bits. -/
theorem gadget_bits (value : Vector Exception.Entry digitCount) :
    byteBits (encodeOf gadget value) =
      (List.ofFn fun index : Fin gadgetCellsCount => lsbs 3 (gadgetCell value index).toNat).flatten ++
        [false, false, false, false] := by
  have bound := packBitsNat_lt 3 gadgetCellsCount (gadgetCell value)
  have padding : lsbs 4 0 = [false, false, false, false] := by decide
  rw [gadget_natural, show 8 * gadgetBytes = 3 * gadgetCellsCount + 4 from rfl, lsbs_add,
    Nat.div_eq_of_lt bound, padding]
  refine congrArg (· ++ [false, false, false, false]) ?_
  exact digitSum_bits 3 gadgetCellsCount (fun index => (gadgetCell value index).toNat)
    (fun index => (gadgetCell value index).isLt)

theorem chunkWord_bits (value : BitVec chunkJoinBits) :
    byteBits (encodeOf chunkWord value) = lsbs (8 * chunkJoinBytes) value.toNat :=
  natural_byteBits chunkJoinBytes _

/-- **The bits of the wire encoding.** -/
theorem wire_bits (value : Public) :
    byteBits (encoding.encode value) =
      lsbs (8 * fieldsBytes) (packBaseCells fieldCellsCount (fieldsCell (value.curve, value.rows))) ++
      ((List.ofFn fun index : Fin gadgetCellsCount =>
          lsbs 3 (gadgetCell value.exception index).toNat).flatten ++
        [false, false, false, false]) ++
      (List.ofFn fun chunk : Fin foldStepCount => lsbs 128 value.curveXHot[chunk.val].toNat).flatten ++
      (List.ofFn fun chunk : Fin foldStepCount => lsbs 128 value.curveYHot[chunk.val].toNat).flatten ++
      (List.ofFn fun chunk : Fin foldStepCount => lsbs 128 value.pointXHot[chunk.val].toNat).flatten ++
      (List.ofFn fun chunk : Fin foldStepCount => lsbs 128 value.pointYHot[chunk.val].toNat).flatten ++
      (List.ofFn fun chunk : Fin chunkCount =>
          lsbs (8 * chunkJoinBytes) value.scale[chunk.val].toNat).flatten := by
  rw [encode_eq]
  unfold encoding
  rw [encodeOf_map, encodeOf_pair, encodeOf_pair, encodeOf_pair, encodeOf_pair, encodeOf_pair,
    encodeOf_pair]
  simp only [byteBits_append]
  rw [fieldsWord_natural]
  rw [gadget_bits]
  rw [show hotVector = block.vector foldStepCount from rfl, byteBits_vector, byteBits_vector,
    byteBits_vector, byteBits_vector]
  rw [show scaleVector = chunkWord.vector chunkCount from rfl, byteBits_vector]
  simp only [block_bits, chunkWord_bits, List.append_assoc]

end Fields

end Kriterion.ArgoMAC.PlanB.Wire
