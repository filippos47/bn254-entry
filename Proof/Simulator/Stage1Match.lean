/-
**The serialized RAM is the wire.**

`serial_wire`: the bits the serializer pushes, read from the RAM stage 1 stores, are the byte bits
of `Wire.encoding.encode` of the drawn source's public value. Both sides are regrouped by
`List.ofFn_add` / `List.ofFn_mul` into the same segments (curve and rows, gadget bytes, the four
fold-join vectors, the chunk words slot by slot) and compared cell by cell.
-/

import Proof.Simulator.Stage1Ram
import Proof.Simulator.Stage1Wire

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### Regrouping flattened lists -/

theorem flatten_ofFn_add {α : Type} {first second : Nat} (lists : Fin (first + second) → List α) :
    (List.ofFn lists).flatten =
      (List.ofFn fun index : Fin first => lists (index.castAdd second)).flatten ++
        (List.ofFn fun index : Fin second => lists (index.natAdd first)).flatten := by
  rw [List.ofFn_add, List.flatten_append]
  rfl

theorem flatten_ofFn_mul {α : Type} {outer inner : Nat} (lists : Fin (outer * inner) → List α) :
    (List.ofFn lists).flatten =
      (List.ofFn fun block : Fin outer => (List.ofFn fun index : Fin inner =>
        lists ⟨block.val * inner + index.val, by
          have blockSmall := block.isLt
          have indexSmall := index.isLt
          calc block.val * inner + index.val < (block.val + 1) * inner := by
                rw [Nat.add_mul, Nat.one_mul]; omega
            _ ≤ outer * inner := Nat.mul_le_mul_right _ blockSmall⟩).flatten).flatten := by
  rw [List.ofFn_mul, List.flatten_flatten, List.map_ofFn]
  rfl

/-- The emitted bits of a stored word. -/
theorem bitRun_ofNat (value width : Nat) (small : width ≤ 256) :
    bitRun (BitVec.ofNat 256 value) 0 width = lsbs width value := by
  unfold bitRun lsbs
  refine congrArg List.ofFn (funext fun index => ?_)
  rw [Nat.zero_add, BitVec.getLsbD_ofNat]
  have : index.val < 256 := lt_of_lt_of_le index.isLt small
  simp [this]

/-! ### Reading the drawn source -/

section Match

variable [FieldCertificate]

omit [FieldCertificate] in
theorem publicValue_rows (source : Stage1Source) : source.publicValue.rows = source.rows := rfl

theorem publicValue_exception (source : Stage1Source) :
    source.publicValue.exception = source.exception := rfl

theorem drawSource_row (draw : Stage1Draw) (digit : Fin digitCount) (field : Nat)
    (small : field < 10) :
    rowField (drawSource draw).rows[digit.val] field = total 0 draw.1 (3 + 10 * digit.val + field) := by
  simp only [drawSource, sourceOfDraws, Vector.getElem_ofFn]
  interval_cases field <;> rfl

/-- The stored field cell at a position, read as its drawn value. -/
theorem stored_field (memory : Memory) (draw : Stage1Draw) (index : Nat) (bound : index < fieldCellCount)
    (width : Nat) (small : width ≤ 256) :
    bitRun ((storedMemory memory draw).ram (word (fieldBase + index))) 0 width =
      lsbs width (total 0 draw.1 index).val := by
  rw [show fieldBase + index = fieldBase + (⟨index, bound⟩ : Fin fieldCellCount).val from rfl,
    ram_field, bitRun_ofNat _ _ small, total_apply _ _ _ bound]

theorem stored_byte (memory : Memory) (draw : Stage1Draw) (index : Nat)
    (bound : index < exceptionByteCount) :
    bitRun ((storedMemory memory draw).ram (word (exceptionBase + index))) 0 8 =
      lsbs 8 (BitVec.ofNat 8 (total 0 draw.2.1 index)).toNat := by
  rw [show exceptionBase + index =
      exceptionBase + (⟨index, bound⟩ : Fin exceptionByteCount).val from rfl,
    ram_byte, bitRun_ofNat _ _ (by norm_num), total_apply _ _ _ bound, BitVec.toNat_ofNat,
    lsbs_mod]

theorem stored_hot (memory : Memory) (draw : Stage1Draw) (index : Nat)
    (bound : index < hotBlockCount) :
    bitRun ((storedMemory memory draw).ram (word (hotBase + index))) 0 128 =
      lsbs 128 (BitVec.ofNat 128 (total 0 draw.2.2.1 index)).toNat := by
  rw [show hotBase + index = hotBase + (⟨index, bound⟩ : Fin hotBlockCount).val from rfl,
    ram_hot, bitRun_ofNat _ _ (by norm_num), total_apply _ _ _ bound, BitVec.toNat_ofNat,
    lsbs_mod]

/-! ### The four segments -/

/-- **Curve and rows.** -/
theorem serial_fields (memory : Memory) (draw : Stage1Draw) :
    (List.ofFn fun index : Fin (curveCellCount + rowCellCount) =>
        bitRun ((storedMemory memory draw).ram (word (fieldBase + index.val))) 0 256).flatten =
      (lsbs 256 (drawSource draw).publicValue.curve.1.val ++
        (lsbs 256 (drawSource draw).publicValue.curve.2.1.val ++
          lsbs 256 (drawSource draw).publicValue.curve.2.2.val)) ++
      (List.ofFn fun digit : Fin digitCount =>
        (List.ofFn fun index : Fin 10 =>
          lsbs 256 (rowField (drawSource draw).publicValue.rows[digit.val] index.val).val).flatten).flatten := by
  have cellCount := fieldCellCount_eq
  rw [flatten_ofFn_add]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · show (List.ofFn fun index : Fin 3 =>
        bitRun ((storedMemory memory draw).ram (word (fieldBase + index.val))) 0 256).flatten = _
    simp only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil,
      Fin.val_zero, Fin.val_succ]
    rw [show fieldBase + 0 = fieldBase + 0 from rfl, stored_field memory draw 0 (by omega) 256 le_rfl,
      stored_field memory draw (0 + 1) (by omega) 256 le_rfl,
      stored_field memory draw (0 + 1 + 1) (by omega) 256 le_rfl]
    rfl
  · show (List.ofFn fun index : Fin (digitCount * 10) =>
        bitRun ((storedMemory memory draw).ram (word (fieldBase + (3 + index.val)))) 0 256).flatten = _
    rw [flatten_ofFn_mul]
    refine congrArg List.flatten (congrArg List.ofFn (funext fun digit => ?_))
    refine congrArg List.flatten (congrArg List.ofFn (funext fun index => ?_))
    have digitSmall : digit.val < 91 := digit.isLt
    have indexSmall := index.isLt
    simp only [Fin.val_mk]
    rw [stored_field memory draw _ (by omega) 256 le_rfl, publicValue_rows,
      drawSource_row draw digit index.val indexSmall,
      show 3 + (digit.val * 10 + index.val) = 3 + 10 * digit.val + index.val by ring]

/-- **The gadget bytes.** -/
theorem serial_bytes (memory : Memory) (draw : Stage1Draw) :
    (List.ofFn fun index : Fin exceptionByteCount =>
        bitRun ((storedMemory memory draw).ram (word (exceptionBase + index.val))) 0 8).flatten =
      (List.ofFn fun digit : Fin digitCount =>
        (List.ofFn fun index : Fin 12 =>
          lsbs 8 (drawSource draw).publicValue.exception[digit.val][index.val].toNat).flatten).flatten := by
  show (List.ofFn fun index : Fin (digitCount * 12) =>
      bitRun ((storedMemory memory draw).ram (word (exceptionBase + index.val))) 0 8).flatten = _
  rw [flatten_ofFn_mul]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun digit => ?_))
  refine congrArg List.flatten (congrArg List.ofFn (funext fun index => ?_))
  have digitSmall : digit.val < 91 := digit.isLt
  have indexSmall := index.isLt
  simp only [Fin.val_mk]
  rw [stored_byte memory draw _ (by unfold exceptionByteCount; omega), publicValue_exception]
  simp only [drawSource, sourceOfDraws, Vector.getElem_ofFn]
  rw [show digit.val * 12 + index.val = 12 * digit.val + index.val by ring]

/-- **The fold joins.** -/
theorem serial_hot (memory : Memory) (draw : Stage1Draw) :
    (List.ofFn fun index : Fin hotBlockCount =>
        bitRun ((storedMemory memory draw).ram (word (hotBase + index.val))) 0 128).flatten =
      (List.ofFn fun chunk : Fin foldStepCount =>
          lsbs 128 (drawSource draw).publicValue.curveXHot[chunk.val].toNat).flatten ++
        ((List.ofFn fun chunk : Fin foldStepCount =>
          lsbs 128 (drawSource draw).publicValue.curveYHot[chunk.val].toNat).flatten ++
        ((List.ofFn fun chunk : Fin foldStepCount =>
          lsbs 128 (drawSource draw).publicValue.pointXHot[chunk.val].toNat).flatten ++
        (List.ofFn fun chunk : Fin foldStepCount =>
          lsbs 128 (drawSource draw).publicValue.pointYHot[chunk.val].toNat).flatten)) := by
  show (List.ofFn fun index : Fin (foldStepCount + (foldStepCount + (foldStepCount + foldStepCount))) =>
      bitRun ((storedMemory memory draw).ram (word (hotBase + index.val))) 0 128).flatten = _
  rw [flatten_ofFn_add, flatten_ofFn_add, flatten_ofFn_add]
  have lane : ∀ (offset : Nat) (small : offset ≤ 606) (vector : Vector Block foldStepCount)
      (position : Fin foldStepCount → Nat),
      (∀ chunk : Fin foldStepCount, position chunk = offset + chunk.val) →
      (∀ chunk : Fin foldStepCount,
        vector[chunk.val] = BitVec.ofNat 128 (total 0 draw.2.2.1 (offset + chunk.val))) →
      (List.ofFn fun chunk : Fin foldStepCount =>
          bitRun ((storedMemory memory draw).ram (word (hotBase + position chunk))) 0 128).flatten =
        (List.ofFn fun chunk : Fin foldStepCount => lsbs 128 vector[chunk.val].toNat).flatten := by
    intro offset small vector position located read
    refine congrArg List.flatten (congrArg List.ofFn (funext fun chunk => ?_))
    have chunkSmall : chunk.val < 202 := chunk.isLt
    rw [located chunk, stored_hot memory draw _ (by unfold hotBlockCount; omega), read chunk]
  refine congrArg₂ (· ++ ·) (lane 0 (by omega) _ _
      (fun chunk => by simp [Fin.castAdd, Fin.castLE]) (fun chunk => ?_))
    (congrArg₂ (· ++ ·) (lane 202 (by omega) _ _
      (fun chunk => by simp [Fin.castAdd, Fin.castLE, Fin.natAdd, foldStepCount])
      (fun chunk => ?_)) (congrArg₂ (· ++ ·) (lane 404 (by omega) _ _
        (fun chunk => by simp [Fin.castAdd, Fin.castLE, Fin.natAdd, foldStepCount]; omega)
        (fun chunk => ?_))
        (lane 606 (by omega) _ _
          (fun chunk => by simp [Fin.castAdd, Fin.castLE, Fin.natAdd, foldStepCount]; omega)
          (fun chunk => ?_))))
  all_goals
    simp only [drawSource, sourceOfDraws, Stage1Source.publicValue, Vector.getElem_ofFn, Nat.zero_add]

theorem publicValue_scale (source : Stage1Source) (chunk : Fin chunkCount) :
    source.publicValue.scale[chunk.val] = pack (source.joins chunk) := by
  simp [Stage1Source.publicValue]

/-- **The chunk words.** A chunk's first `641` cells are `254` bits each and its last cell is
`256` bits: a canonical cell is below `2 ^ 254`, so its two top bits are two of the word's four
zero padding bits, and the serializer pushes the other two. -/
theorem serial_scale (memory : Memory) (draw : Stage1Draw) :
    (List.ofFn fun chunk : Fin 52 => chunkWordBits (storedMemory memory draw).ram chunk.val).flatten =
      (List.ofFn fun chunk : Fin chunkCount =>
          lsbs (8 * chunkJoinBytes) (drawSource draw).publicValue.scale[chunk.val].toNat).flatten := by
  show (List.ofFn fun chunk : Fin chunkCount =>
      chunkWordBits (storedMemory memory draw).ram chunk.val).flatten = _
  refine congrArg List.flatten (congrArg List.ofFn (funext fun chunk => ?_))
  rw [publicValue_scale, pack_bits]
  have chunkSmall : chunk.val < 52 := chunk.isLt
  have cell : ∀ (slot : Nat) (slotSmall : slot < 642) (width : Nat), width ≤ 256 →
      bitRun ((storedMemory memory draw).ram (word (scaleCellBase + 642 * chunk.val + slot))) 0
          width = lsbs width ((drawSource draw).joins chunk ⟨slot, slotSmall⟩).val := by
    intro slot slotSmall width wide
    rw [show scaleCellBase + 642 * chunk.val + slot = fieldBase + (913 + 642 * chunk.val + slot) by
        unfold scaleCellBase curveCellCount rowCellCount; ring,
      stored_field memory draw _ (by unfold fieldCellCount curveCellCount rowCellCount scaleCellCount; omega)
        width wide]
    rfl
  show chunkWordBits _ chunk.val = (List.ofFn fun slot : Fin (641 + 1) =>
      lsbs coordinateBits ((drawSource draw).joins chunk slot).val).flatten ++
        [false, false, false, false]
  rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.append_assoc]
  unfold chunkWordBits
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine congrArg List.flatten (congrArg List.ofFn (funext fun index => ?_))
    have indexSmall : index.val < 642 := by omega
    rw [cell index.val indexSmall 254 (by norm_num)]
    rfl
  · have below : ((drawSource draw).joins chunk ⟨641, by decide⟩).val < 2 ^ 254 := val_lt_slot _
    have padding : lsbs 2 0 = [false, false] := by decide
    rw [cell 641 (by norm_num) 256 le_rfl, show (256 : Nat) = 254 + 2 from rfl, lsbs_add,
      Nat.div_eq_of_lt below, padding, List.append_assoc]
    rfl

/-- **The serialized RAM is the wire.** -/
theorem serial_wire (memory : Memory) (draw : Stage1Draw) :
    serialBits (storedMemory memory draw).ram =
      byteBits (Wire.encoding.encode (drawSource draw).publicValue) := by
  rw [Wire.wire_bits]
  unfold serialBits
  rw [serial_fields, serial_bytes, serial_hot, serial_scale]
  simp only [List.append_assoc]

end Match

end

end Kriterion.ArgoMAC.PlanB.SimMachine
