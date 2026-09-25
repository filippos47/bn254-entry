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
    rowField (drawSource draw).rows[digit.val] field = total 0 draw.1 (1 + 10 * digit.val + field) := by
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
    bitRun ((storedMemory memory draw).ram (word (exceptionBase + index))) 0 3 =
      lsbs 3 (BitVec.ofNat 3 (total 0 draw.2.1 index)).toNat := by
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

/-- The drawn source's cell `index` of the curve-and-rows word is its drawn field cell. -/
theorem fieldsCell_drawSource (draw : Stage1Draw) (index : Fin Wire.fieldCellsCount) :
    Wire.fieldsCell ((drawSource draw).publicValue.curve, (drawSource draw).publicValue.rows)
        index = total 0 draw.1 index.val := by
  have small := index.isLt
  unfold Wire.fieldCellsCount at small
  by_cases zero : index.val = 0
  · unfold Wire.fieldsCell
    rw [if_pos zero, zero]
    rfl
  unfold Wire.fieldsCell
  rw [if_neg zero]
  have digitSmall : (index.val - 1) / 10 < digitCount := by unfold digitCount; omega
  have fieldSmall : (index.val - 1) % 10 < 10 := Nat.mod_lt _ (by decide)
  have row := drawSource_row draw ⟨(index.val - 1) / 10, digitSmall⟩ ((index.val - 1) % 10)
    fieldSmall
  have cellEq : ∀ (row : RowGamma) (field : Nat), RowGamma.cell row field = rowField row field := by
    intro row field
    match field with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
    | 5 => rfl
    | 6 => rfl
    | 7 => rfl
    | 8 => rfl
    | _ + 9 => rfl
  have position : 1 + 10 * ((index.val - 1) / 10) + (index.val - 1) % 10 = index.val := by omega
  rw [position] at row
  rw [cellEq, publicValue_rows]
  exact row

/-- The limb scratch lies below every stored region, so stage 1's draws leave it as it was. -/
theorem storedMemory_limb (memory : Memory) (draw : Stage1Draw) (index : Nat)
    (bound : index < serialLimbCount) :
    (storedMemory memory draw).ram (word (serialLimbBase + index)) =
      memory.ram (word (serialLimbBase + index)) := by
  obtain ⟨fieldByte, byteHot, hotKey, top⟩ := regions
  have below : serialLimbBase + index < fieldBase := by
    unfold serialLimbCount at bound; unfold serialLimbBase fieldBase; omega
  unfold storedMemory
  rw [words_ram_off keyBase keyBlockCount top _ _ _ (by omega),
    words_ram_off hotBase hotBlockCount (by omega) _ _ _ (by omega),
    words_ram_off exceptionBase exceptionByteCount (by omega) _ _ _ (by omega)]
  exact foldStore_ram_off (cellStep fieldBase) (fun index => word (fieldBase + index))
    (fun value : BaseField => BitVec.ofNat 256 value.val) (cellStep_ram fieldBase) fieldCellCount
    memory draw.1 _ (region_away _ fieldBase fieldCellCount below (by omega))

/-- **The gadget bytes.** -/
theorem serial_bytes (memory : Memory) (draw : Stage1Draw)
    (zero : memory.ram (word serialLimbBase) = 0) :
    (List.ofFn fun index : Fin exceptionByteCount =>
        bitRun ((storedMemory memory draw).ram (word (exceptionBase + index.val))) 0 3).flatten ++
      bitRun ((storedMemory memory draw).ram (word serialLimbBase)) 0 4 =
      (List.ofFn fun index : Fin Wire.gadgetCellsCount =>
        lsbs 3 (Wire.gadgetCell (drawSource draw).publicValue.exception index).toNat).flatten ++
        [false, false, false, false] := by
  refine congrArg₂ (· ++ ·) ?_ ?_
  · show (List.ofFn fun index : Fin 1092 =>
        bitRun ((storedMemory memory draw).ram (word (exceptionBase + index.val))) 0 3).flatten =
      (List.ofFn fun index : Fin 1092 =>
        lsbs 3 (Wire.gadgetCell (drawSource draw).publicValue.exception index).toNat).flatten
    refine congrArg List.flatten (congrArg List.ofFn (funext fun index => ?_))
    have indexSmall := index.isLt
    rw [stored_byte memory draw _ (by unfold exceptionByteCount; omega), publicValue_exception]
    unfold Wire.gadgetCell
    simp only [drawSource, sourceOfDraws, Vector.get_eq_getElem, Vector.getElem_ofFn]
    rw [show 12 * (index.val / 12) + index.val % 12 = index.val by omega]
  · rw [show serialLimbBase = serialLimbBase + 0 from rfl, storedMemory_limb memory draw 0
      (by decide), Nat.add_zero, zero]
    decide

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

/-- A stored field cell, as a number. -/
theorem stored_field_toNat (memory : Memory) (draw : Stage1Draw) (index : Nat)
    (bound : index < fieldCellCount) :
    ((storedMemory memory draw).ram (word (fieldBase + index))).toNat =
      (total 0 draw.1 index).val := by
  rw [show fieldBase + index = fieldBase + (⟨index, bound⟩ : Fin fieldCellCount).val from rfl,
    ram_field, total_apply _ _ _ bound, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le (val_lt_slot _)
    (Nat.pow_le_pow_right (by norm_num) (by unfold coordinateBits; norm_num))

/-- **Curve and rows.** The curve-and-rows word is the base-`p` number of the `911` stored
cells, emitted limb by limb (`fieldsLimbBits`); the wire's word is the same number. -/
theorem serial_fields (memory : Memory) (draw : Stage1Draw) :
    fieldsLimbBits (fieldsWordValue (storedMemory memory draw).ram) =
      lsbs (8 * Wire.fieldsBytes) (packBaseCells Wire.fieldCellsCount
        (Wire.fieldsCell ((drawSource draw).publicValue.curve,
          (drawSource draw).publicValue.rows))) := by
  rw [lsbs_fieldsLimbBits]
  refine congrArg fieldsLimbBits ?_
  unfold fieldsWordValue BigInt.encNat packBaseCells
  rw [← Fin.sum_univ_eq_sum_range
    (fun e => ((storedMemory memory draw).ram (word (fieldBase + e))).toNat * pNat ^ e)
    (curveCellCount + rowCellCount)]
  show (∑ e : Fin Wire.fieldCellsCount,
      ((storedMemory memory draw).ram (word (fieldBase + e.val))).toNat * pNat ^ e.val) = _
  refine Finset.sum_congr rfl fun slot _ => ?_
  have small := slot.isLt
  unfold Wire.fieldCellsCount at small
  rw [stored_field_toNat memory draw slot.val (by rw [fieldCellCount_eq]; omega),
    fieldsCell_drawSource draw slot]
  rfl

/-- **The chunk words.** Each chunk word is the base-`p` number of its `642` cells, emitted limb
by limb (`chunkWordBits`); the wire's word is the same number (`pack_toNat`,
`lsbs_chunkLimbBits`). -/
theorem serial_scale (memory : Memory) (draw : Stage1Draw) :
    (List.ofFn fun chunk : Fin 52 => chunkWordBits (storedMemory memory draw).ram chunk.val).flatten =
      (List.ofFn fun chunk : Fin chunkCount =>
          lsbs (8 * chunkJoinBytes) (drawSource draw).publicValue.scale[chunk.val].toNat).flatten := by
  show (List.ofFn fun chunk : Fin chunkCount =>
      chunkWordBits (storedMemory memory draw).ram chunk.val).flatten = _
  refine congrArg List.flatten (congrArg List.ofFn (funext fun chunk => ?_))
  rw [publicValue_scale, pack_toNat, lsbs_chunkLimbBits, chunkWordBits]
  refine congrArg chunkLimbBits ?_
  have chunkSmall : chunk.val < 52 := chunk.isLt
  unfold chunkWordValue BigInt.encNat packWord
  rw [← Fin.sum_univ_eq_sum_range
    (fun e => ((storedMemory memory draw).ram (word (scaleCellBase + 642 * chunk.val + e))).toNat *
      pNat ^ e) 642]
  refine Finset.sum_congr rfl fun slot _ => ?_
  have slotSmall : slot.val < 642 := slot.isLt
  rw [show scaleCellBase + 642 * chunk.val + slot.val = fieldBase + (911 + 642 * chunk.val + slot.val) by
      unfold scaleCellBase curveCellCount rowCellCount; ring,
    stored_field_toNat memory draw _
      (by unfold fieldCellCount curveCellCount rowCellCount scaleCellCount; omega)]
  rfl

/-- **The serialized RAM is the wire.** -/
theorem serial_wire (memory : Memory) (draw : Stage1Draw)
    (zero : memory.ram (word serialLimbBase) = 0) :
    serialBits (storedMemory memory draw).ram =
      byteBits (Wire.encoding.encode (drawSource draw).publicValue) := by
  rw [Wire.wire_bits]
  unfold serialBits
  rw [serial_fields, serial_bytes memory draw zero, serial_hot, serial_scale]
  simp only [List.append_assoc]

end Match

end

end Kriterion.ArgoMAC.PlanB.SimMachine
