/-
**The machine's stage-1 source law against the uniform source.**

The machine's draws are `34,297` field cells (bounded rejection), `1,092` bytes, `808` fold-join
blocks and the `1016`-block key (fair coins). `sourceOfDraws` reads them as a `Stage1Source`, and
this reading is a bijection from the exact draws (`drawsEquiv`), so exact draws give the uniform
source (`idealSource_eq`). The field cells are the only cut-off draws: `source_close`.
-/

import Proof.Simulator.CutoffSamplers

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

section Source

variable [FieldCertificate]

/-- The exact draws: field elements, bytes, blocks, key blocks. -/
abbrev Draws := (Fin fieldCellCount → BaseField) × (Fin exceptionByteCount → Fin (2 ^ 8)) ×
  (Fin hotBlockCount → Fin (2 ^ 128)) × (Fin keyBlockCount → Fin (2 ^ 128))

/-- The source of exact draws. -/
def sourceOf (draws : Draws) : Stage1Source :=
  sourceOfDraws (total 0 draws.1) (total 0 fun index => (draws.2.1 index).val)
    (total 0 fun index => (draws.2.2.1 index).val) (total 0 fun index => (draws.2.2.2 index).val)

/-- Field `k` of a row, in the machine's cell order. -/
def rowField (row : RowGamma) : Nat → BaseField
  | 0 => row.xC0
  | 1 => row.xC1
  | 2 => row.xC2
  | 3 => row.xC4
  | 4 => row.yC0
  | 5 => row.yC2
  | 6 => row.yC4
  | 7 => row.yC5
  | 8 => row.zC0
  | _ => row.zC1

theorem digit_lt (index : Nat) (above : 3 ≤ index) (below : index < 913) :
    (index - 3) / 10 < digitCount := by
  unfold digitCount
  omega

theorem chunk_lt (index : Nat) (below : index < fieldCellCount) :
    (index - 913) / 642 < chunkCount := by
  unfold chunkCount
  rw [fieldCellCount_eq] at below
  omega

theorem slot_lt (index : Nat) : (index - 913) % 642 < elementCount := by
  unfold elementCount
  omega

/-- The field cells of a source, in the machine's order. -/
def cellsOf (source : Stage1Source) (index : Fin fieldCellCount) : BaseField :=
  if small : index.val < 3 then
    (if index.val = 0 then source.curve.1 else if index.val = 1 then source.curve.2.1
      else source.curve.2.2)
  else if below : index.val < 913 then
    rowField (source.rows.get ⟨(index.val - 3) / 10, digit_lt index.val (by omega) below⟩)
      ((index.val - 3) % 10)
  else source.joins ⟨(index.val - 913) / 642, chunk_lt index.val index.isLt⟩
    ⟨(index.val - 913) % 642, slot_lt index.val⟩

theorem byteDigit_lt (index : Fin exceptionByteCount) : index.val / 12 < digitCount := by
  have := index.isLt
  unfold exceptionByteCount at this
  unfold digitCount
  omega

/-- The bytes of a source. -/
def bytesOf (source : Stage1Source) (index : Fin exceptionByteCount) : Fin (2 ^ 8) :=
  ((source.exception.get ⟨index.val / 12, byteDigit_lt index⟩).get
    ⟨index.val % 12, Nat.mod_lt _ (by norm_num)⟩).toFin

theorem hotChunk_lt (index : Nat) (offset : Nat) (above : offset ≤ index)
    (below : index < offset + 202) : index - offset < foldStepCount := by
  unfold foldStepCount
  omega

theorem hotIndex_lt (index : Fin hotBlockCount) : index.val < 606 + 202 := by
  have := index.isLt
  unfold hotBlockCount at this
  omega

/-- The fold-join blocks of a source. -/
def hotOf (source : Stage1Source) (index : Fin hotBlockCount) : Fin (2 ^ 128) :=
  if first : index.val < 202 then
    (source.curveXHot.get ⟨index.val - 0, hotChunk_lt index.val 0 (by omega) (by omega)⟩).toFin
  else if second : index.val < 404 then
    (source.curveYHot.get ⟨index.val - 202, hotChunk_lt index.val 202 (by omega) (by omega)⟩).toFin
  else if third : index.val < 606 then
    (source.pointXHot.get ⟨index.val - 404, hotChunk_lt index.val 404 (by omega) (by omega)⟩).toFin
  else
    (source.pointYHot.get ⟨index.val - 606,
      hotChunk_lt index.val 606 (by omega) (hotIndex_lt index)⟩).toFin

/-- A label of a key pair. -/
def labelOf (key : BitAdaptor.Key) (half : Nat) : Block :=
  if half = 0 then key.falseLabel else key.trueLabel

theorem keyY_lt (index : Fin keyBlockCount) : index.val / 2 - 254 < coordinateBitCount := by
  have := index.isLt
  unfold keyBlockCount at this
  show _ < 254
  omega

/-- The key blocks of a source. -/
def keyOf (source : Stage1Source) (index : Fin keyBlockCount) : Fin (2 ^ 128) :=
  if first : index.val / 2 < 254 then
    (labelOf (source.key.x.get ⟨index.val / 2, first⟩) (index.val % 2)).toFin
  else
    (labelOf (source.key.y.get ⟨index.val / 2 - 254, keyY_lt index⟩) (index.val % 2)).toFin

/-- The exact draws of a source. -/
def drawsOf (source : Stage1Source) : Draws :=
  (cellsOf source, bytesOf source, hotOf source, keyOf source)

theorem total_apply {count : Nat} {α : Type} (zero : α) (family : Fin count → α) (index : Nat)
    (inside : index < count) : total zero family index = family ⟨index, inside⟩ := by
  simp [total, inside]

/-! ### The cells of a source, by position -/

theorem cell_lt (index : Nat) (below : index < 34297) : index < fieldCellCount := by
  rw [fieldCellCount_eq]
  exact below

theorem cellsOf_curve0 (source : Stage1Source) :
    total 0 (cellsOf source) 0 = source.curve.1 := by
  rw [total_apply _ _ _ (cell_lt 0 (by omega))]
  simp [cellsOf]

theorem cellsOf_curve1 (source : Stage1Source) :
    total 0 (cellsOf source) 1 = source.curve.2.1 := by
  rw [total_apply _ _ _ (cell_lt 1 (by omega))]
  simp [cellsOf]

theorem cellsOf_curve2 (source : Stage1Source) :
    total 0 (cellsOf source) 2 = source.curve.2.2 := by
  rw [total_apply _ _ _ (cell_lt 2 (by omega))]
  simp [cellsOf]

theorem cellsOf_row (source : Stage1Source) (digit : Fin digitCount) (field : Nat)
    (small : field < 10) :
    total 0 (cellsOf source) (3 + 10 * digit.val + field) =
      rowField (source.rows.get digit) field := by
  have digitSmall : digit.val < 91 := digit.isLt
  rw [total_apply _ _ _ (cell_lt _ (by omega))]
  unfold cellsOf
  rw [dif_neg (by simp only; omega), dif_pos (by simp only; omega)]
  simp only [show (3 + 10 * digit.val + field - 3) / 10 = digit.val by omega,
    show (3 + 10 * digit.val + field - 3) % 10 = field by omega, Fin.eta]

theorem cellsOf_join (source : Stage1Source) (chunk : Fin chunkCount) (slot : Fin elementCount) :
    total 0 (cellsOf source) (913 + 642 * chunk.val + slot.val) = source.joins chunk slot := by
  have chunkSmall : chunk.val < 52 := chunk.isLt
  have slotSmall : slot.val < 642 := slot.isLt
  rw [total_apply _ _ _ (cell_lt _ (by omega))]
  unfold cellsOf
  rw [dif_neg (by simp only; omega), dif_neg (by simp only; omega)]
  have first : (913 + 642 * chunk.val + slot.val - 913) / 642 = chunk.val := by omega
  have second : (913 + 642 * chunk.val + slot.val - 913) % 642 = slot.val := by omega
  exact congrArg₂ source.joins (Fin.ext first) (Fin.ext second)

/-! ### The bytes, blocks and key of a source, by position -/

theorem bitVec_ofNat_toNat {width : Nat} (value : BitVec width) :
    BitVec.ofNat width value.toNat = value := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt value.isLt]

theorem bytesOf_at (source : Stage1Source) (digit : Fin digitCount) (slot : Fin 12) :
    total 0 (fun index => (bytesOf source index).val) (12 * digit.val + slot.val) =
      ((source.exception.get digit).get slot).toNat := by
  have digitSmall : digit.val < 91 := digit.isLt
  have slotSmall : slot.val < 12 := slot.isLt
  rw [total_apply _ _ _ (by unfold exceptionByteCount; omega)]
  unfold bytesOf
  have first : (12 * digit.val + slot.val) / 12 = digit.val := by omega
  have second : (12 * digit.val + slot.val) % 12 = slot.val := by omega
  simp only [BitVec.val_toFin]
  exact congrArg BitVec.toNat (congrArg₂ (fun (d : Fin digitCount) (e : Fin 12) =>
    (source.exception.get d).get e) (Fin.ext first) (Fin.ext second))

theorem hot_lt (offset : Nat) (chunk : Fin foldStepCount) (small : offset ≤ 606) :
    offset + chunk.val < hotBlockCount := by
  have := chunk.isLt
  unfold foldStepCount at this
  unfold hotBlockCount
  omega

theorem hotOf_curveX (source : Stage1Source) (chunk : Fin foldStepCount) :
    total 0 (fun index => (hotOf source index).val) chunk.val = (source.curveXHot.get chunk).toNat := by
  have small : chunk.val < 202 := chunk.isLt
  rw [total_apply _ _ _ (by simpa using hot_lt 0 chunk (by omega))]
  unfold hotOf
  rw [dif_pos (by simp only; omega)]
  simp only [BitVec.val_toFin, Nat.sub_zero]

theorem hotOf_curveY (source : Stage1Source) (chunk : Fin foldStepCount) :
    total 0 (fun index => (hotOf source index).val) (202 + chunk.val) =
      (source.curveYHot.get chunk).toNat := by
  have small : chunk.val < 202 := chunk.isLt
  rw [total_apply _ _ _ (hot_lt 202 chunk (by omega))]
  unfold hotOf
  rw [dif_neg (by simp only; omega), dif_pos (by simp only; omega)]
  have index : 202 + chunk.val - 202 = chunk.val := by omega
  simp only [BitVec.val_toFin]
  exact congrArg (fun (c : Fin foldStepCount) => (source.curveYHot.get c).toNat) (Fin.ext index)

theorem hotOf_pointX (source : Stage1Source) (chunk : Fin foldStepCount) :
    total 0 (fun index => (hotOf source index).val) (404 + chunk.val) =
      (source.pointXHot.get chunk).toNat := by
  have small : chunk.val < 202 := chunk.isLt
  rw [total_apply _ _ _ (hot_lt 404 chunk (by omega))]
  unfold hotOf
  rw [dif_neg (by simp only; omega), dif_neg (by simp only; omega), dif_pos (by simp only; omega)]
  have index : 404 + chunk.val - 404 = chunk.val := by omega
  simp only [BitVec.val_toFin]
  exact congrArg (fun (c : Fin foldStepCount) => (source.pointXHot.get c).toNat) (Fin.ext index)

theorem hotOf_pointY (source : Stage1Source) (chunk : Fin foldStepCount) :
    total 0 (fun index => (hotOf source index).val) (606 + chunk.val) =
      (source.pointYHot.get chunk).toNat := by
  have small : chunk.val < 202 := chunk.isLt
  rw [total_apply _ _ _ (hot_lt 606 chunk (by omega))]
  unfold hotOf
  rw [dif_neg (by simp only; omega), dif_neg (by simp only; omega), dif_neg (by simp only; omega)]
  have index : 606 + chunk.val - 606 = chunk.val := by omega
  simp only [BitVec.val_toFin]
  exact congrArg (fun (c : Fin foldStepCount) => (source.pointYHot.get c).toNat) (Fin.ext index)

theorem key_lt (bit : Nat) (half : Nat) (small : bit < 508) (halfSmall : half < 2) :
    2 * bit + half < keyBlockCount := by
  unfold keyBlockCount
  omega

theorem keyOf_x (source : Stage1Source) (bit : Fin coordinateBitCount) (half : Nat)
    (halfSmall : half < 2) :
    total 0 (fun index => (keyOf source index).val) (2 * bit.val + half) =
      (labelOf (source.key.x.get bit) half).toNat := by
  have small : bit.val < 254 := bit.isLt
  rw [total_apply _ _ _ (key_lt _ _ (by omega) halfSmall)]
  unfold keyOf
  rw [dif_pos (by simp only; omega)]
  have first : (2 * bit.val + half) / 2 = bit.val := by omega
  have second : (2 * bit.val + half) % 2 = half := by omega
  simp only [BitVec.val_toFin]
  exact congrArg BitVec.toNat (congrArg₂ (fun (b : Fin coordinateBitCount) (h : Nat) =>
    labelOf (source.key.x.get b) h) (Fin.ext first) second)

theorem keyOf_y (source : Stage1Source) (bit : Fin coordinateBitCount) (half : Nat)
    (halfSmall : half < 2) :
    total 0 (fun index => (keyOf source index).val) (2 * (254 + bit.val) + half) =
      (labelOf (source.key.y.get bit) half).toNat := by
  have small : bit.val < 254 := bit.isLt
  rw [total_apply _ _ _ (key_lt _ _ (by omega) halfSmall)]
  unfold keyOf
  rw [dif_neg (by simp only; omega)]
  have first : (2 * (254 + bit.val) + half) / 2 - 254 = bit.val := by omega
  have second : (2 * (254 + bit.val) + half) % 2 = half := by omega
  simp only [BitVec.val_toFin]
  exact congrArg BitVec.toNat (congrArg₂ (fun (b : Fin coordinateBitCount) (h : Nat) =>
    labelOf (source.key.y.get b) h) (Fin.ext first) second)

theorem stage1Source_ext {first second : Stage1Source} (curve : first.curve = second.curve)
    (rows : first.rows = second.rows) (exception : first.exception = second.exception)
    (curveXHot : first.curveXHot = second.curveXHot) (curveYHot : first.curveYHot = second.curveYHot)
    (pointXHot : first.pointXHot = second.pointXHot) (pointYHot : first.pointYHot = second.pointYHot)
    (joins : first.joins = second.joins) (key : first.key = second.key) : first = second := by
  cases first
  cases second
  simp_all

theorem inputMacKey_ext {first second : InputMacKey} (x : first.x = second.x)
    (y : first.y = second.y) : first = second := by
  cases first
  cases second
  simp_all

theorem bitAdaptorKey_ext {first second : BitAdaptor.Key}
    (falseLabel : first.falseLabel = second.falseLabel)
    (trueLabel : first.trueLabel = second.trueLabel) : first = second := by
  cases first
  cases second
  simp_all

theorem rowGamma_eq (row : RowGamma) :
    (⟨rowField row 0, rowField row 1, rowField row 2, rowField row 3, rowField row 4,
      rowField row 5, rowField row 6, rowField row 7, rowField row 8, rowField row 9⟩ :
      RowGamma) = row := by
  cases row
  rfl

/-- **The reading is onto**: every source is the reading of its draws. -/
theorem sourceOf_drawsOf (source : Stage1Source) : sourceOf (drawsOf source) = source := by
  apply stage1Source_ext
  · show (total 0 (cellsOf source) 0, total 0 (cellsOf source) 1, total 0 (cellsOf source) 2) = _
    rw [cellsOf_curve0, cellsOf_curve1, cellsOf_curve2]
  · apply Vector.ext
    intro digit bound
    simp only [sourceOf, sourceOfDraws, drawsOf, Vector.getElem_ofFn]
    have row := cellsOf_row source ⟨digit, bound⟩
    have row0 := row 0 (by omega)
    simp only [Nat.add_zero] at row0
    rw [row0, row 1 (by omega), row 2 (by omega), row 3 (by omega), row 4 (by omega),
      row 5 (by omega), row 6 (by omega), row 7 (by omega), row 8 (by omega), row 9 (by omega),
      rowGamma_eq]
    simp only [Vector.get_eq_getElem]
  · apply Vector.ext
    intro digit bound
    apply Vector.ext
    intro slot slotBound
    simp only [sourceOf, sourceOfDraws, drawsOf, Vector.getElem_ofFn]
    rw [bytesOf_at source ⟨digit, bound⟩ ⟨slot, slotBound⟩, bitVec_ofNat_toNat]
    simp only [Vector.get_eq_getElem]
  · apply Vector.ext
    intro chunk bound
    simp only [sourceOf, sourceOfDraws, drawsOf, Vector.getElem_ofFn]
    rw [hotOf_curveX source ⟨chunk, bound⟩, bitVec_ofNat_toNat]
    simp only [Vector.get_eq_getElem]
  · apply Vector.ext
    intro chunk bound
    simp only [sourceOf, sourceOfDraws, drawsOf, Vector.getElem_ofFn]
    rw [hotOf_curveY source ⟨chunk, bound⟩, bitVec_ofNat_toNat]
    simp only [Vector.get_eq_getElem]
  · apply Vector.ext
    intro chunk bound
    simp only [sourceOf, sourceOfDraws, drawsOf, Vector.getElem_ofFn]
    rw [hotOf_pointX source ⟨chunk, bound⟩, bitVec_ofNat_toNat]
    simp only [Vector.get_eq_getElem]
  · apply Vector.ext
    intro chunk bound
    simp only [sourceOf, sourceOfDraws, drawsOf, Vector.getElem_ofFn]
    rw [hotOf_pointY source ⟨chunk, bound⟩, bitVec_ofNat_toNat]
    simp only [Vector.get_eq_getElem]
  · funext chunk slot
    exact cellsOf_join source chunk slot
  · apply inputMacKey_ext
    · apply Vector.ext
      intro bit bound
      simp only [sourceOf, sourceOfDraws, drawsOf, Vector.getElem_ofFn]
      have falseAt := keyOf_x source ⟨bit, bound⟩ 0 (by omega)
      have trueAt := keyOf_x source ⟨bit, bound⟩ 1 (by omega)
      simp only [Nat.add_zero] at falseAt
      rw [falseAt, trueAt, bitVec_ofNat_toNat, bitVec_ofNat_toNat]
      apply bitAdaptorKey_ext <;> simp [labelOf, Vector.get_eq_getElem]
    · apply Vector.ext
      intro bit bound
      simp only [sourceOf, sourceOfDraws, drawsOf, Vector.getElem_ofFn]
      have falseAt := keyOf_y source ⟨bit, bound⟩ 0 (by omega)
      have trueAt := keyOf_y source ⟨bit, bound⟩ 1 (by omega)
      simp only [Nat.add_zero] at falseAt
      rw [falseAt, trueAt, bitVec_ofNat_toNat, bitVec_ofNat_toNat]
      apply bitAdaptorKey_ext <;> simp [labelOf, Vector.get_eq_getElem]

/-! ### The reading is one-to-one -/

theorem cellsOf_sourceOf (draws : Draws) (index : Fin fieldCellCount) :
    cellsOf (sourceOf draws) index = draws.1 index := by
  have indexSmall : index.val < 34297 := lt_of_lt_of_eq index.isLt fieldCellCount_eq
  unfold cellsOf
  by_cases small : index.val < 3
  · rw [dif_pos small]
    simp only [sourceOf, sourceOfDraws]
    by_cases zero : index.val = 0
    · rw [if_pos zero, total_apply _ _ _ (cell_lt 0 (by omega))]
      exact congrArg draws.1 (Fin.ext zero.symm)
    · by_cases one : index.val = 1
      · rw [if_neg zero, if_pos one, total_apply _ _ _ (cell_lt 1 (by omega))]
        exact congrArg draws.1 (Fin.ext one.symm)
      · rw [if_neg zero, if_neg one, total_apply _ _ _ (cell_lt 2 (by omega))]
        exact congrArg draws.1 (Fin.ext (by simp only; omega))
  · rw [dif_neg small]
    by_cases below : index.val < 913
    · rw [dif_pos below]
      have remainder : (index.val - 3) % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have position : 3 + 10 * ((index.val - 3) / 10) + (index.val - 3) % 10 = index.val := by
        omega
      have read : ∀ field, field < 10 →
          rowField ((sourceOf draws).rows.get ⟨(index.val - 3) / 10,
            digit_lt index.val (by omega) below⟩) field =
          total 0 draws.1 (3 + 10 * ((index.val - 3) / 10) + field) := by
        intro field fieldSmall
        simp only [sourceOf, sourceOfDraws, Vector.get_ofFn]
        interval_cases field <;> rfl
      rw [read _ remainder, total_apply _ _ _ (cell_lt _ (by omega))]
      exact congrArg draws.1 (Fin.ext position)
    · rw [dif_neg below]
      have position : 913 + 642 * ((index.val - 913) / 642) + (index.val - 913) % 642 =
          index.val := by omega
      simp only [sourceOf, sourceOfDraws]
      rw [total_apply _ _ _ (cell_lt _ (by omega))]
      exact congrArg draws.1 (Fin.ext position)

theorem bytesOf_sourceOf (draws : Draws) (index : Fin exceptionByteCount) :
    bytesOf (sourceOf draws) index = draws.2.1 index := by
  have indexSmall : index.val < 1092 := index.isLt
  unfold bytesOf
  simp only [sourceOf, sourceOfDraws, Vector.get_ofFn]
  have position : 12 * (index.val / 12) + index.val % 12 = index.val := by omega
  rw [total_apply _ _ _ (by unfold exceptionByteCount; omega)]
  apply Fin.ext
  simp only [BitVec.toFin_ofNat, Fin.val_ofNat]
  rw [Nat.mod_eq_of_lt (draws.2.1 _).isLt]
  exact congrArg (fun position : Fin exceptionByteCount => (draws.2.1 position).val)
    (Fin.ext position)

theorem blockFin_ofNat (value : Fin (2 ^ 128)) : (BitVec.ofNat 128 value.val).toFin = value := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt value.isLt]

theorem hotOf_sourceOf (draws : Draws) (index : Fin hotBlockCount) :
    hotOf (sourceOf draws) index = draws.2.2.1 index := by
  have indexSmall : index.val < 808 := index.isLt
  unfold hotOf
  simp only [sourceOf, sourceOfDraws, Vector.get_ofFn]
  by_cases first : index.val < 202
  · rw [dif_pos first, total_apply _ _ _ (by unfold hotBlockCount; omega), blockFin_ofNat]
    exact congrArg draws.2.2.1 (Fin.ext (by simp only; omega))
  · rw [dif_neg first]
    by_cases second : index.val < 404
    · rw [dif_pos second, total_apply _ _ _ (by unfold hotBlockCount; omega), blockFin_ofNat]
      exact congrArg draws.2.2.1 (Fin.ext (by simp only; omega))
    · rw [dif_neg second]
      by_cases third : index.val < 606
      · rw [dif_pos third, total_apply _ _ _ (by unfold hotBlockCount; omega), blockFin_ofNat]
        exact congrArg draws.2.2.1 (Fin.ext (by simp only; omega))
      · rw [dif_neg third, total_apply _ _ _ (by unfold hotBlockCount; omega), blockFin_ofNat]
        exact congrArg draws.2.2.1 (Fin.ext (by simp only; omega))

theorem keyOf_sourceOf (draws : Draws) (index : Fin keyBlockCount) :
    keyOf (sourceOf draws) index = draws.2.2.2 index := by
  have indexSmall : index.val < 1016 := index.isLt
  have parity : index.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
  unfold keyOf
  simp only [sourceOf, sourceOfDraws, Vector.get_ofFn]
  by_cases first : index.val / 2 < 254
  · rw [dif_pos first]
    by_cases even : index.val % 2 = 0
    · simp only [labelOf, if_pos even]
      rw [total_apply _ _ _ (by unfold keyBlockCount; omega), blockFin_ofNat]
      exact congrArg draws.2.2.2 (Fin.ext (by simp only; omega))
    · simp only [labelOf, if_neg even]
      rw [total_apply _ _ _ (by unfold keyBlockCount; omega), blockFin_ofNat]
      exact congrArg draws.2.2.2 (Fin.ext (by simp only; omega))
  · rw [dif_neg first]
    by_cases even : index.val % 2 = 0
    · simp only [labelOf, if_pos even]
      rw [total_apply _ _ _ (by unfold keyBlockCount; omega), blockFin_ofNat]
      exact congrArg draws.2.2.2 (Fin.ext (by simp only; omega))
    · simp only [labelOf, if_neg even]
      rw [total_apply _ _ _ (by unfold keyBlockCount; omega), blockFin_ofNat]
      exact congrArg draws.2.2.2 (Fin.ext (by simp only; omega))

/-- **The reading of exact draws is a bijection onto the sources.** -/
def drawsEquiv : Draws ≃ Stage1Source where
  toFun := sourceOf
  invFun := drawsOf
  left_inv draws := by
    unfold drawsOf
    rcases draws with ⟨cells, bytes, hot, key⟩
    simp only [Prod.mk.injEq]
    refine ⟨funext fun index => cellsOf_sourceOf _ index, funext fun index =>
      bytesOf_sourceOf _ index, funext fun index => hotOf_sourceOf _ index,
      funext fun index => keyOf_sourceOf _ index⟩
  right_inv := sourceOf_drawsOf

/-! ### The draws -/

/-- The exact field cell. -/
def idealCell : PMF (Option BaseField) := (PMF.uniformOfFintype BaseField).map some

/-- The stage-1 draws with a given field-cell law. -/
def drawsWith (cell : PMF (Option BaseField)) : PMF (Option ((Fin fieldCellCount → BaseField) ×
    (Fin exceptionByteCount → Nat) × (Fin hotBlockCount → Nat) × (Fin keyBlockCount → Nat))) :=
  (optionProduct fieldCellCount fun _ => cell).bind fun cells => match cells with
    | none => PMF.pure none
    | some cells =>
      (optionProduct exceptionByteCount fun _ => (wordLaw 8).map some).bind fun bytes =>
      (optionProduct hotBlockCount fun _ => (wordLaw 128).map some).bind fun hot =>
      (optionProduct keyBlockCount fun _ => (wordLaw 128).map some).map fun key =>
        match bytes, hot, key with
        | some bytes, some hot, some key => some (cells, bytes, hot, key)
        | _, _, _ => none

/-- The word draws of the machine, as uniform `Fin` draws. -/
theorem wordProduct_eq (count width : Nat) :
    optionProduct count (fun _ => (wordLaw width).map some) =
      (PMF.uniformOfFintype (Fin count → Fin (2 ^ width))).map
        fun words => some fun index => (words index).val := by
  have single : (wordLaw width).map some =
      ((PMF.uniformOfFintype (Fin (2 ^ width))).map some).map (Option.map Fin.val) := by
    unfold wordLaw
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  have : Nonempty (Fin (2 ^ width)) := ⟨⟨0, Nat.two_pow_pos width⟩⟩
  simp only [single]
  rw [optionProduct_map, optionProduct_uniform, PMF.map_comp]
  rfl

/-- The reading of exact draws into the machine's `Nat`-valued draws. -/
def drawsNat (draws : Draws) : (Fin fieldCellCount → BaseField) × (Fin exceptionByteCount → Nat) ×
    (Fin hotBlockCount → Nat) × (Fin keyBlockCount → Nat) :=
  (draws.1, fun index => (draws.2.1 index).val, fun index => (draws.2.2.1 index).val,
    fun index => (draws.2.2.2 index).val)

/-- **Exact draws are uniform.** -/
theorem idealDraws_eq : drawsWith idealCell = (PMF.uniformOfFintype Draws).map
    fun draws => some (drawsNat draws) := by
  have : Nonempty (Fin (2 ^ 8)) := ⟨⟨0, by norm_num⟩⟩
  have : Nonempty (Fin (2 ^ 128)) := ⟨⟨0, by norm_num⟩⟩
  unfold drawsWith idealCell
  rw [optionProduct_uniform, wordProduct_eq, wordProduct_eq, wordProduct_eq]
  rw [← uniform_product (A := Fin fieldCellCount → BaseField),
    ← uniform_product (A := Fin exceptionByteCount → Fin (2 ^ 8)),
    ← uniform_product (A := Fin hotBlockCount → Fin (2 ^ 128))]
  simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp]
  rfl

/-- The machine's source law with exact cells is the uniform source. -/
theorem idealSource_eq : (drawsWith idealCell).map (Option.map fun draws =>
    sourceOfDraws (total 0 draws.1) (total 0 draws.2.1) (total 0 draws.2.2.1)
      (total 0 draws.2.2.2)) = (PMF.uniformOfFintype Stage1Source).map some := by
  have : Nonempty (Fin (2 ^ 8)) := ⟨⟨0, by norm_num⟩⟩
  have : Nonempty (Fin (2 ^ 128)) := ⟨⟨0, by norm_num⟩⟩
  rw [idealDraws_eq, PMF.map_comp, ← uniform_equiv drawsEquiv, PMF.map_comp]
  rfl

/-- **The machine's source law is abort-close to the uniform source.** -/
theorem source_close :
    AbortClose (fieldCellCount * rejectLaw fieldWidth (fun value => decide (value < pNat))
      attempts none + 0) sourceLaw ((PMF.uniformOfFintype Stage1Source).map some) := by
  have cells := AbortClose.optionProduct fieldCellCount (fun _ => fieldCellLaw)
    (fun _ => idealCell) (fun _ => fieldCell_close)
  have draws := AbortClose.bind_opt cells
    (fun cells => match cells with
      | none => PMF.pure none
      | some cells =>
        (optionProduct exceptionByteCount fun _ => (wordLaw 8).map some).bind fun bytes =>
        (optionProduct hotBlockCount fun _ => (wordLaw 128).map some).bind fun hot =>
        (optionProduct keyBlockCount fun _ => (wordLaw 128).map some).map fun key =>
          match bytes, hot, key with
          | some bytes, some hot, some key => some (cells, bytes, hot, key)
          | _, _, _ => none)
    (fun cells => match cells with
      | none => PMF.pure none
      | some cells =>
        (optionProduct exceptionByteCount fun _ => (wordLaw 8).map some).bind fun bytes =>
        (optionProduct hotBlockCount fun _ => (wordLaw 128).map some).bind fun hot =>
        (optionProduct keyBlockCount fun _ => (wordLaw 128).map some).map fun key =>
          match bytes, hot, key with
          | some bytes, some hot, some key => some (cells, bytes, hot, key)
          | _, _, _ => none)
    rfl rfl (fun _ => AbortClose.refl _)
  have mapped := draws.map_opt (Option.map fun draws =>
    sourceOfDraws (total 0 draws.1) (total 0 draws.2.1) (total 0 draws.2.2.1)
      (total 0 draws.2.2.2)) rfl
  rw [← idealSource_eq]
  exact mapped

end Source

end

end Kriterion.ArgoMAC.PlanB.SimMachine
