/-
**The replay's inputs and pieces, for the whole `Replay.program`.**

* `ReplayStart`: what the replay reads from the memory the prefix leaves (request, curve constants,
  selected labels, fold joins, scale joins), in terms of a `Stage1Source` and the label vector;
* `OffReplay`: the cells the replay never writes (outside the accumulators, the fold cells and
  `E*`, the temporaries, the digit-extraction region, the whitened labels);
* `rtree_initAcc`: the accumulator clear;
* `laneCells_*`: each lane's `LaneCells` from `ReplayStart` (the point lanes' labels from the
  whitening);
* `bridge_value`: the bridge value of `CurveMembership.evaluate` in the machine's order;
* `replay_treeOps`: the replay is a tree block (no coin, no lookup, no program).
-/

import Proof.Simulator.ReplayWhitenAll
import Proof.Simulator.ValidOps

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Cells the replay never writes -/

/-- Outside the work cells and the whitened labels. -/
def OffReplay (address : Word) : Prop :=
  OffWork address ∧ ∀ i, i < 508 → address ≠ word (whiteBase + i)

/-- Every address below `whiteBase` is never written by the replay. -/
theorem offReplay_of_lt {value : Nat} (small : value < 2 ^ 45) : OffReplay (word value) :=
  ⟨offWork_of_lt (by omega), fun i bound =>
    word_ne (by omega) (by unfold whiteBase; omega) (by unfold whiteBase; omega)⟩

/-! ### What the replay reads -/

/-- **The replay's start memory**, read through a source and the selected labels. -/
structure ReplayStart (source : Stage1Source) (input : AffineInput) (labels : LamportSignature)
    (memory : Memory) : Prop where
  reqXCell : memory.ram (word reqX) = fieldWord input.x
  reqYCell : memory.ram (word reqY) = fieldWord input.y
  curve0 : memory.ram (word fieldBase) = fieldWord source.curve.1
  curve1 : memory.ram (word (fieldBase + 1)) = fieldWord source.curve.2.1
  curve2 : memory.ram (word (fieldBase + 2)) = fieldWord source.curve.2.2
  labelCells : ∀ (i : Nat) (bound : i < 508),
    memory.ram (word (labelBase + i)) = blockWord (labels[i]'bound)
  hotX : ∀ s : Fin foldStepCount,
    memory.ram (word (hotBase + foldStepCount * 0 + s.val)) = blockWord (source.curveXHot.get s)
  hotY : ∀ s : Fin foldStepCount,
    memory.ram (word (hotBase + foldStepCount * 1 + s.val)) = blockWord (source.curveYHot.get s)
  hotPX : ∀ s : Fin foldStepCount,
    memory.ram (word (hotBase + foldStepCount * 2 + s.val)) = blockWord (source.pointXHot.get s)
  hotPY : ∀ s : Fin foldStepCount,
    memory.ram (word (hotBase + foldStepCount * 3 + s.val)) = blockWord (source.pointYHot.get s)
  scaleCells : ∀ (c : Fin chunkCount) (slot : Fin elementCount),
    memory.ram (word (scaleCellBase + elementCount * c.val + slot.val)) =
      fieldWord (source.joins c slot)

/-! ### The accumulator clear -/

theorem fieldWord_zero : fieldWord (0 : BaseField) = 0 := by
  unfold fieldWord
  rw [ZMod.val_zero]
  rfl

theorem rtree_initStores (memory : Memory) (zero : memory.registers rA = 0) :
    ∀ count, count ≤ 733 → ∃ after,
      rtree (Prog.rep count fun index => storeAt (accBase + index) rA) memory = .pure (some after) ∧
      (∀ e, e < count → after.ram (word (accBase + e)) = fieldWord 0) ∧
      (∀ address, (∀ e, e < count → address ≠ word (accBase + e)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧ after.registers rA = 0
  | 0, _ => ⟨memory, by rw [Prog.rep]; rfl, fun e bound => absurd bound (Nat.not_lt_zero _),
      fun _ _ => rfl, rfl, zero⟩
  | count + 1, bound => by
      obtain ⟨middle, run, cells, frame, bitsSame, regA⟩ :=
        rtree_initStores memory zero count (by omega)
      refine ⟨storeRam (setReg middle rAddr (word (accBase + count))) (word (accBase + count))
        (middle.registers rA), ?_, fun e small => ?_, fun address outside => ?_, ?_, ?_⟩
      · rw [Prog.rep, rtree_seq, run, bindOpt_pure, rtree_storeAt _ _ _ (by decide)]
      · rw [storeRam_ram]
        by_cases last : e = count
        · subst last
          rw [Function.update_self, regA, fieldWord_zero]
        · rw [Function.update_of_ne (word_ne (by unfold accBase; omega) (by unfold accBase; omega)
            (by omega))]
          simp only [setReg_ram]
          exact cells e (by omega)
      · rw [storeRam_ram, Function.update_of_ne (outside count (by omega))]
        simp only [setReg_ram]
        exact frame address fun e small => outside e (by omega)
      · simp only [storeRam_bits, setReg_bits]
        exact bitsSame
      · simp only [storeRam_registers, setReg_registers]
        simp (config := {decide := true}) only [reduceIte]
        exact regA

/-- **The accumulator clear.** -/
theorem rtree_initAcc (memory : Memory) : ∃ after,
    rtree Replay.initAcc memory = .pure (some after) ∧
      (∀ e, e < 733 → after.ram (word (accBase + e)) = fieldWord 0) ∧
      (∀ address, (∀ e, e < 733 → address ≠ word (accBase + e)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits := by
  unfold Replay.initAcc
  rw [rtree_cst_seq]
  obtain ⟨after, run, cells, frame, bitsSame, _⟩ :=
    rtree_initStores (setReg memory rA (word 0)) (by rw [reg_same]; rfl) 733 le_rfl
  exact ⟨after, run, cells, fun address outside => by rw [frame address outside]; rfl,
    by rw [bitsSame]; rfl⟩

/-! ### The lanes' cells -/

omit [FieldCertificate] in
theorem unpack_scale (source : Stage1Source) (c : Fin chunkCount) :
    unpack (source.publicValue.scale.get c) = source.joins c := by
  simp only [Stage1Source.publicValue, Vector.get_ofFn, unpack_pack_eq]

omit [FieldCertificate] in
theorem coordBits_x (input : AffineInput) :
    (Pipeline.coordBits (BitInput.ofAffine input) .x).toNat = input.x.val :=
  coordinateBitsToNat input.x

omit [FieldCertificate] in
theorem coordBits_y (input : AffineInput) :
    (Pipeline.coordBits (BitInput.ofAffine input) .y).toNat = input.y.val :=
  coordinateBitsToNat input.y

omit [FieldCertificate] in
theorem restore_x (input : AffineInput) (labels : LamportSignature) (i : Fin coordinateBitCount) :
    Pipeline.macLabels (Lamport.restore input labels).inputMac .x i =
      labels[i.val]'(by have := i.isLt; unfold coordinateBitCount at this; omega) := by
  simp only [Pipeline.macLabels, Lamport.restore, Vector.get_ofFn]

omit [FieldCertificate] in
theorem restore_y (input : AffineInput) (labels : LamportSignature) (i : Fin coordinateBitCount) :
    Pipeline.macLabels (Lamport.restore input labels).inputMac .y i =
      labels[254 + i.val]'(by have := i.isLt; unfold coordinateBitCount at this; omega) := by
  simp only [Pipeline.macLabels, Lamport.restore, Vector.get_ofFn]

omit [FieldCertificate] in
theorem readCurveY_eq (values : Fin elementCount → BaseField) (e : Fin curveElementCountY) :
    Pipeline.readCurveY values e =
      values ⟨731 + e.val, by have := e.isLt; unfold curveElementCountY at this; unfold elementCount; omega⟩ := by
  unfold Pipeline.readCurveY Pipeline.yCurvePart Pipeline.yPart
  congr 1
  apply Fin.ext
  show elementCountX + (pointElementCountY + e.val) = 731 + e.val
  unfold elementCountX pointElementCountY
  omega

omit [FieldCertificate] in
theorem reqX_small : reqX < 2 ^ 45 := by unfold reqX requestBase; norm_num
omit [FieldCertificate] in
theorem reqY_small : reqY < 2 ^ 45 := by unfold reqY requestBase; norm_num

omit [FieldCertificate] in
theorem hot_small (row : Nat) (small : row < 4) (s : Fin foldStepCount) :
    hotBase + foldStepCount * row + s.val < 2 ^ 45 := by
  have := s.isLt
  unfold foldStepCount at this ⊢
  unfold hotBase
  omega

omit [FieldCertificate] in
theorem scale_small (c : Fin chunkCount) (slot : Nat) (small : slot < 733) :
    scaleCellBase + elementCount * c.val + slot < 2 ^ 45 := by
  have := c.isLt
  unfold chunkCount at this
  unfold scaleCellBase fieldBase curveCellCount rowCellCount elementCount
  omega

omit [FieldCertificate] in
theorem label_small (i : Nat) (small : i < 508) : labelBase + i < 2 ^ 45 := by
  unfold labelBase
  omega

section Lanes

variable {source : Stage1Source} {input : AffineInput} {labels : LamportSignature}
  {start memory : Memory}

theorem laneCells_curveX (cells : ReplayStart source input labels start)
    (frame : ∀ address, OffReplay address → memory.ram address = start.ram address) :
    LaneCells Replay.curveXSpec (Pipeline.coordBits (BitInput.ofAffine input) .x).toNat
      (Pipeline.macLabels (Lamport.restore input labels).inputMac .x) source.publicValue.curveXHot
      (fun chunk => Pipeline.readCurveX (unpack (source.publicValue.scale.get chunk))) memory where
  coordCell := by
    show memory.ram (word reqX) = _
    rw [frame (word reqX) (offReplay_of_lt reqX_small), cells.reqXCell, coordBits_x]
    rfl
  labelCells i := by
    have small : i.val < 254 := i.isLt
    show memory.ram (word (labelBase + i.val)) = _
    rw [frame (word (labelBase + i.val)) (offReplay_of_lt (label_small i.val (by omega))),
      cells.labelCells i.val (by omega),
      restore_x]
  hotCells s := by
    show memory.ram (word (hotBase + foldStepCount * 0 + s.val)) = _
    rw [frame (word (hotBase + foldStepCount * 0 + s.val))
      (offReplay_of_lt (hot_small 0 (by omega) s)), cells.hotX s]
    rfl
  scaleCells c e := by
    have small : e.val < 3 := e.isLt
    show memory.ram (word (scaleCellBase + elementCount * c.val + 455 + e.val)) = _
    rw [frame (word (scaleCellBase + elementCount * c.val + 455 + e.val))
        (offReplay_of_lt (by rw [Nat.add_assoc]; exact scale_small c (455 + e.val) (by omega))),
      Nat.add_assoc (scaleCellBase + elementCount * c.val), cells.scaleCells c ⟨455 + e.val, by
        unfold elementCount; omega⟩]
    simp only [unpack_scale]
    rfl

theorem laneCells_curveY (cells : ReplayStart source input labels start)
    (frame : ∀ address, OffReplay address → memory.ram address = start.ram address) :
    LaneCells Replay.curveYSpec (Pipeline.coordBits (BitInput.ofAffine input) .y).toNat
      (Pipeline.macLabels (Lamport.restore input labels).inputMac .y) source.publicValue.curveYHot
      (fun chunk => Pipeline.readCurveY (unpack (source.publicValue.scale.get chunk))) memory where
  coordCell := by
    show memory.ram (word reqY) = _
    rw [frame (word reqY) (offReplay_of_lt reqY_small), cells.reqYCell, coordBits_y]
    rfl
  labelCells i := by
    have small : i.val < 254 := i.isLt
    show memory.ram (word (labelBase + 254 + i.val)) = _
    rw [frame (word (labelBase + 254 + i.val))
        (offReplay_of_lt (by unfold labelBase; omega)),
      Nat.add_assoc, cells.labelCells (254 + i.val) (by omega), restore_y]
  hotCells s := by
    show memory.ram (word (hotBase + foldStepCount * 1 + s.val)) = _
    rw [frame (word (hotBase + foldStepCount * 1 + s.val))
      (offReplay_of_lt (hot_small 1 (by omega) s)), cells.hotY s]
    rfl
  scaleCells c e := by
    have small : e.val < 2 := e.isLt
    show memory.ram (word (scaleCellBase + elementCount * c.val + 731 + e.val)) = _
    rw [frame (word (scaleCellBase + elementCount * c.val + 731 + e.val))
        (offReplay_of_lt (by rw [Nat.add_assoc]; exact scale_small c (731 + e.val) (by omega))),
      Nat.add_assoc (scaleCellBase + elementCount * c.val), cells.scaleCells c ⟨731 + e.val, by
        unfold elementCount; omega⟩]
    simp only [unpack_scale]
    rw [readCurveY_eq (source.joins c) e]

/-- The point lanes read the whitened labels. -/
theorem laneCells_pointX (cells : ReplayStart source input labels start) (white : InputMac)
    (frame : ∀ address, OffReplay address → memory.ram address = start.ram address)
    (whites : ∀ i : Fin coordinateBitCount,
      memory.ram (word (whiteBase + i.val)) = blockWord (white.x.get i)) :
    LaneCells Replay.pointXSpec (Pipeline.coordBits (BitInput.ofAffine input) .x).toNat
      (Pipeline.macLabels white .x) source.publicValue.pointXHot
      (fun chunk => Pipeline.readPointX (unpack (source.publicValue.scale.get chunk))) memory where
  coordCell := by
    show memory.ram (word reqX) = _
    rw [frame (word reqX) (offReplay_of_lt reqX_small), cells.reqXCell, coordBits_x]
    rfl
  labelCells i := whites i
  hotCells s := by
    show memory.ram (word (hotBase + foldStepCount * 2 + s.val)) = _
    rw [frame (word (hotBase + foldStepCount * 2 + s.val))
      (offReplay_of_lt (hot_small 2 (by omega) s)), cells.hotPX s]
    rfl
  scaleCells c e := by
    have small : e.val < 455 := e.isLt
    show memory.ram (word (scaleCellBase + elementCount * c.val + 0 + e.val)) = _
    rw [frame (word (scaleCellBase + elementCount * c.val + 0 + e.val))
        (offReplay_of_lt (by rw [Nat.add_assoc]; exact scale_small c (0 + e.val) (by omega))),
      Nat.add_assoc (scaleCellBase + elementCount * c.val), cells.scaleCells c ⟨0 + e.val, by
        unfold elementCount; omega⟩]
    simp only [unpack_scale]
    congr 1
    exact congrArg (source.joins c) (Fin.ext (Nat.zero_add _))

theorem laneCells_pointY (cells : ReplayStart source input labels start) (white : InputMac)
    (frame : ∀ address, OffReplay address → memory.ram address = start.ram address)
    (whites : ∀ i : Fin coordinateBitCount,
      memory.ram (word (whiteBase + 254 + i.val)) = blockWord (white.y.get i)) :
    LaneCells Replay.pointYSpec (Pipeline.coordBits (BitInput.ofAffine input) .y).toNat
      (Pipeline.macLabels white .y) source.publicValue.pointYHot
      (fun chunk => Pipeline.readPointY (unpack (source.publicValue.scale.get chunk))) memory where
  coordCell := by
    show memory.ram (word reqY) = _
    rw [frame (word reqY) (offReplay_of_lt reqY_small), cells.reqYCell, coordBits_y]
    rfl
  labelCells i := whites i
  hotCells s := by
    show memory.ram (word (hotBase + foldStepCount * 3 + s.val)) = _
    rw [frame (word (hotBase + foldStepCount * 3 + s.val))
      (offReplay_of_lt (hot_small 3 (by omega) s)), cells.hotPY s]
    rfl
  scaleCells c e := by
    have small : e.val < 273 := e.isLt
    show memory.ram (word (scaleCellBase + elementCount * c.val + 458 + e.val)) = _
    rw [frame (word (scaleCellBase + elementCount * c.val + 458 + e.val))
        (offReplay_of_lt (by rw [Nat.add_assoc]; exact scale_small c (458 + e.val) (by omega))),
      Nat.add_assoc (scaleCellBase + elementCount * c.val), cells.scaleCells c ⟨458 + e.val, by
        unfold elementCount; omega⟩]
    simp only [unpack_scale]
    rfl

end Lanes

/-! ### The bridge value -/

/-- The bridge value in the machine's order. -/
theorem bridge_value (table : CurveMembership.Table) (input : AffineInput)
    (curveX : Fin curveElementCountX → BaseField) (curveY : Fin curveElementCountY → BaseField) :
    CurveMembership.evaluate table (BitInput.ofAffine input).toAffine
        (Pipeline.curveValues curveX curveY) =
      table.1 + table.2.1 * input.x ^ 3 + table.2.2 * input.y ^ 2 +
        curveX ⟨0, by decide⟩ * input.x ^ 2 + curveY ⟨0, by decide⟩ * input.y +
        curveX ⟨1, by decide⟩ * input.x + curveY ⟨1, by decide⟩ + curveX ⟨2, by decide⟩ := by
  rw [BitInput.toAffineOfAffine]
  rfl

/-! ### The replay is a tree block -/

section Ops

variable (ordF : PlanB.FixedIndex → Nat) (ordE : EncPRF.PermutationIndex → Nat)

omit [FieldCertificate] in
/-- A plain block is a tree block. -/
theorem BigInt.IsPlain.treeOps : ∀ {program : Prog}, BigInt.IsPlain program → program.OpsSatisfy TreeOp
  | .op operation, plain => by cases operation <;> trivial
  | .popBit _ _, _ | .skip _, _ | .abort _, _ => trivial
  | .seq _ _, plain => ⟨plain.1.treeOps, plain.2.treeOps⟩
  | .ite _ _ _, plain => ⟨plain.1.treeOps, plain.2.treeOps⟩

omit [FieldCertificate] in
theorem tree_switchStep (spec : Replay.LaneSpec) (designated : Bool) (chunk switch : Nat) :
    (Replay.switchStep spec designated chunk switch).OpsSatisfy TreeOp := by
  unfold Replay.switchStep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, BigInt.IsPlain.treeOps (BigInt.plain_digitsOf _ _ _ _), ?_, trivial⟩ <;>
    ops_split

omit [FieldCertificate] in
theorem tree_chunkBody (spec : Replay.LaneSpec) (designated : Bool) (chunk : Nat) :
    (Replay.chunkBody ordF spec designated chunk).OpsSatisfy TreeOp := by
  unfold Replay.chunkBody
  refine ⟨?_, opsSatisfy_rep _ _ fun _ _ => ?_, ?_,
    opsSatisfy_rep _ _ fun _ _ => tree_switchStep _ _ _ _, ?_, ?_, trivial⟩
  · unfold Replay.chunkPrefix; ops_split
  · unfold Replay.foldStep Replay.foldEntry Replay.foldGate Replay.foldPair Replay.absorbEntry
      Replay.extendEntry
    ops_split
  · cases designated
    · trivial
    · unfold Replay.designatedPart Replay.designatedPrefix; ops_split
  · ops_split
  · unfold Replay.joinTerm; ops_split

omit [FieldCertificate] in
/-- **The replay is a tree block.** -/
theorem replay_treeOps : (Replay.program ordF ordE).OpsSatisfy TreeOp := by
  unfold Replay.program Replay.lane Replay.designatedLane
  have lane (spec : Replay.LaneSpec) (designated : Bool) :
      (Prog.seq (Replay.chunkBody ordF spec designated 0) (Prog.rep (chunkCount - 1) fun chunk =>
        Replay.chunkBody ordF spec false (chunk + 1))).OpsSatisfy TreeOp :=
    ⟨tree_chunkBody ordF _ _ _, opsSatisfy_rep _ _ fun _ _ => tree_chunkBody ordF _ _ _⟩
  refine ⟨?_, lane _ _, lane _ _, ?_, ?_, lane _ _, lane _ _⟩
  · unfold Replay.initAcc; ops_split
  · unfold Replay.bridge; ops_split
  · unfold Replay.whiten Replay.whitenOne; ops_split

end Ops

end

end Kriterion.ArgoMAC.PlanB.SimMachine
