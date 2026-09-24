/-
**Stage 2 starts from stage 1's support.**

* `machine_stage1`: the machine's stage-1 kernel is `stage1Draws` mapped to the retained
  configuration `stage1Final … draw`;
* `stage1Draws_support`: a drawn fold join and a drawn key word are below `2^128`;
* `prefix_start`: from such a retained memory, the prefix of a valid request (`f_k u = some Q`)
  leaves a memory satisfying `ReplayStart` for the drawn source and the selected labels, the
  output cells of `Q`, the row constants, the set flag and an empty response stack.
-/

import Proof.Simulator.Stage2Programs

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### The support of the stage-1 draws -/

/-- A value of an `optionProduct` is a value of every factor. -/
theorem optionProduct_support {α : Type} :
    ∀ (count : Nat) (sample : Fin count → PMF (Option α)) (values : Fin count → α),
      some values ∈ (optionProduct count sample).support →
        ∀ index, some (values index) ∈ (sample index).support
  | 0, _, _, _, index => index.elim0
  | count + 1, sample, values, member, index => by
      simp only [optionProduct, PMF.mem_support_bind_iff] at member
      obtain ⟨head, headMember, rest⟩ := member
      cases head with
      | none => simp at rest
      | some head =>
          simp only [PMF.mem_support_map_iff] at rest
          obtain ⟨tail, tailMember, same⟩ := rest
          cases tail with
          | none => simp at same
          | some tail =>
              simp only [Option.map_some, Option.some.injEq] at same
              subst same
              refine Fin.cases ?_ (fun later => ?_) index
              · simpa using headMember
              · simpa using optionProduct_support count (fun index => sample index.succ) tail
                  tailMember later

theorem wordLaw_support (width value : Nat)
    (member : some value ∈ ((wordLaw width).map some).support) : value < 2 ^ width := by
  simp only [PMF.mem_support_map_iff, wordLaw, Option.some.injEq] at member
  obtain ⟨drawn, drawnMember, same⟩ := member
  obtain ⟨index, _, rfl⟩ := drawnMember
  exact same ▸ index.isLt

/-- **The drawn fold joins and key words are `128`-bit.** -/
theorem stage1Draws_support [FieldCertificate] (draw : Stage1Draw)
    (member : some draw ∈ stage1Draws.support) :
    (∀ index, draw.2.2.1 index < 2 ^ 128) ∧ (∀ index, draw.2.2.2 index < 2 ^ 128) := by
  simp only [stage1Draws, PMF.mem_support_bind_iff] at member
  obtain ⟨cells, _, rest⟩ := member
  cases cells with
  | none => simp at rest
  | some cells =>
      simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at rest
      obtain ⟨bytes, _, hot, hotMember, key, keyMember, same⟩ := rest
      cases bytes <;> cases hot <;> cases key <;> simp only [reduceCtorEq] at same
      rename_i bytes hot key
      simp only [Option.some.injEq] at same
      subst same
      exact ⟨fun index => wordLaw_support 128 _ (optionProduct_support _ _ hot hotMember index),
        fun index => wordLaw_support 128 _ (optionProduct_support _ _ key keyMember index)⟩

/-! ### The machine's stage 1 -/

/-- The retained memory of a stage-1 draw. -/
def retained [FieldCertificate] (parameter : Nat) (draw : Stage1Draw) : Memory :=
  stage1Final (Top.afterTag (stage1Memory parameter) (stage1Rest parameter)) draw

/-- **The machine's stage-1 kernel.** -/
theorem machine_stage1 [FieldCertificate] (parameter : Nat) :
    (machineKernels).stage1 parameter LazyOracle.empty =
      stage1Draws.map (Option.map fun draw => ((drawSource draw).publicValue,
        atPc planBSimulator Design.stage1Halt (retained parameter draw), LazyOracle.empty)) := by
  unfold machineKernels machineAbstract
  dsimp only
  rw [planB_stage1_run, optionT_mk_map, bind_assoc]
  simp only [pure_bind, atPc_memory,
    publicValue_final (Top.afterTag (stage1Memory parameter) (stage1Rest parameter))
      (stage1Start_stack3 parameter), optionT_mk_pure_some]
  rw [← optionT_mk_map, OptionT.run_mk]
  rfl

/-- **A retained configuration comes from a draw in the support.** -/
theorem stage1_support [FieldCertificate] (parameter : Nat) result
    (member : some result ∈ ((machineKernels).stage1 parameter LazyOracle.empty).support) :
    ∃ draw, some draw ∈ stage1Draws.support ∧ result.2.1.memory = retained parameter draw := by
  rw [machine_stage1] at member
  obtain ⟨drawn, drawnMember, same⟩ := (PMF.mem_support_map_iff _ _ _).1 member
  cases drawn with
  | none => cases same
  | some draw =>
      injection same with same
      subst same
      exact ⟨draw, drawnMember, rfl⟩

/-! ### The retained cells -/

section Cells

variable [FieldCertificate]

omit [FieldCertificate] in
theorem blockWord_ofNat (value : Nat) (small : value < 2 ^ 128) :
    blockWord (BitVec.ofNat 128 value) = BitVec.ofNat 256 value := by
  unfold blockWord
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

theorem retained_field (parameter : Nat) (draw : Stage1Draw) (index : Nat)
    (bound : index < fieldCellCount) :
    (retained parameter draw).ram (word (fieldBase + index)) = fieldWord (total 0 draw.1 index) := by
  unfold retained
  rw [stage1Final_ram, show fieldBase + index = fieldBase + (⟨index, bound⟩ : Fin fieldCellCount).val
    from rfl, ram_field, total_apply _ _ _ bound]
  rfl

theorem retained_hot (parameter : Nat) (draw : Stage1Draw)
    (small : ∀ index, draw.2.2.1 index < 2 ^ 128) (index : Nat) (bound : index < hotBlockCount) :
    (retained parameter draw).ram (word (hotBase + index)) =
      blockWord (BitVec.ofNat 128 (total 0 draw.2.2.1 index)) := by
  unfold retained
  rw [stage1Final_ram, show hotBase + index = hotBase + (⟨index, bound⟩ : Fin hotBlockCount).val
    from rfl, ram_hot, total_apply _ _ _ bound, blockWord_ofNat _ (small _)]

theorem retained_key (parameter : Nat) (draw : Stage1Draw)
    (small : ∀ index, draw.2.2.2 index < 2 ^ 128) (index : Nat) (bound : index < keyBlockCount) :
    (retained parameter draw).ram (word (keyBase + index)) =
      blockWord (BitVec.ofNat 128 ((retained parameter draw).ram (word (keyBase + index))).toNat) := by
  unfold retained
  rw [stage1Final_ram, show keyBase + index = keyBase + (⟨index, bound⟩ : Fin keyBlockCount).val
    from rfl, ram_key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans (small _) (by norm_num)),
    blockWord_ofNat _ (small _)]

end Cells

theorem drawSource_row_get (draw : Stage1Draw) (digit : Fin digitCount) (field : Nat)
    (small : field < 11) :
    rowField ((drawSource draw).rows.get digit) field = total 0 draw.1 (3 + 11 * digit.val + field) := by
  simp only [drawSource, sourceOfDraws, Vector.get_ofFn]
  interval_cases field <;> rfl

/-! ### The prefix of a valid request -/

section Prefix

variable [FieldCertificate]

/-- The request's output tags and `Q` for a defined output. -/
def outTags : Point → Bool × Bool × Nat × Nat
  | .zero => (false, true, 0, 0)
  | .some (x := x) (y := y) _ => (true, false, x.val, y.val)

theorem outTags_bits (target : Point) :
    OutBits (SimulatorProtocol.output (some target)) (outTags target).1 (outTags target).2.1
      (outTags target).2.2.1 (outTags target).2.2.2 := by
  cases target with
  | zero => simp [OutBits, outTags, SimulatorProtocol.output]
  | some nonsingular =>
      simp only [OutBits, outTags, ↓reduceIte]
      refine ⟨?_, coord_small _, coord_small _⟩
      simp only [SimulatorProtocol.output, SimulatorProtocol.affine, bits_eq_lsbs]
      rfl

theorem outTags_flag (target : Point) :
    bitWord (outTags target).1 + bitWord (outTags target).2.1 ≠ 0 := by
  cases target with
  | zero =>
      show bitWord false + bitWord true ≠ 0
      decide
  | some nonsingular =>
      show bitWord true + bitWord false ≠ 0
      decide

theorem outTags_words (target : Point) :
    outputWords target = (bitWord (outTags target).1, word (outTags target).2.2.1,
      word (outTags target).2.2.2) := by
  cases target <;> rfl

/-- The memory stage 2's prefix starts from. -/
def prefixStart (memory : Memory) (input : AffineInput) (target : Point) : Memory :=
  Top.afterTag (stage2Memory memory input (some target)) (stage2Rest input (some target))

/-- **The prefix of a valid request**: the flag is set, the response stack is empty, the cells
below the label region read as the parse, and the labels are the selected key words. -/
theorem prefix_middle (memory : Memory) (input : AffineInput) (target : Point) :
    ∃ middle, Request.prefixProgram.memSem (prefixStart memory input target) =
        PMF.pure (some middle) ∧
      middle.registers rFlag ≠ 0 ∧ middle.bits 3 = [] ∧
      (∀ value, value < 2 ^ 44 → middle.ram (word value) =
        parsedRam memory.ram input.x.val input.y.val (outTags target).1 (outTags target).2.1
          (outTags target).2.2.1 (outTags target).2.2.2 (word value)) ∧
      (∀ i, i < 508 → middle.ram (word (labelBase + i)) =
        memory.ram (word (keyBase + 2 * i + inputBit input.x.val input.y.val i))) := by
  obtain ⟨middle, run, bitsAfter, labels, away, flag⟩ := memSem_prefix
    (prefixStart memory input target) input.x.val input.y.val (coord_small _) (coord_small _)
    (SimulatorProtocol.output (some target)) (outTags target).1 (outTags target).2.1
    (outTags target).2.2.1 (outTags target).2.2.2 (outTags_bits target)
    (afterTag_request memory input (some target))
  refine ⟨middle, run, by rw [flag]; exact outTags_flag target, ?_, fun value small => ?_,
    fun i bound => labels i bound⟩
  · rw [bitsAfter, Function.update_of_ne (by decide)]
    exact afterTag_response memory input (some target)
  · rw [away _ fun position bound => word_ne (by omega) (labelCell_lt position bound)
      (by unfold labelBase; omega)]
    rfl

theorem parsed_outside (ram : Word → Word) (x y : Nat) (t0 t1 : Bool) (qx qy value : Nat)
    (small : value < 2 ^ 43) :
    parsedRam ram x y t0 t1 qx qy (word value) = ram (word value) :=
  parsedRam_off _ _ _ _ _ _ _ _ fun offset bound =>
    word_ne (by omega) (by unfold requestBase; omega) (by unfold requestBase; omega)

/-- The retained memory's label, through the selection. -/
theorem retained_label (parameter : Nat) (draw : Stage1Draw)
    (keySmall : ∀ index, draw.2.2.2 index < 2 ^ 128) (input : AffineInput) (i : Nat)
    (bound : i < 508) :
    (retained parameter draw).ram (word (keyBase + 2 * i + inputBit input.x.val input.y.val i)) =
      blockWord ((Lamport.selectedLabels
        ((drawSource draw).key.encode (BitInput.ofAffine input)))[i]'bound) := by
  have bitLe := inputBit_le input.x.val input.y.val i
  have keyCell := retained_key parameter draw keySmall (2 * i + inputBit input.x.val input.y.val i)
    (by unfold keyBlockCount; omega)
  rw [← Nat.add_assoc] at keyCell
  rw [keyCell]
  refine congrArg blockWord ?_
  rw [show drawSource draw = extractSource (retained parameter draw) from
    (extractSource_final _ draw).symm]
  exact (selectedLabel_extract (retained parameter draw) input i bound).symm

omit [FieldCertificate] in
theorem hot_source (draw : Stage1Draw) (s : Fin foldStepCount) :
    (drawSource draw).curveXHot.get s = BitVec.ofNat 128 (total 0 draw.2.2.1 (0 + s.val)) ∧
    (drawSource draw).curveYHot.get s = BitVec.ofNat 128 (total 0 draw.2.2.1 (198 + s.val)) ∧
    (drawSource draw).pointXHot.get s = BitVec.ofNat 128 (total 0 draw.2.2.1 (396 + s.val)) ∧
    (drawSource draw).pointYHot.get s = BitVec.ofNat 128 (total 0 draw.2.2.1 (594 + s.val)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [drawSource, sourceOfDraws, Vector.get_ofFn, Nat.zero_add]

/-- **The replay's start**, from the prefix of a valid request on a retained memory. -/
theorem prefix_replayStart (parameter : Nat) (draw : Stage1Draw)
    (member : some draw ∈ stage1Draws.support) (input : AffineInput) (target : Point)
    (middle : Memory)
    (parsed : ∀ value, value < 2 ^ 44 → middle.ram (word value) =
      parsedRam (retained parameter draw).ram input.x.val input.y.val (outTags target).1
        (outTags target).2.1 (outTags target).2.2.1 (outTags target).2.2.2 (word value))
    (labels : ∀ i, i < 508 → middle.ram (word (labelBase + i)) =
      (retained parameter draw).ram (word (keyBase + 2 * i + inputBit input.x.val input.y.val i))) :
    ReplayStart (drawSource draw) input
      (Lamport.selectedLabels ((drawSource draw).key.encode (BitInput.ofAffine input))) middle := by
  obtain ⟨hotSmall, keySmall⟩ := stage1Draws_support draw member
  have fieldCell : ∀ index, index < fieldCellCount →
      middle.ram (word (fieldBase + index)) = fieldWord (total 0 draw.1 index) := by
    intro index bound
    have : index < 42052 := bound
    rw [parsed _ (by unfold fieldBase; omega), parsed_outside _ _ _ _ _ _ _ _ (by unfold fieldBase; omega)]
    exact retained_field parameter draw index bound
  have hotCell : ∀ index, index < hotBlockCount →
      middle.ram (word (hotBase + index)) = blockWord (BitVec.ofNat 128 (total 0 draw.2.2.1 index)) := by
    intro index bound
    have : index < 792 := bound
    rw [parsed _ (by unfold hotBase; omega), parsed_outside _ _ _ _ _ _ _ _ (by unfold hotBase; omega)]
    exact retained_hot parameter draw hotSmall index bound
  refine
    { reqXCell := ?_, reqYCell := ?_, curve0 := ?_, curve1 := ?_, curve2 := ?_,
      labelCells := fun i bound => (labels i bound).trans (retained_label parameter draw keySmall input i bound),
      hotX := fun s => ?_, hotY := fun s => ?_, hotPX := fun s => ?_, hotPY := fun s => ?_,
      scaleCells := fun c slot => ?_ }
  · rw [parsed reqX (by unfold reqX requestBase; norm_num), parsedRam_x]
    rfl
  · rw [parsed reqY (by unfold reqY requestBase; norm_num), parsedRam_y]
    rfl
  · exact fieldCell 0 (by decide)
  · exact fieldCell 1 (by decide)
  · exact fieldCell 2 (by decide)
  · have := s.isLt
    unfold foldStepCount at this
    rw [Nat.add_assoc, hotCell _ (by unfold hotBlockCount foldStepCount; omega), (hot_source draw s).1]
    rfl
  · have := s.isLt
    unfold foldStepCount at this
    rw [Nat.add_assoc, hotCell _ (by unfold hotBlockCount foldStepCount; omega), (hot_source draw s).2.1]
    rfl
  · have := s.isLt
    unfold foldStepCount at this
    rw [Nat.add_assoc, hotCell _ (by unfold hotBlockCount foldStepCount; omega), (hot_source draw s).2.2.1]
    rfl
  · have := s.isLt
    unfold foldStepCount at this
    rw [Nat.add_assoc, hotCell _ (by unfold hotBlockCount foldStepCount; omega), (hot_source draw s).2.2.2]
    rfl
  · have chunkBound := c.isLt
    have slotBound := slot.isLt
    unfold chunkCount at chunkBound
    unfold elementCount at slotBound
    rw [show scaleCellBase + elementCount * c.val + slot.val =
        fieldBase + (1004 + 733 * c.val + slot.val) by
        unfold scaleCellBase curveCellCount rowCellCount elementCount; omega,
      fieldCell _ (by unfold fieldCellCount curveCellCount rowCellCount scaleCellCount; omega)]
    rfl

/-- The output cells of the parse. -/
theorem prefix_output (memory middle : Memory) (input : AffineInput) (target : Point)
    (parsed : ∀ value, value < 2 ^ 44 → middle.ram (word value) =
      parsedRam memory.ram input.x.val input.y.val (outTags target).1 (outTags target).2.1
        (outTags target).2.2.1 (outTags target).2.2.2 (word value)) :
    (middle.ram (word reqTag0), middle.ram (word reqQX), middle.ram (word reqQY)) =
      outputWords target := by
  rw [outTags_words, parsed reqTag0 (by unfold reqTag0 requestBase; norm_num),
    parsed reqQX (by unfold reqQX requestBase; norm_num),
    parsed reqQY (by unfold reqQY requestBase; norm_num), parsedRam_tag0, parsedRam_qx,
    parsedRam_qy]

/-- The row constants, read through the parse. -/
theorem prefix_rows (parameter : Nat) (draw : Stage1Draw) (input : AffineInput) (target : Point)
    (middle : Memory)
    (parsed : ∀ value, value < 2 ^ 44 → middle.ram (word value) =
      parsedRam (retained parameter draw).ram input.x.val input.y.val (outTags target).1
        (outTags target).2.1 (outTags target).2.2.1 (outTags target).2.2.2 (word value))
    (digit : Fin digitCount) (slot : Nat) (small : slot < 11) :
    middle.ram (word (Opening.rowCell digit.val slot)) =
      fieldWord (rowField ((drawSource draw).rows.get digit) slot) := by
  have := digit.isLt
  unfold digitCount at this
  rw [show Opening.rowCell digit.val slot = fieldBase + (3 + 11 * digit.val + slot) by
      unfold Opening.rowCell curveCellCount; omega,
    parsed _ (by unfold fieldBase; omega), parsed_outside _ _ _ _ _ _ _ _ (by unfold fieldBase; omega),
    retained_field parameter draw _ (by unfold fieldCellCount curveCellCount rowCellCount scaleCellCount; omega),
    drawSource_row_get draw digit slot small]

end Prefix

end

end Kriterion.ArgoMAC.PlanB.SimMachine
