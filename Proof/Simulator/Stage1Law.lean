/-
**`Stage1Law`**: the machine's stage-1 kernel is the abstract stage 1 of its bounded samplers.

* `memSem_finish`: the serializer and the final register clear leave `stage1Final`;
* `stage1_program_law`: the whole stage-1 program is `stage1Draws` followed by `stage1Final`,
  assembled block by block (`memSem_fields`, `memSem_words`) by `PMF.bind` congruence;
* `publicValue_final`: the protocol's parse of the final response stack is the drawn source's
  public value (`serial_wire`, `publicValue_encode`);
* `extractSource_final`: the retained RAM reads back as the drawn source;
* `stage1Law`: P3's `Stage1Law`.
-/

import Proof.Simulator.Stage1Match
import Proof.Simulator.Law

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

section Program

variable [FieldCertificate]

/-- **The serializer and the register clear.** -/
theorem memSem_finish (memory : Memory) (draw : Stage1Draw) :
    (Prog.seq Stage1.serialize (zeroRegs allRegisters)).memSem (storedMemory memory draw) =
      PMF.pure (some (stage1Final memory draw)) := by
  obtain ⟨after, run, emits⟩ := memSem_serialize (storedMemory memory draw)
  rw [memSem_seq, run, PMF.pure_bind]
  simp only [kleisli]
  rw [memSem_zeroRegs]
  congr 2
  apply memory_ext
  · rw [(clearRegs_other _ _).2, stage1Final_bits]
    funext stack
    by_cases three : stack = 3
    · subst three
      rw [emits.2.1, Function.update_self, storedMemory_bits]
    · rw [emits.2.2 stack three, Function.update_of_ne three, storedMemory_bits]
  · rw [stage1Final_registers]
    funext register
    rw [clearRegs_registers, if_pos (by simp [allRegisters])]
  · rw [(clearRegs_other _ _).1, stage1Final_ram, emits.1]

/-- The serializer and the register clear, on the stored memory spelled out. -/
theorem memSem_finish' (memory : Memory) (cells : Fin fieldCellCount → BaseField)
    (bytes : Fin exceptionByteCount → Nat) (hot : Fin hotBlockCount → Nat)
    (key : Fin keyBlockCount → Nat) :
    (Prog.seq Stage1.serialize (zeroRegs allRegisters)).memSem
      (foldStore (wordStep keyBase) keyBlockCount (foldStore (wordStep hotBase) hotBlockCount
        (foldStore (wordStep exceptionBase) exceptionByteCount
          (foldStore (cellStep fieldBase) fieldCellCount memory cells) bytes) hot) key) =
      PMF.pure (some (stage1Final memory (cells, bytes, hot, key))) := by
  have finish := memSem_finish memory (cells, bytes, hot, key)
  unfold storedMemory at finish
  exact finish

/-- **The stage-1 program's law.** -/
theorem stage1_program_law (memory : Memory) :
    Stage1.program.memSem memory = stage1Draws.map (Option.map (stage1Final memory)) := by
  have bytesLaw := wordProduct_eq exceptionByteCount 8
  have hotLaw := wordProduct_eq hotBlockCount 128
  have keyLaw := wordProduct_eq keyBlockCount 128
  unfold Stage1.program stage1Draws
  rw [memSem_seq, show Stage1.fields = Prog.rep fieldCellCount
      (fun index => Stage1.fieldCell (fieldBase + index)) from rfl, memSem_fields, PMF.bind_map,
    PMF.map_bind]
  congr 1
  funext cells
  cases cells with
  | none => simp [kleisli, PMF.pure_map]
  | some cells =>
      simp only [Function.comp_apply, Option.map_some, kleisli]
      rw [memSem_seq, show Stage1.bytes = Prog.rep exceptionByteCount
          (fun index => Stage1.wordCell 8 (exceptionBase + index)) from rfl,
        memSem_words 8 exceptionBase exceptionByteCount (by norm_num), bytesLaw, PMF.map_comp,
        PMF.bind_map, PMF.bind_map, PMF.map_bind]
      congr 1
      funext bytes
      simp only [Function.comp_apply, Option.map_some, kleisli]
      rw [memSem_seq, show Stage1.blocks = Prog.rep hotBlockCount
          (fun index => Stage1.wordCell 128 (hotBase + index)) from rfl,
        memSem_words 128 hotBase hotBlockCount (by norm_num), hotLaw, PMF.map_comp,
        PMF.bind_map, PMF.bind_map, PMF.map_bind]
      congr 1
      funext hot
      simp only [Function.comp_apply, Option.map_some, kleisli]
      rw [memSem_seq, show Stage1.key = Prog.rep keyBlockCount
          (fun index => Stage1.wordCell 128 (keyBase + index)) from rfl,
        memSem_words 128 keyBase keyBlockCount (by norm_num), keyLaw, PMF.map_comp,
        PMF.bind_map, PMF.map_comp, PMF.map_comp, ← PMF.bind_pure_comp]
      congr 1
      funext key
      simp only [Function.comp_apply, Option.map_some, kleisli]
      exact memSem_finish' memory cells (fun index => (bytes index).val)
        (fun index => (hot index).val) (fun index => (key index).val)

end Program

/-! ### The parse and the kernel -/

section Kernel

variable [FieldCertificate]

/-- **The protocol's parse of the final response stack.** -/
theorem publicValue_final (memory : Memory) (empty : memory.bits 3 = []) (draw : Stage1Draw) :
    SimulatorProtocol.publicValue Wire.encoding 1348634 ((stage1Final memory draw).bits 3) =
      some (drawSource draw).publicValue := by
  rw [stage1Final_bits, Function.update_self, empty, List.append_nil, serial_wire]
  exact publicValue_encode _ _ _ (Wire.garble_length _)

theorem atPc_memory (machine : Simulator) (pc : Nat) (memory : Memory) :
    (atPc machine pc memory).memory = memory := rfl

theorem optionT_mk_pure_some {α : Type} (value : α) :
    (OptionT.mk (PMF.pure (some value)) : OptionT PMF α) = pure value := rfl

/-- The initial stage-1 memory of the protocol. -/
def stage1Memory (parameter : Nat) : Memory :=
  { bits := fun stack => if stack = 0 then
      [false, false] ++ SimulatorProtocol.natural parameter ++ SimulatorProtocol.natural 1348634
    else [] }

/-- The request after the two tag bits. -/
def stage1Rest (parameter : Nat) : List Bool :=
  SimulatorProtocol.natural parameter ++ SimulatorProtocol.natural 1348634

theorem stage1Memory_request (parameter : Nat) :
    (stage1Memory parameter).bits 0 = false :: false :: stage1Rest parameter := by
  simp [stage1Memory, stage1Rest]

theorem stage1Start_stack3 (parameter : Nat) :
    (Top.afterTag (stage1Memory parameter) (stage1Rest parameter)).bits 3 = [] := by
  simp [Top.afterTag, stage1Memory]

/-- **The machine's stage-1 run.** -/
theorem planB_stage1_run (parameter : Nat) :
    @Simulator.run _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
        (Fintype.ofFinite _) (Classical.decEq _) (Classical.decEq _) planBSimulator
        planBSimulator.firstFuel ⟨0, { bits := fun stack =>
          if stack = 0 then ([false, false] ++ SimulatorProtocol.natural parameter ++
            SimulatorProtocol.natural 1348634) else [] }⟩ LazyOracle.empty =
      stage1Draws.map (Option.map fun draw =>
        (atPc planBSimulator Design.stage1Halt
          (stage1Final (Top.afterTag (stage1Memory parameter) (stage1Rest parameter)) draw),
          LazyOracle.empty, Design.firstFuel)) := by
  have run := @stage1_run_oracle _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
    (Fintype.ofFinite _) (Classical.decEq _) (Classical.decEq _)
    (@ordinal PlanB.FixedIndex (Fintype.ofFinite PlanB.FixedIndex))
    (@ordinal EncPRF.PermutationIndex (Fintype.ofFinite EncPRF.PermutationIndex))
    (stage1Memory parameter) (stage1Rest parameter) (stage1Memory_request parameter)
    LazyOracle.empty
  refine run.trans ?_
  rw [stage1_program_law, PMF.map_comp]
  congr 1
  funext drawn
  cases drawn <;> rfl

end Kernel

/-! ### The law -/

/-- **`Stage1Law`**: the machine's stage-1 kernel is the abstract stage 1 of `boundedSamplers`,
with the retained configuration read back by `extractSource`. -/
theorem stage1Law : Stage1Law := by
  intro field group parameter
  unfold machineKernels machineAbstract boundedKernels planBAbstractSimulator
  dsimp only
  rw [planB_stage1_run, optionT_mk_map, bind_assoc]
  simp only [pure_bind, atPc_memory,
    publicValue_final (Top.afterTag (stage1Memory parameter) (stage1Rest parameter))
      (stage1Start_stack3 parameter), optionT_mk_pure_some]
  rw [← optionT_mk_map, OptionT.run_mk, PMF.map_comp,
    show boundedSamplers.source = sourceLaw from rfl, sourceLaw, PMF.map_comp]
  congr 1
  funext drawn
  cases drawn with
  | none => rfl
  | some draw =>
      simp only [Function.comp_apply, Option.map_some, atPc_memory, extractSource_final]
      rfl



end

end Kriterion.ArgoMAC.PlanB.SimMachine
