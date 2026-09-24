/-
**Stage 2, the invalid arm** (`f_k u = none`): the machine's stage-2 kernel returns the selected
labels and the incoming oracle state, with no oracle instruction, exactly as P3's abstract stage 2
does (`stage2_none`).

* `memSem_emitLabels`: `Request.emitLabels` pushes the `508` label runs on stack `3`;
* `words_labelRuns_ram`: the protocol parse of those runs is the label vector;
* `selectedLabels_extract`: the label vector the prefix selects is
  `Lamport.selectedLabels ((extractSource memory).key.encode (BitInput.ofAffine u))`.
-/

import Proof.Simulator.Stage2Request

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

section Labels

variable [FieldCertificate]

/-- The `508` label runs, label `0` on top. -/
def labelRuns (ram : Word → Word) : List Bool :=
  (List.ofFn fun index : Fin 508 => bitRun (ram (word (labelBase + index.val))) 0 128).flatten

/-- The labels as blocks. -/
def labelVector (ram : Word → Word) : Vector Block 508 :=
  Vector.ofFn fun index : Fin 508 => BitVec.ofNat 128 (ram (word (labelBase + index.val))).toNat

theorem emitLabels_eq : Request.emitLabels =
    Prog.rep 508 fun index => emitWord (labelBase + 507 - index) 128 := by
  unfold Request.emitLabels labelCount
  rfl

/-- **The label emission.** -/
theorem memSem_emitLabels (memory : Memory) :
    ∃ after, Request.emitLabels.memSem memory = PMF.pure (some after) ∧
      after.ram = memory.ram ∧ after.bits 3 = labelRuns memory.ram ++ memory.bits 3 ∧
      ∀ stack, stack ≠ 3 → after.bits stack = memory.bits stack := by
  obtain ⟨after, run, emits⟩ := memSem_emitBlock 128 (by norm_num) (labelBase + 507) 508
    (by unfold labelBase; omega) memory
  refine ⟨after, by rw [emitLabels_eq]; exact run, emits.1, ?_, emits.2.2⟩
  rw [emits.2.1]
  congr 2

theorem labelRuns_words (ram : Word → Word) :
    SimulatorProtocol.words 128 508 (labelRuns ram) = some (labelVector ram) :=
  words_labelRuns 508 fun index => ram (word (labelBase + index.val))

omit [FieldCertificate] in
theorem testBit_shift (value index : Nat) :
    (value >>> index) % 2 = if value.testBit index then 1 else 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (value / 2 ^ index) with h | h <;> simp [h]

theorem selectedLabel_extract (memory : Memory) (input : AffineInput) (index : Nat)
    (bound : index < 508) :
    (Lamport.selectedLabels ((extractSource memory).key.encode (BitInput.ofAffine input)))[index] =
      BitVec.ofNat 128 (memory.ram (word (keyBase + 2 * index +
        inputBit input.x.val input.y.val index))).toNat := by
  have xSmall : input.x.val < 2 ^ 254 :=
    lt_trans input.x.val_lt (by unfold baseFieldModulus; norm_num)
  have ySmall : input.y.val < 2 ^ 254 :=
    lt_trans input.y.val_lt (by unfold baseFieldModulus; norm_num)
  simp only [Lamport.selectedLabels, Vector.getElem_ofFn, InputMacKey.encode, encodeCoordinate,
    BitInput.ofAffine, extractSource, sourceOfDraws, Vector.get_ofFn, BitAdaptor.encode,
    ArgoMAC.coordinateBits, BitVec.getLsb, inputBit, testBit_shift]
  have xMod : (BitVec.ofNat coordinateBitCount input.x.val).toNat = input.x.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt xSmall]
  have yMod : (BitVec.ofNat coordinateBitCount input.y.val).toNat = input.y.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ySmall]
  rw [xMod, yMod]
  split
  · by_cases bit : input.x.val.testBit index
    · simp [bit, Nat.add_assoc]
    · simp [bit]
  · rename_i high
    have shifted : index % 254 = index - 254 := by omega
    have keyIndex : 2 * (254 + (index - 254)) = 2 * index := by omega
    by_cases bit : input.y.val.testBit (index - 254)
    · simp [bit, shifted, keyIndex, Nat.add_assoc]
    · simp [bit, shifted, keyIndex]

/-- **The selected labels, read through `extractSource`.** -/
theorem selectedLabels_extract (memory : Memory) (input : AffineInput) :
    Lamport.selectedLabels ((extractSource memory).key.encode (BitInput.ofAffine input)) =
      Vector.ofFn fun index : Fin 508 => BitVec.ofNat 128 (memory.ram
        (word (keyBase + 2 * index.val + inputBit input.x.val input.y.val index.val))).toNat := by
  apply Vector.ext
  intro index bound
  rw [selectedLabel_extract memory input index bound]
  simp only [Vector.getElem_ofFn]

end Labels

/-! ### The stage-2 run -/

section Run

variable [FieldCertificate]

/-- The memory stage 2 starts from: the retained configuration with the request on stack `0`
and an empty response stack. -/
def stage2Memory (memory : Memory) (input : AffineInput) (output : Option Point) : Memory :=
  { bits := Function.update (Function.update memory.bits 0
      ([false, true] ++ SimulatorProtocol.affine input ++ SimulatorProtocol.output output)) 3 [],
    registers := memory.registers, ram := memory.ram }

/-- The request after the two tag bits. -/
def stage2Rest (input : AffineInput) (output : Option Point) : List Bool :=
  SimulatorProtocol.affine input ++ SimulatorProtocol.output output

theorem stage2Memory_request (memory : Memory) (input : AffineInput) (output : Option Point) :
    (stage2Memory memory input output).bits 0 = false :: true :: stage2Rest input output := by
  simp [stage2Memory, stage2Rest]

/-- **The machine's stage-2 run**, split at the output tag (`stage2_run_split` at the
`planBSimulator` instances). -/
theorem planB_stage2_run (memory : Memory) (input : AffineInput) (output : Option Point)
    (oracle : LazyOracle.State PlanB.FixedIndex EncPRF.PermutationIndex) :
    @Simulator.run _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
        (Fintype.ofFinite _) (Classical.decEq _) (Classical.decEq _) planBSimulator
        planBSimulator.secondFuel ⟨0, stage2Memory memory input output⟩ oracle =
      (Request.prefixProgram.memSem (Top.afterTag (stage2Memory memory input output)
          (stage2Rest input output))).bind fun result => match result with
        | none => PMF.pure none
        | some middle =>
            if middle.registers rFlag = 0 then
              (Stage2.invalid.memSem middle).map fun final => final.map fun last =>
                (atPc planBSimulator Design.invalidHalt last, oracle,
                  2 + Design.prefixCost + 1 + Design.invalidSize + 1)
            else
              (@Prog.sem _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
                  (Fintype.ofFinite _) (Classical.decEq _) (Classical.decEq _)
                  (Stage2.valid (@ordinal PlanB.FixedIndex (Fintype.ofFinite PlanB.FixedIndex))
                    (@ordinal EncPRF.PermutationIndex (Fintype.ofFinite EncPRF.PermutationIndex)))
                  middle oracle).bind fun final => match final with
                | none => PMF.pure none
                | some (last, updated) =>
                    PMF.pure (some (atPc planBSimulator Design.validHalt last, updated,
                      Design.secondFuel)) := by
  refine (@stage2_run_split _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
    (Fintype.ofFinite _) (Classical.decEq _) (Classical.decEq _)
    (@ordinal PlanB.FixedIndex (Fintype.ofFinite PlanB.FixedIndex))
    (@ordinal EncPRF.PermutationIndex (Fintype.ofFinite EncPRF.PermutationIndex))
    (stage2Memory memory input output) (stage2Rest input output)
    (stage2Memory_request memory input output) oracle).trans ?_
  congr 1
  funext result
  cases result with
  | none => rfl
  | some middle =>
      dsimp only
      split
      · rfl
      · congr 1
        funext final
        rcases final with _ | ⟨last, updated⟩
        · rfl
        · rfl

theorem affine_lsbs (input : AffineInput) :
    SimulatorProtocol.affine input = lsbs 254 input.x.val ++ lsbs 254 input.y.val := by
  simp only [SimulatorProtocol.affine, bits_eq_lsbs]

theorem coord_small (value : BaseField) : value.val < 2 ^ 254 :=
  lt_trans value.val_lt (by unfold baseFieldModulus; norm_num)

theorem afterTag_request (memory : Memory) (input : AffineInput) (output : Option Point) :
    (Top.afterTag (stage2Memory memory input output) (stage2Rest input output)).bits 0 =
      lsbs 254 input.x.val ++ (lsbs 254 input.y.val ++ SimulatorProtocol.output output) := by
  simp [Top.afterTag, stage2Rest, affine_lsbs]

theorem afterTag_response (memory : Memory) (input : AffineInput) (output : Option Point) :
    (Top.afterTag (stage2Memory memory input output) (stage2Rest input output)).bits 3 = [] := by
  simp [Top.afterTag, stage2Memory]

theorem afterTag_ram (memory : Memory) (input : AffineInput) (output : Option Point) :
    (Top.afterTag (stage2Memory memory input output) (stage2Rest input output)).ram = memory.ram :=
  rfl

/-- **Stage 2 on an undefined output**: the selected labels and the incoming oracle state. -/
theorem stage2_none (initial : Configuration (planBSimulator.size + 1)) (input : AffineInput)
    (oracle : LazyOracle.State PlanB.FixedIndex EncPRF.PermutationIndex) :
    (machineKernels).stage2 initial input none oracle =
      PMF.pure (some (Lamport.selectedLabels ((extractSource initial.memory).key.encode
        (BitInput.ofAffine input)), oracle)) := by
  set start := Top.afterTag (stage2Memory initial.memory input none) (stage2Rest input none)
    with startDef
  obtain ⟨middle, runPrefix, bitsPrefix, labels, _, flag⟩ := memSem_prefix start
    input.x.val input.y.val (coord_small _) (coord_small _) [false, false] false false 0 0
    (by simp [OutBits]) (afterTag_request initial.memory input none)
  obtain ⟨last, runEmit, _, bitsEmit, _⟩ := memSem_emitLabels middle
  have flagZero : middle.registers rFlag = 0 := by rw [flag]; rfl
  have response : last.bits 3 = labelRuns middle.ram := by
    rw [bitsEmit, bitsPrefix, Function.update_of_ne (by decide), startDef, afterTag_response,
      List.append_nil]
  have vector : labelVector middle.ram = Lamport.selectedLabels
      ((extractSource initial.memory).key.encode (BitInput.ofAffine input)) := by
    rw [selectedLabels_extract]
    unfold labelVector
    congr 1
    funext index
    rw [labels index.val index.isLt, startDef, afterTag_ram]
  unfold machineKernels machineAbstract
  dsimp only
  have run := planB_stage2_run initial.memory input none oracle
  rw [← startDef, runPrefix, PMF.pure_bind] at run
  simp only [flagZero, if_true, Stage2.invalid, runEmit, PMF.pure_map, Option.map_some] at run
  rw [show (⟨Function.update (Function.update initial.memory.bits 0
      ([false, true] ++ SimulatorProtocol.affine input ++ SimulatorProtocol.output none)) 3 [],
      initial.memory.registers, initial.memory.ram⟩ : Memory) =
      stage2Memory initial.memory input none from rfl, run]
  simp only [optionT_mk_pure_some, pure_bind, atPc_memory, response, labelRuns_words, vector]
  rfl

/-- **The invalid arm of `Stage2Law`**: on an undefined output the machine's stage 2 is the
abstract stage 2 of the extracted source, for every retained configuration. -/
theorem stage2Law_none [GroupCertificate] (initial : Configuration (planBSimulator.size + 1))
    (input : AffineInput) (oracle : LazyOracle.State PlanB.FixedIndex EncPRF.PermutationIndex) :
    (boundedKernels).stage2 (extractSource initial.memory) input none oracle =
      (machineKernels).stage2 initial input none oracle := by
  rw [stage2_none]
  rfl

end Run

end

end Kriterion.ArgoMAC.PlanB.SimMachine
