/-
**The replay, the whitening pads** — one whitened label (`agree_whitenOne`) against the evaluator's
bit-`false` pad `padM keys c i false` (an EncPRF forward query at `k1`, xor `k2`), stored xor the
raw label at `whiteBase + position`.
-/

import Proof.Simulator.ReplayBridge

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-- What one whitened label leaves. -/
def WhitePost (memory : Memory) (position : Nat) (label : Block) (pad : Block) (after : Memory) : Prop :=
  after.ram = Function.update memory.ram (word (whiteBase + position)) (blockWord (pad ^^^ label)) ∧
    after.bits = memory.bits ∧ after.registers rInput = memory.registers rInput ∧
    after.registers rF = memory.registers rF

omit [FieldCertificate] in
theorem encodeBit_false_xor (key : Block) : encodeBit false ^^^ key = key := by
  simp [encodeBit]

/-- An EncPRF forward query instruction, its answer read as a block. -/
theorem Agree.queryEnc {β : Type} {Post : β → Memory → Prop} (index input first second : Register)
    (memory : Memory) (target : EncPRF.PermutationIndex) (block : Block)
    (decode : @queryFromRegisters PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
      (Fintype.ofFinite _) 2 (memory.registers index) (memory.registers input) =
        some (.encForward target block))
    (rest : Memory → FreeQuery Programs.Spec (Option Memory)) (next : Block → FreeQuery Programs.Spec β)
    (each : ∀ answer : Block, Agree Post (rest (writePair memory first second (blockWord answer, 0)))
      (next answer)) :
    Agree Post (SimMachine.bindOpt (rtree (.op (.query 2 index input first second)) memory) rest)
      (.query (.encForward target block) next) :=
  Agree.query 2 index input first second memory _ decode rest next fun answer => each answer

/-- **One whitened label.** -/
theorem agree_whitenOne (position : Nat) (index : EncPRF.PermutationIndex)
    (named : Replay.encIdx position = index) (memory : Memory) (keys : WhiteningKeys) (label : Block)
    (firstKey : memory.registers rInput = blockWord keys.first)
    (secondKey : memory.registers rF = blockWord keys.second)
    (labelCell : memory.ram (word (labelBase + position)) = blockWord label) :
    Agree (WhitePost memory position label) (rtree (Replay.whitenOne ordE0 position) memory)
      (Programs.padM keys index.1 index.2 false) := by
  unfold Replay.whitenOne Programs.padM Programs.askEnc
  rw [named, rtree_cst_seq]
  have decode : @queryFromRegisters PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
      (Fintype.ofFinite _) 2 ((setReg memory rIndex (word (ordE0 index))).registers rIndex)
      ((setReg memory rIndex (word (ordE0 index))).registers rInput) =
        some (.encForward index (encodeBit false ^^^ keys.first)) := by
    rw [reg_same, reg_ne _ _ _ _ (by decide), firstKey, query_enc, blockWord_block,
      encodeBit_false_xor]
  refine Agree.queryEnc rIndex rInput rFirst rSecond _ _ _ decode
    (rtree (.seq (ar .xor rFirst rFirst rF) (.seq (loadAt rA (labelBase + position))
      (.seq (ar .xor rFirst rFirst rA) (storeAt (whiteBase + position) rFirst))))) _
    fun answer => ?_
  rw [rtree_ar_val _ _ _ _ _ _ (blockWord answer) (blockWord keys.second)
      (by rw [writePair_registers]; simp (config := {decide := true}) only [reduceIte])
      (by rw [writePair_registers]; simp (config := {decide := true}) only [reduceIte];
          rw [reg_ne _ _ _ _ (by decide), secondKey]),
    eval_xor, blockWord_xor, rtree_loadAt_seq]
  simp only [setReg_ram, writePair_ram, labelCell]
  rw [rtree_ar_val _ _ _ _ _ _ (blockWord (answer ^^^ keys.second)) (blockWord label)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte])
      (reg_same _ _ _), eval_xor, blockWord_xor, rtree_storeAt _ _ _ (by decide), reg_same]
  refine .leaf ⟨?_, ?_, ?_, ?_⟩
  · simp only [storeRam_ram, setReg_ram, writePair_ram]
  · simp only [storeRam_bits, setReg_bits, writePair_bits]
  · simp only [storeRam_registers, setReg_registers, writePair_registers]
    simp (config := {decide := true}) only [reduceIte]
  · simp only [storeRam_registers, setReg_registers, writePair_registers]
    simp (config := {decide := true}) only [reduceIte]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
