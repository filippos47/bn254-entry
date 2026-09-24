/-
Where the structured blocks sit in the assembled machine, and the machine's code at the few
hand-placed slots (the dispatcher, the halts, the output-tag branch).
-/

import Proof.Simulator.Machine
import Proof.Simulator.Semantics

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine Design

namespace Top

variable (ordF : FixedIndex → Nat) (ordE : EncPRF.PermutationIndex → Nat)

theorem codeAt_machine {pc : Nat} (inside : pc ≤ Design.size) :
    codeAt (machine ordF ordE) pc = (code ordF ordE pc).toInstr Design.size := by
  rw [codeAt_of_lt _ (Nat.lt_succ_of_le inside)]
  simp only [machine, assemble, Vector.getElem_ofFn]

/-- The layout facts, as linear arithmetic over the block sizes. -/
theorem layout :
    stage1Halt = 2 + stage1Size ∧ stage2Base = 3 + stage1Size ∧
      branchAt = 3 + stage1Size + prefixSize ∧ invalidBase = 4 + stage1Size + prefixSize ∧
      invalidHalt = 4 + stage1Size + prefixSize + invalidSize ∧
      validBase = 5 + stage1Size + prefixSize + invalidSize ∧
      validHalt = 5 + stage1Size + prefixSize + invalidSize + validSize ∧
      rejectAt = 6 + stage1Size + prefixSize + invalidSize + validSize ∧
      Design.size = 6 + stage1Size + prefixSize + invalidSize + validSize := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [stage1Halt, stage2Base, branchAt, invalidBase, invalidHalt, validBase, validHalt,
      rejectAt, Design.size, stage1Base] <;> omega

theorem placed_stage1 : Placed (machine ordF ordE) Stage1.program stage1Base := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout
  have size1 := stage1_size
  have base : stage1Base = 2 := rfl
  refine ⟨by rw [machine_size, size1]; omega, fun offset inside => ?_⟩
  rw [size1] at inside
  rw [codeAt_machine ordF ordE (by omega)]
  unfold code
  rw [if_neg (show stage1Base + offset ≠ 0 by omega), if_neg (show stage1Base + offset ≠ 1 by omega),
    if_pos (show stage1Base + offset < stage1Halt by omega),
    show stage1Base + offset - stage1Base = offset by omega]
  rfl

theorem placed_prefix : Placed (machine ordF ordE) Request.prefixProgram stage2Base := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout
  have sizeP := prefix_size
  refine ⟨by rw [machine_size, sizeP]; omega, fun offset inside => ?_⟩
  rw [sizeP] at inside
  rw [codeAt_machine ordF ordE (by omega)]
  unfold code
  rw [if_neg (show stage2Base + offset ≠ 0 by omega), if_neg (show stage2Base + offset ≠ 1 by omega),
    if_neg (show ¬ stage2Base + offset < stage1Halt by omega),
    if_neg (show stage2Base + offset ≠ stage1Halt by omega),
    if_pos (show stage2Base + offset < branchAt by omega),
    show stage2Base + offset - stage2Base = offset by omega]
  rfl

theorem placed_invalid : Placed (machine ordF ordE) Stage2.invalid invalidBase := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout
  have sizeI := invalid_size
  refine ⟨by rw [machine_size, sizeI]; omega, fun offset inside => ?_⟩
  rw [sizeI] at inside
  rw [codeAt_machine ordF ordE (by omega)]
  unfold code
  rw [if_neg (show invalidBase + offset ≠ 0 by omega),
    if_neg (show invalidBase + offset ≠ 1 by omega),
    if_neg (show ¬ invalidBase + offset < stage1Halt by omega),
    if_neg (show invalidBase + offset ≠ stage1Halt by omega),
    if_neg (show ¬ invalidBase + offset < branchAt by omega),
    if_neg (show invalidBase + offset ≠ branchAt by omega),
    if_pos (show invalidBase + offset < invalidHalt by omega),
    show invalidBase + offset - invalidBase = offset by omega]
  rfl

theorem placed_valid : Placed (machine ordF ordE) (Stage2.valid ordF ordE) validBase := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout
  have sizeV := valid_size ordF ordE
  refine ⟨by rw [machine_size, sizeV]; omega, fun offset inside => ?_⟩
  rw [sizeV] at inside
  rw [codeAt_machine ordF ordE (by omega)]
  unfold code
  rw [if_neg (show validBase + offset ≠ 0 by omega), if_neg (show validBase + offset ≠ 1 by omega),
    if_neg (show ¬ validBase + offset < stage1Halt by omega),
    if_neg (show validBase + offset ≠ stage1Halt by omega),
    if_neg (show ¬ validBase + offset < branchAt by omega),
    if_neg (show validBase + offset ≠ branchAt by omega),
    if_neg (show ¬ validBase + offset < invalidHalt by omega),
    if_neg (show validBase + offset ≠ invalidHalt by omega),
    if_pos (show validBase + offset < validHalt by omega),
    show validBase + offset - validBase = offset by omega]
  rfl

/-! ### The hand-placed slots -/

theorem code_zero : codeAt (machine ordF ordE) 0 =
    (NInstr.pop 0 rejectAt 1 rejectAt).toInstr Design.size := by
  rw [codeAt_machine ordF ordE (by rw [layout.2.2.2.2.2.2.2.2]; omega)]
  unfold code
  rw [if_pos rfl]

theorem code_one : codeAt (machine ordF ordE) 1 =
    (NInstr.pop 0 rejectAt stage1Base stage2Base).toInstr Design.size := by
  rw [codeAt_machine ordF ordE (by rw [layout.2.2.2.2.2.2.2.2]; omega)]
  unfold code
  rw [if_neg (show (1 : Nat) ≠ 0 by omega), if_pos rfl]

theorem code_stage1Halt : codeAt (machine ordF ordE) stage1Halt = NInstr.halt.toInstr Design.size := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout
  rw [codeAt_machine ordF ordE (by omega)]
  unfold code
  rw [if_neg (show stage1Halt ≠ 0 by omega), if_neg (show stage1Halt ≠ 1 by omega),
    if_neg (show ¬ stage1Halt < stage1Halt by omega), if_pos rfl]

theorem code_branch : codeAt (machine ordF ordE) branchAt =
    (NInstr.branch rFlag invalidBase validBase).toInstr Design.size := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout
  rw [codeAt_machine ordF ordE (by omega)]
  unfold code
  rw [if_neg (show branchAt ≠ 0 by omega), if_neg (show branchAt ≠ 1 by omega),
    if_neg (show ¬ branchAt < stage1Halt by omega), if_neg (show branchAt ≠ stage1Halt by omega),
    if_neg (show ¬ branchAt < branchAt by omega), if_pos rfl]

theorem code_invalidHalt : codeAt (machine ordF ordE) invalidHalt =
    NInstr.halt.toInstr Design.size := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout
  rw [codeAt_machine ordF ordE (by omega)]
  unfold code
  rw [if_neg (show invalidHalt ≠ 0 by omega), if_neg (show invalidHalt ≠ 1 by omega),
    if_neg (show ¬ invalidHalt < stage1Halt by omega),
    if_neg (show invalidHalt ≠ stage1Halt by omega),
    if_neg (show ¬ invalidHalt < branchAt by omega), if_neg (show invalidHalt ≠ branchAt by omega),
    if_neg (show ¬ invalidHalt < invalidHalt by omega), if_pos rfl]

theorem code_validHalt : codeAt (machine ordF ordE) validHalt =
    NInstr.halt.toInstr Design.size := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout
  rw [codeAt_machine ordF ordE (by omega)]
  unfold code
  rw [if_neg (show validHalt ≠ 0 by omega), if_neg (show validHalt ≠ 1 by omega),
    if_neg (show ¬ validHalt < stage1Halt by omega), if_neg (show validHalt ≠ stage1Halt by omega),
    if_neg (show ¬ validHalt < branchAt by omega), if_neg (show validHalt ≠ branchAt by omega),
    if_neg (show ¬ validHalt < invalidHalt by omega),
    if_neg (show validHalt ≠ invalidHalt by omega),
    if_neg (show ¬ validHalt < validHalt by omega)]

end Top

end Kriterion.ArgoMAC.PlanB.SimMachine
