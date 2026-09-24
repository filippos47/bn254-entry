/-
The two protocol runs of the Plan B simulator machine, reduced to the laws of its structured
stage programs.

* `stage1_run`: from the stage-1 request (`[false, false] ++ …` on stack `0`), the machine pops
  the tag, runs `Stage1.program` by its law and halts; a non-aborting run costs exactly
  `firstFuel`.
* `stage2_run`: from the stage-2 request (`[false, true] ++ …`), it pops the tag, runs the
  prefix, branches on `rFlag` (the output tag), runs the selected arm and halts, within
  `secondFuel`.

Both are exact `PMF` equalities; no fuel is ever exhausted on a non-aborting path.
-/

import Proof.Simulator.Placement

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine Design

section Halt

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- A halt stops the run, charging one. -/
theorem run_halt (machine : Simulator) {pc : Nat} (inside : pc ≤ machine.size)
    (code : codeAt machine pc = NInstr.halt.toInstr machine.size) (fuel : Nat)
    (memory : Memory) (oracle : OState FixedIndex EncIndex) :
    machine.run (fuel + 1) (atPc machine pc memory) oracle =
      PMF.pure (some (atPc machine pc memory, oracle, 1)) := by
  have located := code_atPc machine inside memory
  rw [code] at located
  have arith := arithmetic_code_of machine (atPc machine pc memory).pc.isLt located
  rw [run_succ]
  unfold Simulator.step
  rw [located]
  dsimp only [NInstr.toInstr]
  unfold BoundedMachine.step
  rw [arith]
  simp [PMF.pure_map, PMF.pure_bind]

/-- A pop of a known bit. -/
theorem run_pop_bit (machine : Simulator) {pc : Nat} (inside : pc ≤ machine.size)
    {stack : Fin 4} {empty onZero onOne : Nat}
    (code : codeAt machine pc = (NInstr.pop stack empty onZero onOne).toInstr machine.size)
    (fuel : Nat) (memory : Memory) (bit : Bool) (rest : List Bool)
    (top : memory.bits stack = bit :: rest) (oracle : OState FixedIndex EncIndex) :
    machine.run (fuel + 1) (atPc machine pc memory) oracle =
      (machine.run fuel (atPc machine (if bit then onOne else onZero)
          { memory with bits := Function.update memory.bits stack rest }) oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 1)) := by
  rw [run_succ, step_pop machine inside stack empty onZero onOne code memory oracle, PMF.pure_bind]
  simp only [top]

end Halt

namespace Top

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]
variable (ordF : PlanB.FixedIndex → Nat) (ordE : EncPRF.PermutationIndex → Nat)

/-- The memory after the tag pops. -/
def afterTag (memory : Memory) (rest : List Bool) : Memory :=
  { memory with bits := Function.update memory.bits 0 rest }

theorem atPc_zero (machine : Simulator) (memory : Memory) :
    (⟨0, memory⟩ : Configuration (machine.size + 1)) = atPc machine 0 memory := by
  simp only [atPc, label]
  congr

/-- **Stage 1.** -/
theorem stage1_run (memory : Memory) (rest : List Bool)
    (request : memory.bits 0 = false :: false :: rest) (oracle : OState FixedIndex EncIndex) :
    (machine ordF ordE).run Design.firstFuel ⟨0, memory⟩ oracle =
      (Stage1.program.sem (afterTag memory rest) oracle).bind fun result => match result with
        | none => PMF.pure none
        | some (final, updated) =>
            PMF.pure (some (atPc (machine ordF ordE) stage1Halt final, updated, Design.firstFuel)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout
  have size1 := stage1_size
  have cost1 := stage1_cost
  rw [atPc_zero, show Design.firstFuel = (stage1Cost + 1) + 1 + 1 by simp only [Design.firstFuel]; omega]
  rw [run_pop_bit _ (by rw [machine_size]; omega) (code_zero ordF ordE) _ memory false
    (false :: rest) request]
  have second : ({ memory with bits := Function.update memory.bits 0 (false :: rest) } : Memory).bits 0 =
      false :: rest := by simp
  rw [if_neg (by simp), run_pop_bit _ (by rw [machine_size]; omega) (code_one ordF ordE) _ _ false
    rest second]
  simp only [Bool.false_eq_true, if_false]
  have block := run_placed (FixedIndex := FixedIndex) (EncIndex := EncIndex) (machine ordF ordE)
    Stage1.program stage1Base (placed_stage1 ordF ordE)
  rw [size1, cost1, show stage1Base + stage1Size = stage1Halt by simp only [stage1Base]; omega]
    at block
  have memoryEq : ({ ({ memory with bits := Function.update memory.bits 0 (false :: rest) } : Memory)
      with bits := Function.update (Function.update memory.bits 0 (false :: rest)) 0 rest } : Memory)
      = afterTag memory rest := by
    simp [afterTag]
  rw [memoryEq, block, PMF.map_bind, PMF.map_bind]
  congr 1
  funext result
  cases result with
  | none => simp [after, PMF.pure_map]
  | some result =>
      rcases result with ⟨final, updated⟩
      simp only [after, Nat.add_sub_cancel_left]
      rw [if_pos (by omega), run_halt (fuel := 0) _ (by rw [machine_size]; omega)
        (code_stage1Halt ordF ordE)]
      simp only [PMF.pure_map, Option.map_some]
      rw [show 1 + stage1Cost + 1 + 1 = stage1Cost + 1 + 1 + 1 by omega]

theorem invalid_le_valid : invalidSize ≤ validCost := by
  rw [validCost_eq]; decide

/-- **Stage 2.** The prefix runs, then the arm selected by `rFlag` (the output tag), then halt. -/
theorem stage2_run (memory : Memory) (rest : List Bool)
    (request : memory.bits 0 = false :: true :: rest) (oracle : OState FixedIndex EncIndex) :
    (machine ordF ordE).run Design.secondFuel ⟨0, memory⟩ oracle =
      (Request.prefixProgram.sem (afterTag memory rest) oracle).bind fun result => match result with
        | none => PMF.pure none
        | some (middle, midOracle) =>
            if middle.registers rFlag = 0 then
              (Stage2.invalid.sem middle midOracle).bind fun final => match final with
                | none => PMF.pure none
                | some (last, updated) => PMF.pure (some (atPc (machine ordF ordE) invalidHalt last,
                    updated, 2 + prefixCost + 1 + invalidSize + 1))
            else
              (Stage2.valid ordF ordE |>.sem middle midOracle).bind fun final => match final with
                | none => PMF.pure none
                | some (last, updated) => PMF.pure (some (atPc (machine ordF ordE) validHalt last,
                    updated, Design.secondFuel)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := layout
  have sizeP := prefix_size
  have costP := prefix_cost
  have sizeI := invalid_size
  have costI := invalid_cost
  have sizeV := valid_size ordF ordE
  have costV := valid_cost ordF ordE
  have small := invalid_le_valid
  rw [atPc_zero, show Design.secondFuel = (prefixCost + (validCost + 1 + 1)) + 1 + 1 by
    simp only [Design.secondFuel]; omega]
  rw [run_pop_bit _ (by rw [machine_size]; omega) (code_zero ordF ordE) _ memory false
    (true :: rest) request]
  have second : ({ memory with bits := Function.update memory.bits 0 (true :: rest) } : Memory).bits 0 =
      true :: rest := by simp
  rw [if_neg (by simp), run_pop_bit _ (by rw [machine_size]; omega) (code_one ordF ordE) _ _ true
    rest second]
  simp only [if_true]
  have memoryEq : ({ ({ memory with bits := Function.update memory.bits 0 (true :: rest) } : Memory)
      with bits := Function.update (Function.update memory.bits 0 (true :: rest)) 0 rest } : Memory)
      = afterTag memory rest := by
    simp [afterTag]
  have block := run_placed (FixedIndex := FixedIndex) (EncIndex := EncIndex) (machine ordF ordE)
    Request.prefixProgram stage2Base (placed_prefix ordF ordE)
  rw [sizeP, costP, show stage2Base + prefixSize = branchAt by omega] at block
  rw [memoryEq, block, PMF.map_bind, PMF.map_bind]
  congr 1
  funext result
  cases result with
  | none => simp [after, PMF.pure_map]
  | some result =>
      rcases result with ⟨middle, midOracle⟩
      simp only [after, if_pos (show prefixCost ≤ prefixCost + (validCost + 1 + 1) by omega),
        Nat.add_sub_cancel_left]
      rw [run_branch _ (by rw [machine_size]; omega) rFlag invalidBase validBase
        (code_branch ordF ordE)]
      by_cases zero : middle.registers rFlag = 0
      · simp only [zero, if_true]
        have arm := run_placed (FixedIndex := FixedIndex) (EncIndex := EncIndex)
          (machine ordF ordE) Stage2.invalid invalidBase (placed_invalid ordF ordE)
        rw [sizeI, costI, show invalidBase + invalidSize = invalidHalt by omega] at arm
        rw [arm]
        simp only [PMF.map_bind]
        congr 1
        funext final
        cases final with
        | none => simp [after, PMF.pure_map]
        | some final =>
            rcases final with ⟨last, updated⟩
            simp only [after, if_pos (show invalidSize ≤ validCost + 1 by omega)]
            rw [show validCost + 1 - invalidSize = (validCost - invalidSize) + 1 by omega,
              run_halt _ (by rw [machine_size]; omega) (code_invalidHalt ordF ordE)]
            simp only [PMF.pure_map, Option.map_some]
            rw [show 1 + invalidSize + 1 + prefixCost + 1 + 1 = 2 + prefixCost + 1 + invalidSize + 1
              by omega]
      · simp only [zero, if_false]
        have arm := run_placed (FixedIndex := FixedIndex) (EncIndex := EncIndex)
          (machine ordF ordE) (Stage2.valid ordF ordE) validBase (placed_valid ordF ordE)
        rw [sizeV, costV, show validBase + validSize = validHalt by omega] at arm
        rw [arm]
        simp only [PMF.map_bind]
        congr 1
        funext final
        cases final with
        | none => simp [after, PMF.pure_map]
        | some final =>
            rcases final with ⟨last, updated⟩
            simp only [after, if_pos (show validCost ≤ validCost + 1 by omega),
              show validCost + 1 - validCost = 0 + 1 by omega]
            rw [run_halt _ (by rw [machine_size]; omega) (code_validHalt ordF ordE)]
            simp only [PMF.pure_map, Option.map_some]
            rw [show 1 + validCost + 1 + prefixCost + 1 + 1 =
              prefixCost + (validCost + 1 + 1) + 1 + 1 by omega]

end Top

end Kriterion.ArgoMAC.PlanB.SimMachine
