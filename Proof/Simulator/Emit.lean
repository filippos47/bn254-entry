/-
The law of the bit emitter: `emitBits width` pushes the low `width` bits of `rAcc` onto the
response stack so that the stack reads them least significant first.
-/

import Proof.Simulator.Rejection

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine Blocks

section Emit

variable [BN254.FieldCertificate]

/-- The bits `offset, offset + 1, …, offset + count − 1` of a word, least significant first. -/
def bitRun (value : Word) (offset count : Nat) : List Bool :=
  List.ofFn fun index : Fin count => value.getLsbD (offset + index.val)

/-- One emission step at bit `bit`. -/
def emitStep (memory : Memory) (bit : Nat) : Memory :=
  pushOn (setReg (setReg memory rOut (word bit)) rFlag
    (Arithmetic.shiftRight.eval (memory.registers rAcc) (word bit))) 3
    ((memory.registers rAcc).getLsbD bit)

theorem memSem_emitOne (width index : Nat) (small : width ≤ 256) (memory : Memory) :
    (Prog.seq (cst rOut (width - 1 - index))
        (.seq (ar .shiftRight rFlag rAcc rOut) (.op (.pushBit 3 rFlag)))).memSem memory =
      PMF.pure (some (emitStep memory (width - 1 - index))) := by
  have bitSmall : width - 1 - index < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_le_of_lt (Nat.sub_le _ _)
      (lt_of_le_of_lt small (by norm_num)))
  simp only [cst, ar, Prog.memSem, Op.memSem, PMF.pure_bind, emitStep]
  congr 3
  simp only [setReg_registers, show rAcc ≠ rOut by decide, if_false, if_true,
    Arithmetic.eval, BitVec.getLsbD_ushiftRight, Nat.add_zero, word, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bitSmall]

/-- The memory after the first `steps` emission steps of a `width`-bit emitter. -/
def emitFold (memory : Memory) (width : Nat) : Nat → Memory
  | 0 => memory
  | steps + 1 => emitStep (emitFold memory width steps) (width - 1 - steps)

theorem memSem_emitSteps (width : Nat) (small : width ≤ 256) (memory : Memory) (steps : Nat) :
    (Prog.rep steps fun index => Prog.seq (cst rOut (width - 1 - index))
        (.seq (ar .shiftRight rFlag rAcc rOut) (.op (.pushBit 3 rFlag)))).memSem memory =
      PMF.pure (some (emitFold memory width steps)) := by
  induction steps with
  | zero => rw [Prog.rep]; rfl
  | succ steps ih =>
      rw [Prog.rep, memSem_seq, ih, PMF.pure_bind]
      exact memSem_emitOne width steps small _

omit [BN254.FieldCertificate] in
theorem emitStep_acc (memory : Memory) (bit : Nat) :
    (emitStep memory bit).registers rAcc = memory.registers rAcc := by
  simp [emitStep, pushOn, setReg_registers, show rAcc ≠ rFlag by decide,
    show rAcc ≠ rOut by decide]

omit [BN254.FieldCertificate] in
theorem emitFold_acc (memory : Memory) (width steps : Nat) :
    (emitFold memory width steps).registers rAcc = memory.registers rAcc := by
  induction steps with
  | zero => rfl
  | succ steps ih => rw [emitFold, emitStep_acc, ih]

omit [BN254.FieldCertificate] in
/-- **The emitted bits**: after `steps ≤ width` steps the response stack is the bits
`width − steps … width − 1` of `rAcc`, least significant first, on top of the old stack. -/
theorem emitFold_bits (memory : Memory) (width steps : Nat) (bounded : steps ≤ width) :
    (emitFold memory width steps).bits 3 =
      bitRun (memory.registers rAcc) (width - steps) steps ++ memory.bits 3 := by
  induction steps with
  | zero => simp [emitFold, bitRun]
  | succ steps ih =>
      rw [emitFold, emitStep, emitFold_acc]
      simp only [pushOn, setReg, Function.update_self]
      rw [ih (by omega), bitRun, bitRun, List.ofFn_succ]
      simp only [List.cons_append, Fin.val_zero, Fin.val_succ]
      congr 1
      · congr 1; omega
      · congr 1
        refine congrArg List.ofFn (funext fun index => ?_)
        congr 1
        omega

/-- **The emitter's law.** -/
theorem memSem_emitBits (width : Nat) (small : width ≤ 256) (memory : Memory) :
    (emitBits width).memSem memory = PMF.pure (some (emitFold memory width width)) :=
  memSem_emitSteps width small memory width

omit [BN254.FieldCertificate] in
theorem emitFold_stack3 (memory : Memory) (width : Nat) :
    (emitFold memory width width).bits 3 = bitRun (memory.registers rAcc) 0 width ++ memory.bits 3 := by
  rw [emitFold_bits memory width width le_rfl, Nat.sub_self]

omit [BN254.FieldCertificate] in
/-- **Decoding an emitted run**: the protocol's little-endian fold of the bits
`offset … offset + count − 1` of `value` is that bit field of `value`. -/
theorem bitRun_decode (value : Word) (count offset : Nat) :
    (bitRun value offset count).foldr (fun bit acc => bit.toNat + 2 * acc) 0 =
      value.toNat / 2 ^ offset % 2 ^ count := by
  induction count generalizing offset with
  | zero => simp [bitRun, Nat.mod_one]
  | succ count ih =>
      rw [bitRun, List.ofFn_succ, List.foldr_cons]
      have tail := ih (offset + 1)
      simp only [bitRun] at tail
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
      have shift : (fun index : Fin count => value.getLsbD (offset + (index.val + 1))) =
          fun index : Fin count => value.getLsbD (offset + 1 + index.val) := by
        funext index; congr 1; omega
      rw [shift, tail]
      have bit : (value.getLsbD offset).toNat = value.toNat / 2 ^ offset % 2 := by
        rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
        rcases Nat.mod_two_eq_zero_or_one (value.toNat / 2 ^ offset) with even | odd
        · rw [even]; rfl
        · rw [odd]; rfl
      rw [bit, show 2 ^ (count + 1) = 2 * 2 ^ count by ring, Nat.mod_mul, Nat.div_div_eq_div_mul,
        pow_succ]

end Emit

end Kriterion.ArgoMAC.PlanB.SimMachine
