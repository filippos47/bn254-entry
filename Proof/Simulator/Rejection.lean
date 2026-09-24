/-
The machine realisation of bounded rejection.

`attempt_law`: one constant-time attempt, read on the memory with the attempt scratch and the
test's junk registers cleared, is a uniform draw `c` followed by the rule "keep `c` iff nothing
was kept and `c` is accepted". `attempts_law`: `n` attempts from an empty sampler state are
`rejectLaw` (read through `rOut`/`rFlag`).
-/

import Proof.Simulator.Sampling

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine Blocks

/-! ### Register bookkeeping -/

/-- Zero a list of registers. -/
def clearRegs (memory : Memory) : List Register → Memory
  | [] => memory
  | register :: rest => setReg (clearRegs memory rest) register 0

theorem setReg_registers (memory : Memory) (target : Register) (value : Word) (index : Register) :
    (setReg memory target value).registers index =
      if index = target then value else memory.registers index := by
  simp only [setReg, Function.update_apply]

theorem setReg_same (memory : Memory) (target : Register) (first second : Word) :
    setReg (setReg memory target first) target second = setReg memory target second := by
  simp only [setReg, Function.update_idem]

theorem setReg_comm (memory : Memory) {one two : Register} (different : one ≠ two)
    (first second : Word) :
    setReg (setReg memory one first) two second = setReg (setReg memory two second) one first := by
  simp only [setReg, Function.update_comm different]

theorem clearRegs_registers (memory : Memory) (registers : List Register) (index : Register) :
    (clearRegs memory registers).registers index =
      if index ∈ registers then 0 else memory.registers index := by
  induction registers with
  | nil => simp [clearRegs]
  | cons register rest ih =>
      simp only [clearRegs, setReg_registers, ih, List.mem_cons]
      by_cases same : index = register <;> simp [same]

theorem clearRegs_other (memory : Memory) (registers : List Register) :
    (clearRegs memory registers).ram = memory.ram ∧ (clearRegs memory registers).bits = memory.bits := by
  induction registers with
  | nil => exact ⟨rfl, rfl⟩
  | cons register rest ih => exact ih

theorem memory_ext {first second : Memory} (bits : first.bits = second.bits)
    (registers : first.registers = second.registers) (ram : first.ram = second.ram) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Two memories agree after clearing iff they agree outside the cleared registers. -/
theorem clearRegs_eq_iff (first second : Memory) (registers : List Register) :
    clearRegs first registers = clearRegs second registers ↔
      first.ram = second.ram ∧ first.bits = second.bits ∧
        ∀ index, index ∉ registers → first.registers index = second.registers index := by
  constructor
  · intro equal
    refine ⟨?_, ?_, fun index outside => ?_⟩
    · rw [← (clearRegs_other first registers).1, equal, (clearRegs_other second registers).1]
    · rw [← (clearRegs_other first registers).2, equal, (clearRegs_other second registers).2]
    · have := congrArg (fun memory => memory.registers index) equal
      simpa [clearRegs_registers, outside] using this
  · rintro ⟨ram, bits, registers'⟩
    apply memory_ext
    · rw [(clearRegs_other first registers).2, (clearRegs_other second registers).2, bits]
    · funext index
      rw [clearRegs_registers, clearRegs_registers]
      split
      · rfl
      · exact registers' index (by assumption)
    · rw [(clearRegs_other first registers).1, (clearRegs_other second registers).1, ram]

theorem clearRegs_setReg_mem (memory : Memory) (registers : List Register) {target : Register}
    (inside : target ∈ registers) (value : Word) :
    clearRegs (setReg memory target value) registers = clearRegs memory registers := by
  rw [clearRegs_eq_iff]
  refine ⟨rfl, rfl, fun index outside => ?_⟩
  rw [setReg_registers, if_neg (fun same : index = target => outside (same ▸ inside))]

theorem clearRegs_setReg_not_mem (memory : Memory) (registers : List Register) {target : Register}
    (outside : target ∉ registers) (value : Word) :
    clearRegs (setReg memory target value) registers =
      setReg (clearRegs memory registers) target value := by
  apply memory_ext
  · exact (clearRegs_other _ _).2.trans ((clearRegs_other memory registers).2).symm
  · funext index
    rw [clearRegs_registers, setReg_registers, setReg_registers, clearRegs_registers]
    by_cases same : index = target
    · subst same; simp [outside]
    · simp [same]
  · exact (clearRegs_other _ _).1.trans ((clearRegs_other memory registers).1).symm

/-! ### Tests -/

section Tests

variable [BN254.FieldCertificate]

/-- A test block with junk registers: it sets `rBit` to the acceptance bit of `rAcc` and changes
nothing outside `junk` (besides `rBit`). -/
def IsTestJ (test : Prog) (accept : Nat → Bool) (junk : List Register) : Prop :=
  ∀ memory : Memory, ∃ result : Memory,
    test.memSem memory = PMF.pure (some (setReg result rBit
      (bitWord (accept (memory.registers rAcc).toNat)))) ∧
    clearRegs result junk = clearRegs memory junk

/-- The registers an attempt may leave as junk. -/
def attemptScratch (junk : List Register) : List Register := rAcc :: rBit :: rAddr :: rSel :: junk

/-- The sampler state after one more draw `value`: keep it iff nothing was kept yet and it is
accepted. -/
def keepMem (accept : Nat → Bool) (memory : Memory) (value : Nat) : Memory :=
  if memory.registers rFlag = 0 ∧ accept value = true then
    setReg (setReg memory rOut (BitVec.ofNat 256 value)) rFlag 1
  else memory

theorem bitWord_toNat (bit : Bool) : (bitWord bit).toNat = if bit then 1 else 0 := by
  cases bit <;> rfl

theorem less_bitWord (flag bit : Bool) :
    Arithmetic.less.eval (bitWord flag) (bitWord bit) = bitWord (!flag && bit) := by
  cases flag <;> cases bit <;> rfl

theorem wordMem_acc (memory : Memory) (width value : Nat) :
    (wordMem (setReg memory rAcc 0) width value).registers rAcc = BitVec.ofNat 256 value := by
  simp [wordMem, setReg_registers]

theorem wordMem_other (memory : Memory) (width value : Nat) (index : Register)
    (notAcc : index ≠ rAcc) (notBit : index ≠ rBit) :
    (wordMem (setReg memory rAcc 0) width value).registers index = memory.registers index := by
  simp [wordMem, setReg_registers, notAcc, notBit]

theorem wordMem_ram (memory : Memory) (width value : Nat) :
    (wordMem (setReg memory rAcc 0) width value).ram = memory.ram ∧
      (wordMem (setReg memory rAcc 0) width value).bits = memory.bits := ⟨rfl, rfl⟩

theorem keepMem_ram_bits {accept : Nat → Bool} {memory : Memory} {value : Nat} :
    (keepMem accept memory value).ram = memory.ram ∧ (keepMem accept memory value).bits = memory.bits := by
  unfold keepMem
  split <;> exact ⟨rfl, rfl⟩

omit [BN254.FieldCertificate] in
theorem keepMem_flag (accept : Nat → Bool) (memory : Memory) (value : Nat) (flag : Bool)
    (flagged : memory.registers rFlag = bitWord flag) :
    (keepMem accept memory value).registers rFlag = bitWord (flag || accept value) := by
  unfold keepMem
  have one : (1 : Word) ≠ 0 := by decide
  cases flag <;> cases accept value <;> simp [bitWord, setReg_registers, one, flagged]

omit [BN254.FieldCertificate] in
theorem keepMem_out (accept : Nat → Bool) (memory : Memory) (value : Nat) (flag : Bool)
    (flagged : memory.registers rFlag = bitWord flag) :
    (keepMem accept memory value).registers rOut =
      if !flag && accept value then BitVec.ofNat 256 value else memory.registers rOut := by
  unfold keepMem
  rw [flagged]
  have one : (1 : Word) ≠ 0 := by decide
  cases flag <;> cases accept value <;>
    simp [bitWord, setReg_registers, show rOut ≠ rFlag by decide, one]

omit [BN254.FieldCertificate] in
theorem keepMem_other (accept : Nat → Bool) (memory : Memory) (value : Nat) (index : Register)
    (notFlag : index ≠ rFlag) (notOut : index ≠ rOut) :
    (keepMem accept memory value).registers index = memory.registers index := by
  unfold keepMem
  split <;> simp [setReg_registers, notFlag, notOut]

/-- **One attempt**, read with the scratch cleared. -/
theorem attempt_law (width : Nat) (small : width ≤ 256) (test : Prog) (accept : Nat → Bool)
    (junk : List Register) (isTest : IsTestJ test accept junk) (keepOut : rOut ∉ junk)
    (keepFlag : rFlag ∉ junk) (keepAcc : rAcc ∉ junk) (memory : Memory) (flag : Bool)
    (flagged : memory.registers rFlag = bitWord flag) :
    ((attempt width test).memSem memory).map (Option.map fun final =>
        clearRegs final (attemptScratch junk)) =
      (PMF.uniformOfFintype (Fin (2 ^ width))).map fun value =>
        some (clearRegs (keepMem accept memory value.val) (attemptScratch junk)) := by
  unfold attempt
  simp only [Prog.memSem, memSem_sampleWord, PMF.bind_map, PMF.map_bind]
  rw [PMF.map]
  congr 1
  funext value
  simp only [Function.comp_apply]
  obtain ⟨result, testLaw, sameOutside⟩ := isTest (wordMem (setReg memory rAcc 0) width value.val)
  rw [testLaw, PMF.pure_bind]
  simp only [ar, Prog.memSem, Op.memSem, PMF.pure_bind, PMF.pure_map, Option.map_some]
  rw [clearRegs_eq_iff] at sameOutside
  obtain ⟨sameRam, sameBits, sameRegs⟩ := sameOutside
  have valueSmall : value.val < 2 ^ 256 :=
    lt_of_lt_of_le value.isLt (Nat.pow_le_pow_right (by norm_num) small)
  have accValue : (wordMem (setReg memory rAcc 0) width value.val).registers rAcc =
      BitVec.ofNat 256 value.val := wordMem_acc memory width value.val
  have accToNat : ((wordMem (setReg memory rAcc 0) width value.val).registers rAcc).toNat =
      value.val := by
    rw [accValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt valueSmall]
  rw [accToNat]
  -- the registers the tail of the attempt reads
  have resultAcc : result.registers rAcc = BitVec.ofNat 256 value.val := by
    rw [sameRegs rAcc keepAcc, accValue]
  have resultOut : result.registers rOut = memory.registers rOut := by
    rw [sameRegs rOut keepOut, wordMem_other memory width value.val rOut (by decide) (by decide)]
  have resultFlag : result.registers rFlag = bitWord flag := by
    rw [sameRegs rFlag keepFlag, wordMem_other memory width value.val rFlag (by decide) (by decide),
      flagged]
  congr 1
  congr 1
  have ne1 : rFlag ≠ rBit := by decide
  have ne2 : rAcc ≠ rSel := by decide
  have ne3 : rAcc ≠ rBit := by decide
  have ne4 : rOut ≠ rSel := by decide
  have ne5 : rOut ≠ rBit := by decide
  have ne6 : rAddr ≠ rOut := by decide
  have ne7 : rSel ≠ rAddr := by decide
  have ne8 : rSel ≠ rOut := by decide
  have ne9 : rFlag ≠ rSel := by decide
  have ne10 : rFlag ≠ rAddr := by decide
  have ne11 : rFlag ≠ rOut := by decide
  simp only [setReg_registers, if_pos rfl, if_neg ne1, if_neg ne2, if_neg ne3, if_neg ne4,
    if_neg ne5, if_neg ne6, if_neg ne7, if_neg ne8, if_neg ne9, if_neg ne10, if_neg ne11,
    resultAcc, resultOut, resultFlag, less_bitWord]
  rw [clearRegs_eq_iff]
  refine ⟨?_, ?_, fun index outside => ?_⟩
  · rw [keepMem_ram_bits.1]
    exact sameRam
  · rw [keepMem_ram_bits.2]
    exact sameBits
  · simp only [attemptScratch, List.mem_cons, not_or] at outside
    obtain ⟨notAcc, notBit, notAddr, notSel, notJunk⟩ := outside
    have base := sameRegs index notJunk
    rw [wordMem_other memory width value.val index notAcc notBit] at base
    by_cases isFlag : index = rFlag
    · subst isFlag
      rw [setReg_registers, if_pos rfl, keepMem_flag accept memory value.val flag flagged]
      simp (config := { decide := true }) only [setReg_registers, if_true, if_false]
      cases flag <;> cases accept value.val <;> rfl
    · rw [setReg_registers, if_neg isFlag]
      by_cases isOut : index = rOut
      · subst isOut
        rw [setReg_registers, if_pos rfl, keepMem_out accept memory value.val flag flagged]
        simp (config := { decide := true }) only [setReg_registers, if_true, if_false]
        cases flag <;> cases accept value.val <;>
          simp [Arithmetic.eval, bitWord, BitVec.toNat_ofNat]
      · rw [setReg_registers, if_neg isOut, setReg_registers, if_neg notAddr, setReg_registers,
          if_neg notAddr, setReg_registers, if_neg notSel, setReg_registers, if_neg notBit, base,
          keepMem_other accept memory value.val index isFlag isOut]

/-! ### Many attempts -/

omit [BN254.FieldCertificate] in
theorem clearRegs_idem (memory : Memory) (registers : List Register) :
    clearRegs (clearRegs memory registers) registers = clearRegs memory registers := by
  rw [clearRegs_eq_iff]
  refine ⟨(clearRegs_other _ _).1, (clearRegs_other _ _).2, fun index outside => ?_⟩
  rw [clearRegs_registers, if_neg outside]

omit [BN254.FieldCertificate] in
theorem clearRegs_keepMem (accept : Nat → Bool) (memory : Memory) (value : Nat)
    (registers : List Register) (keepOut : rOut ∉ registers) (keepFlag : rFlag ∉ registers) :
    clearRegs (keepMem accept memory value) registers =
      clearRegs (keepMem accept (clearRegs memory registers) value) registers := by
  have flagSame : (clearRegs memory registers).registers rFlag = memory.registers rFlag := by
    rw [clearRegs_registers, if_neg keepFlag]
  unfold keepMem
  rw [flagSame]
  split
  · rw [clearRegs_setReg_not_mem _ _ keepFlag, clearRegs_setReg_not_mem _ _ keepOut,
      clearRegs_setReg_not_mem _ _ keepFlag, clearRegs_setReg_not_mem _ _ keepOut, clearRegs_idem]
  · rw [clearRegs_idem]

/-- One attempt on a cleared state. -/
noncomputable def attemptStep (width : Nat) (accept : Nat → Bool) (registers : List Register)
    (memory : Memory) : PMF (Option Memory) :=
  (PMF.uniformOfFintype (Fin (2 ^ width))).map fun value =>
    some (clearRegs (keepMem accept memory value.val) registers)

/-- Kleisli extension of an abort-or-memory kernel. -/
noncomputable def kleisli (kernel : Memory → PMF (Option Memory)) :
    Option Memory → PMF (Option Memory)
  | none => PMF.pure none
  | some memory => kernel memory

/-- `count` attempts on a cleared state, appended at the end (the machine's `rep` order). -/
noncomputable def attemptsLaw (width : Nat) (accept : Nat → Bool) (registers : List Register) :
    Nat → Memory → PMF (Option Memory)
  | 0, memory => PMF.pure (some memory)
  | count + 1, memory =>
      (attemptsLaw width accept registers count memory).bind (kleisli (attemptStep width accept registers))

/-- The flag of every memory an attempt law can reach is `0` or `1`. -/
def FlagBit (memory : Memory) : Prop := ∃ flag, memory.registers rFlag = bitWord flag

omit [BN254.FieldCertificate] in
theorem flagBit_keep (accept : Nat → Bool) (memory : Memory) (value : Nat)
    (registers : List Register) (keepFlag : rFlag ∉ registers) (bit : FlagBit memory) :
    FlagBit (clearRegs (keepMem accept memory value) registers) := by
  obtain ⟨flag, flagged⟩ := bit
  refine ⟨flag || accept value, ?_⟩
  rw [clearRegs_registers, if_neg keepFlag, keepMem_flag accept memory value flag flagged]

theorem attemptsLaw_flag (width : Nat) (accept : Nat → Bool) (registers : List Register)
    (keepFlag : rFlag ∉ registers) (count : Nat) (memory : Memory) (bit : FlagBit memory) :
    ∀ final ∈ (attemptsLaw width accept registers count memory).support, ∀ reached ∈ final,
      FlagBit reached := by
  induction count with
  | zero =>
      intro final member reached inFinal
      simp only [attemptsLaw, PMF.support_pure, Set.mem_singleton_iff] at member
      subst member
      simp only [Option.mem_def, Option.some.injEq] at inFinal
      exact inFinal ▸ bit
  | succ count ih =>
      intro final member reached inFinal
      simp only [attemptsLaw, PMF.mem_support_bind_iff] at member
      obtain ⟨middle, middleIn, member⟩ := member
      cases middle with
      | none => simp [kleisli] at member; subst member; simp at inFinal
      | some middle =>
          simp only [kleisli, attemptStep, PMF.support_map, Set.mem_image] at member
          obtain ⟨value, _, same⟩ := member
          subst same
          simp only [Option.mem_def, Option.some.injEq] at inFinal
          subst inFinal
          exact flagBit_keep accept middle value.val registers keepFlag
            (ih middle middleIn middle rfl)

/-- **`count` attempts** on the machine are `attemptsLaw`, read with the scratch cleared. -/
theorem rep_attempt_law (width : Nat) (small : width ≤ 256) (test : Prog) (accept : Nat → Bool)
    (junk : List Register) (isTest : IsTestJ test accept junk) (keepOut : rOut ∉ junk)
    (keepFlag : rFlag ∉ junk) (keepAcc : rAcc ∉ junk) (count : Nat) (memory : Memory)
    (bit : FlagBit memory) :
    ((Prog.rep count fun _ => attempt width test).memSem memory).map
        (Option.map fun final => clearRegs final (attemptScratch junk)) =
      attemptsLaw width accept (attemptScratch junk) count (clearRegs memory (attemptScratch junk)) := by
  have outOut : rOut ∉ attemptScratch junk := by
    simp only [attemptScratch, List.mem_cons, not_or]; exact ⟨by decide, by decide, by decide, by decide, keepOut⟩
  have flagOut : rFlag ∉ attemptScratch junk := by
    simp only [attemptScratch, List.mem_cons, not_or]; exact ⟨by decide, by decide, by decide, by decide, keepFlag⟩
  induction count with
  | zero =>
      rw [Prog.rep]
      simp [Prog.memSem, attemptsLaw, PMF.pure_map]
  | succ count ih =>
      rw [Prog.rep]
      simp only [Prog.memSem, attemptsLaw]
      rw [← ih, PMF.bind_map, PMF.map_bind]
      apply PMF.bind_congr
      intro result member
      cases result with
      | none => simp [kleisli, PMF.pure_map]
      | some reached =>
          simp only [Function.comp_apply, Option.map_some, kleisli, attemptStep]
          have reachedIn : some (clearRegs reached (attemptScratch junk)) ∈
              (attemptsLaw width accept (attemptScratch junk) count
                (clearRegs memory (attemptScratch junk))).support := by
            rw [← ih, PMF.support_map]
            exact ⟨some reached, member, rfl⟩
          have clearedBit := attemptsLaw_flag width accept (attemptScratch junk) flagOut count
            (clearRegs memory (attemptScratch junk))
            (by obtain ⟨flag, flagged⟩ := bit
                exact ⟨flag, by rw [clearRegs_registers, if_neg flagOut, flagged]⟩)
            _ reachedIn _ rfl
          obtain ⟨flag, flagged⟩ := clearedBit
          rw [clearRegs_registers, if_neg flagOut] at flagged
          rw [attempt_law width small test accept junk isTest keepOut keepFlag keepAcc reached flag
            flagged]
          congr 1
          funext value
          rw [clearRegs_keepMem accept reached value.val _ outOut flagOut]

theorem kleisli_bind (first second : Memory → PMF (Option Memory)) (result : Option Memory) :
    (kleisli first result).bind (kleisli second) =
      kleisli (fun memory => (first memory).bind (kleisli second)) result := by
  cases result <;> simp [kleisli]

theorem kleisli_pure (result : Option Memory) :
    kleisli (fun memory => PMF.pure (some memory)) result = PMF.pure result := by
  cases result <;> rfl

/-- The attempts, peeled from the front. -/
theorem attemptsLaw_succ_front (width : Nat) (accept : Nat → Bool) (registers : List Register)
    (count : Nat) (memory : Memory) :
    attemptsLaw width accept registers (count + 1) memory =
      (attemptStep width accept registers memory).bind
        (kleisli (attemptsLaw width accept registers count)) := by
  induction count generalizing memory with
  | zero =>
      simp only [attemptsLaw, PMF.pure_bind, kleisli]
      conv_lhs => rw [← PMF.bind_pure (attemptStep width accept registers memory)]
      congr 1
      funext result
      exact (kleisli_pure result).symm
  | succ count ih =>
      conv_lhs => rw [attemptsLaw, ih memory, PMF.bind_bind]
      congr 1
      funext result
      rw [kleisli_bind]
      rfl

/-- The sampler state recording the kept draw. -/
def keptMem (registers : List Register) (memory : Memory) : Option Nat → Memory
  | none => memory
  | some value => clearRegs (setReg (setReg memory rOut (BitVec.ofNat 256 value)) rFlag 1) registers

theorem attemptsLaw_full (width : Nat) (accept : Nat → Bool) (registers : List Register)
    (count : Nat) (memory : Memory) (cleared : clearRegs memory registers = memory)
    (full : memory.registers rFlag = 1) :
    attemptsLaw width accept registers count memory = PMF.pure (some memory) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [attemptsLaw, ih, PMF.pure_bind]
      simp only [kleisli, attemptStep]
      have keep : ∀ value, keepMem accept memory value = memory := by
        intro value
        unfold keepMem
        rw [if_neg (by rw [full]; intro both; exact absurd both.1 (by decide))]
      simp only [keep, cleared]
      exact PMF.map_const _ _

/-- **Bounded rejection on the machine is `rejectLaw`**, read through the kept draw. -/
theorem attemptsLaw_eq_rejectLaw (width : Nat) (accept : Nat → Bool) (registers : List Register)
    (keepOut : rOut ∉ registers) (keepFlag : rFlag ∉ registers) (count : Nat) (memory : Memory)
    (cleared : clearRegs memory registers = memory) (empty : memory.registers rFlag = 0) :
    attemptsLaw width accept registers count memory =
      (rejectLaw width accept count).map fun kept => some (keptMem registers memory kept) := by
  induction count with
  | zero => simp [attemptsLaw, rejectLaw, keptMem, PMF.pure_map]
  | succ count ih =>
      rw [attemptsLaw_succ_front, rejectLaw, attemptStep, PMF.bind_map, PMF.map_bind]
      congr 1
      funext value
      simp only [Function.comp_apply, kleisli]
      unfold keepMem
      rw [if_congr (show (memory.registers rFlag = 0 ∧ accept value.val = true) ↔
        accept value.val = true by rw [empty]; simp) rfl rfl]
      split
      · rw [attemptsLaw_full, PMF.pure_map]
        · rfl
        · exact clearRegs_idem _ _
        · rw [clearRegs_registers, if_neg keepFlag, setReg_registers, if_pos rfl]
      · rw [cleared, ih]

/-! ### A field cell -/

omit [BN254.FieldCertificate] in
theorem clearRegs_cons (memory : Memory) (register : Register) (rest : List Register) :
    clearRegs (setReg memory register 0) rest = clearRegs memory (register :: rest) := by
  apply memory_ext
  · rw [(clearRegs_other _ _).2, (clearRegs_other _ _).2]; rfl
  · funext index
    simp only [clearRegs_registers, setReg_registers, List.mem_cons]
    by_cases same : index = register <;> by_cases inRest : index ∈ rest <;> simp [same, inRest]
  · rw [(clearRegs_other _ _).1, (clearRegs_other _ _).1]; rfl

theorem memSem_zeroRegs (registers : List Register) (memory : Memory) :
    (zeroRegs registers).memSem memory = PMF.pure (some (clearRegs memory registers)) := by
  induction registers generalizing memory with
  | nil => rfl
  | cons register rest ih =>
      simp only [zeroRegs, Prog.memSem, cst, Op.memSem, PMF.pure_bind, ih]
      rw [show word 0 = 0 from rfl, clearRegs_cons]

/-- The test `rAcc < bound` has junk `rAddr` only. -/
theorem isTest_testBelow (bound : Nat) (small : bound < 2 ^ 256) :
    IsTestJ (testBelow bound) (fun value => decide (value < bound)) [rAddr] := by
  intro memory
  refine ⟨setReg memory rAddr (word bound), ?_, clearRegs_setReg_mem _ _ (by simp) _⟩
  have toNatBound : (BitVec.ofNat 256 bound).toNat = bound := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  simp only [testBelow, Prog.memSem, cst, ar, Op.memSem, PMF.pure_bind]
  have value : Arithmetic.less.eval ((setReg memory rAddr (word bound)).registers rAcc)
      ((setReg memory rAddr (word bound)).registers rAddr) =
      bitWord (decide ((memory.registers rAcc).toNat < bound)) := by
    rw [setReg_registers, if_neg (show rAcc ≠ rAddr by decide), setReg_registers, if_pos rfl]
    unfold Arithmetic.eval word
    rw [toNatBound]
    by_cases below : (memory.registers rAcc).toNat < bound <;> simp [below, bitWord]
  rw [value]

/-- What follows the attempts in a cell: the success branch stores `rOut` at `address`, then
the scratch is cleared. -/
noncomputable def cellTail (address : Nat) (memory : Memory) : PMF (Option Memory) :=
  if memory.registers rFlag = 0 then PMF.pure none
  else PMF.pure (some (clearRegs (storeRam (setReg memory rAddr (word address)) (word address)
    (memory.registers rOut)) samplerScratch))

omit [BN254.FieldCertificate] in
theorem cellTail_clear (address : Nat) (memory : Memory) :
    cellTail address (clearRegs memory (attemptScratch [rAddr])) = cellTail address memory := by
  have flagSame : (clearRegs memory (attemptScratch [rAddr])).registers rFlag =
      memory.registers rFlag := by
    rw [clearRegs_registers, if_neg (by simp [attemptScratch]; decide)]
  have outSame : (clearRegs memory (attemptScratch [rAddr])).registers rOut =
      memory.registers rOut := by
    rw [clearRegs_registers, if_neg (by simp [attemptScratch]; decide)]
  unfold cellTail
  rw [flagSame, outSame]
  split
  · rfl
  · congr 2
    rw [clearRegs_eq_iff]
    refine ⟨?_, (clearRegs_other _ _).2, fun index outside => ?_⟩
    · simp only [storeRam, setReg, (clearRegs_other _ _).1]
    · simp only [storeRam, setReg_registers]
      split
      · rfl
      · rw [clearRegs_registers, if_neg]
        intro inside
        apply outside
        simp only [attemptScratch, List.mem_cons, List.mem_singleton] at inside
        simp only [samplerScratch, List.mem_cons]
        rcases inside with h | h | h | h | h | h <;> simp [h]

theorem memSem_cellContinuation (address : Nat) (memory : Memory) :
    (Prog.seq (.ite rFlag (storeAt address rOut) (.abort rSel)) (zeroRegs samplerScratch)).memSem
      memory = cellTail address memory := by
  simp only [Prog.memSem, memSem_zeroRegs, cellTail]
  split
  · simp
  · simp only [storeAt, cst, Prog.memSem, Op.memSem, PMF.pure_bind]
    rw [setReg_registers, if_pos rfl, setReg_registers, if_neg (show rOut ≠ rAddr by decide)]

theorem memSem_seq (first second : Prog) (memory : Memory) :
    (Prog.seq first second).memSem memory = (first.memSem memory).bind (kleisli second.memSem) := by
  simp only [Prog.memSem]
  congr 1

/-- **A field cell**: bounded rejection below `p`, stored at `address`, scratch cleared. -/
theorem memSem_fieldCell (address : Nat) (memory : Memory) :
    (Stage1.fieldCell address).memSem memory =
      (rejectLaw fieldWidth (fun value => decide (value < pNat)) attempts).map fun kept =>
        kept.map fun value =>
          clearRegs (storeRam memory (word address) (BitVec.ofNat 256 value)) samplerScratch := by
  have scratchJunk : attemptScratch [rAddr] = [rAcc, rBit, rAddr, rSel, rAddr] := rfl
  have outOut : rOut ∉ attemptScratch [rAddr] := by rw [scratchJunk]; decide
  have flagOut : rFlag ∉ attemptScratch [rAddr] := by rw [scratchJunk]; decide
  set start := setReg (setReg memory rOut (word 0)) rFlag (word 0) with startDef
  have startFlag : start.registers rFlag = bitWord false := by
    rw [startDef, setReg_registers, if_pos rfl]; rfl
  have shape : (Stage1.fieldCell address).memSem memory =
      ((Prog.rep attempts fun _ => attempt fieldWidth (testBelow pNat)).memSem start).bind
        (kleisli (cellTail address)) := by
    unfold Stage1.fieldCell bounded rejection
    rw [memSem_seq, memSem_seq, PMF.bind_bind]
    simp only [cst, Prog.memSem, Op.memSem, PMF.pure_bind]
    rw [startDef]
    have tailIs : cellTail address =
        (Prog.seq (.ite rFlag (storeAt address rOut) (.abort rSel)) (zeroRegs samplerScratch)).memSem :=
      funext fun final => (memSem_cellContinuation address final).symm
    rw [tailIs]
    congr 1
    funext result
    rw [kleisli_bind]
    congr 1
  rw [shape]
  have tailClear : ((Prog.rep attempts fun _ => attempt fieldWidth (testBelow pNat)).memSem start).bind
      (kleisli (cellTail address)) =
      (((Prog.rep attempts fun _ => attempt fieldWidth (testBelow pNat)).memSem start).map
        (Option.map fun final => clearRegs final (attemptScratch [rAddr]))).bind
        (kleisli (cellTail address)) := by
    rw [PMF.bind_map]
    congr 1
    funext result
    cases result with
    | none => rfl
    | some final => exact (cellTail_clear address final).symm
  rw [tailClear, rep_attempt_law fieldWidth (by unfold fieldWidth; omega) (testBelow pNat)
      (fun value => decide (value < pNat)) [rAddr] (isTest_testBelow pNat (by unfold pNat; norm_num))
      (by decide) (by decide) (by decide) attempts start ⟨false, startFlag⟩,
    attemptsLaw_eq_rejectLaw fieldWidth _ (attemptScratch [rAddr]) outOut flagOut attempts _
      (clearRegs_idem _ _) (by rw [clearRegs_registers, if_neg flagOut, startFlag]; rfl),
    PMF.bind_map]
  rw [PMF.map]
  congr 1
  funext kept
  cases kept with
  | none =>
      simp only [Function.comp_apply, kleisli, keptMem, cellTail]
      rw [if_pos (by rw [clearRegs_registers, if_neg flagOut, startFlag]; rfl)]
      rfl
  | some value =>
      simp only [Function.comp_apply, kleisli, keptMem, cellTail]
      have flagOne : (clearRegs (setReg (setReg (clearRegs start (attemptScratch [rAddr])) rOut
          (BitVec.ofNat 256 value)) rFlag 1) (attemptScratch [rAddr])).registers rFlag = 1 := by
        rw [clearRegs_registers, if_neg flagOut, setReg_registers, if_pos rfl]
      rw [if_neg (by rw [flagOne]; decide)]
      simp only [Option.map_some]
      refine congrArg (fun final => PMF.pure (some final)) ?_
      rw [clearRegs_eq_iff]
      refine ⟨?_, ?_, fun index outside => ?_⟩
      · simp only [storeRam, setReg, (clearRegs_other _ _).1, clearRegs_registers, if_neg outOut,
          Function.update_of_ne (show rOut ≠ rFlag by decide), Function.update_self]
        rw [startDef]
        rfl
      · simp only [storeRam, setReg, (clearRegs_other _ _).2]
        rw [startDef]
        rfl
      · have notOut : index ≠ rOut := fun same => outside (by rw [same]; decide)
        have notFlag : index ≠ rFlag := fun same => outside (by rw [same]; decide)
        have notScratch : index ∉ attemptScratch [rAddr] := by
          intro inside
          apply outside
          rw [scratchJunk] at inside
          simp only [samplerScratch, List.mem_cons] at inside ⊢
          rcases inside with h | h | h | h | h | h <;> simp [h]
        have notAddr : index ≠ rAddr := fun same => notScratch (by rw [same, scratchJunk]; decide)
        simp only [storeRam, setReg_registers, clearRegs_registers, notAddr, notOut, notFlag,
          notScratch, if_false, startDef]

end Tests

end Kriterion.ArgoMAC.PlanB.SimMachine
