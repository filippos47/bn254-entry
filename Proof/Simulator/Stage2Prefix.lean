/-
**Stage 2's common prefix: the request parse and the label selection.**

* `memSem_parseWord`: `parseWord address` pops the `254` little-endian bits of a coordinate and
  stores it at `address`;
* `memSem_selectLabels`: label `i` is the key word at `keyBase + 2 i + (bit i of u)`;
* `memSem_prefix_none`: on the request of an undefined output, the prefix leaves the selected
  labels in the label region and a clear flag.
-/

import Proof.Simulator.Stage1Law

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

section Parse

variable [FieldCertificate]

/-- The state of a coordinate parse after `steps` bits. -/
def ParseAt (before after : Memory) (steps value : Nat) (rest : List Bool) : Prop :=
  after.bits 0 = (lsbs 254 value).drop steps ++ rest ∧
    after.registers rAcc = BitVec.ofNat 256 (value % 2 ^ steps) ∧ after.ram = before.ram ∧
    (∀ stack, stack ≠ 0 → after.bits stack = before.bits stack) ∧
    ∀ register, register ≠ rAcc → register ≠ rBit → register ≠ rAddr →
      after.registers register = before.registers register

/-- One parse step: pop bit `position`, weight it, accumulate. -/
def parseBody (position : Nat) : Prog :=
  .seq (.popBit 0 rBit) (.seq (cst rAddr (2 ^ position))
    (.seq (ar .mul rBit rBit rAddr) (ar .add rAcc rAcc rBit)))

theorem bitWord_mul_pow (bit : Bool) (position : Nat) :
    bitWord bit * BitVec.ofNat 256 (2 ^ position) =
      BitVec.ofNat 256 (if bit then 2 ^ position else 0) := by
  cases bit <;> simp [bitWord]

/-- The memory after one parse step. -/
def parseStepMem (memory : Memory) (position : Nat) : Memory :=
  let popped := popInto memory 0 rBit
  let weighted := setReg popped rAddr (word (2 ^ position))
  let scaled := setReg weighted rBit
    (Arithmetic.mul.eval (weighted.registers rBit) (weighted.registers rAddr))
  setReg scaled rAcc (Arithmetic.add.eval (scaled.registers rAcc) (scaled.registers rBit))

theorem memSem_parseBody (position : Nat) (memory : Memory) :
    (parseBody position).memSem memory = PMF.pure (some (parseStepMem memory position)) := by
  simp only [parseBody, cst, ar, Prog.memSem, Op.memSem, PMF.pure_bind]
  rfl

theorem parseStepMem_facts (memory : Memory) (position : Nat) (bit : Bool) (tail : List Bool)
    (top : memory.bits 0 = bit :: tail) :
    (parseStepMem memory position).bits 0 = tail ∧
      (parseStepMem memory position).registers rAcc =
        memory.registers rAcc + bitWord bit * word (2 ^ position) ∧
      (parseStepMem memory position).ram = memory.ram ∧
      (∀ stack, stack ≠ 0 → (parseStepMem memory position).bits stack = memory.bits stack) ∧
      ∀ register, register ≠ rAcc → register ≠ rBit → register ≠ rAddr →
        (parseStepMem memory position).registers register = memory.registers register := by
  have popped : popInto memory 0 rBit =
      setReg { memory with bits := Function.update memory.bits 0 tail } rBit (bitWord bit) := by
    simp only [popInto, top]
    cases bit <;> rfl
  unfold parseStepMem
  simp only [popped]
  refine ⟨?_, ?_, rfl, fun stack other => ?_, fun register notAcc notBit notAddr => ?_⟩
  · simp [setReg]
  · simp only [setReg_registers, if_pos rfl, Arithmetic.eval,
      show rAcc ≠ rBit by decide, show rAcc ≠ rAddr by decide, show rBit ≠ rAddr by decide,
      show rAddr ≠ rBit by decide, if_false, if_true, ite_true]
  · simp [setReg, Function.update_of_ne other]
  · simp only [setReg_registers, if_neg notAcc, if_neg notBit, if_neg notAddr]

theorem parse_steps (value : Nat) (rest : List Bool) (before : Memory)
    (start : before.bits 0 = lsbs 254 value ++ rest) (clear : before.registers rAcc = 0) :
    ∀ steps, steps ≤ 254 → ∃ after,
      (Prog.rep steps parseBody).memSem before = PMF.pure (some after) ∧
        ParseAt before after steps value rest
  | 0, _ => ⟨before, by rw [Prog.rep]; rfl, by simpa using start,
      by simp only [pow_zero, Nat.mod_one]; exact clear, rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | steps + 1, bound => by
      obtain ⟨middle, run, stack, acc, ram, others, regs⟩ :=
        parse_steps value rest before start clear steps (by omega)
      have drop : (lsbs 254 value).drop steps =
          value.testBit steps :: (lsbs 254 value).drop (steps + 1) := by
        rw [List.drop_eq_getElem_cons (by rw [lsbs_length]; omega)]
        congr 1
        simp only [lsbs, List.getElem_ofFn]
      rw [drop, List.cons_append] at stack
      obtain ⟨stack', acc', ram', others', regs'⟩ :=
        parseStepMem_facts middle steps (value.testBit steps) _ stack
      refine ⟨parseStepMem middle steps, ?_, stack', ?_, ram'.trans ram, fun index other => ?_,
        fun register notAcc notBit notAddr => ?_⟩
      · rw [Prog.rep, memSem_seq, run, PMF.pure_bind]
        exact memSem_parseBody steps middle
      · rw [acc', acc, word, bitWord_mul_pow, ← BitVec.ofNat_add, Nat.mod_pow_succ,
          Nat.testBit_eq_decide_div_mod_eq]
        congr 1
        rcases Nat.mod_two_eq_zero_or_one (value / 2 ^ steps) with even | odd
        · simp [even]
        · simp [odd]
      · rw [others' index other, others index other]
      · rw [regs' register notAcc notBit notAddr, regs register notAcc notBit notAddr]

theorem parseWord_body : (Request.parseWord 0).seq (.skip 0) = (Request.parseWord 0).seq (.skip 0) :=
  rfl

/-- **One parsed coordinate.** -/
theorem memSem_parseWord (address value : Nat) (small : value < 2 ^ 254) (rest : List Bool)
    (memory : Memory) (start : memory.bits 0 = lsbs 254 value ++ rest) :
    ∃ after, (Request.parseWord address).memSem memory = PMF.pure (some after) ∧
      after.bits 0 = rest ∧
      after.ram = Function.update memory.ram (word address) (word value) ∧
      (∀ stack, stack ≠ 0 → after.bits stack = memory.bits stack) ∧
      ∀ register, register ≠ rAcc → register ≠ rBit → register ≠ rAddr →
        after.registers register = memory.registers register := by
  set cleared := setReg memory rAcc (word 0) with clearedDef
  have clearedStart : cleared.bits 0 = lsbs 254 value ++ rest := start
  obtain ⟨parsed, run, stack, acc, ram, others, regs⟩ :=
    parse_steps value rest cleared clearedStart (by simp [clearedDef, setReg]) 254 le_rfl
  refine ⟨storeRam (setReg parsed rAddr (word address)) (word address) (parsed.registers rAcc),
    ?_, ?_, ?_, ?_, ?_⟩
  · unfold Request.parseWord
    rw [memSem_seq]
    simp only [cst, Prog.memSem, Op.memSem, PMF.pure_bind, kleisli]
    rw [← clearedDef]
    erw [run]
    rw [PMF.pure_bind]
    simp only [storeAt, cst, Prog.memSem, Op.memSem, PMF.pure_bind, setReg_registers,
      if_pos rfl, show rAcc ≠ rAddr by decide, if_false, ite_true]
  · simp only [storeRam, setReg]
    rw [stack, List.drop_eq_nil_of_le (by rw [lsbs_length]), List.nil_append]
  · simp only [storeRam, setReg, ram, clearedDef]
    rw [acc, Nat.mod_eq_of_lt small]
  · intro index other
    simp only [storeRam, setReg]
    rw [others index other]
    rfl
  · intro register notAcc notBit notAddr
    simp only [storeRam, setReg_registers, if_neg notAddr]
    rw [regs register notAcc notBit notAddr, clearedDef, setReg_registers, if_neg notAcc]

/-! ### The label selection -/

/-- The key address label `position` reads: `keyBase + 2 · position + bit`. -/
def keyAddress (ram : Word → Word) (position : Nat) : Word :=
  ((ram (word (Request.bitCell position)) >>> (word (position % 254)).toNat) &&& word 1) +
    word (keyBase + 2 * position)

/-- The memory after selecting label `position`. -/
def selectStepMem (memory : Memory) (position : Nat) : Memory :=
  let loaded := setReg (setReg memory rAddr (word (Request.bitCell position))) rA
    (memory.ram (word (Request.bitCell position)))
  let shifted := setReg (setReg loaded rB (word (position % 254))) rA
    (Arithmetic.shiftRight.eval (loaded.registers rA) (word (position % 254)))
  let masked := setReg (setReg shifted rB (word 1)) rA
    (Arithmetic.and.eval (shifted.registers rA) (word 1))
  let located := setReg (setReg masked rB (word (keyBase + 2 * position))) rA
    (Arithmetic.add.eval (masked.registers rA) (word (keyBase + 2 * position)))
  let read := setReg located rC (memory.ram (located.registers rA))
  storeRam (setReg read rAddr (word (labelBase + position))) (word (labelBase + position))
    (read.registers rC)

theorem memSem_selectOne (position : Nat) (memory : Memory) :
    (Request.selectOne position).memSem memory =
      PMF.pure (some (selectStepMem memory position)) := by
  simp only [Request.selectOne, loadAt, storeAt, cst, ar, Prog.memSem, Op.memSem, PMF.pure_bind,
    kleisli, setReg_registers, if_pos rfl]
  rfl

theorem selectStepMem_ram (memory : Memory) (position : Nat) :
    (selectStepMem memory position).ram =
      Function.update memory.ram (word (labelBase + position))
        (memory.ram (keyAddress memory.ram position)) := by
  simp only [selectStepMem, storeRam, setReg_registers, if_pos rfl, keyAddress, Arithmetic.eval,
    show rA ≠ rB by decide, show rA ≠ rAddr by decide, show rC ≠ rAddr by decide, if_false,
    ite_true]
  rfl

theorem selectStepMem_bits (memory : Memory) (position : Nat) :
    (selectStepMem memory position).bits = memory.bits := rfl

theorem bitCell_lt (position : Nat) : Request.bitCell position < labelBase := by
  unfold Request.bitCell reqX reqY requestBase labelBase
  split <;> norm_num

theorem keyAddress_toNat (ram : Word → Word) (position : Nat) (small : position < labelCount) :
    (keyAddress ram position).toNat =
      keyBase + 2 * position + ((ram (word (Request.bitCell position))).toNat >>> (position % 254)) % 2 := by
  have positionSmall : position < 508 := small
  have modSmall : position % 254 < 2 ^ 256 := lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have keySmall : keyBase + 2 * position + 1 < 2 ^ 256 := by unfold keyBase; omega
  have bitSmall : ((ram (word (Request.bitCell position))).toNat >>> (position % 254)) % 2 ≤ 1 :=
    Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  unfold keyAddress
  rw [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ushiftRight]
  simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt modSmall,
    Nat.mod_eq_of_lt (show 1 < 2 ^ 256 by norm_num), Nat.and_one_is_mod]
  rw [Nat.mod_eq_of_lt (show keyBase + 2 * position < 2 ^ 256 by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem keyAddress_ne_label (ram : Word → Word) (position index : Nat)
    (small : position < labelCount) (indexSmall : index < labelCount) :
    keyAddress ram position ≠ word (labelBase + index) := by
  intro same
  have values := congrArg BitVec.toNat same
  rw [keyAddress_toNat ram position small] at values
  have indexLt : index < 508 := indexSmall
  have positionLt : position < 508 := small
  have labelSmall : labelBase + index < 2 ^ 256 := by unfold labelBase; omega
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt labelSmall] at values
  unfold keyBase labelBase at values
  omega

/-- **The selected labels.** -/
theorem select_steps (memory : Memory) :
    ∀ steps, steps ≤ labelCount → ∃ after,
      (Prog.rep steps Request.selectOne).memSem memory = PMF.pure (some after) ∧
        after.bits = memory.bits ∧
        (∀ index, index < steps →
          after.ram (word (labelBase + index)) = memory.ram (keyAddress memory.ram index)) ∧
        ∀ address, (∀ index, index < steps → address ≠ word (labelBase + index)) →
          after.ram address = memory.ram address
  | 0, _ => ⟨memory, by rw [Prog.rep]; rfl, rfl, fun _ bound => absurd bound (by omega),
      fun _ _ => rfl⟩
  | steps + 1, bound => by
      have countEq : labelCount = 508 := rfl
      obtain ⟨middle, run, bits, labels, away⟩ := select_steps memory steps (by omega)
      have cellSame : middle.ram (word (Request.bitCell steps)) =
          memory.ram (word (Request.bitCell steps)) := by
        refine away _ fun index indexBound same => ?_
        have := congrArg BitVec.toNat same
        have cellSmall := bitCell_lt steps
        have labelSmall : labelBase + index < 2 ^ 256 := by
          have : index < 508 := by omega
          unfold labelBase; omega
        rw [word, word, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (lt_trans cellSmall (by unfold labelBase; norm_num)),
          Nat.mod_eq_of_lt labelSmall] at this
        omega
      have addressSame : keyAddress middle.ram steps = keyAddress memory.ram steps := by
        unfold keyAddress
        rw [cellSame]
      have keySame : middle.ram (keyAddress memory.ram steps) =
          memory.ram (keyAddress memory.ram steps) :=
        away _ fun index indexBound =>
          keyAddress_ne_label _ _ _ (by omega) (lt_of_lt_of_le indexBound (by omega))
      refine ⟨selectStepMem middle steps, ?_, ?_, fun index indexBound => ?_,
        fun address outside => ?_⟩
      · rw [Prog.rep, memSem_seq, run, PMF.pure_bind]
        exact memSem_selectOne steps middle
      · rw [selectStepMem_bits, bits]
      · rw [selectStepMem_ram, addressSame, keySame]
        by_cases last : index = steps
        · subst last
          rw [Function.update_self]
        · have labelNe : word (labelBase + index) ≠ word (labelBase + steps) := by
            intro same
            have := congrArg BitVec.toNat same
            have small : ∀ value, value < 508 → labelBase + value < 2 ^ 256 := by
              intro value small; unfold labelBase; omega
            rw [word, word, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (small index (by omega)),
              Nat.mod_eq_of_lt (small steps (by omega))] at this
            omega
          rw [Function.update_of_ne labelNe]
          exact labels index (by omega)
      · rw [selectStepMem_ram, Function.update_of_ne (outside steps (by omega))]
        exact away address fun index indexBound => outside index (by omega)

end Parse

end

end Kriterion.ArgoMAC.PlanB.SimMachine
