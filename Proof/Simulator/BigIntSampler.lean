/-
**The preimage sampler** (A1 §4 item 5; task T9a).

Each attempt draws `t` from `hiWidth + 256 = 107 + 256` fair coins, computes `V = t · p^n + enc` on `K` limbs by the
Horner passes, and keeps `t` iff nothing was kept and the top limb of `V` is `0`. After `R`
attempts the kept `t` is recomputed into `V` and split into the `128`-bit halves a hash program
takes; with nothing kept the run aborts.

* `det_initFrom`, `det_keepTest`, `det_selectCell`, `det_flagStep`, `det_keepBlock`,
  `det_attemptTail`: the deterministic blocks;
* `tAttempt_law`: one attempt, read through `scrub` (the scratch registers, the draw cells and the
  working limbs blanked), is a uniform `363`-bit draw followed by `keepT`;
* `attempts_law`: `R` attempts are `rejectLaw 363 accept R`, read through the kept draw;
* `memSem_preimageSampler`: **the sampler's law** — `rejectLaw 363 accept R`, mapped to the final
  memory `samplerFinal` (the halves of `V = enc + p^n · t`, all scratch cleared);
* `noOracle_preimageSampler`: the sampler touches no oracle, so on the lazy oracle its law is
  `memSem_preimageSampler` with the oracle state passed through (`sem_noOracle`).
-/

import Proof.Simulator.BigIntMachine
import Proof.Simulator.AbortMass

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine Blocks

namespace BigInt

/-! ### Address facts -/

theorem word_ne_of_ne {first second : Nat} (firstSmall : first < 2 ^ 256)
    (secondSmall : second < 2 ^ 256) (different : first ≠ second) : word first ≠ word second := by
  intro same
  have := congrArg BitVec.toNat same
  rw [toNat_word_of_lt firstSmall, toNat_word_of_lt secondSmall] at this
  exact different this

/-! ### Initialising the working limbs -/

theorem limb_pair_zero (lo hi : Nat) (loSmall : lo < 2 ^ 256) : limb (lo + 2 ^ 256 * hi) 0 = lo := by
  simp only [limb, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt loSmall]

theorem limb_pair_one (lo hi : Nat) (loSmall : lo < 2 ^ 256) (hiSmall : hi < 2 ^ 256) :
    limb (lo + 2 ^ 256 * hi) 1 = hi := by
  simp only [limb, Nat.mul_one]
  rw [add_mul_div_of_lt loSmall, Nat.mod_eq_of_lt hiSmall]

theorem limb_pair_high (lo hi index : Nat) (loSmall : lo < 2 ^ 256) (hiSmall : hi < 2 ^ 256) :
    limb (lo + 2 ^ 256 * hi) (index + 2) = 0 := by
  unfold limb
  have grow : 2 ^ 256 * 2 ^ 256 ≤ 2 ^ (256 * (index + 2)) := by
    rw [show index + 2 = index + 1 + 1 from rfl, pow_limb_succ, pow_limb_succ, Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have small : lo + 2 ^ 256 * hi < 2 ^ (256 * (index + 2)) := by
    calc lo + 2 ^ 256 * hi < 2 ^ 256 + 2 ^ 256 * hi := by omega
      _ = 2 ^ 256 * (hi + 1) := by ring
      _ ≤ 2 ^ 256 * 2 ^ 256 := Nat.mul_le_mul_left _ hiSmall
      _ ≤ 2 ^ (256 * (index + 2)) := grow
  rw [Nat.div_eq_of_lt small, Nat.zero_mod]

/-- **The working limbs `← (lo, hi, 0, …)`**, i.e. the limbs of `lo + 2^256 · hi`. -/
theorem det_initFrom (loCell hiCell base count : Nat) (two : 2 ≤ count)
    (small : base + count < 2 ^ 256)
    (hiCellSmall : hiCell < 2 ^ 256) (hiApart : hiCell < base ∨ base + count ≤ hiCell)
    (memory : Memory) (lo hi : Nat) (loSmall : lo < 2 ^ 256) (hiSmall : hi < 2 ^ 256)
    (loIn : memory.ram (word loCell) = word lo) (hiIn : memory.ram (word hiCell) = word hi) :
    ∃ after, det (initFrom loCell hiCell base count) memory = some after ∧
      after.ram = writeCells memory.ram base count (limb (lo + 2 ^ 256 * hi)) ∧
      after.bits = memory.bits ∧
      ∀ index, index ≠ rAddr → index ≠ bV → after.registers index = memory.registers index := by
  have hiNe : word hiCell ≠ word base := word_ne_of_ne hiCellSmall (by omega) (by omega)
  obtain ⟨head, headDet, headV, headRam, headBits, headSame⟩ : ∃ head,
      det (Prog.seqList [loadAt bV loCell, storeAt base bV, loadAt bV hiCell, storeAt (base + 1) bV,
        cst bV 0]) memory = some head ∧ head.registers bV = word 0 ∧
      head.ram = writeCells memory.ram base 2 (limb (lo + 2 ^ 256 * hi)) ∧ head.bits = memory.bits ∧
      ∀ index, index ≠ rAddr → index ≠ bV → head.registers index = memory.registers index := by
    refine ⟨_, rfl, by reg_eval, ?_, by reg_eval, fun index n1 n2 => ?_⟩
    · reg_eval
      rw [writeCells_succ _ _ _ _ (by omega), writeCells_succ _ _ _ _ (by omega), writeCells_zero,
        Nat.add_zero, limb_pair_zero lo hi loSmall, limb_pair_one lo hi loSmall hiSmall,
        Function.update_apply, if_neg hiNe, loIn, hiIn]
      rfl
    · simp (config := { decide := true }) only [regs_setReg, regs_storeRam, n1, n2, ↓reduceIte]
  obtain ⟨after, reach, holds⟩ := det_rep_inv (fun step current =>
      current.registers bV = word 0 ∧
        current.ram = writeCells memory.ram base (2 + step) (limb (lo + 2 ^ 256 * hi)) ∧
        current.bits = memory.bits ∧ ∀ index, index ≠ rAddr → index ≠ bV →
          current.registers index = memory.registers index)
    (fun index => storeAt (base + 2 + index) bV) (count - 2) (fun index bound current holds => by
      obtain ⟨cV, cRam, cBits, cSame⟩ := holds
      refine ⟨_, rfl, by reg_eval; exact cV, ?_, by reg_eval; exact cBits,
        fun register n1 n2 => ?_⟩
      · reg_eval
        rw [cV, cRam, show 2 + (index + 1) = 2 + index + 1 by omega,
          writeCells_succ _ _ _ _ (by omega), show base + (2 + index) = base + 2 + index by omega,
          show 2 + index = index + 2 by omega, limb_pair_high lo hi index loSmall hiSmall]
      · simp (config := { decide := true }) only [regs_setReg, regs_storeRam, n1, ↓reduceIte]
        exact cSame register n1 n2)
    head ⟨headV, headRam, headBits, headSame⟩
  obtain ⟨_, aRam, aBits, aSame⟩ := holds
  refine ⟨after, ?_, by rw [aRam, show 2 + (count - 2) = count by omega], by rw [aBits],
    fun index n1 n2 => by rw [aSame index n1 n2]⟩
  rw [show initFrom loCell hiCell base count = Prog.seqList ([loadAt bV loCell, storeAt base bV,
      loadAt bV hiCell, storeAt (base + 1) bV, cst bV 0] ++
        [Prog.rep (count - 2) fun index => storeAt (base + 2 + index) bV]) from rfl,
    det_seqList_append, headDet, Option.bind_some, Prog.seqList, Prog.seqList, det_seq, reach]
  rfl

/-! ### The keep block -/

/-- The selection bit as a word. -/
def selWord (flag : Word) (top : Nat) : Word := if flag = 0 ∧ top = 0 then 1 else 0

theorem less_one (value : Word) :
    Arithmetic.less.eval value (word 1) = if value = 0 then 1 else 0 := by
  show (if value.toNat < (word 1).toNat then (1 : Word) else 0) = _
  rw [toNat_word_of_lt (by norm_num)]
  by_cases zero : value = 0
  · subst zero; rfl
  · rw [if_neg zero, if_neg]
    intro below
    have isZero : value.toNat = 0 := by omega
    exact zero (BitVec.eq_of_toNat_eq (by rw [isZero]; rfl))

theorem and_bits (first second : Prop) [Decidable first] [Decidable second] :
    Arithmetic.and.eval (if first then (1 : Word) else 0) (if second then 1 else 0) =
      if first ∧ second then 1 else 0 := by
  by_cases one : first <;> by_cases two : second <;> simp only [one, two, if_true, if_false,
    and_false, and_true] <;> rfl

theorem word_eq_zero {value : Nat} (small : value < 2 ^ 256) : (word value = 0) = (value = 0) := by
  apply propext
  constructor
  · intro zero
    have := congrArg BitVec.toNat zero
    rwa [toNat_word_of_lt small] at this
  · intro zero; subst zero; rfl

theorem det_keepTest (work count : Nat) (memory : Memory) (top : Nat) (topSmall : top < 2 ^ 256)
    (topIn : memory.ram (word (limbBase work + (count - 1))) = word top) :
    ∃ after, det (keepTest work count) memory = some after ∧
      after.registers bZ = selWord (memory.ram (word (flagCell work))) top ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      ∀ index, index ∉ scratch → after.registers index = memory.registers index := by
  refine ⟨_, rfl, ?_, by reg_eval, by reg_eval, fun index outside => ?_⟩
  · reg_eval
    rw [topIn, less_one, less_one, and_bits]
    simp only [word_eq_zero topSmall, selWord]
  · obtain ⟨n0, _, _, n3, n4, _, _, _, n8, _, n10, n11, _⟩ := not_mem_scratch outside
    simp (config := { decide := true }) only [regs_setReg, n0, n3, n4, n8, n10, n11, ↓reduceIte]

theorem det_selectCell (kept draw : Nat) (memory : Memory) :
    ∃ after, det (selectCell kept draw) memory = some after ∧
      after.ram = Function.update memory.ram (word kept) (memory.ram (word kept) +
        (memory.ram (word draw) - memory.ram (word kept)) * memory.registers bZ) ∧
      after.bits = memory.bits ∧
      ∀ index, index ≠ rAddr → index ≠ bV → index ≠ bY →
        after.registers index = memory.registers index := by
  refine ⟨_, rfl, by reg_eval; rfl, by reg_eval, fun index n1 n2 n3 => ?_⟩
  simp (config := { decide := true }) only [regs_setReg, regs_storeRam, n1, n2, n3, ↓reduceIte]

theorem det_flagStep (work : Nat) (memory : Memory) :
    ∃ after, det (flagStep work) memory = some after ∧
      after.ram = Function.update memory.ram (word (flagCell work))
        (memory.ram (word (flagCell work)) + memory.registers bZ) ∧
      after.bits = memory.bits ∧
      ∀ index, index ≠ rAddr → index ≠ bX → after.registers index = memory.registers index := by
  refine ⟨_, rfl, by reg_eval; rfl, by reg_eval, fun index n1 n2 => ?_⟩
  simp (config := { decide := true }) only [regs_setReg, regs_storeRam, n1, n2, ↓reduceIte]

theorem select_word (kept draw flag : Word) (top : Nat) :
    kept + (draw - kept) * selWord flag top = if flag = 0 ∧ top = 0 then draw else kept := by
  unfold selWord
  split
  · rw [mul_one, add_sub_cancel]
  · rw [mul_zero, add_zero]

theorem flag_word (flag : Word) (top : Nat) :
    flag + selWord flag top = if flag = 0 ∧ top = 0 then 1 else flag := by
  unfold selWord
  split
  · rename_i both; rw [both.1, zero_add]
  · rw [add_zero]

/-- **The keep block**: the draw is kept (and the flag set) iff the flag is `0` and the top limb
is `0`; otherwise the RAM is unchanged. -/
theorem det_keepBlock (work count : Nat) (small : work + 5 < 2 ^ 256) (memory : Memory) (top : Nat)
    (topSmall : top < 2 ^ 256)
    (topIn : memory.ram (word (limbBase work + (count - 1))) = word top) :
    ∃ after, det (keepBlock work count) memory = some after ∧
      after.ram = (if memory.ram (word (flagCell work)) = 0 ∧ top = 0 then
        Function.update (Function.update (Function.update memory.ram (word (keptLoCell work))
          (memory.ram (word (drawLoCell work)))) (word (keptHiCell work))
          (memory.ram (word (drawHiCell work)))) (word (flagCell work)) 1
        else memory.ram) ∧
      after.bits = memory.bits ∧
      ∀ index, index ∉ scratch → after.registers index = memory.registers index := by
  have ne10 : word (keptLoCell work) ≠ word (flagCell work) :=
    word_ne_of_ne (by unfold keptLoCell; omega) (by unfold flagCell; omega) (by unfold keptLoCell flagCell; omega)
  have ne20 : word (keptHiCell work) ≠ word (flagCell work) :=
    word_ne_of_ne (by unfold keptHiCell; omega) (by unfold flagCell; omega) (by unfold keptHiCell flagCell; omega)
  have ne21 : word (keptHiCell work) ≠ word (keptLoCell work) :=
    word_ne_of_ne (by unfold keptHiCell; omega) (by unfold keptLoCell; omega) (by unfold keptHiCell keptLoCell; omega)
  have ne41 : word (drawHiCell work) ≠ word (keptLoCell work) :=
    word_ne_of_ne (by unfold drawHiCell; omega) (by unfold keptLoCell; omega) (by unfold drawHiCell keptLoCell; omega)
  obtain ⟨first, firstDet, firstZ, firstRam, firstBits, firstSame⟩ :=
    det_keepTest work count memory top topSmall topIn
  obtain ⟨second, secondDet, secondRam, secondBits, secondSame⟩ :=
    det_selectCell (keptLoCell work) (drawLoCell work) first
  obtain ⟨third, thirdDet, thirdRam, thirdBits, thirdSame⟩ :=
    det_selectCell (keptHiCell work) (drawHiCell work) second
  obtain ⟨fourth, fourthDet, fourthRam, fourthBits, fourthSame⟩ := det_flagStep work third
  have secondZ : second.registers bZ = selWord (memory.ram (word (flagCell work))) top := by
    rw [secondSame _ (by decide) (by decide) (by decide), firstZ]
  have thirdZ : third.registers bZ = selWord (memory.ram (word (flagCell work))) top := by
    rw [thirdSame _ (by decide) (by decide) (by decide), secondZ]
  refine ⟨fourth, ?_, ?_, by rw [fourthBits, thirdBits, secondBits, firstBits],
    fun index outside => ?_⟩
  · rw [keepBlock, Prog.seqList, Prog.seqList, Prog.seqList, Prog.seqList, Prog.seqList,
      det_seq_some firstDet, det_seq_some secondDet, det_seq_some thirdDet, det_seq_some fourthDet]
    rfl
  · rw [fourthRam, thirdRam, thirdZ, secondRam, secondZ, firstRam, firstZ,
      Function.update_apply _ _ _ (word (keptHiCell work)), if_neg ne21,
      Function.update_apply _ _ _ (word (drawHiCell work)), if_neg ne41,
      Function.update_apply _ _ _ (word (flagCell work)), if_neg (Ne.symm ne20),
      Function.update_apply _ _ _ (word (flagCell work)), if_neg (Ne.symm ne10),
      select_word, select_word, flag_word]
    split
    · rfl
    · rw [Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  · obtain ⟨_, _, _, _, n4, _, _, _, n8, _, n10, n11, _⟩ := not_mem_scratch outside
    rw [fourthSame index n4 n10, thirdSame index n4 n8 n11, secondSame index n4 n8 n11,
      firstSame index outside]

/-! ### One attempt after its draws -/

/-- The sampler's layout: the five cells, the working limbs and the halves fit below `2^256`, and
the digit cells lie outside them. -/
structure SamplerLayout (work count digits yBase : Nat) : Prop where
  two : 2 ≤ count
  fits : work + 5 + count + 2 * (count - 1) < 2 ^ 256
  apart : yBase + digits ≤ work ∨ work + 5 + count + 2 * (count - 1) ≤ yBase
  yFits : yBase + digits < 2 ^ 256

/-- The value an attempt computes from the draw `t`. -/
def samplerValue (digits enc t : Nat) : Nat := t * pNat ^ digits + enc

/-- The machine's acceptance: the top working limb of `t · p^digits + enc` is `0`. -/
def acceptTop (count digits enc t : Nat) : Bool :=
  decide (limb (samplerValue digits enc t) (count - 1) = 0)

/-- The digit cells hold the digits. -/
def DigitsIn (yBase digits : Nat) (digitValues : Nat → Nat) (memory : Memory) : Prop :=
  ∀ e, e < digits → memory.ram (word (yBase + e)) = word (digitValues e)

/-- **The attempt tail**: `V = t · p^n + enc` on the working limbs, then the keep block. -/
theorem det_attemptTail (work count digits yBase : Nat)
    (layout : SamplerLayout work count digits yBase) (memory : Memory) (digitValues : Nat → Nat)
    (digitsSmall : ∀ e, e < digits → digitValues e < pNat)
    (cellsIn : DigitsIn yBase digits digitValues memory) (lo hi : Nat) (loSmall : lo < 2 ^ 256)
    (hiSmall : hi < 2 ^ 256) (loIn : memory.ram (word (drawLoCell work)) = word lo)
    (hiIn : memory.ram (word (drawHiCell work)) = word hi) :
    ∃ after, det (attemptTail work count digits yBase) memory = some after ∧
      after.ram = (if memory.ram (word (flagCell work)) = 0 ∧
          limb (samplerValue digits (encNat digitValues digits) (lo + 2 ^ 256 * hi)) (count - 1) = 0 then
        Function.update (Function.update (Function.update
          (writeCells memory.ram (limbBase work) count
            (limb (samplerValue digits (encNat digitValues digits) (lo + 2 ^ 256 * hi))))
          (word (keptLoCell work)) (word lo)) (word (keptHiCell work)) (word hi)) (word (flagCell work)) 1
        else writeCells memory.ram (limbBase work) count
          (limb (samplerValue digits (encNat digitValues digits) (lo + 2 ^ 256 * hi)))) ∧
      after.bits = memory.bits ∧
      ∀ index, index ∉ scratch → after.registers index = memory.registers index := by
  obtain ⟨two, fits, apart, yFits⟩ := layout
  obtain ⟨first, firstDet, firstConsts, firstRam, firstBits, firstSame⟩ := det_setup memory
  obtain ⟨second, secondDet, secondRam, secondBits, secondSame⟩ :=
    det_initFrom (drawLoCell work) (drawHiCell work) (limbBase work) count two
      (by unfold limbBase; omega) (by unfold drawHiCell; omega)
      (by unfold drawHiCell limbBase; omega) first lo hi loSmall hiSmall
      (by rw [firstRam, loIn]) (by rw [firstRam, hiIn])
  have secondConsts : Consts second := consts_of_regs firstConsts fun index _ _ n4 _ n8 _ _ _ _ =>
    secondSame index n4 n8
  obtain ⟨third, thirdDet, _, thirdRam, thirdBits, thirdSame⟩ :=
    det_macPasses (limbBase work) count digits yBase (by unfold limbBase; omega) yFits
      (by unfold limbBase; omega) second secondConsts (lo + 2 ^ 256 * hi) digitValues digitsSmall
      (fun e bound => by
        rw [secondRam, writeCells_out _ _ _ _ _ (by omega) (by unfold limbBase; omega), firstRam,
          cellsIn e bound])
      (fun index inside => by
        rw [secondRam, writeCells_in _ _ _ _ _ inside (by unfold limbBase; omega)])
  have thirdIs : third.ram = writeCells memory.ram (limbBase work) count
      (limb (samplerValue digits (encNat digitValues digits) (lo + 2 ^ 256 * hi))) := by
    rw [thirdRam, secondRam, writeCells_writeCells, firstRam]
    rfl
  have outside : ∀ cell, cell < limbBase work → third.ram (word cell) = memory.ram (word cell) := by
    intro cell below
    rw [thirdIs, writeCells_out _ _ _ _ _ (by unfold limbBase at below; omega) (Or.inl below)]
  obtain ⟨fourth, fourthDet, fourthRam, fourthBits, fourthSame⟩ :=
    det_keepBlock work count (by omega) third _ (limb_lt _ _)
      (by rw [thirdIs, writeCells_in _ _ _ _ _ (by omega) (by unfold limbBase; omega)])
  refine ⟨fourth, ?_, ?_, by rw [fourthBits, thirdBits, secondBits, firstBits],
    fun index out => ?_⟩
  · rw [attemptTail, Prog.seqList, Prog.seqList, Prog.seqList, Prog.seqList, Prog.seqList,
      det_seq_some firstDet, det_seq_some secondDet, det_seq_some thirdDet, det_seq_some fourthDet]
    rfl
  · rw [fourthRam, outside _ (by unfold flagCell limbBase; omega),
      outside _ (by unfold drawLoCell limbBase; omega), outside _ (by unfold drawHiCell limbBase; omega),
      loIn, hiIn, thirdIs]
  · obtain ⟨_, _, _, _, n4, _, _, _, n8, _, _, _, _⟩ := not_mem_scratch out
    rw [fourthSame index out, thirdSame index out, secondSame index n4 n8, firstSame index out]

/-! ### The kept state -/

/-- The draw cells and the working limbs blanked (`drawLo … limbBase + count − 1`), the scratch
registers cleared: what an attempt leaves behind besides its keep decision. -/
def scrub (work count : Nat) (memory : Memory) : Memory :=
  clearRegs (setRam memory (writeCells memory.ram (drawLoCell work) (count + 2) (fun _ => 0))) scratch

/-- The kept state after one more draw `t`: keep it iff nothing was kept and it is accepted. -/
def keepT (work : Nat) (accept : Nat → Bool) (state : Memory) (t : Nat) : Memory :=
  if state.ram (word (flagCell work)) = 0 ∧ accept t = true then
    setRam state (Function.update (Function.update (Function.update state.ram
      (word (keptLoCell work)) (word (t % 2 ^ 256))) (word (keptHiCell work)) (word (t / 2 ^ 256)))
      (word (flagCell work)) 1)
  else state

theorem scrub_ram (work count : Nat) (memory : Memory) :
    (scrub work count memory).ram = writeCells memory.ram (drawLoCell work) (count + 2) (fun _ => 0) := by
  rw [scrub, (clearRegs_other _ _).1, ram_setRam]

theorem setRam_clearRegs (memory : Memory) (registers : List Register) (ram : Word → Word) :
    setRam (clearRegs memory registers) ram = clearRegs (setRam memory ram) registers := by
  apply memory_ext
  · rw [bits_setRam, (clearRegs_other _ _).2, (clearRegs_other _ _).2, bits_setRam]
  · funext index
    rw [regs_setRam, clearRegs_registers, clearRegs_registers, regs_setRam]
  · rw [ram_setRam, (clearRegs_other _ _).1, ram_setRam]

theorem setRam_setRam (memory : Memory) (first second : Word → Word) :
    setRam (setRam memory first) second = setRam memory second := rfl

/-- **What an attempt tail leaves, scrubbed, is the kept state.** -/
theorem scrub_attemptTail (work count digits yBase : Nat)
    (layout : SamplerLayout work count digits yBase) (memory after : Memory) (enc lo hi : Nat)
    (loSmall : lo < 2 ^ 256) (values : Nat → Nat)
    (ramIs : after.ram = (if memory.ram (word (flagCell work)) = 0 ∧
          limb (samplerValue digits enc (lo + 2 ^ 256 * hi)) (count - 1) = 0 then
        Function.update (Function.update (Function.update
          (writeCells memory.ram (limbBase work) count values)
          (word (keptLoCell work)) (word lo)) (word (keptHiCell work)) (word hi)) (word (flagCell work)) 1
        else writeCells memory.ram (limbBase work) count values))
    (bits : after.bits = memory.bits)
    (same : ∀ index, index ∉ scratch → after.registers index = memory.registers index) :
    scrub work count after =
      keepT work (acceptTop count digits enc) (scrub work count memory) (lo + 2 ^ 256 * hi) := by
  obtain ⟨two, fits, _, _⟩ := layout
  have flagScrub : (scrub work count memory).ram (word (flagCell work)) =
      memory.ram (word (flagCell work)) := by
    rw [scrub_ram, writeCells_out _ _ _ _ _ (by unfold flagCell; omega)
      (Or.inl (by unfold flagCell drawLoCell; omega))]
  have lowIs : (lo + 2 ^ 256 * hi) % 2 ^ 256 = lo := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt loSmall]
  have highIs : (lo + 2 ^ 256 * hi) / 2 ^ 256 = hi := add_mul_div_of_lt loSmall
  have limbsIn : drawLoCell work ≤ limbBase work ∧
      limbBase work + count ≤ drawLoCell work + (count + 2) := by
    unfold drawLoCell limbBase; omega
  have o0 : flagCell work < limbBase work ∨ limbBase work + count ≤ flagCell work := by
    unfold flagCell limbBase; omega
  have o1 : keptLoCell work < limbBase work ∨ limbBase work + count ≤ keptLoCell work := by
    unfold keptLoCell limbBase; omega
  have o2 : keptHiCell work < limbBase work ∨ limbBase work + count ≤ keptHiCell work := by
    unfold keptHiCell limbBase; omega
  have b0 : flagCell work < drawLoCell work ∨ drawLoCell work + (count + 2) ≤ flagCell work := by
    unfold flagCell drawLoCell; omega
  have b1 : keptLoCell work < drawLoCell work ∨ drawLoCell work + (count + 2) ≤ keptLoCell work := by
    unfold keptLoCell drawLoCell; omega
  have b2 : keptHiCell work < drawLoCell work ∨ drawLoCell work + (count + 2) ≤ keptHiCell work := by
    unfold keptHiCell drawLoCell; omega
  have s0 : flagCell work < 2 ^ 256 := by unfold flagCell; omega
  have s1 : keptLoCell work < 2 ^ 256 := by unfold keptLoCell; omega
  have s2 : keptHiCell work < 2 ^ 256 := by unfold keptHiCell; omega
  unfold keepT acceptTop
  rw [flagScrub]
  simp only [decide_eq_true_eq]
  unfold scrub
  split
  · rename_i kept
    rw [setRam_clearRegs, setRam_setRam, clearRegs_eq_iff]
    refine ⟨?_, by rw [bits_setRam, bits_setRam, bits], fun index outside => ?_⟩
    · rw [ram_setRam, ram_setRam, ramIs, if_pos kept, (clearRegs_other _ _).1, ram_setRam, lowIs,
        highIs, update_writeCells_out _ _ _ _ _ _ s1 o1, update_writeCells_out _ _ _ _ _ _ s2 o2,
        update_writeCells_out _ _ _ _ _ _ s0 o0, writeCells_writeCells_sub _ _ _ _ _ _ _ limbsIn,
        update_writeCells_out _ _ _ _ _ _ s1 b1, update_writeCells_out _ _ _ _ _ _ s2 b2,
        update_writeCells_out _ _ _ _ _ _ s0 b0]
    · rw [regs_setRam, regs_setRam, same index outside]
  · rename_i notKept
    rw [clearRegs_eq_iff]
    refine ⟨?_, by rw [bits_setRam, bits_setRam, bits], fun index outside => ?_⟩
    · rw [ram_setRam, ram_setRam, ramIs, if_neg notKept, writeCells_writeCells_sub _ _ _ _ _ _ _ limbsIn]
    · rw [regs_setRam, regs_setRam, same index outside]

/-! ### The law of one attempt -/

theorem memSem_seq_plain [BN254.FieldCertificate] {first rest : Prog} (plain : IsPlain first)
    {memory middle : Memory} (step : det first memory = some middle) :
    (Prog.seq first rest).memSem memory = rest.memSem middle := by
  rw [memSem_seq, memSem_det first plain, step, PMF.pure_bind]
  rfl

theorem memSem_seq_sampleWord [BN254.FieldCertificate] (width : Nat) (rest : Prog) (memory : Memory) :
    (Prog.seq (sampleWord width) rest).memSem memory =
      (PMF.uniformOfFintype (Fin (2 ^ width))).bind fun value =>
        rest.memSem (wordMem (setReg memory rAcc 0) width value.val) := by
  rw [memSem_seq, memSem_sampleWord, PMF.bind_map]
  rfl

/-- Two uniform coin words make one uniform draw `t = lo + 2^b · hi`. (The `FieldCertificate`
binder is required by `Sampling`'s `uniform_product`/`uniform_equiv`/`uniform_nonempty_pow`, which
carry their section's instance.) -/
theorem uniform_pair_gen [BN254.FieldCertificate] {β : Type} (a b : Nat) (g : Nat → β) :
    (PMF.uniformOfFintype (Fin (2 ^ a))).bind (fun hi =>
        (PMF.uniformOfFintype (Fin (2 ^ b))).map fun lo => g (lo.val + 2 ^ b * hi.val)) =
      (PMF.uniformOfFintype (Fin (2 ^ (a + b)))).map fun t => g t.val := by
  have := uniform_nonempty_pow a
  have := uniform_nonempty_pow b
  have := uniform_nonempty_pow (a + b)
  let pairing : Fin (2 ^ a) × Fin (2 ^ b) ≃ Fin (2 ^ (a + b)) :=
    finProdFinEquiv.trans (finCongr (by rw [Nat.pow_add]))
  have pairingVal : ∀ pair, (pairing pair).val = pair.2.val + 2 ^ b * pair.1.val := fun _ => rfl
  rw [← uniform_equiv pairing, ← uniform_product, PMF.map_comp, PMF.map_bind]
  congr 1
  funext hi
  rw [PMF.map_comp]
  congr 1

/-- The high and the low coin words make one uniform `(70 + 256)`-bit draw
`t = lo + 2^256 · hi`. -/
theorem uniform_pair [BN254.FieldCertificate] {β : Type} (g : Nat → β) :
    (PMF.uniformOfFintype (Fin (2 ^ hiWidth))).bind (fun hi =>
        (PMF.uniformOfFintype (Fin (2 ^ 256))).map fun lo => g (lo.val + 2 ^ 256 * hi.val)) =
      (PMF.uniformOfFintype (Fin (2 ^ (hiWidth + 256)))).map fun t => g t.val :=
  uniform_pair_gen hiWidth 256 g

/-- The memory after the two draws: `hi` at `drawHi`, `lo` at `drawLo`. -/
def drawnMem (work : Nat) (memory : Memory) (hi lo : Nat) : Memory :=
  let first := wordMem (setReg memory rAcc 0) hiWidth hi
  let stored := storeRam (setReg first rAddr (word (drawHiCell work))) (word (drawHiCell work))
    (word hi)
  let second := wordMem (setReg stored rAcc 0) 256 lo
  storeRam (setReg second rAddr (word (drawLoCell work))) (word (drawLoCell work)) (word lo)

theorem drawnMem_ram (work : Nat) (memory : Memory) (hi lo : Nat) :
    (drawnMem work memory hi lo).ram = Function.update (Function.update memory.ram
      (word (drawHiCell work)) (word hi)) (word (drawLoCell work)) (word lo) := rfl

theorem drawnMem_regs [BN254.FieldCertificate] (work : Nat) (memory : Memory) (hi lo : Nat) (index : Register)
    (notAcc : index ≠ rAcc) (notBit : index ≠ rBit) (notAddr : index ≠ rAddr) :
    (drawnMem work memory hi lo).registers index = memory.registers index := by
  simp only [drawnMem, regs_storeRam, regs_setReg, if_neg notAddr]
  rw [wordMem_other _ _ _ _ notAcc notBit, regs_storeRam, regs_setReg, if_neg notAddr,
    wordMem_other _ _ _ _ notAcc notBit]

theorem memSem_tAttempt [BN254.FieldCertificate] (work count digits yBase : Nat) (memory : Memory) :
    (tAttempt work count digits yBase).memSem memory =
      (PMF.uniformOfFintype (Fin (2 ^ hiWidth))).bind fun hi =>
        (PMF.uniformOfFintype (Fin (2 ^ 256))).bind fun lo =>
          (Prog.seq (attemptTail work count digits yBase) (.skip 0)).memSem
            (drawnMem work memory hi.val lo.val) := by
  rw [tAttempt, Prog.seqList, memSem_seq_sampleWord]
  congr 1
  funext hi
  rw [Prog.seqList, memSem_seq_plain (first := storeAt (drawHiCell work) rAcc) ⟨trivial, trivial⟩ rfl,
    Prog.seqList, memSem_seq_sampleWord]
  congr 1
  funext lo
  rw [Prog.seqList, memSem_seq_plain (first := storeAt (drawLoCell work) rAcc) ⟨trivial, trivial⟩ rfl,
    Prog.seqList, Prog.seqList]
  congr 1
  simp only [drawnMem, regs_setReg, if_neg (show rAcc ≠ rAddr by decide), wordMem_acc]
  rfl

theorem plain_attemptTail (work count digits yBase : Nat) :
    IsPlain (attemptTail work count digits yBase) :=
  ⟨plain_setup, ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial,
      plain_rep _ _ fun _ _ => ⟨trivial, trivial⟩, trivial⟩,
    plain_macPasses _ _ _ _,
    ⟨⟨⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩, trivial, trivial, trivial, trivial⟩,
      ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, trivial, trivial, ⟨trivial, trivial⟩, trivial⟩,
      ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, trivial, trivial, ⟨trivial, trivial⟩, trivial⟩,
      ⟨⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial⟩, trivial⟩, trivial⟩

/-- **The law of one attempt**, read through `scrub`: a uniform `363`-bit draw `t`, then
`keepT`. -/
theorem tAttempt_law [BN254.FieldCertificate] (work count digits yBase : Nat)
    (layout : SamplerLayout work count digits yBase) (digitValues : Nat → Nat)
    (digitsSmall : ∀ e, e < digits → digitValues e < pNat) (memory : Memory)
    (cellsIn : DigitsIn yBase digits digitValues memory) :
    ((tAttempt work count digits yBase).memSem memory).map (Option.map (scrub work count)) =
      (PMF.uniformOfFintype (Fin (2 ^ (hiWidth + 256)))).map fun t =>
        some (keepT work (acceptTop count digits (encNat digitValues digits))
          (scrub work count memory) t.val) := by
  obtain ⟨two, fits, apart, yFits⟩ := layout
  rw [memSem_tAttempt, show ((PMF.uniformOfFintype (Fin (2 ^ (hiWidth + 256)))).map fun t =>
      some (keepT work (acceptTop count digits (encNat digitValues digits))
        (scrub work count memory) t.val)) = (PMF.uniformOfFintype (Fin (2 ^ hiWidth))).bind (fun hi =>
        (PMF.uniformOfFintype (Fin (2 ^ 256))).map fun lo =>
          some (keepT work (acceptTop count digits (encNat digitValues digits))
            (scrub work count memory) (lo.val + 2 ^ 256 * hi.val))) from
      (uniform_pair fun n => some (keepT work (acceptTop count digits (encNat digitValues digits))
        (scrub work count memory) n)).symm,
    PMF.map_bind]
  congr 1
  funext hi
  rw [PMF.map_bind]
  have hiSmall : hi.val < 2 ^ 256 := lt_of_lt_of_le hi.isLt (Nat.pow_le_pow_right (by norm_num)
    (by unfold hiWidth; omega))
  have neHL : word (drawLoCell work) ≠ word (drawHiCell work) :=
    word_ne_of_ne (by unfold drawLoCell; omega) (by unfold drawHiCell; omega)
      (by unfold drawLoCell drawHiCell; omega)
  rw [← PMF.bind_pure_comp]
  congr 1
  funext lo
  obtain ⟨after, afterDet, afterRam, afterBits, afterSame⟩ := det_attemptTail work count digits yBase
    ⟨two, fits, apart, yFits⟩ (drawnMem work memory hi.val lo.val) digitValues digitsSmall
    (fun e bound => by
      rw [drawnMem_ram, Function.update_of_ne, Function.update_of_ne, cellsIn e bound]
      · exact word_ne_of_ne (by omega) (by unfold drawHiCell; omega) (by unfold drawHiCell; omega)
      · exact word_ne_of_ne (by omega) (by unfold drawLoCell; omega) (by unfold drawLoCell; omega))
    lo.val hi.val lo.isLt hiSmall
    (by rw [drawnMem_ram, Function.update_self])
    (by rw [drawnMem_ram, Function.update_of_ne (Ne.symm neHL), Function.update_self])
  rw [memSem_det (Prog.seq (attemptTail work count digits yBase) (.skip 0))
    ⟨plain_attemptTail work count digits yBase, trivial⟩, det_seq_some afterDet]
  simp only [det, PMF.pure_map, Option.map_some, Function.comp_apply]
  congr 2
  have scrubDrawn : scrub work count (drawnMem work memory hi.val lo.val) = scrub work count memory := by
    unfold scrub
    rw [clearRegs_eq_iff]
    refine ⟨?_, rfl, fun index outside => ?_⟩
    · rw [ram_setRam, ram_setRam, drawnMem_ram,
        writeCells_update_in _ _ _ _ _ _ (by unfold drawLoCell; omega)
          (by unfold drawLoCell; omega),
        writeCells_update_in _ _ _ _ _ _ (by unfold drawHiCell; omega)
          (by unfold drawHiCell drawLoCell; omega)]
    · obtain ⟨n0, _, _, n3, n4, _⟩ := not_mem_scratch outside
      rw [regs_setRam, regs_setRam, drawnMem_regs _ _ _ _ _ n0 n3 n4]
  rw [← scrubDrawn]
  exact scrub_attemptTail work count digits yBase ⟨two, fits, apart, yFits⟩
    (drawnMem work memory hi.val lo.val) after _ lo.val hi.val lo.isLt _ afterRam afterBits afterSame

/-! ### Many attempts -/

/-- `count` kept-state steps in the machine's order (appended at the end). -/
noncomputable def keepLaw (width : Nat) (keep : Memory → Nat → Memory) :
    Nat → Memory → PMF (Option Memory)
  | 0, state => PMF.pure (some state)
  | count + 1, state => (keepLaw width keep count state).bind
      (kleisli fun current => (PMF.uniformOfFintype (Fin (2 ^ width))).map fun t =>
        some (keep current t.val))

theorem digitsIn_scrub (work count digits yBase : Nat) (layout : SamplerLayout work count digits yBase)
    (digitValues : Nat → Nat) (memory : Memory) :
    DigitsIn yBase digits digitValues (scrub work count memory) ↔
      DigitsIn yBase digits digitValues memory := by
  obtain ⟨_, fits, apart, yFits⟩ := layout
  unfold DigitsIn
  refine forall_congr' fun e => imp_congr_right fun bound => ?_
  rw [scrub_ram, writeCells_out _ _ _ _ _ (by omega) (by unfold drawLoCell; omega)]

theorem digitsIn_keepT (work count digits yBase : Nat) (layout : SamplerLayout work count digits yBase)
    (digitValues : Nat → Nat) (accept : Nat → Bool) (state : Memory) (t : Nat)
    (holds : DigitsIn yBase digits digitValues state) :
    DigitsIn yBase digits digitValues (keepT work accept state t) := by
  obtain ⟨_, fits, apart, yFits⟩ := layout
  unfold keepT
  split
  · intro e bound
    rw [ram_setRam, Function.update_of_ne, Function.update_of_ne, Function.update_of_ne, holds e bound]
    · exact word_ne_of_ne (by omega) (by unfold keptLoCell; omega) (by unfold keptLoCell; omega)
    · exact word_ne_of_ne (by omega) (by unfold keptHiCell; omega) (by unfold keptHiCell; omega)
    · exact word_ne_of_ne (by omega) (by unfold flagCell; omega) (by unfold flagCell; omega)
  · exact holds

theorem keepLaw_digitsIn (work count digits yBase : Nat) (layout : SamplerLayout work count digits yBase)
    (digitValues : Nat → Nat) (accept : Nat → Bool) (width : Nat) :
    ∀ steps state, DigitsIn yBase digits digitValues state →
      ∀ reached, some reached ∈ (keepLaw width (keepT work accept) steps state).support →
        DigitsIn yBase digits digitValues reached
  | 0, state, holds, reached, member => by
      simp only [keepLaw, PMF.support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
      exact member ▸ holds
  | steps + 1, state, holds, reached, member => by
      simp only [keepLaw, PMF.mem_support_bind_iff] at member
      obtain ⟨middle, middleIn, member⟩ := member
      cases middle with
      | none => simp [kleisli] at member
      | some middle =>
          simp only [kleisli, PMF.support_map, Set.mem_image, Option.some.injEq] at member
          obtain ⟨t, _, same⟩ := member
          rw [← same]
          exact digitsIn_keepT work count digits yBase layout digitValues accept middle t.val
            (keepLaw_digitsIn work count digits yBase layout digitValues accept width steps state holds
              middle middleIn)

theorem memSem_rep_succ' [BN254.FieldCertificate] (count : Nat) (body : Nat → Prog) (memory : Memory) :
    (Prog.rep (count + 1) body).memSem memory =
      ((Prog.rep count body).memSem memory).bind (kleisli (body count).memSem) := by
  rw [Prog.rep, memSem_seq]

/-- **`attempts` attempts**, read through `scrub`, are `keepLaw`. -/
theorem rep_tAttempt_law [BN254.FieldCertificate] (work count digits yBase : Nat)
    (layout : SamplerLayout work count digits yBase) (digitValues : Nat → Nat)
    (digitsSmall : ∀ e, e < digits → digitValues e < pNat) :
    ∀ attempts memory, DigitsIn yBase digits digitValues memory →
      ((Prog.rep attempts fun _ => tAttempt work count digits yBase).memSem memory).map
          (Option.map (scrub work count)) =
        keepLaw (hiWidth + 256) (keepT work (acceptTop count digits (encNat digitValues digits)))
          attempts (scrub work count memory)
  | 0, memory, _ => by
      rw [Prog.rep]
      simp only [Prog.memSem, PMF.pure_map, Option.map_some, keepLaw]
  | attempts + 1, memory, holds => by
      rw [memSem_rep_succ', PMF.map_bind, keepLaw,
        ← rep_tAttempt_law work count digits yBase layout digitValues digitsSmall attempts memory holds,
        PMF.bind_map]
      apply PMF.bind_congr
      intro result member
      cases result with
      | none =>
          show (PMF.pure none).map _ = PMF.pure none
          rw [PMF.pure_map]
          rfl
      | some reached =>
          simp only [kleisli, Function.comp_apply, Option.map_some]
          have reachedIn : some (scrub work count reached) ∈ (keepLaw (hiWidth + 256)
              (keepT work (acceptTop count digits (encNat digitValues digits))) attempts
              (scrub work count memory)).support := by
            rw [← rep_tAttempt_law work count digits yBase layout digitValues digitsSmall attempts memory
              holds, PMF.support_map]
            exact ⟨some reached, member, rfl⟩
          have reachedHolds := (digitsIn_scrub work count digits yBase layout digitValues reached).mp
            (keepLaw_digitsIn work count digits yBase layout digitValues _ _ attempts _
              ((digitsIn_scrub work count digits yBase layout digitValues memory).mpr holds) _ reachedIn)
          exact tAttempt_law work count digits yBase layout digitValues digitsSmall reached reachedHolds

/-- The kept state recording the kept draw. -/
def keptState (work : Nat) (accept : Nat → Bool) (state : Memory) : Option Nat → Memory
  | none => state
  | some t => keepT work accept state t

theorem kleisli_bind' (first second : Memory → PMF (Option Memory)) (result : Option Memory) :
    (kleisli first result).bind (kleisli second) =
      kleisli (fun memory => (first memory).bind (kleisli second)) result := by
  cases result <;> simp [kleisli]

theorem keepLaw_succ_front (width : Nat) (keep : Memory → Nat → Memory) (count : Nat)
    (state : Memory) :
    keepLaw width keep (count + 1) state =
      ((PMF.uniformOfFintype (Fin (2 ^ width))).map fun t => some (keep state t.val)).bind
        (kleisli (keepLaw width keep count)) := by
  induction count generalizing state with
  | zero =>
      simp only [keepLaw, PMF.pure_bind, kleisli]
      conv_lhs => rw [← PMF.bind_pure ((PMF.uniformOfFintype (Fin (2 ^ width))).map _)]
      congr 1
      funext result
      cases result <;> rfl
  | succ count ih =>
      conv_lhs => rw [keepLaw, ih state, PMF.bind_bind]
      congr 1
      funext result
      rw [kleisli_bind']
      rfl

theorem keepLaw_full (width work : Nat) (accept : Nat → Bool) (count : Nat) (state : Memory)
    (full : state.ram (word (flagCell work)) ≠ 0) :
    keepLaw width (keepT work accept) count state = PMF.pure (some state) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [keepLaw, ih, PMF.pure_bind]
      simp only [kleisli, keepT, if_neg (fun both : _ ∧ _ => full both.1)]
      exact PMF.map_const _ _

/-- **The kept-state steps are bounded rejection**, read through the kept draw. -/
theorem keepLaw_eq_rejectLaw (width work : Nat) (accept : Nat → Bool) (count : Nat) (state : Memory)
    (empty : state.ram (word (flagCell work)) = 0) :
    keepLaw width (keepT work accept) count state =
      (rejectLaw width accept count).map fun kept => some (keptState work accept state kept) := by
  induction count with
  | zero => simp [keepLaw, rejectLaw, keptState, PMF.pure_map]
  | succ count ih =>
      rw [keepLaw_succ_front, rejectLaw, PMF.bind_map, PMF.map_bind]
      congr 1
      funext t
      simp only [Function.comp_apply, kleisli]
      by_cases accepted : accept t.val = true
      · rw [if_pos accepted, PMF.pure_map, keepLaw_full]
        · rfl
        · unfold keepT
          rw [if_pos ⟨empty, accepted⟩, ram_setRam, Function.update_self]
          decide
      · rw [if_neg accepted, ← ih]
        unfold keepT
        rw [if_neg (fun both : _ ∧ _ => accepted both.2)]

theorem kept_accepted (width : Nat) (accept : Nat → Bool) (count value : Nat)
    (member : some value ∈ (rejectLaw width accept count).support) :
    accept value = true ∧ value < 2 ^ width := by
  by_contra bad
  exact (PMF.mem_support_iff _ _).mp member (rejectLaw_off width accept count value bad)

/-! ### The acceptance continuation -/

/-- Half `j` of the low limbs of `V`: `V_{j/2} mod 2^128` for even `j`, `V_{j/2} / 2^128` for
odd `j` (the two words of the hash answer `(first, second)` a program writes). -/
def halfValue (value half : Nat) : Nat :=
  if half % 2 = 0 then limb value (half / 2) % 2 ^ 128 else limb value (half / 2) / 2 ^ 128

theorem det_splitHalves (base halves count : Nat) (apart : base + count ≤ halves)
    (small : halves + 2 * count < 2 ^ 256) (memory : Memory) (consts : Consts memory) (value : Nat)
    (limbsIn : ∀ index, index < count → memory.ram (word (base + index)) = word (limb value index)) :
    ∃ after, det (splitHalves base halves count) memory = some after ∧ Consts after ∧
      after.ram = writeCells memory.ram halves (2 * count) (halfValue value) ∧
      after.bits = memory.bits ∧
      ∀ index, index ≠ rAddr → index ≠ bV → index ≠ bX →
        after.registers index = memory.registers index := by
  obtain ⟨after, reach, holds⟩ := det_rep_inv (fun step current =>
      Consts current ∧ current.ram = writeCells memory.ram halves (2 * step) (halfValue value) ∧
        current.bits = memory.bits ∧ ∀ index, index ≠ rAddr → index ≠ bV → index ≠ bX →
          current.registers index = memory.registers index)
    (fun index => Prog.seqList [loadAt bV (base + index), ar .and bX bV bMask,
      storeAt (halves + 2 * index) bX, ar .shiftRight bX bV bC128,
      storeAt (halves + 2 * index + 1) bX]) count (fun index bound current holds => by
      obtain ⟨cConsts, cRam, cBits, cSame⟩ := holds
      obtain ⟨hMask, hC, hP0, hP1⟩ := cConsts
      have vIn : current.ram (word (base + index)) = word (limb value index) := by
        rw [cRam, writeCells_out _ _ _ _ _ (by omega) (Or.inl (by omega)), limbsIn index bound]
      refine ⟨_, rfl, ⟨by reg_eval; exact hMask, by reg_eval; exact hC, by reg_eval; exact hP0,
          by reg_eval; exact hP1⟩, ?_, by reg_eval; exact cBits, fun register n1 n2 n3 => ?_⟩
      · reg_eval
        rw [vIn, hMask, hC, eval_and_mask, eval_shr128, Nat.mod_eq_of_lt (limb_lt value index), cRam,
          show 2 * (index + 1) = 2 * index + 1 + 1 by omega, writeCells_succ _ _ _ _ (by omega),
          writeCells_succ _ _ _ _ (by omega)]
        have even : halfValue value (2 * index) = limb value index % 2 ^ 128 := by
          unfold halfValue
          rw [if_pos (by omega), show 2 * index / 2 = index by omega]
        have odd : halfValue value (2 * index + 1) = limb value index / 2 ^ 128 := by
          unfold halfValue
          rw [if_neg (by omega), show (2 * index + 1) / 2 = index by omega]
        rw [even, odd, show halves + 2 * index + 1 = halves + (2 * index + 1) by omega]
      · simp (config := { decide := true }) only [regs_setReg, regs_storeRam, n1, n2, n3, ↓reduceIte]
        exact cSame register n1 n2 n3)
    memory ⟨consts, by rw [Nat.mul_zero, writeCells_zero], rfl, fun _ _ _ _ => rfl⟩
  obtain ⟨aConsts, aRam, aBits, aSame⟩ := holds
  exact ⟨after, reach, aConsts, aRam, aBits, aSame⟩

theorem det_clearCells (work : Nat) (small : work + 5 < 2 ^ 256) (memory : Memory) :
    ∃ after, det (clearCells work) memory = some after ∧
      after.ram = writeCells memory.ram work 5 (fun _ => 0) ∧ after.bits = memory.bits ∧
      ∀ index, index ≠ rAddr → index ≠ bV → after.registers index = memory.registers index := by
  refine ⟨_, rfl, ?_, by reg_eval, fun index n1 n2 => ?_⟩
  · reg_eval
    rw [show (5 : Nat) = 0 + 1 + 1 + 1 + 1 + 1 from rfl, writeCells_succ _ _ _ _ (by omega),
      writeCells_succ _ _ _ _ (by omega), writeCells_succ _ _ _ _ (by omega),
      writeCells_succ _ _ _ _ (by omega), writeCells_succ _ _ _ _ (by omega), writeCells_zero]
    rfl
  · simp (config := { decide := true }) only [regs_setReg, regs_storeRam, n1, n2, ↓reduceIte]

/-- The RAM the sampler leaves for the kept draw `t`: the working limbs of `V = t · p^n + enc`,
the halves of its low `count − 1` limbs, and the five cells zeroed. -/
def finalRam (work count digits enc : Nat) (ram : Word → Word) (t : Nat) : Word → Word :=
  writeCells (writeCells (writeCells ram (limbBase work) count (limb (samplerValue digits enc t)))
    (halfBase work count) (2 * (count - 1)) (halfValue (samplerValue digits enc t))) work 5
    (fun _ => 0)

/-- `finalRam` reads nothing of the sampler's region. -/
theorem finalRam_agree (work count digits enc : Nat) (first second : Word → Word) (t : Nat)
    (agree : ∀ address : Word,
      ¬ (work ≤ address.toNat ∧ address.toNat < work + 5 + count + 2 * (count - 1)) →
        first address = second address) :
    finalRam work count digits enc first t = finalRam work count digits enc second t := by
  unfold finalRam
  apply writeCells_agree
  intro address outside
  simp only [writeCells]
  split
  · rfl
  · split
    · rfl
    · apply agree
      unfold limbBase halfBase at *
      omega

theorem plain_useKept (work count digits yBase : Nat) : IsPlain (useKept work count digits yBase) :=
  ⟨plain_setup, ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial,
      plain_rep _ _ fun _ _ => ⟨trivial, trivial⟩, trivial⟩,
    plain_macPasses _ _ _ _,
    plain_rep _ _ fun _ _ => ⟨⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial,
      ⟨trivial, trivial⟩, trivial⟩,
    ⟨trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩,
      ⟨trivial, trivial⟩, trivial⟩, trivial⟩

/-- **The acceptance continuation** from kept cells holding `lo`, `hi`. -/
theorem det_useKept (work count digits yBase : Nat) (layout : SamplerLayout work count digits yBase)
    (memory : Memory) (digitValues : Nat → Nat) (digitsSmall : ∀ e, e < digits → digitValues e < pNat)
    (cellsIn : DigitsIn yBase digits digitValues memory) (lo hi : Nat) (loSmall : lo < 2 ^ 256)
    (hiSmall : hi < 2 ^ 256) (loIn : memory.ram (word (keptLoCell work)) = word lo)
    (hiIn : memory.ram (word (keptHiCell work)) = word hi) :
    ∃ after, det (useKept work count digits yBase) memory = some after ∧
      after.ram = finalRam work count digits (encNat digitValues digits) memory.ram (lo + 2 ^ 256 * hi) ∧
      after.bits = memory.bits ∧
      ∀ index, index ∉ scratch → after.registers index = memory.registers index := by
  obtain ⟨two, fits, apart, yFits⟩ := layout
  obtain ⟨first, firstDet, firstConsts, firstRam, firstBits, firstSame⟩ := det_setup memory
  obtain ⟨second, secondDet, secondRam, secondBits, secondSame⟩ :=
    det_initFrom (keptLoCell work) (keptHiCell work) (limbBase work) count two
      (by unfold limbBase; omega) (by unfold keptHiCell; omega)
      (by unfold keptHiCell limbBase; omega) first lo hi loSmall hiSmall
      (by rw [firstRam, loIn]) (by rw [firstRam, hiIn])
  have secondConsts : Consts second := consts_of_regs firstConsts fun index _ _ n4 _ n8 _ _ _ _ =>
    secondSame index n4 n8
  obtain ⟨third, thirdDet, thirdConsts, thirdRam, thirdBits, thirdSame⟩ :=
    det_macPasses (limbBase work) count digits yBase (by unfold limbBase; omega) yFits
      (by unfold limbBase; omega) second secondConsts (lo + 2 ^ 256 * hi) digitValues digitsSmall
      (fun e bound => by
        rw [secondRam, writeCells_out _ _ _ _ _ (by omega) (by unfold limbBase; omega), firstRam,
          cellsIn e bound])
      (fun index inside => by
        rw [secondRam, writeCells_in _ _ _ _ _ inside (by unfold limbBase; omega)])
  have thirdIs : third.ram = writeCells memory.ram (limbBase work) count
      (limb (samplerValue digits (encNat digitValues digits) (lo + 2 ^ 256 * hi))) := by
    rw [thirdRam, secondRam, writeCells_writeCells, firstRam]
    rfl
  obtain ⟨fourth, fourthDet, _, fourthRam, fourthBits, fourthSame⟩ :=
    det_splitHalves (limbBase work) (halfBase work count) (count - 1) (by unfold limbBase halfBase; omega)
      (by unfold halfBase; omega) third thirdConsts _
      (fun index inside => by rw [thirdIs, writeCells_in _ _ _ _ _ (by omega) (by unfold limbBase; omega)])
  obtain ⟨fifth, fifthDet, fifthRam, fifthBits, fifthSame⟩ := det_clearCells work (by omega) fourth
  refine ⟨fifth, ?_, by rw [fifthRam, fourthRam, thirdIs]; rfl,
    by rw [fifthBits, fourthBits, thirdBits, secondBits, firstBits], fun index out => ?_⟩
  · rw [useKept, Prog.seqList, Prog.seqList, Prog.seqList, Prog.seqList, Prog.seqList, Prog.seqList,
      det_seq_some firstDet, det_seq_some secondDet, det_seq_some thirdDet, det_seq_some fourthDet,
      det_seq_some fifthDet]
    rfl
  · obtain ⟨_, _, _, _, n4, _, _, _, n8, _, n10, _, _⟩ := not_mem_scratch out
    rw [fifthSame index n4 n8, fourthSame index n4 n8 n10, thirdSame index out,
      secondSame index n4 n8, firstSame index out]

/-- The kept draw, read from the kept cells. -/
def keptValue (work : Nat) (memory : Memory) : Nat :=
  (memory.ram (word (keptLoCell work))).toNat + 2 ^ 256 * (memory.ram (word (keptHiCell work))).toNat

/-- The continuation's result on a memory: abort on an empty flag, else the final memory. -/
def finishResult (work count digits enc : Nat) (memory : Memory) : Option Memory :=
  if memory.ram (word (flagCell work)) = 0 then none
  else some (clearRegs (setRam memory (finalRam work count digits enc memory.ram
    (keptValue work memory))) scratch)

theorem plain_finish (work count digits yBase : Nat) : IsPlain (finish work count digits yBase) :=
  ⟨⟨trivial, trivial⟩, ⟨plain_useKept work count digits yBase, trivial⟩, plain_zeroRegs _, trivial⟩

theorem det_finish (work count digits yBase : Nat) (layout : SamplerLayout work count digits yBase)
    (memory : Memory) (digitValues : Nat → Nat) (digitsSmall : ∀ e, e < digits → digitValues e < pNat)
    (cellsIn : DigitsIn yBase digits digitValues memory) :
    det (Prog.seq (finish work count digits yBase) (.skip 0)) memory =
      finishResult work count digits (encNat digitValues digits) memory := by
  obtain ⟨two, fits, apart, yFits⟩ := layout
  set loaded := setReg (setReg memory rAddr (word (flagCell work))) bV (memory.ram (word (flagCell work)))
    with hLoaded
  have loadDet : det (loadAt bV (flagCell work)) memory = some loaded := rfl
  rw [det_seq, finish, Prog.seqList, det_seq_some loadDet, Prog.seqList, det_seq, det]
  have flagIs : loaded.registers bV = memory.ram (word (flagCell work)) := by
    rw [hLoaded, regs_setReg, if_pos rfl]
  rw [flagIs]
  unfold finishResult
  split
  · rfl
  · obtain ⟨after, afterDet, afterRam, afterBits, afterSame⟩ := det_useKept work count digits yBase
      ⟨two, fits, apart, yFits⟩ loaded digitValues digitsSmall cellsIn
      (memory.ram (word (keptLoCell work))).toNat (memory.ram (word (keptHiCell work))).toNat
      (BitVec.isLt _) (BitVec.isLt _) (by rw [hLoaded, ram_setReg, ram_setReg, word_toNat])
      (by rw [hLoaded, ram_setReg, ram_setReg, word_toNat])
    rw [afterDet, Option.bind_some, Prog.seqList, det_seq, det_zeroRegs, Option.bind_some,
      Prog.seqList]
    show some (clearRegs after scratch) = _
    congr 1
    rw [clearRegs_eq_iff]
    refine ⟨by rw [afterRam, hLoaded, ram_setReg, ram_setReg, ram_setRam]; rfl,
      by rw [afterBits, hLoaded, bits_setReg, bits_setReg, bits_setRam], fun index out => ?_⟩
    obtain ⟨_, _, _, _, n4, _, _, _, n8, _, _, _, _⟩ := not_mem_scratch out
    rw [afterSame index out, hLoaded, regs_setReg, if_neg n8, regs_setReg, if_neg n4, regs_setRam]

/-- The continuation reads only what `scrub` keeps. -/
theorem finishResult_scrub (work count digits yBase enc : Nat)
    (layout : SamplerLayout work count digits yBase) (memory : Memory) :
    finishResult work count digits enc (scrub work count memory) =
      finishResult work count digits enc memory := by
  obtain ⟨two, fits, _, _⟩ := layout
  have outside : ∀ cell, cell < drawLoCell work →
      (scrub work count memory).ram (word cell) = memory.ram (word cell) := by
    intro cell below
    rw [scrub_ram, writeCells_out _ _ _ _ _ (by unfold drawLoCell at below; omega) (Or.inl below)]
  unfold finishResult keptValue
  rw [outside _ (by unfold flagCell drawLoCell; omega), outside _ (by unfold keptLoCell drawLoCell; omega),
    outside _ (by unfold keptHiCell drawLoCell; omega)]
  split
  · rfl
  · refine congrArg some ?_
    rw [clearRegs_eq_iff]
    refine ⟨?_, by rw [bits_setRam, bits_setRam, scrub, (clearRegs_other _ _).2, bits_setRam],
      fun index out => ?_⟩
    · rw [ram_setRam, ram_setRam]
      apply finalRam_agree
      intro address outsideRegion
      rw [scrub_ram]
      simp only [writeCells]
      rw [if_neg (by unfold drawLoCell; omega)]
    · rw [regs_setRam, regs_setRam, scrub, clearRegs_registers, if_neg out, regs_setRam]

/-! ### The sampler -/

/-- **The sampler's final memory** for the kept draw `t`: `finalRam` (the halves of
`V = t · p^digits + enc`), every scratch register cleared, nothing else changed. -/
def samplerFinal (work count digits enc : Nat) (memory : Memory) (t : Nat) : Memory :=
  clearRegs (setRam memory (finalRam work count digits enc memory.ram t)) scratch

theorem plain_initCells (work : Nat) : IsPlain (initCells work) :=
  ⟨trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial⟩

/-- **The preimage sampler issues no oracle operation**: its only non-plain parts are the two
coin draws of each attempt. -/
theorem noOracle_preimageSampler (work count digits yBase attempts : Nat) :
    (preimageSampler work count digits yBase attempts).NoOracle :=
  ⟨(plain_initCells work).noOracle, noOracle_rep _ _ fun _ _ =>
      ⟨noOracle_sampleWord _, ⟨rfl, rfl⟩, noOracle_sampleWord _, ⟨rfl, rfl⟩,
        (plain_attemptTail work count digits yBase).noOracle, trivial⟩,
    (plain_finish work count digits yBase).noOracle, trivial⟩

/-- **The law of the preimage sampler** (A1 §4 item 5): bounded rejection over
`hiWidth + 256 = 363` coins with the machine's acceptance (`acceptTop`: the top working limb of
`t · p^digits + enc` is `0`), `attempts` attempts, the kept `t` mapped to `samplerFinal`; an abort
(`none`) iff every attempt was rejected. -/
theorem memSem_preimageSampler [BN254.FieldCertificate] (work count digits yBase attempts : Nat)
    (layout : SamplerLayout work count digits yBase) (memory : Memory) (digitValues : Nat → Nat)
    (digitsSmall : ∀ e, e < digits → digitValues e < pNat)
    (cellsIn : DigitsIn yBase digits digitValues memory) :
    (preimageSampler work count digits yBase attempts).memSem memory =
      (rejectLaw (hiWidth + 256) (acceptTop count digits (encNat digitValues digits)) attempts).map
        (Option.map (samplerFinal work count digits (encNat digitValues digits) memory)) := by
  have layout' := layout
  obtain ⟨two, fits, apart, yFits⟩ := layout'
  set start := storeRam (setReg (storeRam (setReg (storeRam (setReg (setReg memory bV (word 0)) rAddr
      (word (flagCell work))) (word (flagCell work)) (word 0)) rAddr (word (keptLoCell work)))
      (word (keptLoCell work)) (word 0)) rAddr (word (keptHiCell work))) (word (keptHiCell work))
      (word 0) with hStart
  have startDet : det (initCells work) memory = some start := rfl
  have startRam : start.ram = Function.update (Function.update (Function.update memory.ram
      (word (flagCell work)) (word 0)) (word (keptLoCell work)) (word 0)) (word (keptHiCell work))
      (word 0) := rfl
  have ne10 : word (keptLoCell work) ≠ word (flagCell work) :=
    word_ne_of_ne (by unfold keptLoCell; omega) (by unfold flagCell; omega)
      (by unfold keptLoCell flagCell; omega)
  have ne20 : word (keptHiCell work) ≠ word (flagCell work) :=
    word_ne_of_ne (by unfold keptHiCell; omega) (by unfold flagCell; omega)
      (by unfold keptHiCell flagCell; omega)
  have ne21 : word (keptHiCell work) ≠ word (keptLoCell work) :=
    word_ne_of_ne (by unfold keptHiCell; omega) (by unfold keptLoCell; omega)
      (by unfold keptHiCell keptLoCell; omega)
  have startDigits : DigitsIn yBase digits digitValues start := by
    intro e bound
    rw [startRam, Function.update_of_ne, Function.update_of_ne, Function.update_of_ne, cellsIn e bound]
    · exact word_ne_of_ne (by omega) (by unfold flagCell; omega) (by unfold flagCell; omega)
    · exact word_ne_of_ne (by omega) (by unfold keptLoCell; omega) (by unfold keptLoCell; omega)
    · exact word_ne_of_ne (by omega) (by unfold keptHiCell; omega) (by unfold keptHiCell; omega)
  have startFlag : (scrub work count start).ram (word (flagCell work)) = 0 := by
    rw [scrub_ram, writeCells_out _ _ _ _ _ (by unfold flagCell; omega)
      (Or.inl (by unfold flagCell drawLoCell; omega)), startRam, Function.update_of_ne (Ne.symm ne20),
      Function.update_of_ne (Ne.symm ne10), Function.update_self]
    rfl
  have finishLaw : ∀ reached, DigitsIn yBase digits digitValues reached →
      (Prog.seq (finish work count digits yBase) (Prog.seqList [])).memSem reached =
        PMF.pure (finishResult work count digits (encNat digitValues digits)
          (scrub work count reached)) := by
    intro reached holds
    rw [memSem_det (Prog.seq (finish work count digits yBase) (Prog.seqList []))
      ⟨plain_finish work count digits yBase, trivial⟩, Prog.seqList,
      det_finish work count digits yBase layout reached digitValues digitsSmall holds,
      finishResult_scrub work count digits yBase _ layout]
  rw [preimageSampler, Prog.seqList, memSem_seq_plain (plain_initCells work) startDet, Prog.seqList,
    memSem_seq, Prog.seqList]
  have reshape : ((Prog.rep attempts fun _ => tAttempt work count digits yBase).memSem start).bind
      (kleisli (Prog.seq (finish work count digits yBase) (Prog.seqList [])).memSem) =
      (((Prog.rep attempts fun _ => tAttempt work count digits yBase).memSem start).map
        (Option.map (scrub work count))).bind fun state =>
          PMF.pure (state.bind (finishResult work count digits (encNat digitValues digits))) := by
    rw [PMF.bind_map]
    apply PMF.bind_congr
    intro result member
    cases result with
    | none => rfl
    | some reached =>
        simp only [kleisli, Function.comp_apply, Option.map_some, Option.bind_some]
        have reachedIn : some (scrub work count reached) ∈ (keepLaw (hiWidth + 256)
            (keepT work (acceptTop count digits (encNat digitValues digits))) attempts
            (scrub work count start)).support := by
          rw [← rep_tAttempt_law work count digits yBase layout digitValues digitsSmall attempts start
            startDigits, PMF.support_map]
          exact ⟨some reached, member, rfl⟩
        exact finishLaw reached ((digitsIn_scrub work count digits yBase layout digitValues reached).mp
          (keepLaw_digitsIn work count digits yBase layout digitValues _ _ attempts _
            ((digitsIn_scrub work count digits yBase layout digitValues start).mpr startDigits) _
            reachedIn))
  rw [reshape, rep_tAttempt_law work count digits yBase layout digitValues digitsSmall attempts start
      startDigits, keepLaw_eq_rejectLaw _ _ _ _ _ startFlag, PMF.bind_map, ← PMF.bind_pure_comp]
  apply PMF.bind_congr
  intro kept member
  cases kept with
  | none =>
      simp only [Function.comp_apply, keptState, Option.bind_some, Option.map_none]
      unfold finishResult
      rw [if_pos startFlag]
  | some t =>
      obtain ⟨accepted, tSmall⟩ := kept_accepted _ _ _ _ member
      simp only [Function.comp_apply, keptState, Option.bind_some, Option.map_some]
      have keptIs : keepT work (acceptTop count digits (encNat digitValues digits))
          (scrub work count start) t =
          setRam (scrub work count start) (Function.update (Function.update (Function.update
            (scrub work count start).ram (word (keptLoCell work)) (word (t % 2 ^ 256)))
            (word (keptHiCell work)) (word (t / 2 ^ 256))) (word (flagCell work)) 1) := by
        unfold keepT
        rw [if_pos ⟨startFlag, accepted⟩]
      rw [keptIs]
      unfold finishResult
      rw [ram_setRam, Function.update_self, if_neg (by decide)]
      refine congrArg (fun final => PMF.pure (some final)) ?_
      have highSmall : t / 2 ^ 256 < 2 ^ 256 := Nat.div_lt_of_lt_mul (lt_of_lt_of_le tSmall
        (by rw [Nat.pow_add]
            exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by unfold hiWidth; omega))))
      have valueIs : keptValue work (setRam (scrub work count start) (Function.update
          (Function.update (Function.update (scrub work count start).ram (word (keptLoCell work))
            (word (t % 2 ^ 256))) (word (keptHiCell work)) (word (t / 2 ^ 256)))
          (word (flagCell work)) 1)) = t := by
        unfold keptValue
        rw [ram_setRam, Function.update_of_ne ne10, Function.update_of_ne (Ne.symm ne21), Function.update_self,
          Function.update_of_ne ne20, Function.update_self, toNat_word_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)),
          toNat_word_of_lt highSmall, Nat.mod_add_div]
      rw [valueIs]
      unfold samplerFinal
      rw [clearRegs_eq_iff]
      refine ⟨?_, ?_, fun index out => ?_⟩
      · rw [ram_setRam, ram_setRam]
        apply finalRam_agree
        intro address outsideRegion
        have notFlag : address ≠ word (flagCell work) := by
          intro same; rw [same, toNat_word_of_lt (by unfold flagCell; omega)] at outsideRegion
          unfold flagCell at outsideRegion; omega
        have notLo : address ≠ word (keptLoCell work) := by
          intro same; rw [same, toNat_word_of_lt (by unfold keptLoCell; omega)] at outsideRegion
          unfold keptLoCell at outsideRegion; omega
        have notHi : address ≠ word (keptHiCell work) := by
          intro same; rw [same, toNat_word_of_lt (by unfold keptHiCell; omega)] at outsideRegion
          unfold keptHiCell at outsideRegion; omega
        rw [Function.update_of_ne notFlag, Function.update_of_ne notHi, Function.update_of_ne notLo,
          scrub_ram]
        simp only [writeCells]
        rw [if_neg (by unfold drawLoCell; omega), startRam, Function.update_of_ne notHi,
          Function.update_of_ne notLo, Function.update_of_ne notFlag]
      · rw [bits_setRam, bits_setRam, scrub, (clearRegs_other _ _).2, bits_setRam, hStart]
        rfl
      · obtain ⟨_, _, _, _, n4, _, _, _, n8, _, _, _, _⟩ := not_mem_scratch out
        rw [regs_setRam, regs_setRam, scrub, clearRegs_registers, if_neg out, regs_setRam, hStart]
        simp (config := { decide := true }) only [regs_storeRam, regs_setReg, n4, n8, ↓reduceIte]
        rfl

end BigInt

end Kriterion.ArgoMAC.PlanB.SimMachine
