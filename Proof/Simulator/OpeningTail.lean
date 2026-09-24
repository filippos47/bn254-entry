/-
**The opening, step 1: the tail** (`Opening.tail`).

The machine draws the `90` tail digit points `D_1 … D_90` as uniform finite curve points: `x`
by bounded rejection over `254` coins (accepted when `x < p` and `x³ + 3` is a square, the
candidate `(x³ + 3) ^ ((p + 1) / 4)` squaring back), then a fair sign. This is exactly
`curvePointLaw` per digit (`memSem_tailOne`), so the tail is `optionProduct 90 curvePointLaw`
(`memSem_tail`), the product part of the machine's `tailLaw = boundedSamplers.tail` (the clamp
check is the head, `OpeningHorner`). The distance of `tailLaw` to P3's `coinOffsetsLaw` is the
sampler cutoff (`CutoffTail.tail_close`, counted in `samplerCutoff`).

* `memSem_sqrtRounds`, `memSem_curveRoot`: square-and-multiply over the `252` bits of
  `sqrtExponent`, kept symbolic;
* `isTest_testCurveX`: the acceptance test is `curveXAccept`;
* `memSem_tailTail`: the success branch stores `(1, x, ±√(x³ + 3))` at `openPoint d`.
-/

import Proof.Simulator.OpeningBase

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Words -/

omit [FieldCertificate] in
theorem xor_eq_zero_iff (first second : Word) : first ^^^ second = 0 ↔ first = second := by
  constructor
  · intro zero
    have := congrArg (fun value => value ^^^ second) zero
    simpa [BitVec.xor_assoc] using this
  · intro same
    rw [same, BitVec.xor_self]
    rfl

omit [FieldCertificate] in
theorem eval_sub (first second : Word) : Arithmetic.sub.eval first second = first - second := rfl

omit [FieldCertificate] in
theorem eval_mul (first second : Word) : Arithmetic.mul.eval first second = first * second := rfl

omit [FieldCertificate] in
theorem eval_add (first second : Word) : Arithmetic.add.eval first second = first + second := rfl

omit [FieldCertificate] in
theorem word_toNat_eq_zero (value : Word) : value.toNat = 0 ↔ value = 0 := by
  show value.toNat = (0 : Word).toNat ↔ _
  exact BitVec.toNat_inj

omit [FieldCertificate] in
theorem bitWord_and (first second : Bool) :
    Arithmetic.and.eval (bitWord first) (bitWord second) = bitWord (first && second) := by
  cases first <;> cases second <;> rfl

omit [FieldCertificate] in
theorem less_word (value bound : Word) :
    Arithmetic.less.eval value bound = bitWord (decide (value.toNat < bound.toNat)) := by
  unfold Arithmetic.eval bitWord
  by_cases below : value.toNat < bound.toNat <;> simp [below]

theorem fieldWord_one : fieldWord 1 = word 1 := by
  unfold fieldWord
  rw [ZMod.val_one]

theorem fieldWord_natCast {value : Nat} (small : value < pNat) :
    fieldWord (value : BaseField) = word value := by
  unfold fieldWord
  rw [ZMod.val_natCast_of_lt (by unfold pNat at small; exact small)]

omit [FieldCertificate] in
theorem regs_of_clearRegs {first second : Memory} {registers : List Register}
    (same : clearRegs first registers = clearRegs second registers) {index : Register}
    (outside : index ∉ registers) : first.registers index = second.registers index := by
  have := congrArg (fun memory => memory.registers index) same
  simpa [clearRegs_registers, outside] using this

omit [FieldCertificate] in
theorem setReg_self (memory : Memory) (target : Register) (value : Word)
    (already : memory.registers target = value) : setReg memory target value = memory := by
  unfold setReg
  rw [← already, Function.update_eq_self]

/-! ### The square root -/

omit [FieldCertificate] in
theorem sqrtExponent_lt : sqrtExponent < 2 ^ 252 := by decide

omit [FieldCertificate] in
/-- One more exponent bit, most significant first. -/
theorem exponent_step (exponent rounds : Nat) (small : rounds < 252) :
    exponent / 2 ^ (252 - (rounds + 1)) =
      2 * (exponent / 2 ^ (252 - rounds)) + (if exponent.testBit (251 - rounds) then 1 else 0) := by
  have shape : 252 - rounds = (252 - (rounds + 1)) + 1 := by omega
  have index : 251 - rounds = 252 - (rounds + 1) := by omega
  rw [shape, index, pow_succ, ← Nat.div_div_eq_div_mul, Nat.testBit_eq_decide_div_mod_eq]
  generalize exponent / 2 ^ (252 - (rounds + 1)) = value
  have := Nat.div_add_mod value 2
  rcases Nat.mod_two_eq_zero_or_one value with zero | one
  · rw [zero]; simp; omega
  · rw [one]; simp; omega

theorem memSem_sqrtRound (bit : Nat) (base value : BaseField) (memory : Memory)
    (hA : memory.registers rA = fieldWord base) (hB : memory.registers rB = fieldWord value) :
    (Opening.sqrtRound bit).memSem memory =
      PMF.pure (some (setReg memory rB
        (fieldWord (value * value * (if sqrtExponent.testBit bit then base else 1))))) := by
  unfold Opening.sqrtRound
  rw [memSem_ar_val _ _ _ _ _ _ (fieldWord value) (fieldWord value) hB hB, fieldMul_words]
  split
  · rename_i set
    rw [memSem_ar _ _ _ _ _ (fieldWord (value * value)) (fieldWord base) (reg_same _ _ _)
      (by rw [reg_ne _ _ _ _ (by decide), hA]), fieldMul_words, setReg_same]
  · rw [memSem_skip, mul_one]

/-- **`rounds` rounds of square-and-multiply** from `1`: the top `rounds` bits of the exponent. -/
theorem memSem_sqrtRounds (base : BaseField) (memory : Memory)
    (hA : memory.registers rA = fieldWord base) (hB : memory.registers rB = fieldWord 1) :
    ∀ rounds, rounds ≤ 252 →
      (Prog.rep rounds fun round => Opening.sqrtRound (251 - round)).memSem memory =
        PMF.pure (some (setReg memory rB
          (fieldWord (base ^ (sqrtExponent / 2 ^ (252 - rounds))))))
  | 0, _ => by
      rw [Prog.rep, Nat.sub_zero, Nat.div_eq_of_lt sqrtExponent_lt, pow_zero, setReg_self _ _ _ hB]
      rfl
  | rounds + 1, bound => by
      rw [memSem_rep_succ, memSem_sqrtRounds base memory hA hB rounds (by omega), PMF.pure_bind]
      show (Opening.sqrtRound (251 - rounds)).memSem _ = _
      have power : ∀ (bit : Bool) (exponent : Nat), base ^ exponent * base ^ exponent *
          (if bit then base else 1) = base ^ (2 * exponent + if bit then 1 else 0) := by
        intro bit exponent
        cases bit <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring
      rw [memSem_sqrtRound _ base _ _ (by rw [reg_ne _ _ _ _ (by decide), hA]) (reg_same _ _ _),
        setReg_same, exponent_step _ _ (by omega), power]

/-- The curve's right-hand side at the word `value`. -/
def curveRhs (value : Word) : BaseField := ((value.toNat : Nat) : BaseField) ^ 3 + 3

/-- **The candidate root**: `rA = x³ + 3`, `rB = (x³ + 3) ^ ((p + 1) / 4)`. -/
theorem memSem_curveRoot (source : Register) (memory : Memory) (s1 : source ≠ rA) :
    ∃ after, (Opening.curveRoot source).memSem memory = PMF.pure (some after) ∧
      after.registers rA = fieldWord (curveRhs (memory.registers source)) ∧
      after.registers rB = fieldWord (curveRhs (memory.registers source) ^ sqrtExponent) ∧
      clearRegs after [rA, rAddr, rB] = clearRegs memory [rA, rAddr, rB] := by
  set value := memory.registers source with valueDef
  set x : BaseField := ((value.toNat : Nat) : BaseField) with xDef
  unfold Opening.curveRoot
  simp only [Prog.seqList]
  rw [memSem_ar_val _ _ _ _ _ _ value value rfl rfl, eval_fieldMul,
    memSem_ar_val _ _ _ _ _ _ (fieldWord (x * x)) value (reg_same _ _ _)
      (by rw [reg_ne _ _ _ _ s1]), eval_fieldMul, fieldWord_cast, memSem_cst_seq,
    memSem_ar_val _ _ _ _ _ _ (fieldWord (x * x * x)) (word 3)
      (by rw [reg_ne _ _ _ _ (by decide), reg_same]) (reg_same _ _ _),
    eval_fieldAdd, fieldWord_cast, word_small (show 3 < 2 ^ 256 by norm_num), memSem_cst_seq]
  have rhs : x * x * x + ((3 : Nat) : BaseField) = curveRhs value := by
    rw [curveRhs, ← xDef]; push_cast; ring
  rw [rhs]
  set middle := setReg (setReg (setReg (setReg (setReg memory rA (fieldWord (x * x))) rA
    (fieldWord (x * x * x))) rAddr (word 3)) rA (fieldWord (curveRhs value))) rB (word 1)
    with middleDef
  rw [memSem_pure_seq (memSem_sqrtRounds (curveRhs value) middle
      (by rw [middleDef, reg_ne _ _ _ _ (by decide), reg_same])
      (by rw [middleDef, reg_same, fieldWord_one]) 252 le_rfl), memSem_skip]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [reg_ne _ _ _ _ (by decide), middleDef, reg_ne _ _ _ _ (by decide), reg_same]
  · rw [reg_same, Nat.sub_self, pow_zero, Nat.div_one]
  · rw [middleDef]
    simp only [clearRegs_setReg_mem _ _ (show rB ∈ [rA, rAddr, rB] by decide),
      clearRegs_setReg_mem _ _ (show rA ∈ [rA, rAddr, rB] by decide),
      clearRegs_setReg_mem _ _ (show rAddr ∈ [rA, rAddr, rB] by decide)]

/-- **The acceptance test is `curveXAccept`** (junk `rAddr`, `rA` … `rD`). -/
theorem isTest_testCurveX :
    IsTestJ Opening.testCurveX curveXAccept [rAddr, rA, rB, rC, rD] := by
  intro memory
  set value := memory.registers rAcc with valueDef
  have pSmall : pNat < 2 ^ 256 := by decide
  unfold Opening.testCurveX
  simp only [Prog.seqList]
  rw [memSem_cst_seq, memSem_ar_val _ _ _ _ _ _ value (word pNat)
      (by rw [reg_ne _ _ _ _ (by decide)]) (reg_same _ _ _), less_word, word_small pSmall]
  set start := setReg (setReg memory rAddr (word pNat)) rBit
    (bitWord (decide (value.toNat < pNat))) with startDef
  obtain ⟨root, rootRun, rootA, rootB, rootFrame⟩ := memSem_curveRoot rAcc start (by decide)
  have startAcc : start.registers rAcc = value := by
    rw [startDef, reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide)]
  rw [startAcc] at rootA rootB
  rw [memSem_pure_seq rootRun]
  set rhs := curveRhs value with rhsDef
  rw [memSem_ar_val _ _ _ _ _ _ (fieldWord (rhs ^ sqrtExponent)) (fieldWord (rhs ^ sqrtExponent))
      rootB rootB, fieldMul_words,
    memSem_ar_val _ _ _ _ _ _ (fieldWord (rhs ^ sqrtExponent * rhs ^ sqrtExponent)) (fieldWord rhs)
      (reg_same _ _ _) (by rw [reg_ne _ _ _ _ (by decide), rootA]),
    memSem_cst_seq,
    memSem_ar_val _ _ _ _ _ _
      (Arithmetic.xor.eval (fieldWord (rhs ^ sqrtExponent * rhs ^ sqrtExponent)) (fieldWord rhs))
      (word 1) (by rw [reg_ne _ _ _ _ (by decide), reg_same]) (reg_same _ _ _),
    less_word, word_small (show 1 < 2 ^ 256 by norm_num)]
  have rootBit : root.registers rBit = bitWord (decide (value.toNat < pNat)) := by
    rw [regs_of_clearRegs rootFrame (by decide), startDef, reg_same]
  set squareBit := decide ((Arithmetic.xor.eval (fieldWord (rhs ^ sqrtExponent *
    rhs ^ sqrtExponent)) (fieldWord rhs)).toNat < 1) with squareBitDef
  set before := setReg (setReg (setReg (setReg root rC (fieldWord (rhs ^ sqrtExponent *
    rhs ^ sqrtExponent))) rC (Arithmetic.xor.eval (fieldWord (rhs ^ sqrtExponent *
    rhs ^ sqrtExponent)) (fieldWord rhs))) rD (word 1)) rC (bitWord squareBit) with beforeDef
  rw [memSem_ar_val _ _ _ _ _ _ (bitWord (decide (value.toNat < pNat))) (bitWord squareBit)
      (by rw [beforeDef, reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide),
        reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), rootBit])
      (by rw [beforeDef, reg_same]), bitWord_and, memSem_skip]
  have square : squareBit = decide (rhs ^ sqrtExponent * rhs ^ sqrtExponent = rhs) := by
    rw [squareBitDef]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_iff, Nat.lt_one_iff, word_toNat_eq_zero, eval_xor, xor_eq_zero_iff]
    exact ⟨fieldWord_injective, fun same => by rw [same]⟩
  have accept : (decide (value.toNat < pNat) && squareBit) = curveXAccept value.toNat := by
    rw [square, curveXAccept, rhsDef, curveRhs]
  refine ⟨setReg before rBit (memory.registers rBit), ?_, ?_⟩
  · rw [setReg_same, accept]
  · rw [clearRegs_eq_iff]
    refine ⟨?_, ?_, fun index outside => ?_⟩
    · simp only [beforeDef, setReg_ram]
      rw [← (clearRegs_other root [rA, rAddr, rB]).1, rootFrame, (clearRegs_other _ _).1, startDef]
      rfl
    · simp only [beforeDef, setReg_bits]
      rw [← (clearRegs_other root [rA, rAddr, rB]).2, rootFrame, (clearRegs_other _ _).2, startDef]
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
      obtain ⟨notAddr, notA, notB, notC, notD⟩ := outside
      by_cases isBit : index = rBit
      · subst isBit; rw [reg_same]
      · rw [reg_ne _ _ _ _ isBit, beforeDef, reg_ne _ _ _ _ notC, reg_ne _ _ _ _ notD,
          reg_ne _ _ _ _ notC, reg_ne _ _ _ _ notC,
          regs_of_clearRegs rootFrame (by simp [notA, notAddr, notB]), startDef,
          reg_ne _ _ _ _ isBit, reg_ne _ _ _ _ notAddr]

/-! ### One tail digit -/

omit [FieldCertificate] in
/-- The registers one tail digit clears. -/
def tailScratch : List Register := [rAcc, rOut, rFlag, rBit, rAddr, rSel, rA, rB, rC, rD]

/-- The sign-selected root `±(x³ + 3) ^ ((p + 1) / 4)` at the word `value`. -/
def rootY (value : Word) (sign : Bool) : BaseField :=
  if sign then -(curveRhs value ^ sqrtExponent) else curveRhs value ^ sqrtExponent

/-- The memory the success branch of a tail digit leaves: `(1, x, y)` at `openPoint d`, the
scratch cleared. -/
def tailOut (memory : Memory) (digit : Nat) (sign : Bool) : Memory :=
  clearRegs (withRam memory (putPoint memory.ram (openPoint digit)
    (word 1, memory.registers rOut, fieldWord (rootY (memory.registers rOut) sign)))) tailScratch

theorem fieldSub_zero (value : BaseField) :
    Arithmetic.fieldSub.eval (word 0) (fieldWord value) = fieldWord (-value) := by
  rw [eval_fieldSub, fieldWord_cast, word_small (show 0 < 2 ^ 256 by norm_num), Nat.cast_zero,
    zero_sub]

theorem select_sign (value : BaseField) (sign : Bool) :
    (fieldWord (-value) - fieldWord value) * bitWord sign + fieldWord value =
      fieldWord (if sign then -value else value) := by
  cases sign
  · simp only [bitWord, Bool.false_eq_true, if_false]; ring
  · simp only [bitWord, if_true]; ring

/-- What follows the attempts of a tail digit: abort on exhaustion, else the point. -/
def tailTail (digit : Nat) (memory : Memory) : PMF (Option Memory) :=
  if memory.registers rFlag = 0 then PMF.pure none
  else (PMF.uniformOfFintype Bool).map fun sign => some (tailOut memory digit sign)

/-- **The success branch of a tail digit** (then the scratch cleared). -/
theorem memSem_tailTail (digit : Nat) (memory : Memory) :
    (Prog.seq (.ite rFlag (Opening.storeCurvePoint digit) (.abort rSel))
        (Prog.seq (zeroRegs tailScratch) (.skip 0))).memSem memory = tailTail digit memory := by
  unfold tailTail
  rw [memSem_seq]
  have branch : (Prog.ite rFlag (Opening.storeCurvePoint digit) (.abort rSel)).memSem memory =
      if memory.registers rFlag = 0 then PMF.pure none
      else (Opening.storeCurvePoint digit).memSem memory := rfl
  rw [branch]
  split
  · rw [PMF.pure_bind]; rfl
  obtain ⟨root, rootRun, _, rootB, rootFrame⟩ := memSem_curveRoot rOut memory (by decide)
  set rootValue := curveRhs (memory.registers rOut) ^ sqrtExponent with rootValueDef
  unfold Opening.storeCurvePoint
  simp only [Prog.seqList]
  rw [memSem_pure_seq rootRun, memSem_seq, memSem_coinBit, PMF.bind_map, PMF.bind_bind,
    ← PMF.bind_pure_comp]
  refine congrArg (PMF.bind (PMF.uniformOfFintype Bool)) (funext fun sign => ?_)
  simp only [Function.comp_apply, kleisli]
  rw [memSem_cst_seq,
    memSem_ar_val _ _ _ _ _ _ (word 0) (fieldWord rootValue) (reg_same _ _ _)
      (by rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), rootB]), fieldSub_zero,
    memSem_ar_val _ _ _ _ _ _ (fieldWord (-rootValue)) (fieldWord rootValue) (reg_same _ _ _)
      (by rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide),
        rootB]), eval_sub,
    memSem_ar_val _ _ _ _ _ _ (fieldWord (-rootValue) - fieldWord rootValue) (bitWord sign)
      (reg_same _ _ _)
      (by rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide),
        reg_same]), eval_mul,
    memSem_ar_val _ _ _ _ _ _ ((fieldWord (-rootValue) - fieldWord rootValue) * bitWord sign)
      (fieldWord rootValue) (reg_same _ _ _)
      (by rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide),
        reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), rootB]),
    eval_add, select_sign, memSem_cst_seq,
    memSem_storeAt_seq _ _ _ _ (by decide), memSem_storeAt_seq _ _ _ _ (by decide),
    memSem_storeAt_seq _ _ _ _ (by decide), memSem_skip, PMF.pure_bind]
  show (Prog.seq (zeroRegs tailScratch) (.skip 0)).memSem _ = _
  rw [memSem_zeroRegs_seq, memSem_skip]
  have rootRam : root.ram = memory.ram := by
    rw [← (clearRegs_other root [rA, rAddr, rB]).1, rootFrame, (clearRegs_other _ _).1]
  have rootBits : root.bits = memory.bits := by
    rw [← (clearRegs_other root [rA, rAddr, rB]).2, rootFrame, (clearRegs_other _ _).2]
  have rootOut : root.registers rOut = memory.registers rOut :=
    regs_of_clearRegs rootFrame (by decide)
  refine congrArg (fun final => PMF.pure (some final)) ?_
  unfold tailOut
  apply clearRegs_withRam_eq
  · simp only [storeRam_ram, setReg_ram, storeRam_registers, setReg_registers, rootRam, putPoint]
    simp (config := { decide := true }) only [if_true, if_false, rootOut, rootValueDef, rootY]
  · simp only [storeRam_bits, setReg_bits, rootBits]
  · intro index outside
    simp only [tailScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := outside
    simp only [storeRam_registers, setReg_registers, if_neg n0, if_neg n3, if_neg n4, if_neg n8,
      if_neg n9]
    exact regs_of_clearRegs rootFrame (by simp [n4, n6, n7])

/-- A tail offset's three words. -/
def offsetWords (offset : FieldMacToECMac.AffineOffset) : Word × Word × Word :=
  (word 1, fieldWord offset.coordinates.x, fieldWord offset.coordinates.y)

/-- **The memory one tail digit leaves**: the offset's point at `openPoint d`, scratch cleared. -/
def tailMem (memory : Memory) (digit : Nat) (offset : FieldMacToECMac.AffineOffset) : Memory :=
  clearRegs (withRam memory (putPoint memory.ram (openPoint digit) (offsetWords offset))) tailScratch

/-- An accepted `x` gives a point for either sign, stored as the machine stores it. -/
theorem curvePointOf_accepted (value : Nat) (sign : Bool) (accepted : curveXAccept value = true)
    (memory : Memory) (digit : Nat) :
    (curvePointOf value sign).map (tailMem memory digit) =
      some (clearRegs (withRam memory (putPoint memory.ram (openPoint digit)
        (word 1, word value, fieldWord (rootY (word value) sign)))) tailScratch) := by
  have below : value < pNat := by
    unfold curveXAccept at accepted
    simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
    exact accepted.1
  have square : ((value : BaseField) ^ 3 + 3) ^ sqrtExponent * ((value : BaseField) ^ 3 + 3) ^ sqrtExponent =
      (value : BaseField) ^ 3 + 3 := by
    unfold curveXAccept at accepted
    simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
    exact accepted.2
  have rhsWord : curveRhs (word value) = (value : BaseField) ^ 3 + 3 := by
    rw [curveRhs, word_small (lt_trans below (by decide))]
  have onCurve : (if sign then -(((value : BaseField) ^ 3 + 3) ^ sqrtExponent)
      else ((value : BaseField) ^ 3 + 3) ^ sqrtExponent) ^ 2 = (value : BaseField) ^ 3 + 3 := by
    split
    · rw [neg_sq, sq, square]
    · rw [sq, square]
  unfold curvePointOf
  simp only
  rw [dif_pos onCurve, Option.map_some]
  unfold tailMem offsetWords
  simp only [fieldWord_natCast below, rootY, rhsWord]

/-- **One tail digit is `curvePointLaw`**, stored at `openPoint d` (exact). -/
theorem memSem_tailOne (digit : Nat) (memory : Memory) :
    (Opening.tailOne digit).memSem memory =
      curvePointLaw.map (Option.map (tailMem memory digit)) := by
  have scratchJunk : attemptScratch [rAddr, rA, rB, rC, rD] =
      [rAcc, rBit, rAddr, rSel, rAddr, rA, rB, rC, rD] := rfl
  have outOut : rOut ∉ attemptScratch [rAddr, rA, rB, rC, rD] := by rw [scratchJunk]; decide
  have flagOut : rFlag ∉ attemptScratch [rAddr, rA, rB, rC, rD] := by rw [scratchJunk]; decide
  have inside : ∀ index, index ∈ attemptScratch [rAddr, rA, rB, rC, rD] → index ∈ tailScratch := by
    intro index member
    rw [scratchJunk] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    simp only [tailScratch, List.mem_cons, List.not_mem_nil, or_false]
    rcases member with h | h | h | h | h | h | h | h | h <;> simp [h]
  set start := setReg (setReg memory rOut (word 0)) rFlag (word 0) with startDef
  have startFlag : start.registers rFlag = bitWord false := by
    rw [startDef, setReg_registers, if_pos rfl]; rfl
  have shape : (Opening.tailOne digit).memSem memory =
      ((Prog.rep attempts fun _ => attempt fieldWidth Opening.testCurveX).memSem start).bind
        (kleisli (tailTail digit)) := by
    have tailIs : tailTail digit = (Prog.seq (.ite rFlag (Opening.storeCurvePoint digit)
        (.abort rSel)) (Prog.seq (zeroRegs tailScratch) (.skip 0))).memSem :=
      funext fun final => (memSem_tailTail digit final).symm
    unfold Opening.tailOne bounded rejection
    simp only [Prog.seqList]
    rw [memSem_seq, memSem_seq, PMF.bind_bind, memSem_cst_seq, memSem_cst_seq, tailIs]
    refine congrArg (PMF.bind _) (funext fun result => ?_)
    rw [kleisli_bind]
    refine congrArg (kleisli · result) (funext fun final => ?_)
    rw [memSem_seq]
    rfl
  have tailClear : ∀ final, tailTail digit (clearRegs final (attemptScratch [rAddr, rA, rB, rC, rD])) =
      tailTail digit final := by
    intro final
    unfold tailTail
    rw [clearRegs_registers, if_neg flagOut]
    split
    · rfl
    · refine congrArg (PMF.map · _) (funext fun sign => ?_)
      unfold tailOut
      rw [clearRegs_registers, if_neg outOut, (clearRegs_other _ _).1]
      refine congrArg some ?_
      rw [clearRegs_eq_iff]
      refine ⟨rfl, (clearRegs_other _ _).2, fun index outside => ?_⟩
      simp only [withRam_registers]
      rw [clearRegs_registers, if_neg (fun member => outside (inside index member))]
  rw [shape]
  have cleared : ((Prog.rep attempts fun _ => attempt fieldWidth Opening.testCurveX).memSem start).bind
      (kleisli (tailTail digit)) =
      (((Prog.rep attempts fun _ => attempt fieldWidth Opening.testCurveX).memSem start).map
        (Option.map fun final => clearRegs final (attemptScratch [rAddr, rA, rB, rC, rD]))).bind
        (kleisli (tailTail digit)) := by
    rw [PMF.bind_map]
    refine congrArg (PMF.bind _) (funext fun result => ?_)
    cases result with
    | none => rfl
    | some final => exact (tailClear final).symm
  rw [cleared, rep_attempt_law fieldWidth (by unfold fieldWidth; omega) Opening.testCurveX
      curveXAccept [rAddr, rA, rB, rC, rD] isTest_testCurveX (by decide) (by decide) (by decide)
      attempts start ⟨false, startFlag⟩,
    attemptsLaw_eq_rejectLaw fieldWidth _ (attemptScratch [rAddr, rA, rB, rC, rD]) outOut flagOut
      attempts _ (clearRegs_idem _ _) (by rw [clearRegs_registers, if_neg flagOut, startFlag]; rfl),
    PMF.bind_map]
  unfold curvePointLaw
  rw [PMF.map_bind]
  apply PMF.bind_congr
  intro kept positive
  cases kept with
  | none =>
      simp only [Function.comp_apply, kleisli, keptMem, tailTail]
      rw [clearRegs_registers, if_neg flagOut, startFlag,
        if_pos (show bitWord false = 0 from rfl), PMF.pure_map]
      rfl
  | some value =>
      have good := rejectLaw_support fieldWidth curveXAccept attempts value
        ((PMF.mem_support_iff _ _).mpr positive)
      simp only [Function.comp_apply, kleisli, keptMem, tailTail]
      rw [clearRegs_registers, if_neg flagOut, setReg_registers, if_pos rfl,
        if_neg (show (1 : Word) ≠ 0 by decide), PMF.map_comp]
      refine congrArg (PMF.map · _) (funext fun sign => ?_)
      simp only [Function.comp_apply]
      rw [curvePointOf_accepted value sign good.1]
      unfold tailOut
      rw [clearRegs_registers, if_neg outOut, setReg_registers,
        if_neg (show rOut ≠ rFlag by decide), setReg_registers, if_pos rfl,
        (clearRegs_other _ _).1]
      have valueWord : BitVec.ofNat 256 value = word value := rfl
      rw [valueWord]
      refine congrArg some ?_
      rw [clearRegs_eq_iff]
      refine ⟨?_, ?_, fun index outside => ?_⟩
      · simp only [withRam_ram, setReg_ram, (clearRegs_other _ _).1, startDef]
      · simp only [withRam_bits, setReg_bits, (clearRegs_other _ _).2, startDef]
      · simp only [withRam_registers]
        simp only [tailScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
        obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := outside
        rw [clearRegs_registers, if_neg (fun member => by
            rw [scratchJunk] at member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with h | h | h | h | h | h | h | h | h <;> simp_all),
          setReg_registers, if_neg n2, setReg_registers, if_neg n1, clearRegs_registers,
          if_neg (fun member => by
            rw [scratchJunk] at member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with h | h | h | h | h | h | h | h | h <;> simp_all),
          startDef, setReg_registers, if_neg n2, setReg_registers, if_neg n1]

/-- **The tail**: `90` independent `curvePointLaw` draws, digit `k + 1` stored at `openPoint`. -/
theorem memSem_tail (memory : Memory) :
    Opening.tail.memSem memory =
      (optionProduct 90 fun _ => curvePointLaw).map
        (Option.map (foldStore (fun index memory offset => tailMem memory (index + 1) offset) 90
          memory)) :=
  memSem_rep_law curvePointLaw 90 _ _ (fun index memory => memSem_tailOne (index + 1) memory) memory

/-! ### The RAM the tail leaves -/

/-- The memory after the tail's `90` digits. -/
abbrev tailFold (memory : Memory) (points : Fin 90 → FieldMacToECMac.AffineOffset) : Memory :=
  foldStore (fun index memory offset => tailMem memory (index + 1) offset) 90 memory points

omit [FieldCertificate] in
theorem tailMem_ram (memory : Memory) (digit : Nat) (offset : FieldMacToECMac.AffineOffset) :
    (tailMem memory digit offset).ram = putPoint memory.ram (openPoint digit) (offsetWords offset) := by
  unfold tailMem
  rw [(clearRegs_other _ _).1]
  rfl

omit [FieldCertificate] in
theorem tailMem_bits (memory : Memory) (digit : Nat) (offset : FieldMacToECMac.AffineOffset) :
    (tailMem memory digit offset).bits = memory.bits := by
  unfold tailMem
  rw [(clearRegs_other _ _).2]
  rfl

theorem tailFold_bits (memory : Memory) (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    (tailFold memory points).bits = memory.bits :=
  foldStore_bits _ (fun index memory offset => tailMem_bits memory (index + 1) offset) _ _ _

theorem tailFold_sameOff (memory : Memory) (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    SameOff memory.ram (tailFold memory points).ram :=
  foldStore_invariant (fun later => SameOff memory.ram later.ram) _ 90
    (fun index bound later offset previous => previous.trans (by
      rw [tailMem_ram]
      exact sameOff_putPoint _ (3 * (index + 1)) (by omega) _)) memory points (SameOff.refl _)

/-- The tail's cells hold the drawn points. -/
theorem tailFold_at (memory : Memory) (points : Fin 90 → FieldMacToECMac.AffineOffset)
    (index : Fin 90) (position : Nat) (inside : position < 3) :
    (tailFold memory points).ram (word (openPoint (index.val + 1) + position)) =
      wordAt (offsetWords (points index)) position :=
  foldStore_putPoint_at _ (fun index => openPoint (index + 1)) offsetWords
    (fun index memory offset => tailMem_ram memory (index + 1) offset) 90
    (fun index bound => by unfold openPoint openBase; omega)
    (fun first second firstBound secondBound different position position' inside inside' =>
      word_ne (by unfold openPoint openBase; omega) (by unfold openPoint openBase; omega)
        (by unfold openPoint; omega))
    memory points index position inside

/-- Addresses off the tail's cells keep their contents. -/
theorem tailFold_off (memory : Memory) (points : Fin 90 → FieldMacToECMac.AffineOffset)
    (target : Word)
    (away : ∀ index, index < 90 → ∀ position, position < 3 →
      target ≠ word (openPoint (index + 1) + position)) :
    (tailFold memory points).ram target = memory.ram target :=
  foldStore_putPoint_off _ (fun index => openPoint (index + 1)) offsetWords
    (fun index memory offset => tailMem_ram memory (index + 1) offset) 90 memory points target away

end

end Kriterion.ArgoMAC.PlanB.SimMachine
