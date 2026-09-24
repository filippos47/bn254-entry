/-
**Stage 2's request prefix, end to end.**

* `memSem_parse`: the parse of `affine u ++ output (f_k u)` stores `u.x`, `u.y`, both tag bits
  and `Q` (zero when absent) in the request cells and empties stack `0`;
* `memSem_prefix`: the whole prefix (parse, label selection, flag) leaves label `i` equal to
  the key cell `keyBase + 2 i + (bit i of u)`, every other RAM cell outside the request and
  label regions unchanged, and `rFlag = tag₀ + tag₁`.
-/

import Proof.Simulator.Stage2Labels

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

section Request

variable [FieldCertificate]

/-- The request cells after the parse. -/
def parsedRam (ram : Word → Word) (x y : Nat) (t0 t1 : Bool) (qx qy : Nat) : Word → Word :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update ram (word reqX) (word x)) (word reqY) (word y)) (word reqTag0) (bitWord t0))
    (word reqTag1) (bitWord t1)) (word reqQX) (word qx)) (word reqQY) (word qy)

/-- The output bits of a request, after the two coordinates: the tags, then `Q` when `t₀`. -/
def OutBits (out : List Bool) (t0 t1 : Bool) (qx qy : Nat) : Prop :=
  if t0 then out = true :: t1 :: (lsbs 254 qx ++ lsbs 254 qy) ∧ qx < 2 ^ 254 ∧ qy < 2 ^ 254
  else out = [false, t1] ∧ qx = 0 ∧ qy = 0

omit [FieldCertificate] in
theorem setReg_ram (memory : Memory) (target : Register) (value : Word) :
    (setReg memory target value).ram = memory.ram := rfl

omit [FieldCertificate] in
theorem setReg_bits (memory : Memory) (target : Register) (value : Word) :
    (setReg memory target value).bits = memory.bits := rfl

/-- Pop one bit of the request and store it. -/
def popStoreMem (memory : Memory) (address : Nat) (bit : Bool) (rest : List Bool) : Memory :=
  storeRam (setReg (setReg { memory with bits := Function.update memory.bits 0 rest } rBit
    (bitWord bit)) rAddr (word address)) (word address) (bitWord bit)

theorem memSem_popStore (address : Nat) (memory : Memory) (bit : Bool) (rest : List Bool)
    (top : memory.bits 0 = bit :: rest) :
    (Prog.seq (.popBit 0 rBit) (storeAt address rBit)).memSem memory =
      PMF.pure (some (popStoreMem memory address bit rest)) := by
  have popped : popInto memory 0 rBit =
      setReg { memory with bits := Function.update memory.bits 0 rest } rBit (bitWord bit) := by
    simp only [popInto, top]
    cases bit <;> rfl
  simp only [storeAt, cst, Prog.memSem, Op.memSem, PMF.pure_bind, popped]
  simp only [setReg_registers, show rBit ≠ rAddr by decide, if_false]
  rfl

theorem memSem_popStore_seq (address : Nat) (memory : Memory) (bit : Bool) (rest : List Bool)
    (top : memory.bits 0 = bit :: rest) (next : Prog) :
    (Prog.seq (.popBit 0 rBit) (.seq (storeAt address rBit) next)).memSem memory =
      next.memSem (popStoreMem memory address bit rest) := by
  have popped : popInto memory 0 rBit =
      setReg { memory with bits := Function.update memory.bits 0 rest } rBit (bitWord bit) := by
    simp only [popInto, top]
    cases bit <;> rfl
  simp only [storeAt, cst, Prog.memSem, Op.memSem, PMF.pure_bind, popped]
  simp only [setReg_registers, show rBit ≠ rAddr by decide, if_false]
  rfl

theorem memSem_ite_set (source : Register) (whenSet whenClear : Prog) (memory : Memory)
    (set : memory.registers source ≠ 0) :
    (Prog.ite source whenSet whenClear).memSem memory = whenSet.memSem memory := by
  simp only [Prog.memSem, if_neg set]

theorem memSem_ite_clear (source : Register) (whenSet whenClear : Prog) (memory : Memory)
    (clear : memory.registers source = 0) :
    (Prog.ite source whenSet whenClear).memSem memory = whenClear.memSem memory := by
  simp only [Prog.memSem, if_pos clear]

theorem popStoreMem_bits (memory : Memory) (address : Nat) (bit : Bool) (rest : List Bool) :
    (popStoreMem memory address bit rest).bits = Function.update memory.bits 0 rest := rfl

theorem popStoreMem_ram (memory : Memory) (address : Nat) (bit : Bool) (rest : List Bool) :
    (popStoreMem memory address bit rest).ram =
      Function.update memory.ram (word address) (bitWord bit) := rfl

theorem word_request_lt (offset : Nat) (small : offset < 6) : requestBase + offset < 2 ^ 256 := by
  unfold requestBase; omega

theorem bitWord_ne_zero_iff (bit : Bool) : bitWord bit ≠ 0 ↔ bit = true := by
  cases bit <;> decide

/-- **The parse.** -/
theorem memSem_parse (memory : Memory) (x y : Nat) (hx : x < 2 ^ 254) (hy : y < 2 ^ 254)
    (out : List Bool) (t0 t1 : Bool) (qx qy : Nat) (shape : OutBits out t0 t1 qx qy)
    (start : memory.bits 0 = lsbs 254 x ++ (lsbs 254 y ++ out)) :
    ∃ after, Request.parse.memSem memory = PMF.pure (some after) ∧
      after.bits = Function.update memory.bits 0 [] ∧
      after.ram = parsedRam memory.ram x y t0 t1 qx qy := by
  obtain ⟨m1, run1, bits1, ram1, others1, _⟩ := memSem_parseWord reqX x hx _ memory start
  obtain ⟨m2, run2, bits2, ram2, others2, _⟩ := memSem_parseWord reqY y hy out m1 bits1
  -- the tags
  obtain ⟨rest, outEq⟩ : ∃ rest, out = t0 :: t1 :: rest := by
    unfold OutBits at shape
    cases t0
    · rw [if_neg (by decide)] at shape
      exact ⟨[], shape.1⟩
    · rw [if_pos rfl] at shape
      exact ⟨_, shape.1⟩
  rw [outEq] at bits2
  set m3 := popStoreMem m2 reqTag0 t0 (t1 :: rest) with m3Def
  have run3 := memSem_popStore reqTag0 m2 t0 (t1 :: rest) bits2
  have bits3 : m3.bits 0 = t1 :: rest := by rw [m3Def, popStoreMem_bits, Function.update_self]
  set m4 := popStoreMem m3 reqTag1 t1 rest with m4Def
  have run4 := memSem_popStore reqTag1 m3 t1 rest bits3
  set m5 := setReg (setReg m4 rAddr (word reqTag0)) rFlag (m4.ram (word reqTag0)) with m5Def
  have tag0Cell : m4.ram (word reqTag0) = bitWord t0 := by
    have ne : word reqTag0 ≠ word reqTag1 := word_ne (by unfold reqTag0 requestBase; norm_num)
      (by unfold reqTag1 requestBase; norm_num) (by unfold reqTag0 reqTag1; omega)
    rw [m4Def, popStoreMem_ram, Function.update_of_ne ne, m3Def, popStoreMem_ram,
      Function.update_self]
  have flag5 : m5.registers rFlag = bitWord t0 := by
    rw [m5Def, setReg_registers, if_pos rfl, tag0Cell]
  have ram5 : m5.ram = Function.update (Function.update
      (Function.update (Function.update memory.ram (word reqX) (word x)) (word reqY) (word y))
      (word reqTag0) (bitWord t0)) (word reqTag1) (bitWord t1) := by
    rw [m5Def]
    show m4.ram = _
    rw [m4Def, popStoreMem_ram, m3Def, popStoreMem_ram, ram2, ram1]
  have bitsRest : m5.bits 0 = rest := by
    rw [m5Def]
    show m4.bits 0 = rest
    rw [m4Def, popStoreMem_bits, Function.update_self]
  have bitsOther : ∀ stack, stack ≠ 0 → m5.bits stack = memory.bits stack := by
    intro stack other
    show m4.bits stack = _
    rw [m4Def, popStoreMem_bits, Function.update_of_ne other, m3Def, popStoreMem_bits,
      Function.update_of_ne other, others2 stack other, others1 stack other]
  -- the prefix up to the branch
  have upToBranch : Request.parse.memSem memory =
      (Prog.seq (.ite rFlag (.seq (Request.parseWord reqQX) (Request.parseWord reqQY))
        (.seq (cst rA 0) (.seq (storeAt reqQX rA) (storeAt reqQY rA))))
        (zeroRegs [rAcc, rBit, rAddr, rFlag, rA])).memSem m5 := by
    unfold Request.parse
    rw [memSem_seq, run1, PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_seq, run2, PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_popStore_seq reqTag0 m2 t0 (t1 :: rest) bits2, ← m3Def,
      memSem_popStore_seq reqTag1 m3 t1 rest bits3, ← m4Def, memSem_seq]
    simp only [loadAt, cst, Prog.memSem, Op.memSem, PMF.pure_bind, kleisli, setReg_registers,
      if_pos rfl]
    rfl
  rw [upToBranch]
  unfold OutBits at shape
  cases t0 with
  | false =>
      obtain ⟨outShape, qx0, qy0⟩ := shape
      subst qx0 qy0
      have restNil : rest = [] := by
        rw [outEq] at outShape
        simp only [List.cons.injEq] at outShape
        exact outShape.2.2
      subst restNil
      refine ⟨clearRegs (storeRam (setReg (storeRam (setReg (setReg m5 rA (word 0)) rAddr
        (word reqQX)) (word reqQX) (word 0)) rAddr (word reqQY)) (word reqQY) (word 0))
        [rAcc, rBit, rAddr, rFlag, rA], ?_, ?_, ?_⟩
      · rw [memSem_seq, memSem_ite_clear _ _ _ _ (by rw [flag5]; rfl)]
        simp only [storeAt, cst, Prog.memSem, Op.memSem, PMF.pure_bind, setReg_registers,
          if_pos rfl, show rA ≠ rAddr by decide, if_false, kleisli, memSem_zeroRegs]
        rfl
      · rw [(clearRegs_other _ _).2]
        funext stack
        by_cases zero : stack = 0
        · subst zero
          simp only [storeRam, setReg, Function.update_self]
          exact bitsRest
        · simp only [storeRam, setReg, Function.update_of_ne zero]
          exact bitsOther stack zero
      · rw [(clearRegs_other _ _).1]
        simp only [storeRam, setReg]
        rw [ram5]
        rfl
  | true =>
      obtain ⟨outShape, qxSmall, qySmall⟩ := shape
      rw [outEq] at outShape
      simp only [List.cons.injEq, true_and] at outShape
      rw [outShape] at bitsRest
      obtain ⟨m6, run6, bits6, ram6, others6, _⟩ :=
        memSem_parseWord reqQX qx qxSmall _ m5 bitsRest
      obtain ⟨m7, run7, bits7, ram7, others7, _⟩ :=
        memSem_parseWord reqQY qy qySmall [] m6 (by rw [bits6, List.append_nil])
      refine ⟨clearRegs m7 [rAcc, rBit, rAddr, rFlag, rA], ?_, ?_, ?_⟩
      · rw [memSem_seq, memSem_ite_set _ _ _ _ (by rw [flag5]; decide), memSem_seq, run6,
          PMF.pure_bind]
        simp only [kleisli]
        rw [run7, PMF.pure_bind]
        simp only [kleisli, memSem_zeroRegs]
      · rw [(clearRegs_other _ _).2]
        funext stack
        by_cases zero : stack = 0
        · subst zero
          rw [bits7, Function.update_self]
        · rw [Function.update_of_ne zero, others7 stack zero, others6 stack zero,
            bitsOther stack zero]
      · rw [(clearRegs_other _ _).1, ram7, ram6, ram5]
        rfl

/-! ### The request cells -/

theorem requestCell_lt (offset : Nat) (small : offset < 6) : requestBase + offset < 2 ^ 256 := by
  unfold requestBase; omega

theorem requestCell_ne (first second : Nat) (firstSmall : first < 6) (secondSmall : second < 6)
    (different : first ≠ second) : word (requestBase + first) ≠ word (requestBase + second) :=
  word_ne (requestCell_lt first firstSmall) (requestCell_lt second secondSmall) (by omega)

theorem reqX_ne_Y : word reqX ≠ word reqY :=
  requestCell_ne 0 1 (by omega) (by omega) (by omega)

theorem reqX_ne_T0 : word reqX ≠ word reqTag0 :=
  requestCell_ne 0 2 (by omega) (by omega) (by omega)

theorem reqX_ne_T1 : word reqX ≠ word reqTag1 :=
  requestCell_ne 0 3 (by omega) (by omega) (by omega)

theorem reqX_ne_QX : word reqX ≠ word reqQX :=
  requestCell_ne 0 4 (by omega) (by omega) (by omega)

theorem reqX_ne_QY : word reqX ≠ word reqQY :=
  requestCell_ne 0 5 (by omega) (by omega) (by omega)

theorem reqY_ne_X : word reqY ≠ word reqX :=
  requestCell_ne 1 0 (by omega) (by omega) (by omega)

theorem reqY_ne_T0 : word reqY ≠ word reqTag0 :=
  requestCell_ne 1 2 (by omega) (by omega) (by omega)

theorem reqY_ne_T1 : word reqY ≠ word reqTag1 :=
  requestCell_ne 1 3 (by omega) (by omega) (by omega)

theorem reqY_ne_QX : word reqY ≠ word reqQX :=
  requestCell_ne 1 4 (by omega) (by omega) (by omega)

theorem reqY_ne_QY : word reqY ≠ word reqQY :=
  requestCell_ne 1 5 (by omega) (by omega) (by omega)

theorem reqT0_ne_X : word reqTag0 ≠ word reqX :=
  requestCell_ne 2 0 (by omega) (by omega) (by omega)

theorem reqT0_ne_Y : word reqTag0 ≠ word reqY :=
  requestCell_ne 2 1 (by omega) (by omega) (by omega)

theorem reqT0_ne_T1 : word reqTag0 ≠ word reqTag1 :=
  requestCell_ne 2 3 (by omega) (by omega) (by omega)

theorem reqT0_ne_QX : word reqTag0 ≠ word reqQX :=
  requestCell_ne 2 4 (by omega) (by omega) (by omega)

theorem reqT0_ne_QY : word reqTag0 ≠ word reqQY :=
  requestCell_ne 2 5 (by omega) (by omega) (by omega)

theorem reqT1_ne_X : word reqTag1 ≠ word reqX :=
  requestCell_ne 3 0 (by omega) (by omega) (by omega)

theorem reqT1_ne_Y : word reqTag1 ≠ word reqY :=
  requestCell_ne 3 1 (by omega) (by omega) (by omega)

theorem reqT1_ne_T0 : word reqTag1 ≠ word reqTag0 :=
  requestCell_ne 3 2 (by omega) (by omega) (by omega)

theorem reqT1_ne_QX : word reqTag1 ≠ word reqQX :=
  requestCell_ne 3 4 (by omega) (by omega) (by omega)

theorem reqT1_ne_QY : word reqTag1 ≠ word reqQY :=
  requestCell_ne 3 5 (by omega) (by omega) (by omega)

theorem reqQX_ne_X : word reqQX ≠ word reqX :=
  requestCell_ne 4 0 (by omega) (by omega) (by omega)

theorem reqQX_ne_Y : word reqQX ≠ word reqY :=
  requestCell_ne 4 1 (by omega) (by omega) (by omega)

theorem reqQX_ne_T0 : word reqQX ≠ word reqTag0 :=
  requestCell_ne 4 2 (by omega) (by omega) (by omega)

theorem reqQX_ne_T1 : word reqQX ≠ word reqTag1 :=
  requestCell_ne 4 3 (by omega) (by omega) (by omega)

theorem reqQX_ne_QY : word reqQX ≠ word reqQY :=
  requestCell_ne 4 5 (by omega) (by omega) (by omega)

theorem reqQY_ne_X : word reqQY ≠ word reqX :=
  requestCell_ne 5 0 (by omega) (by omega) (by omega)

theorem reqQY_ne_Y : word reqQY ≠ word reqY :=
  requestCell_ne 5 1 (by omega) (by omega) (by omega)

theorem reqQY_ne_T0 : word reqQY ≠ word reqTag0 :=
  requestCell_ne 5 2 (by omega) (by omega) (by omega)

theorem reqQY_ne_T1 : word reqQY ≠ word reqTag1 :=
  requestCell_ne 5 3 (by omega) (by omega) (by omega)

theorem reqQY_ne_QX : word reqQY ≠ word reqQX :=
  requestCell_ne 5 4 (by omega) (by omega) (by omega)

/-- An address outside the six request cells. -/
def OffRequest (address : Word) : Prop := ∀ offset, offset < 6 → address ≠ word (requestBase + offset)

theorem parsedRam_off (ram : Word → Word) (x y : Nat) (t0 t1 : Bool) (qx qy : Nat) (address : Word)
    (off : OffRequest address) : parsedRam ram x y t0 t1 qx qy address = ram address := by
  unfold parsedRam
  rw [Function.update_of_ne (show address ≠ word reqQY from off 5 (by omega)),
    Function.update_of_ne (show address ≠ word reqQX from off 4 (by omega)),
    Function.update_of_ne (show address ≠ word reqTag1 from off 3 (by omega)),
    Function.update_of_ne (show address ≠ word reqTag0 from off 2 (by omega)),
    Function.update_of_ne (show address ≠ word reqY from off 1 (by omega)),
    Function.update_of_ne (show address ≠ word reqX from off 0 (by omega))]

theorem parsedRam_x (ram : Word → Word) (x y : Nat) (t0 t1 : Bool) (qx qy : Nat) :
    parsedRam ram x y t0 t1 qx qy (word reqX) = word x := by
  unfold parsedRam
  rw [Function.update_of_ne reqX_ne_QY,
    Function.update_of_ne reqX_ne_QX,
    Function.update_of_ne reqX_ne_T1,
    Function.update_of_ne reqX_ne_T0,
    Function.update_of_ne reqX_ne_Y,
    Function.update_self]

theorem parsedRam_y (ram : Word → Word) (x y : Nat) (t0 t1 : Bool) (qx qy : Nat) :
    parsedRam ram x y t0 t1 qx qy (word reqY) = word y := by
  unfold parsedRam
  rw [Function.update_of_ne reqY_ne_QY,
    Function.update_of_ne reqY_ne_QX,
    Function.update_of_ne reqY_ne_T1,
    Function.update_of_ne reqY_ne_T0,
    Function.update_self]

theorem parsedRam_tag0 (ram : Word → Word) (x y : Nat) (t0 t1 : Bool) (qx qy : Nat) :
    parsedRam ram x y t0 t1 qx qy (word reqTag0) = bitWord t0 := by
  unfold parsedRam
  rw [Function.update_of_ne reqT0_ne_QY,
    Function.update_of_ne reqT0_ne_QX,
    Function.update_of_ne reqT0_ne_T1,
    Function.update_self]

theorem parsedRam_tag1 (ram : Word → Word) (x y : Nat) (t0 t1 : Bool) (qx qy : Nat) :
    parsedRam ram x y t0 t1 qx qy (word reqTag1) = bitWord t1 := by
  unfold parsedRam
  rw [Function.update_of_ne reqT1_ne_QY,
    Function.update_of_ne reqT1_ne_QX,
    Function.update_self]

theorem parsedRam_qx (ram : Word → Word) (x y : Nat) (t0 t1 : Bool) (qx qy : Nat) :
    parsedRam ram x y t0 t1 qx qy (word reqQX) = word qx := by
  unfold parsedRam
  rw [Function.update_of_ne reqQX_ne_QY,
    Function.update_self]

theorem parsedRam_qy (ram : Word → Word) (x y : Nat) (t0 t1 : Bool) (qx qy : Nat) :
    parsedRam ram x y t0 t1 qx qy (word reqQY) = word qy := by
  unfold parsedRam
  rw [Function.update_self]

/-- Bit `i` of the input `(x, y)`, the selector of label `i`. -/
def inputBit (x y : Nat) (position : Nat) : Nat :=
  if position < 254 then (x >>> position) % 2 else (y >>> (position % 254)) % 2

theorem inputBit_le (x y position : Nat) : inputBit x y position ≤ 1 := by
  unfold inputBit
  split <;> omega

theorem labelCell_lt (index : Nat) (small : index < labelCount) : labelBase + index < 2 ^ 256 := by
  have : index < 508 := small
  unfold labelBase; omega

theorem keyCell_lt (index : Nat) (small : index < keyBlockCount) : keyBase + index < 2 ^ 256 := by
  have : index < 1016 := small
  unfold keyBase; omega

theorem label_offRequest (index : Nat) (small : index < labelCount) :
    OffRequest (word (labelBase + index)) := by
  intro offset bound
  have : index < 508 := small
  exact word_ne (labelCell_lt index small) (requestCell_lt offset bound)
    (by unfold labelBase requestBase; omega)

theorem key_offRequest (index : Nat) (small : index < keyBlockCount) :
    OffRequest (word (keyBase + index)) := by
  intro offset bound
  have : index < 1016 := small
  exact word_ne (keyCell_lt index small) (requestCell_lt offset bound)
    (by unfold keyBase requestBase; omega)

theorem keyAddress_parsed (ram : Word → Word) (x y : Nat) (hx : x < 2 ^ 254) (hy : y < 2 ^ 254)
    (t0 t1 : Bool) (qx qy : Nat) (position : Nat) (small : position < labelCount) :
    keyAddress (parsedRam ram x y t0 t1 qx qy) position =
      word (keyBase + 2 * position + inputBit x y position) := by
  have positionSmall : position < 508 := small
  have bitLe := inputBit_le x y position
  apply BitVec.eq_of_toNat_eq
  rw [keyAddress_toNat _ _ small]
  have cell : (parsedRam ram x y t0 t1 qx qy (word (Request.bitCell position))).toNat =
      if position < 254 then x else y := by
    unfold Request.bitCell
    split
    · rw [parsedRam_x, word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [parsedRam_y, word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have sum : keyBase + 2 * position + inputBit x y position < 2 ^ 256 := by
    unfold keyBase; omega
  rw [cell, word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sum]
  unfold inputBit
  split
  · rename_i low
    rw [Nat.mod_eq_of_lt low]
  · rfl

/-! ### The prefix -/

/-- **The prefix.** -/
theorem memSem_prefix (memory : Memory) (x y : Nat) (hx : x < 2 ^ 254) (hy : y < 2 ^ 254)
    (out : List Bool) (t0 t1 : Bool) (qx qy : Nat) (shape : OutBits out t0 t1 qx qy)
    (start : memory.bits 0 = lsbs 254 x ++ (lsbs 254 y ++ out)) :
    ∃ after, Request.prefixProgram.memSem memory = PMF.pure (some after) ∧
      after.bits = Function.update memory.bits 0 [] ∧
      (∀ position, position < labelCount → after.ram (word (labelBase + position)) =
        memory.ram (word (keyBase + 2 * position + inputBit x y position))) ∧
      (∀ address, (∀ position, position < labelCount → address ≠ word (labelBase + position)) →
        after.ram address = parsedRam memory.ram x y t0 t1 qx qy address) ∧
      after.registers rFlag = bitWord t0 + bitWord t1 := by
  obtain ⟨parsed, runParse, bitsParse, ramParse⟩ :=
    memSem_parse memory x y hx hy out t0 t1 qx qy shape start
  obtain ⟨selected, runSelect, bitsSelect, labels, away⟩ := select_steps parsed labelCount le_rfl
  have ramAway : ∀ address, (∀ position, position < labelCount →
      address ≠ word (labelBase + position)) →
      selected.ram address = parsedRam memory.ram x y t0 t1 qx qy address := by
    intro address outside
    rw [away address outside, ramParse]
  have tag0 : selected.ram (word reqTag0) = bitWord t0 := by
    rw [ramAway (word reqTag0) fun position bound same => label_offRequest position bound 2
      (by omega) same.symm, parsedRam_tag0]
  have tag1 : selected.ram (word reqTag1) = bitWord t1 := by
    rw [ramAway (word reqTag1) fun position bound same => label_offRequest position bound 3
      (by omega) same.symm, parsedRam_tag1]
  set cleared := clearRegs selected [rAddr, rA, rB, rC] with clearedDef
  have clearedRam : cleared.ram = selected.ram := (clearRegs_other _ _).1
  refine ⟨setReg (setReg (setReg (setReg (setReg cleared rAddr (word reqTag0)) rFlag
      (bitWord t0)) rAddr (word reqTag1)) rBit (bitWord t1)) rFlag (bitWord t0 + bitWord t1),
    ?_, ?_, fun position bound => ?_, fun address outside => ?_, ?_⟩
  · unfold Request.prefixProgram
    rw [memSem_seq, runParse, PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_seq]
    unfold Request.selectLabels
    rw [memSem_seq, runSelect, PMF.pure_bind]
    simp only [kleisli, memSem_zeroRegs, PMF.pure_bind, ← clearedDef]
    simp only [loadAt, cst, ar, Prog.memSem, Op.memSem, PMF.pure_bind, setReg_registers,
      setReg_ram, if_true, clearedRam, tag0, tag1, show rFlag ≠ rAddr by decide,
      show rFlag ≠ rBit by decide, show rBit ≠ rAddr by decide, if_false,
      Arithmetic.eval]
  · show cleared.bits = _
    rw [(clearRegs_other _ _).2, bitsSelect, bitsParse]
  · show cleared.ram _ = _
    have keySmall : 2 * position + inputBit x y position < keyBlockCount := by
      have := inputBit_le x y position
      have : position < 508 := bound
      unfold keyBlockCount; omega
    rw [clearedRam, labels position bound, ramParse,
      keyAddress_parsed _ x y hx hy t0 t1 qx qy position bound, Nat.add_assoc,
      parsedRam_off _ _ _ _ _ _ _ _ (key_offRequest _ keySmall)]
  · show cleared.ram _ = _
    rw [clearedRam, ramAway address outside]
  · rw [setReg_registers, if_pos rfl]

end Request

end

end Kriterion.ArgoMAC.PlanB.SimMachine
