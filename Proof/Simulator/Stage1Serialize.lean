/-
**The law of stage 1's serializer.**

`serialize` pushes the wire bits in reverse wire order; each `emitWord address width` pushes the
low `width` bits of `RAM[address]`, least significant on top. `memSem_serialize`: the serializer
is deterministic, leaves the RAM and the other stacks unchanged, and leaves stack `3` holding
`serialBits RAM` (the curve-and-rows word, the gadget word, fold joins, the `52` scale chunk
words, each least significant bit first) on top of the old stack. The curve-and-rows word and
each chunk word are base-`p` numbers, built in the limb scratch by the big-integer Horner encoder
and emitted limb by limb (`fieldsLimbBits`, `chunkWordBits`, `memSem_serializeFields`,
`memSem_serializeChunk`).
-/

import Proof.Simulator.Stage1Cells
import Proof.Simulator.Stage1Bits
import Proof.Simulator.BigIntMachine
import Construction.PGS.Encoding

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks

noncomputable section

/-- `after` is `before` with `bits` pushed on top of stack `3`, and nothing else changed except
registers. -/
def Emits (before after : Memory) (bits : List Bool) : Prop :=
  after.ram = before.ram ∧ after.bits 3 = bits ++ before.bits 3 ∧
    ∀ stack, stack ≠ 3 → after.bits stack = before.bits stack

theorem Emits.trans {first middle last : Memory} {bits bits' : List Bool}
    (one : Emits first middle bits) (two : Emits middle last bits') :
    Emits first last (bits' ++ bits) :=
  ⟨two.1.trans one.1, by rw [two.2.1, one.2.1, List.append_assoc], fun stack other => by
    rw [two.2.2 stack other, one.2.2 stack other]⟩

theorem Emits.refl (memory : Memory) : Emits memory memory [] :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

section Serializer

variable [FieldCertificate]

omit [FieldCertificate] in
theorem emitStep_ram (memory : Memory) (bit : Nat) : (emitStep memory bit).ram = memory.ram := rfl

omit [FieldCertificate] in
theorem emitStep_bits_other (memory : Memory) (bit : Nat) (stack : Fin 4) (other : stack ≠ 3) :
    (emitStep memory bit).bits stack = memory.bits stack := by
  simp only [emitStep, pushOn, setReg, Function.update_of_ne other]

omit [FieldCertificate] in
theorem emitFold_ram (memory : Memory) (width steps : Nat) :
    (emitFold memory width steps).ram = memory.ram := by
  induction steps with
  | zero => rfl
  | succ steps ih => rw [emitFold, emitStep_ram, ih]

omit [FieldCertificate] in
theorem emitFold_bits_other (memory : Memory) (width steps : Nat) (stack : Fin 4)
    (other : stack ≠ 3) : (emitFold memory width steps).bits stack = memory.bits stack := by
  induction steps with
  | zero => rfl
  | succ steps ih => rw [emitFold, emitStep_bits_other _ _ _ other, ih]

/-- **One emitted word.** -/
theorem memSem_emitWord (address width : Nat) (small : width ≤ 256) (memory : Memory) :
    ∃ after, (emitWord address width).memSem memory = PMF.pure (some after) ∧
      Emits memory after (bitRun (memory.ram (word address)) 0 width) := by
  refine ⟨emitFold (setReg (setReg memory rAddr (word address)) rAcc
    (memory.ram (word address))) width width, ?_, ?_, ?_, ?_⟩
  · unfold emitWord loadAt
    rw [memSem_seq]
    simp only [cst, Prog.memSem, Op.memSem, PMF.pure_bind, kleisli]
    rw [memSem_emitBits width small]
    simp only [setReg_registers, if_pos rfl, ite_true]
    rfl
  · rw [emitFold_ram]
    rfl
  · rw [emitFold_stack3, setReg_registers, if_pos rfl]
    rfl
  · intro stack other
    rw [emitFold_bits_other _ _ _ _ other]
    rfl

/-- **A block of emitted words**, addresses `top, top − 1, …` pushed in that order: the stack
reads the words from address `top + 1 − count` upward. -/
theorem memSem_emitBlock (width : Nat) (small : width ≤ 256) (top : Nat) :
    ∀ (count : Nat), count ≤ top + 1 → ∀ memory : Memory,
      ∃ after, (Prog.rep count fun index => emitWord (top - index) width).memSem memory =
          PMF.pure (some after) ∧
        Emits memory after (List.ofFn fun index : Fin count =>
          bitRun (memory.ram (word (top + 1 - count + index.val))) 0 width).flatten
  | 0, _, memory => ⟨memory, by rw [Prog.rep]; rfl, by
      simpa using Emits.refl memory⟩
  | count + 1, bound, memory => by
      obtain ⟨middle, run, emits⟩ := memSem_emitBlock width small top count (by omega) memory
      obtain ⟨last, step, emitsLast⟩ := memSem_emitWord (top - count) width small middle
      refine ⟨last, ?_, ?_⟩
      · rw [Prog.rep, memSem_seq, run, PMF.pure_bind]
        exact step
      · have joined := emits.trans emitsLast
        rw [emits.1] at joined
        convert joined using 1
        rw [List.ofFn_succ, List.flatten_cons]
        congr 2
        · congr 3
          simp only [Fin.val_zero]
          omega
        · congr 1
          funext index
          congr 3
          simp only [Fin.val_succ]
          omega

/-! ### The chunk words -/

/-- A stored word's emitted bits. -/
theorem bitRun_word (value width : Nat) (small : width ≤ 256) :
    bitRun (word value) 0 width = lsbs width value := by
  unfold bitRun lsbs
  refine congrArg List.ofFn (funext fun index => ?_)
  rw [Nat.zero_add, BitVec.getLsbD_ofNat]
  have : index.val < 256 := lt_of_lt_of_le index.isLt small
  simp [this]

/-- The low bits of a residue modulo a larger power of two. -/
theorem lsbs_mod_le (width modulus value : Nat) (small : width ≤ modulus) :
    lsbs width (value % 2 ^ modulus) = lsbs width value := by
  unfold lsbs
  refine congrArg List.ofFn (funext fun index => ?_)
  have : index.val < modulus := lt_of_lt_of_le index.isLt small
  simp [Nat.testBit_mod_two_pow, this]

/-- **A number's low bits, limb by limb.** -/
theorem lsbs_limbs (rest : Nat) : ∀ (count value : Nat),
    lsbs (256 * count + rest) value =
      (List.ofFn fun index : Fin count => lsbs 256 (BigInt.limb value index.val)).flatten ++
        lsbs rest (value / 2 ^ (256 * count))
  | 0, value => by simp
  | count + 1, value => by
      rw [show 256 * (count + 1) + rest = 256 + (256 * count + rest) by ring, lsbs_add,
        lsbs_limbs rest count (value / 2 ^ 256), List.ofFn_succ, List.flatten_cons,
        List.append_assoc]
      refine congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ ?_)
      · rw [BigInt.limb, Fin.val_zero, Nat.mul_zero, pow_zero, Nat.div_one, lsbs_mod]
      · refine congrArg List.flatten (congrArg List.ofFn (funext fun index => ?_))
        rw [BigInt.limb, BigInt.limb, Nat.div_div_eq_div_mul, ← pow_add, Fin.val_succ,
          show 256 + 256 * index.val = 256 * (index.val + 1) by ring]
      · rw [Nat.div_div_eq_div_mul, ← pow_add, show 256 + 256 * count = 256 * (count + 1) by ring]

/-- The bits of one chunk word's number: `635` limbs of `256` bits, then the top `256` bits. -/
def chunkLimbBits (value : Nat) : List Bool :=
  (List.ofFn fun index : Fin (chunkLimbCount - 1) =>
      lsbs 256 (BigInt.limb value index.val)).flatten ++
    lsbs topLimbBits (BigInt.limb value (chunkLimbCount - 1))

/-- `chunkLimbBits` is the low `162,816` bits. -/
theorem lsbs_chunkLimbBits (value : Nat) :
    lsbs (8 * chunkJoinBytes) value = chunkLimbBits value := by
  rw [show 8 * chunkJoinBytes = 256 * (chunkLimbCount - 1) + topLimbBits from rfl,
    lsbs_limbs, chunkLimbBits, BigInt.limb, lsbs_mod_le _ _ _ (by decide)]

/-- The base-`p` number of chunk `chunk`'s `642` scale cells, read from RAM. -/
def chunkWordValue (ram : Word → Word) (chunk : Nat) : Nat :=
  BigInt.encNat (fun e => (ram (word (scaleCellBase + 642 * chunk + e))).toNat) 642

/-- **The serialized bits of one chunk word** (chunk `chunk`, counted from the bottom). -/
def chunkWordBits (ram : Word → Word) (chunk : Nat) : List Bool :=
  chunkLimbBits (chunkWordValue ram chunk)

/-- The bits of the curve-and-rows word's number: `902` limbs of `256` bits, then the top
`120` bits. -/
def fieldsLimbBits (value : Nat) : List Bool :=
  (List.ofFn fun index : Fin (fieldsLimbCount - 1) =>
      lsbs 256 (BigInt.limb value index.val)).flatten ++
    lsbs fieldsTopLimbBits (BigInt.limb value (fieldsLimbCount - 1))

/-- `fieldsLimbBits` is the low `231,032` bits. -/
theorem lsbs_fieldsLimbBits (value : Nat) :
    lsbs (8 * Wire.fieldsBytes) value = fieldsLimbBits value := by
  rw [show 8 * Wire.fieldsBytes = 256 * (fieldsLimbCount - 1) + fieldsTopLimbBits from rfl,
    lsbs_limbs, fieldsLimbBits, BigInt.limb, lsbs_mod_le _ _ _ (by decide)]

/-- The base-`p` number of the `911` curve and row cells, read from RAM. -/
def fieldsWordValue (ram : Word → Word) : Nat :=
  BigInt.encNat (fun e => (ram (word (fieldBase + e))).toNat) (curveCellCount + rowCellCount)

/-- What the serializer needs of the RAM: a zero limb scratch, canonical scale cells and
canonical curve and row cells. -/
def SerialReady (ram : Word → Word) : Prop :=
  (∀ index, index < serialLimbCount → ram (word (serialLimbBase + index)) = 0) ∧
    (∀ index, index < scaleCellCount → (ram (word (scaleCellBase + index))).toNat < pNat) ∧
    ∀ index, index < curveCellCount + rowCellCount → (ram (word (fieldBase + index))).toNat < pNat

omit [FieldCertificate] in
theorem plain_clearLimbs : BigInt.IsPlain Stage1.clearLimbs :=
  ⟨trivial, BigInt.plain_rep _ _ fun _ _ => ⟨trivial, trivial⟩⟩

omit [FieldCertificate] in
/-- **Clearing the limb scratch.** -/
theorem det_clearLimbs (memory : Memory) :
    ∃ after, BigInt.det Stage1.clearLimbs memory = some after ∧
      after.ram = BigInt.writeCells memory.ram serialLimbBase serialLimbCount (fun _ => 0) ∧
      after.bits = memory.bits := by
  obtain ⟨after, reach, _, ram, bits⟩ := BigInt.det_rep_inv
    (fun count current => current.registers rAcc = word 0 ∧
      current.ram = BigInt.writeCells memory.ram serialLimbBase count (fun _ => 0) ∧
      current.bits = memory.bits)
    (fun index => storeAt (serialLimbBase + index) rAcc) serialLimbCount
    (fun index bound current holds => by
      obtain ⟨acc, ram, bits⟩ := holds
      refine ⟨_, rfl, ?_, ?_, ?_⟩
      · simp only [BigInt.opDet, Option.bind_some, BigInt.regs_storeRam, BigInt.regs_setReg]
        rw [if_neg (by decide), acc]
      · simp only [BigInt.opDet, Option.bind_some, BigInt.ram_storeRam, BigInt.ram_setReg,
          BigInt.regs_setReg, if_pos, if_neg (show rAcc ≠ rAddr by decide)]
        rw [ram, acc, BigInt.writeCells_succ _ _ _ _
          (by unfold serialLimbBase serialLimbCount at *; omega)]
      · simp only [BigInt.opDet, Option.bind_some, BigInt.bits_storeRam, BigInt.bits_setReg]
        exact bits)
    (setReg memory rAcc (word 0)) ⟨by simp, by rw [BigInt.ram_setReg, BigInt.writeCells_zero], rfl⟩
  refine ⟨after, ?_, ram, bits⟩
  unfold Stage1.clearLimbs
  rw [BigInt.det_seq_some (rfl : BigInt.det (cst rAcc 0) memory = some (setReg memory rAcc (word 0)))]
  exact reach

set_option maxHeartbeats 1000000 in
/-- **One chunk word.** `serializeChunk r` builds chunk `51 − r`'s base-`p` number in the limb
scratch, emits it top limb first, and clears the scratch. -/
theorem memSem_serializeChunk (step : Nat) (small : step < 52) (memory : Memory)
    (ready : SerialReady memory.ram) :
    ∃ after, (Stage1.serializeChunk step).memSem memory = PMF.pure (some after) ∧
      Emits memory after (chunkWordBits memory.ram (51 - step)) := by
  obtain ⟨zero, canonical, _⟩ := ready
  have baseEq : fieldBase + curveCellCount + rowCellCount + 642 * (51 - step) =
      scaleCellBase + 642 * (51 - step) := rfl
  obtain ⟨m1, det1, consts1, ram1, bits1, _⟩ := BigInt.det_setup memory
  obtain ⟨m2, det2, _, ram2, bits2, _⟩ := BigInt.det_macPasses serialLimbBase serialLimbCount 642
    (fieldBase + curveCellCount + rowCellCount + 642 * (51 - step))
    (by unfold serialLimbBase serialLimbCount; norm_num)
    (by unfold fieldBase curveCellCount rowCellCount; omega)
    (Or.inl (by unfold serialLimbBase serialLimbCount fieldBase curveCellCount rowCellCount; omega))
    m1 consts1 0 (fun e => (memory.ram (word (scaleCellBase + 642 * (51 - step) + e))).toNat)
    (fun e bound => by
      have cell := canonical (642 * (51 - step) + e) (by unfold scaleCellCount; omega)
      rwa [← Nat.add_assoc] at cell)
    (fun e bound => by rw [ram1, baseEq, BigInt.word_toNat])
    (fun index bound => by
      rw [ram1, zero index bound]
      simp [BigInt.limb])
  have value : 0 * pNat ^ 642 + BigInt.encNat
      (fun e => (memory.ram (word (scaleCellBase + 642 * (51 - step) + e))).toNat) 642 =
        chunkWordValue memory.ram (51 - step) := by
    rw [Nat.zero_mul, Nat.zero_add, chunkWordValue]
  rw [value] at ram2
  obtain ⟨m3, run3, emits3⟩ :=
    memSem_emitWord (serialLimbBase + (chunkLimbCount - 1)) topLimbBits (by decide) m2
  obtain ⟨m4, run4, emits4⟩ := memSem_emitBlock 256 le_rfl
    (serialLimbBase + (chunkLimbCount - 2)) (chunkLimbCount - 1)
    (by unfold chunkLimbCount; omega) m3
  obtain ⟨m5, det5, ram5, bits5⟩ := det_clearLimbs m4
  have r1 : BigInt.setup.memSem memory = PMF.pure (some m1) := by
    rw [BigInt.memSem_det _ BigInt.plain_setup, det1]
  have r2 : (BigInt.macPasses serialLimbBase serialLimbCount 642
      (fieldBase + curveCellCount + rowCellCount + 642 * (51 - step))).memSem m1 =
        PMF.pure (some m2) := by
    rw [BigInt.memSem_det _ (BigInt.plain_macPasses _ _ _ _), det2]
  have r5 : Stage1.clearLimbs.memSem m4 = PMF.pure (some m5) := by
    rw [BigInt.memSem_det _ plain_clearLimbs, det5]
  have limbAt : ∀ index, index < serialLimbCount →
      m2.ram (word (serialLimbBase + index)) =
        word (BigInt.limb (chunkWordValue memory.ram (51 - step)) index) := by
    intro index bound
    rw [ram2, BigInt.writeCells_in _ _ _ _ _ bound
      (by unfold serialLimbBase serialLimbCount; norm_num)]
  refine ⟨m5, ?_, ?_, ?_, ?_⟩
  · unfold Stage1.serializeChunk
    rw [memSem_seq, r1, PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_seq, r2, PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_seq, run3, PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_seq, run4, PMF.pure_bind]
    simp only [kleisli]
    exact r5
  · rw [ram5, emits4.1, emits3.1, ram2, ram1, BigInt.writeCells_writeCells]
    exact BigInt.writeCells_self _ _ _ _ fun index bound => zero index bound
  · rw [bits5, emits4.2.1, emits3.2.1, bits2, bits1, chunkWordBits, chunkLimbBits,
      List.append_assoc]
    refine congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ rfl)
    · refine congrArg List.flatten (congrArg List.ofFn (funext fun index => ?_))
      have indexSmall : index.val < serialLimbCount := by
        have := index.isLt; unfold chunkLimbCount at this; unfold serialLimbCount; omega
      have shift : ∀ base : Nat, base + (chunkLimbCount - 2) + 1 - (chunkLimbCount - 1) +
          index.val = base + index.val := fun base => by
        rw [Nat.add_assoc base, show chunkLimbCount - 2 + 1 = chunkLimbCount - 1 from rfl,
          Nat.add_sub_cancel]
      rw [emits3.1, shift, limbAt index.val indexSmall, bitRun_word _ _ le_rfl]
    · rw [limbAt _ (by decide), bitRun_word _ _ (by decide)]
  · intro stack other
    rw [bits5, emits4.2.2 stack other, emits3.2.2 stack other, bits2, bits1]

set_option maxHeartbeats 1000000 in
/-- **The curve-and-rows word.** `serializeFields` builds the base-`p` number of the `911` curve
and row cells in the limb scratch, emits it top limb first, and clears the scratch. -/
theorem memSem_serializeFields (memory : Memory) (ready : SerialReady memory.ram) :
    ∃ after, Stage1.serializeFields.memSem memory = PMF.pure (some after) ∧
      Emits memory after (fieldsLimbBits (fieldsWordValue memory.ram)) := by
  obtain ⟨zero, _, canonical⟩ := ready
  obtain ⟨m1, det1, consts1, ram1, bits1, _⟩ := BigInt.det_setup memory
  obtain ⟨m2, det2, _, ram2, bits2, _⟩ := BigInt.det_macPasses serialLimbBase serialLimbCount
    (curveCellCount + rowCellCount) fieldBase
    (by unfold serialLimbBase serialLimbCount; norm_num)
    (by unfold fieldBase curveCellCount rowCellCount; omega)
    (Or.inl (by unfold serialLimbBase serialLimbCount fieldBase; omega))
    m1 consts1 0 (fun e => (memory.ram (word (fieldBase + e))).toNat)
    (fun e bound => canonical e bound)
    (fun e bound => by rw [ram1, BigInt.word_toNat])
    (fun index bound => by
      rw [ram1, zero index bound]
      simp [BigInt.limb])
  have value : 0 * pNat ^ (curveCellCount + rowCellCount) + BigInt.encNat
      (fun e => (memory.ram (word (fieldBase + e))).toNat) (curveCellCount + rowCellCount) =
        fieldsWordValue memory.ram := by
    rw [Nat.zero_mul, Nat.zero_add, fieldsWordValue]
  rw [value] at ram2
  obtain ⟨m3, run3, emits3⟩ :=
    memSem_emitWord (serialLimbBase + (fieldsLimbCount - 1)) fieldsTopLimbBits (by decide) m2
  obtain ⟨m4, run4, emits4⟩ := memSem_emitBlock 256 le_rfl
    (serialLimbBase + (fieldsLimbCount - 2)) (fieldsLimbCount - 1)
    (by unfold fieldsLimbCount; omega) m3
  obtain ⟨m5, det5, ram5, bits5⟩ := det_clearLimbs m4
  have r1 : BigInt.setup.memSem memory = PMF.pure (some m1) := by
    rw [BigInt.memSem_det _ BigInt.plain_setup, det1]
  have r2 : (BigInt.macPasses serialLimbBase serialLimbCount (curveCellCount + rowCellCount)
      fieldBase).memSem m1 = PMF.pure (some m2) := by
    rw [BigInt.memSem_det _ (BigInt.plain_macPasses _ _ _ _), det2]
  have r5 : Stage1.clearLimbs.memSem m4 = PMF.pure (some m5) := by
    rw [BigInt.memSem_det _ plain_clearLimbs, det5]
  have limbAt : ∀ index, index < serialLimbCount →
      m2.ram (word (serialLimbBase + index)) =
        word (BigInt.limb (fieldsWordValue memory.ram) index) := by
    intro index bound
    rw [ram2, BigInt.writeCells_in _ _ _ _ _ bound
      (by unfold serialLimbBase serialLimbCount; norm_num)]
  refine ⟨m5, ?_, ?_, ?_, ?_⟩
  · unfold Stage1.serializeFields
    rw [memSem_seq, r1, PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_seq, r2, PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_seq, run3, PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_seq, run4, PMF.pure_bind]
    simp only [kleisli]
    exact r5
  · rw [ram5, emits4.1, emits3.1, ram2, ram1, BigInt.writeCells_writeCells]
    exact BigInt.writeCells_self _ _ _ _ fun index bound => zero index bound
  · rw [bits5, emits4.2.1, emits3.2.1, bits2, bits1, fieldsLimbBits, List.append_assoc]
    refine congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ rfl)
    · refine congrArg List.flatten (congrArg List.ofFn (funext fun index => ?_))
      have indexSmall : index.val < serialLimbCount := by
        have := index.isLt; unfold fieldsLimbCount at this; unfold serialLimbCount; omega
      have shift : ∀ base : Nat, base + (fieldsLimbCount - 2) + 1 - (fieldsLimbCount - 1) +
          index.val = base + index.val := fun base => by
        rw [Nat.add_assoc base, show fieldsLimbCount - 2 + 1 = fieldsLimbCount - 1 from rfl,
          Nat.add_sub_cancel]
      rw [emits3.1, shift, limbAt index.val indexSmall, bitRun_word _ _ le_rfl]
    · rw [limbAt _ (by decide), bitRun_word _ _ (by decide)]
  · intro stack other
    rw [bits5, emits4.2.2 stack other, emits3.2.2 stack other, bits2, bits1]

/-- **The serialized bits of a RAM**: the curve-and-rows word (`fieldsLimbBits`), the gadget
cells (`3` bits) and four padding bits, the fold joins (`128`), the `52` chunk words
(`chunkWordBits`), each least significant bit first. -/
def serialBits (ram : Word → Word) : List Bool :=
  fieldsLimbBits (fieldsWordValue ram) ++
    (((List.ofFn fun index : Fin exceptionByteCount =>
      bitRun (ram (word (exceptionBase + index.val))) 0 3).flatten ++
      bitRun (ram (word serialLimbBase)) 0 4) ++
    ((List.ofFn fun index : Fin hotBlockCount =>
      bitRun (ram (word (hotBase + index.val))) 0 128).flatten ++
    (List.ofFn fun chunk : Fin 52 => chunkWordBits ram chunk.val).flatten))

/-- **The chunk words**: the first `count` steps emit the top `count` chunk words, in wire order. -/
theorem memSem_serializeChunks :
    ∀ (count : Nat), count ≤ 52 → ∀ memory : Memory, SerialReady memory.ram →
      ∃ after, (Prog.rep count Stage1.serializeChunk).memSem memory = PMF.pure (some after) ∧
        Emits memory after (List.ofFn fun index : Fin count =>
          chunkWordBits memory.ram (52 - count + index.val)).flatten
  | 0, _, memory, _ => ⟨memory, by rw [Prog.rep]; rfl, by simpa using Emits.refl memory⟩
  | count + 1, bound, memory, ready => by
      obtain ⟨middle, run, emits⟩ := memSem_serializeChunks count (by omega) memory ready
      obtain ⟨after, step, emitsStep⟩ := memSem_serializeChunk count (by omega) middle
        (by rw [emits.1]; exact ready)
      refine ⟨after, ?_, ?_⟩
      · rw [Prog.rep, memSem_seq, run, PMF.pure_bind]
        exact step
      · have joined := emits.trans emitsStep
        rw [emits.1] at joined
        have words : (List.ofFn fun index : Fin (count + 1) =>
            chunkWordBits memory.ram (52 - (count + 1) + index.val)).flatten =
            chunkWordBits memory.ram (51 - count) ++ (List.ofFn fun index : Fin count =>
              chunkWordBits memory.ram (52 - count + index.val)).flatten := by
          rw [List.ofFn_succ, List.flatten_cons]
          have head : 52 - (count + 1) + (0 : Fin (count + 1)).val = 51 - count := by
            simp only [Fin.val_zero]
            omega
          have tail : (fun index : Fin count =>
              chunkWordBits memory.ram (52 - (count + 1) + index.succ.val)) =
              fun index : Fin count => chunkWordBits memory.ram (52 - count + index.val) := by
            funext index
            have same : 52 - (count + 1) + index.succ.val = 52 - count + index.val := by
              simp only [Fin.val_succ]
              omega
            rw [same]
          rw [head, tail]
        rw [words]
        exact joined

theorem block_le (base total count : Nat) (le : count ≤ total) (pos : 0 < total) :
    count ≤ base + total - 1 + 1 := by omega

theorem top_sub (base count : Nat) (pos : 0 < count) : base + count - 1 + 1 - count = base := by
  omega

/-- **The serializer's law.** -/
theorem memSem_serialize (memory : Memory) (ready : SerialReady memory.ram) :
    ∃ after, Stage1.serialize.memSem memory = PMF.pure (some after) ∧
      Emits memory after (serialBits memory.ram) := by
  have hotTop : hotBase + hotBlockCount - 1 + 1 - hotBlockCount = hotBase :=
    top_sub _ _ (by decide)
  have byteTop : exceptionBase + exceptionByteCount - 1 + 1 - exceptionByteCount =
      exceptionBase := top_sub _ _ (by decide)
  obtain ⟨afterScale, runScale, emitsScale⟩ := memSem_serializeChunks 52 le_rfl memory ready
  obtain ⟨afterHot, runHot, emitsHot⟩ := memSem_emitBlock 128 (by norm_num)
    (hotBase + hotBlockCount - 1) hotBlockCount
    (block_le _ _ _ le_rfl (by unfold hotBlockCount; decide)) afterScale
  obtain ⟨afterLast, runLast, emitsLast⟩ := memSem_emitWord serialLimbBase 4 (by norm_num) afterHot
  obtain ⟨afterBytes, runBytes, emitsBytes⟩ := memSem_emitBlock 3 (by norm_num)
    (exceptionBase + exceptionByteCount - 1) exceptionByteCount
    (block_le _ _ _ le_rfl (by unfold exceptionByteCount; decide)) afterLast
  obtain ⟨afterFields, runFields, emitsFields⟩ := memSem_serializeFields afterBytes
    (by rw [emitsBytes.1, emitsLast.1, emitsHot.1, emitsScale.1]; exact ready)
  refine ⟨afterFields, ?_, ?_⟩
  · unfold Stage1.serialize
    rw [memSem_seq, runScale, PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_seq, runHot, PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_seq, memSem_seq, runLast, PMF.pure_bind]
    simp only [kleisli]
    rw [runBytes, PMF.pure_bind]
    simp only [kleisli]
    exact runFields
  · have all := (((emitsScale.trans emitsHot).trans emitsLast).trans emitsBytes).trans emitsFields
    rw [emitsBytes.1, emitsLast.1, emitsHot.1, emitsScale.1, hotTop, byteTop] at all
    convert all using 1
    unfold serialBits
    simp only [Nat.sub_self, Nat.zero_add, List.append_assoc]

end Serializer

end

end Kriterion.ArgoMAC.PlanB.SimMachine
