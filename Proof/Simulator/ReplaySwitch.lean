/-
**The replay, one chunk's switches** (`Replay.switchStep`, design A1 §4 item 1).

* `det_digitsOf_limbs`: digit extraction on the packed limbs of `h` leaves the digits of
  `sampleLane n k h` in the digit cells (`BigInt.memSem_digitsOf`, `limb_limbsToNat`);
* `det_axpy`: the accumulation loop `acc[e] += x_e · R[rF]` (the switch term and the published-join
  term have the same shape, `axpyOne`);
* `agree_limbs`: the `k` limb questions against the evaluator's `FreeQuery.vector` of `askHash`;
* `rtree_switchSkip` (the guard is zero: `α`, and `j*` in the designated chunk; the limbs are
  cleared, the digits are `0`) and `agree_switchQuery` (the guard is set: the switch's limbs are
  asked and its vector `sampleLane n k h` accumulated with coefficient `ι(s) − ι(α)`);
* `agree_switchStep`: one switch step against the evaluator's `evalMasksM` body, intercepted;
  `agree_switches`: the `2^w` switch steps;
* `evalScaleOf_eq`: `evalScaleOf` in the machine's accumulation order.
-/

import Proof.Simulator.ReplayDesignated

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-- Split a plain block into its operations. -/
macro "plain_split" : tactic => `(tactic| repeat' (first
  | exact trivial
  | refine ⟨?_, ?_⟩
  | refine BigInt.plain_rep _ _ fun _ _ => ?_))

variable [FieldCertificate]

/-! ### Words and addresses -/

omit [FieldCertificate] in
theorem word_small {value : Nat} (small : value < 2 ^ 256) : (word value).toNat = value := by
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

omit [FieldCertificate] in
theorem eval_xor (first second : Word) : Arithmetic.xor.eval first second = first ^^^ second := rfl

theorem word_xor_eq_zero {first second : Nat} (firstSmall : first < 2 ^ 256)
    (secondSmall : second < 2 ^ 256) : word first ^^^ word second = 0 ↔ first = second := by
  constructor
  · intro zero
    have same : word first = word second := by
      have := congrArg (fun value => value ^^^ word second) zero
      simpa [BitVec.xor_assoc] using this
    exact word_injective firstSmall secondSmall same
  · intro same
    rw [same, BitVec.xor_self]
    rfl

/-- The accumulator cell of element `index` of a lane. -/
abbrev accCell (spec : Replay.LaneSpec) (index : Nat) : Word := word (accBase + spec.slot + index)

theorem accCell_ne (spec : Replay.LaneSpec) {first second : Nat}
    (firstFits : spec.slot + first < 642) (secondFits : spec.slot + second < 642)
    (different : first ≠ second) : accCell spec first ≠ accCell spec second :=
  word_ne (by unfold accBase; omega) (by unfold accBase; omega) (by omega)

/-- An address outside a lane's accumulator cells. -/
def OffAcc (spec : Replay.LaneSpec) (address : Word) : Prop :=
  ∀ e, e < laneCount spec.lane → address ≠ accCell spec e

/-- An address outside the digit-extraction region (the packed limbs and the digits). -/
def OffVector (address : Word) : Prop :=
  ∀ index, index < 1024 → address ≠ word (vectorLimbBase + index)

omit [FieldCertificate] in
/-- A block of cells leaves every address outside it alone. -/
theorem writeCells_off (ram : Word → Word) (base count : Nat) (f : Nat → Nat) (address : Word)
    (_small : base + count ≤ 2 ^ 256)
    (away : ∀ index, index < count → address ≠ word (base + index)) :
    BigInt.writeCells ram base count f address = ram address := by
  simp only [BigInt.writeCells]
  rw [if_neg]
  rintro ⟨low, high⟩
  refine away (address.toNat - base) (by omega) ?_
  rw [Nat.add_sub_cancel' low, BigInt.word_toNat]

omit [FieldCertificate] in
theorem laneCount_le (lane : Lane) : laneCount lane ≤ 364 := by cases lane <;> decide

omit [FieldCertificate] in
theorem limbCount_le (lane : Lane) : limbCount lane ≤ 362 := by cases lane <;> decide

/-- The static facts of a lane description. -/
structure SpecOK (spec : Replay.LaneSpec) : Prop where
  fits : spec.slot + laneCount spec.lane ≤ 642
  labelsLow : spec.labels + 254 < 2 ^ 46
  hotLow : spec.hotRow < 4
  coordLow : spec.coordinate < 2 ^ 46

omit [FieldCertificate] in
theorem SpecOK.accSmall {spec : Replay.LaneSpec} (ok : SpecOK spec) (e : Nat)
    (bound : e < laneCount spec.lane) : accBase + spec.slot + e < 2 ^ 256 := by
  have := ok.fits
  unfold accBase
  omega

/-! ### Plain blocks as determined results -/

/-- A plain block's point law is its `det` result. -/
theorem det_of_memSem {program : Prog} (plain : BigInt.IsPlain program) {memory after : Memory}
    (law : program.memSem memory = PMF.pure (some after)) :
    BigInt.det program memory = some after := by
  rw [BigInt.memSem_det program plain memory] at law
  have same := congrArg PMF.support law
  rw [PMF.support_pure, PMF.support_pure] at same
  exact Set.singleton_eq_singleton_iff.mp same

omit [FieldCertificate] in
/-- The limbs of `limbsToNat k h` are the answers' values. -/
theorem limb_limbsToNat (k : Nat) (h : Fin k → Block × Block) (i : Fin k) :
    BigInt.limb (limbsToNat k h) i.val = limbValue (h i) := by
  have sum : limbsToNat k h = BigInt.limbSum (fun j => if inside : j < k then
      limbValue (h ⟨j, inside⟩) else 0) k := by
    unfold limbsToNat BigInt.limbSum
    rw [← Fin.sum_univ_eq_sum_range (fun j => (if inside : j < k then
      limbValue (h ⟨j, inside⟩) else 0) * 2 ^ (256 * j)) k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dif_pos j.isLt]
  rw [sum, BigInt.limb_limbSum _ (fun j => by
      split
      · exact limbValue_lt _
      · exact Nat.two_pow_pos _) k i.val i.isLt, dif_pos i.isLt]

/-- **Digit extraction on packed answers**: the digit cells hold `sampleLane n k h`; only the
vector region changes. -/
theorem det_digitsOf_limbs (k n : Nat) (kSmall : k ≤ 512) (nSmall : n ≤ 364) (memory : Memory)
    (h : Fin k → Block × Block)
    (limbsIn : ∀ i : Fin k, memory.ram (word (vectorLimbBase + i.val)) = word (limbValue (h i))) :
    ∃ after, BigInt.det (BigInt.digitsOf vectorLimbBase k n vectorDigitBase) memory = some after ∧
      (∀ e : Fin n, ((after.ram (word (vectorDigitBase + e.val))).toNat : BaseField) =
        sampleLane n k h e) ∧
      (∀ address, OffVector address → after.ram address = memory.ram address) ∧
      after.bits = memory.bits := by
  have law := BigInt.memSem_digitsOf vectorLimbBase k n vectorDigitBase
    (by unfold vectorLimbBase vectorDigitBase; omega) (by unfold vectorDigitBase; omega) memory
    (limbsToNat k h) (limbsToNat_lt k h)
    (fun index bound => by rw [limbsIn ⟨index, bound⟩, limb_limbsToNat k h ⟨index, bound⟩])
  refine ⟨_, det_of_memSem (BigInt.plain_digitsOf _ _ _ _) law, fun e => ?_,
    fun address off => ?_, ?_⟩
  · rw [(clearRegs_other _ _).1, BigInt.ram_setRam,
      BigInt.writeCells_in _ _ _ _ _ e.isLt (by unfold vectorDigitBase; omega),
      word_small (lt_trans (Nat.mod_lt _ BigInt.pNat_pos) BigInt.pNat_lt_word),
      show pNat = baseFieldModulus from rfl, ZMod.natCast_mod]
    rfl
  · rw [(clearRegs_other _ _).1, BigInt.ram_setRam,
      writeCells_off _ _ _ _ _ (by unfold vectorDigitBase; omega) fun index bound =>
        (by
          have := off (512 + index) (by omega)
          rwa [show vectorLimbBase + (512 + index) = vectorDigitBase + index by
            unfold vectorLimbBase vectorDigitBase; omega] at this),
      writeCells_off _ _ _ _ _ (by unfold vectorLimbBase; omega) fun index bound =>
        off index (by omega)]
  · rw [(clearRegs_other _ _).2, BigInt.bits_setRam]

/-! ### The accumulation loop -/

/-- One accumulation step `RAM[dst] += RAM[src] · R[rF]` (field arithmetic). -/
def axpyOne (src dst : Nat) : Prog :=
  Prog.seqList [loadAt rC src, ar .fieldMul rC rC rF, loadAt rD dst, ar .fieldAdd rD rD rC,
    storeAt dst rD]

/-- **One accumulation step.** -/
theorem det_axpyOne (src dst : Nat) (memory : Memory) (x y factor : BaseField)
    (srcCell : ((memory.ram (word src)).toNat : BaseField) = x)
    (dstCell : ((memory.ram (word dst)).toNat : BaseField) = y)
    (factorReg : ((memory.registers rF).toNat : BaseField) = factor) :
    ∃ after, BigInt.det (axpyOne src dst) memory = some after ∧
      after.ram = Function.update memory.ram (word dst) (fieldWord (y + x * factor)) ∧
      after.bits = memory.bits ∧ after.registers rF = memory.registers rF := by
  refine ⟨_, rfl, ?_, by reg_eval, by reg_eval⟩
  reg_eval
  rw [eval_fieldAdd, eval_fieldMul, fieldWord_cast, dstCell, srcCell, factorReg]

/-- **The accumulation loop**: `count` steps with distinct destinations, apart from the sources. -/
theorem det_axpy (src dst : Nat → Nat) (count : Nat) (memory : Memory) (x y : Nat → BaseField)
    (factor : BaseField)
    (srcCells : ∀ e, e < count → ((memory.ram (word (src e))).toNat : BaseField) = x e)
    (dstCells : ∀ e, e < count → ((memory.ram (word (dst e))).toNat : BaseField) = y e)
    (factorReg : ((memory.registers rF).toNat : BaseField) = factor)
    (distinct : ∀ e e', e < count → e' < count → e ≠ e' → word (dst e) ≠ word (dst e'))
    (apart : ∀ e e', e < count → e' < count → word (src e) ≠ word (dst e')) :
    ∃ after, BigInt.det (Prog.rep count fun e => axpyOne (src e) (dst e)) memory = some after ∧
      (∀ e, e < count → after.ram (word (dst e)) = fieldWord (y e + x e * factor)) ∧
      (∀ address, (∀ e, e < count → address ≠ word (dst e)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧ after.registers rF = memory.registers rF := by
  obtain ⟨after, run, accs, frame, bitsSame, factorSame⟩ := BigInt.det_rep_inv
    (fun done current =>
      (∀ e, e < done → current.ram (word (dst e)) = fieldWord (y e + x e * factor)) ∧
      (∀ address, (∀ e, e < done → address ≠ word (dst e)) →
        current.ram address = memory.ram address) ∧
      current.bits = memory.bits ∧ current.registers rF = memory.registers rF)
    (fun e => axpyOne (src e) (dst e)) count (fun index bound current holds => by
      obtain ⟨done, frame, bitsSame, factorSame⟩ := holds
      obtain ⟨next, run, ram, bitsNext, factorNext⟩ := det_axpyOne (src index) (dst index) current
        (x index) (y index) factor
        (by rw [frame _ fun e small => apart index e bound (by omega)]; exact srcCells index bound)
        (by rw [frame _ fun e small => distinct index e bound (by omega) (by omega)]
            exact dstCells index bound)
        (by rw [factorSame]; exact factorReg)
      refine ⟨next, run, fun e small => ?_, fun address outside => ?_, bitsNext.trans bitsSame,
        factorNext.trans factorSame⟩
      · rw [ram]
        by_cases last : e = index
        · subst last
          rw [Function.update_self]
        · rw [Function.update_of_ne (distinct e index (by omega) bound last)]
          exact done e (by omega)
      · rw [ram, Function.update_of_ne (outside index (by omega))]
        exact frame address fun e small => outside e (by omega))
    memory ⟨fun e small => absurd small (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl⟩
  exact ⟨after, run, accs, frame, bitsSame, factorSame⟩

/-- **The switch term** `acc[e] += Y[e] · (ι(s) − ι(α))` for every element of the lane. -/
theorem det_accumulate (spec : Replay.LaneSpec) (ok : SpecOK spec) (switch alpha : Nat)
    (switchSmall : switch < 32) (alphaSmall : alpha < 32) (memory : Memory) (Y acc0 : Nat → BaseField)
    (alphaCell : memory.ram (word tmpAlpha) = word alpha)
    (digits : ∀ e, e < laneCount spec.lane →
      ((memory.ram (word (vectorDigitBase + e))).toNat : BaseField) = Y e)
    (cells : ∀ e, e < laneCount spec.lane →
      ((memory.ram (accCell spec e)).toNat : BaseField) = acc0 e) :
    ∃ after, BigInt.det (Replay.accumulate spec switch) memory = some after ∧
      (∀ e, e < laneCount spec.lane → after.ram (accCell spec e) =
        fieldWord (acc0 e + Y e * ((switch : BaseField) - (alpha : BaseField)))) ∧
      (∀ address, OffAcc spec address → after.ram address = memory.ram address) ∧
      after.bits = memory.bits := by
  have fits := ok.fits
  have split : Replay.accumulate spec switch = Prog.seqList
      ([loadAt rA tmpAlpha, cst rF switch, ar .fieldSub rF rF rA] ++
        [Prog.rep (laneCount spec.lane) fun e =>
          axpyOne (vectorDigitBase + e) (accBase + spec.slot + e)]) := rfl
  obtain ⟨start, runStart, ramStart, factorStart, bitsStart⟩ : ∃ start,
      BigInt.det (Prog.seqList [loadAt rA tmpAlpha, cst rF switch, ar .fieldSub rF rF rA]) memory =
        some start ∧ start.ram = memory.ram ∧
      start.registers rF = Arithmetic.fieldSub.eval (word switch) (memory.ram (word tmpAlpha)) ∧
      start.bits = memory.bits := ⟨_, rfl, rfl, by reg_eval, rfl⟩
  obtain ⟨after, runLoop, accs, frame, bitsLoop, _⟩ := det_axpy
    (fun e => vectorDigitBase + e) (fun e => accBase + spec.slot + e) (laneCount spec.lane) start
    Y acc0 ((switch : BaseField) - (alpha : BaseField))
    (fun e bound => by rw [ramStart]; exact digits e bound)
    (fun e bound => by rw [ramStart]; exact cells e bound)
    (by rw [factorStart, alphaCell, eval_fieldSub, fieldWord_cast, word_small (by omega),
      word_small (by omega)])
    (fun e e' bound bound' different => accCell_ne spec (by omega) (by omega) different)
    (fun e e' bound bound' => word_ne (by unfold vectorDigitBase; omega)
      (by unfold accBase; omega) (by unfold vectorDigitBase accBase; omega))
  refine ⟨after, ?_, accs, fun address off => ?_, by rw [bitsLoop, bitsStart]⟩
  · rw [split, BigInt.det_seqList_append, runStart, Option.bind_some]
    show BigInt.det (Prog.seq _ (Prog.skip 0)) start = some after
    rw [BigInt.det_seq_some runLoop]
    rfl
  · rw [frame address fun e bound => off e bound, ramStart]

/-! ### The limb questions -/

omit [FieldCertificate] in
theorem plain_packLimb (address : Nat) : BigInt.IsPlain (BigInt.packLimb address) := by
  unfold BigInt.packLimb storeAt cst ar
  plain_split

/-- The input register of a limb question is the scale input. -/
theorem limbInput (lane : Lane) (chunk : Fin chunkCount) (switch limb : Nat) (label : Block)
    (switchSmall : switch < 32) (limbSmall : limb < 512) :
    Arithmetic.add.eval (blockWord label) (word (2 ^ 128 * scaleTag lane chunk.val switch limb)) =
        word (label.toNat + 2 ^ 128 * scaleTag lane chunk.val switch limb) ∧
      label.toNat + 2 ^ 128 * scaleTag lane chunk.val switch limb < 2 ^ 256 ∧
      ((label.toNat + 2 ^ 128 * scaleTag lane chunk.val switch limb : Nat) : BaseField) =
        scaleInput lane chunk switch limb label := by
  have tag := scaleTag_lt lane (chunk := chunk.val) (switch := switch) (limb := limb) chunk.isLt
    (by show switch < 32; exact switchSmall) limbSmall
  have labelSmall := label.isLt
  refine ⟨?_, by omega, ?_⟩
  · rw [show blockWord label = word label.toNat from rfl, BigInt.eval_add_word]
  · unfold scaleInput
    rw [Nat.mod_eq_of_lt (show switch < 2 ^ chunkBits from switchSmall),
      Nat.mod_eq_of_lt limbSmall]

/-- What one limb question leaves: its packed answer in its limb cell. -/
def LimbPost (memory : Memory) (limb : Nat) (answer : Block × Block) (after : Memory) : Prop :=
  after.ram = Function.update memory.ram (word (vectorLimbBase + limb)) (word (limbValue answer)) ∧
    after.bits = memory.bits ∧ after.registers rA = memory.registers rA

/-- **One limb question** against `askHash` of the scale input. -/
theorem agree_limbQuery (spec : Replay.LaneSpec) (chunk : Fin chunkCount) (switch limb : Nat)
    (label : Block) (memory : Memory) (switchSmall : switch < 32) (limbSmall : limb < 512)
    (labelReg : memory.registers rA = blockWord label) :
    Agree (LimbPost memory limb) (rtree (Replay.limbQuery spec chunk.val switch limb) memory)
      (Programs.askHash (scaleInput spec.lane chunk switch limb label)) := by
  obtain ⟨sum, sumSmall, cast⟩ := limbInput spec.lane chunk switch limb label switchSmall limbSmall
  unfold Replay.limbQuery
  simp only [Prog.seqList]
  rw [rtree_cst_seq, rtree_ar_val _ _ _ _ _ _ (blockWord label)
      (word (2 ^ 128 * scaleTag spec.lane chunk.val switch limb))
      (by rw [reg_ne _ _ _ _ (by decide), labelReg]) (reg_same _ _ _), sum, rtree_seq]
  refine Agree.query 4 rIndex rInput rFirst rSecond _ (.hash (scaleInput spec.lane chunk switch limb
    label)) (by rw [reg_same, query_hash, word_small sumSmall, cast]) _ FreeQuery.pure
    fun answer => ?_
  obtain ⟨after, run, ram, bitsSame, regs⟩ := BigInt.det_packLimb (vectorLimbBase + limb)
    (writePair (setReg (setReg memory rB (word (2 ^ 128 * scaleTag spec.lane chunk.val switch limb)))
      rInput (word (label.toNat + 2 ^ 128 * scaleTag spec.lane chunk.val switch limb))) rFirst rSecond
      (answerWords (.hash (scaleInput spec.lane chunk switch limb label)) answer))
    answer.1.toNat answer.2.toNat
    (by rw [writePair_registers]; simp (config := {decide := true}) only [reduceIte]; rfl)
    (by rw [writePair_registers]; simp (config := {decide := true}) only [reduceIte]; rfl)
  refine agree_plain_leaf (program := .seq (BigInt.packLimb _) (.skip 0))
    ⟨plain_packLimb _, trivial⟩ ((BigInt.det_seq_some run).trans rfl) ⟨?_, ?_, ?_⟩
  · rw [ram, writePair_ram]
    rfl
  · rw [bitsSame, writePair_bits]
    rfl
  · rw [regs rA (by decide) (by decide) (by decide), writePair_registers]
    simp (config := {decide := true}) only [reduceIte, setReg_registers]

/-- A machine `rep` against a (non-intercepted) abstract vector. -/
theorem agree_rep_vector' {α : Type} (body : Nat → Prog)
    (Inv : (count : Nat) → Vector α count → Memory → Prop) :
    ∀ (count : Nat) (program : Fin count → FreeQuery Programs.Spec α),
      (∀ (index : Fin count) (values : Vector α index.val) (memory : Memory),
        Inv index.val values memory →
          Agree (fun (result : α) after => Inv (index.val + 1) (values.push result) after)
            (rtree (body index.val) memory) (program index)) →
      ∀ memory : Memory, Inv 0 #v[] memory →
        Agree (Inv count) (rtree (Prog.rep count body) memory) (FreeQuery.vector count program)
  | 0, _, _, memory, start => by
      rw [Prog.rep]
      exact .leaf start
  | count + 1, program, step, memory, start => by
      rw [Prog.rep, rtree_seq]
      simp only [FreeQuery.vector, TreeLaws.monad_bind, TreeLaws.monad_pure]
      refine Agree.bindOpt (fun collected middle holds => ?_)
        (agree_rep_vector' body Inv count (fun index => program index.castSucc)
          (fun index values memory holds => step index.castSucc values memory holds) memory start)
      exact Agree.map (Post := fun result after =>
          Inv (count + 1) (collected.push result) after)
        (fun result : α => collected.push result) (fun _ _ holds => holds)
        (step (Fin.last count) collected middle holds)

/-- The limb loop's invariant: the label register, the packed answers so far, the rest of RAM. -/
def LimbInv (start : Memory) (label : Block) (count : Nat) (values : Vector (Block × Block) count)
    (memory : Memory) : Prop :=
  memory.registers rA = blockWord label ∧
    (∀ i : Fin count, memory.ram (word (vectorLimbBase + i.val)) = word (limbValue values[i])) ∧
    (∀ address, (∀ i, i < count → address ≠ word (vectorLimbBase + i)) →
      memory.ram address = start.ram address) ∧
    memory.bits = start.bits

/-- **The limb questions of one switch.** -/
theorem agree_limbs (spec : Replay.LaneSpec) (chunk : Fin chunkCount) (switch : Nat)
    (label : Block) (memory : Memory) (switchSmall : switch < 32)
    (labelReg : memory.registers rA = blockWord label) :
    Agree (LimbInv memory label (limbCount spec.lane))
      (rtree (Prog.rep (limbCount spec.lane) fun limb => Replay.limbQuery spec chunk.val switch limb)
        memory)
      (FreeQuery.vector (limbCount spec.lane) fun limb =>
        Programs.askHash (scaleInput spec.lane chunk switch limb.val label)) := by
  have limbsSmall := limbCount_le spec.lane
  refine agree_rep_vector' _ (LimbInv memory label) _ _ (fun index values current holds => ?_)
    memory ⟨labelReg, fun i => i.elim0, fun _ _ => rfl, rfl⟩
  obtain ⟨reg, cells, frame, bitsSame⟩ := holds
  refine (agree_limbQuery spec chunk switch index.val label current switchSmall (by omega)
    reg).mono fun answer after post => ?_
  obtain ⟨ram, bitsAfter, regAfter⟩ := post
  have ne : ∀ i, i < index.val → word (vectorLimbBase + i) ≠ word (vectorLimbBase + index.val) :=
    fun i bound => word_ne (by unfold vectorLimbBase; omega) (by unfold vectorLimbBase; omega)
      (by omega)
  refine ⟨regAfter.trans reg, fun i => ?_, fun address outside => ?_, bitsAfter.trans bitsSame⟩
  · rw [ram]
    by_cases last : i.val = index.val
    · rw [show (word (vectorLimbBase + i.val)) = word (vectorLimbBase + index.val) by rw [last],
        Function.update_self]
      simp only [Fin.getElem_fin, last, Vector.getElem_push_eq]
    · have below : i.val < index.val := by have := i.isLt; omega
      rw [Function.update_of_ne (ne i.val below)]
      simp only [Fin.getElem_fin, Vector.getElem_push_lt below]
      exact cells ⟨i.val, below⟩
  · rw [ram, Function.update_of_ne (outside index.val (by omega))]
    exact frame address fun i bound => outside i (by omega)

/-! ### One switch step -/

/-- What one switch step leaves: every accumulator cell advanced by `Y[e] · coef`. -/
def SwitchCells (spec : Replay.LaneSpec) (acc0 : Nat → BaseField) (start : Memory)
    (Y : Fin (laneCount spec.lane) → BaseField) (coef : BaseField) (after : Memory) : Prop :=
  (∀ e : Fin (laneCount spec.lane),
      after.ram (accCell spec e.val) = fieldWord (acc0 e.val + Y e * coef)) ∧
    (∀ address, OffAcc spec address → OffVector address → after.ram address = start.ram address) ∧
    after.bits = start.bits

omit [FieldCertificate] in
/-- The guard word of switch `s`: `(α ⊕ s) >>> shift`. -/
theorem guard_word (alpha switch shift : Nat) (alphaSmall : alpha < 32) (switchSmall : switch < 32)
    (shiftSmall : shift < 2) :
    Arithmetic.shiftRight.eval (Arithmetic.xor.eval (word alpha) (word switch)) (word shift) =
      word ((alpha ^^^ switch) >>> shift) := by
  have xorSmall : alpha ^^^ switch < 32 :=
    Nat.xor_lt_two_pow (show alpha < 2 ^ 5 by omega) (show switch < 2 ^ 5 by omega)
  apply BitVec.eq_of_toNat_eq
  simp only [Arithmetic.eval, BitVec.toNat_ushiftRight, BitVec.toNat_xor,
    word_small (show alpha < 2 ^ 256 by omega), word_small (show switch < 2 ^ 256 by omega),
    word_small (show shift < 2 ^ 256 by omega)]
  rw [word_small (lt_of_le_of_lt (Nat.shiftRight_le _ _) (by omega))]

omit [FieldCertificate] in
/-- The switch step's guard prefix. -/
theorem det_guard (designated : Bool) (switch alpha : Nat) (alphaSmall : alpha < 32)
    (switchSmall : switch < 32) (memory : Memory)
    (alphaCell : memory.ram (word tmpAlpha) = word alpha) :
    ∃ guarded, BigInt.det (Prog.seqList [loadAt rA tmpAlpha, cst rB switch, ar .xor rA rA rB,
        cst rB (if designated then 1 else 0), ar .shiftRight rA rA rB]) memory = some guarded ∧
      guarded.ram = memory.ram ∧ guarded.bits = memory.bits ∧
      guarded.registers rA = word ((alpha ^^^ switch) >>> (if designated then 1 else 0)) := by
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  reg_eval
  rw [alphaCell, guard_word alpha switch _ alphaSmall switchSmall (by split <;> omega)]

omit [FieldCertificate] in
theorem plain_guard (designated : Bool) (switch : Nat) :
    BigInt.IsPlain (Prog.seqList [loadAt rA tmpAlpha, cst rB switch, ar .xor rA rA rB,
      cst rB (if designated then 1 else 0), ar .shiftRight rA rA rB]) := by
  unfold loadAt cst ar
  plain_split

omit [FieldCertificate] in
theorem plain_tail (spec : Replay.LaneSpec) (switch : Nat) :
    BigInt.IsPlain (Prog.seqList [BigInt.digitsOf vectorLimbBase spec.limbs spec.count
      vectorDigitBase, Replay.accumulate spec switch]) :=
  ⟨BigInt.plain_digitsOf _ _ _ _, ⟨by
    unfold Replay.accumulate Replay.accumulateOne loadAt storeAt cst ar
    plain_split, trivial⟩⟩

/-- **The switch step's tail**: digit extraction of the packed answers `h`, then the switch
term. -/
theorem det_switchTail (spec : Replay.LaneSpec) (ok : SpecOK spec) (switch alpha : Nat)
    (switchSmall : switch < 32) (alphaSmall : alpha < 32) (memory : Memory)
    (h : Fin (limbCount spec.lane) → Block × Block) (acc0 : Nat → BaseField)
    (limbsIn : ∀ i : Fin (limbCount spec.lane),
      memory.ram (word (vectorLimbBase + i.val)) = word (limbValue (h i)))
    (alphaCell : memory.ram (word tmpAlpha) = word alpha)
    (cells : ∀ e, e < laneCount spec.lane → memory.ram (accCell spec e) = fieldWord (acc0 e)) :
    ∃ after, BigInt.det (Prog.seqList [BigInt.digitsOf vectorLimbBase spec.limbs spec.count
        vectorDigitBase, Replay.accumulate spec switch]) memory = some after ∧
      SwitchCells spec acc0 memory (sampleLane (laneCount spec.lane) (limbCount spec.lane) h)
        ((switch : BaseField) - (alpha : BaseField)) after := by
  have fits := ok.fits
  obtain ⟨digited, runDigits, digits, frameDigits, bitsDigits⟩ := det_digitsOf_limbs
    (limbCount spec.lane) (laneCount spec.lane) (by have := limbCount_le spec.lane; omega)
    (laneCount_le spec.lane) memory h limbsIn
  have offVec : ∀ e, e < laneCount spec.lane → OffVector (accCell spec e) :=
    fun e bound index small => word_ne (by unfold accBase; omega)
      (by unfold vectorLimbBase; omega) (by unfold accBase vectorLimbBase; omega)
  obtain ⟨after, runAcc, accs, frameAcc, bitsAcc⟩ := det_accumulate spec ok switch alpha switchSmall
    alphaSmall digited (fun e => if bound : e < laneCount spec.lane then
      sampleLane (laneCount spec.lane) (limbCount spec.lane) h ⟨e, bound⟩ else 0) acc0
    (by rw [frameDigits _ fun index small => word_ne (by unfold tmpAlpha tmpBase; omega)
        (by unfold vectorLimbBase; omega) (by unfold tmpAlpha tmpBase vectorLimbBase; omega),
      alphaCell])
    (fun e bound => by rw [dif_pos bound]; exact digits ⟨e, bound⟩)
    (fun e bound => by rw [frameDigits _ (offVec e bound), cells e bound, fieldWord_cast])
  refine ⟨after, ?_, fun e => ?_, fun address offAcc offVector => ?_, by
    rw [bitsAcc, bitsDigits]⟩
  · show BigInt.det (Prog.seq (BigInt.digitsOf vectorLimbBase (limbCount spec.lane)
      (laneCount spec.lane) vectorDigitBase) (Prog.seq (Replay.accumulate spec switch)
        (Prog.skip 0))) memory = some after
    rw [BigInt.det_seq_some runDigits, BigInt.det_seq_some runAcc]
    rfl
  · rw [accs e.val e.isLt, dif_pos e.isLt]
  · rw [frameAcc address offAcc, frameDigits address offVector]

omit [FieldCertificate] in
/-- The switch step, split: the guard, the limb gate, the tail. -/
theorem switchStep_split (spec : Replay.LaneSpec) (designated : Bool) (chunk switch : Nat) :
    Replay.switchStep spec designated chunk switch = Prog.seqList
      ([loadAt rA tmpAlpha, cst rB switch, ar .xor rA rA rB, cst rB (if designated then 1 else 0),
        ar .shiftRight rA rA rB] ++
      (Replay.limbGate spec chunk switch :: [BigInt.digitsOf vectorLimbBase spec.limbs spec.count
        vectorDigitBase, Replay.accumulate spec switch])) := rfl

/-- **A skipped switch** (`α`, and `j*` in the designated chunk): its limbs are cleared, its
digits are `0`, and it adds nothing. -/
theorem rtree_switchSkip (spec : Replay.LaneSpec) (ok : SpecOK spec) (designated : Bool)
    (chunk switch alpha : Nat) (alphaSmall : alpha < 32) (switchSmall : switch < 32)
    (memory : Memory) (acc0 : Nat → BaseField)
    (skipped : (alpha ^^^ switch) >>> (if designated then 1 else 0) = 0)
    (alphaCell : memory.ram (word tmpAlpha) = word alpha)
    (cells : ∀ e, e < laneCount spec.lane → memory.ram (accCell spec e) = fieldWord (acc0 e)) :
    ∃ after, rtree (Replay.switchStep spec designated chunk switch) memory = .pure (some after) ∧
      SwitchCells spec acc0 memory (fun _ => 0) ((switch : BaseField) - (alpha : BaseField))
        after := by
  have limbsSmall := limbCount_le spec.lane
  obtain ⟨guarded, runGuard, ramGuard, bitsGuard, guardReg⟩ :=
    det_guard designated switch alpha alphaSmall switchSmall memory alphaCell
  obtain ⟨cleared, runClear, ramClear, bitsClear⟩ : ∃ cleared,
      BigInt.det (Replay.clearLimbs spec) guarded = some cleared ∧
      cleared.ram = BigInt.writeCells guarded.ram vectorLimbBase (limbCount spec.lane) (fun _ => 0) ∧
      cleared.bits = guarded.bits := by
    obtain ⟨cleared, run, holds⟩ := BigInt.det_rep_inv
      (fun done current => current.registers rA = word 0 ∧
        current.ram = BigInt.writeCells guarded.ram vectorLimbBase done (fun _ => 0) ∧
        current.bits = guarded.bits)
      (fun limb => storeAt (vectorLimbBase + limb) rA) (limbCount spec.lane)
      (fun index bound current holds => by
        obtain ⟨zero, ram, bitsSame⟩ := holds
        refine ⟨_, rfl, by reg_eval; exact zero, ?_, by reg_eval; exact bitsSame⟩
        reg_eval
        rw [ram, zero, BigInt.writeCells_succ _ _ _ _ (by unfold vectorLimbBase; omega)])
      (setReg guarded rA (word 0)) ⟨by reg_eval, by rw [BigInt.writeCells_zero]; rfl, rfl⟩
    exact ⟨cleared, by unfold Replay.clearLimbs; rw [BigInt.det_seq_some rfl]; exact run,
      holds.2.1, holds.2.2⟩
  obtain ⟨after, runTail, tail⟩ := det_switchTail spec ok switch alpha switchSmall alphaSmall cleared
    (fun _ => (0, 0)) acc0
    (fun i => by
      rw [ramClear, BigInt.writeCells_in _ _ _ _ _ i.isLt (by unfold vectorLimbBase; omega)]
      rfl)
    (by rw [ramClear, writeCells_off _ _ _ _ _ (by unfold vectorLimbBase; omega) fun index small =>
        word_ne (by unfold tmpAlpha tmpBase; omega) (by unfold vectorLimbBase; omega)
          (by unfold tmpAlpha tmpBase vectorLimbBase; omega), ramGuard, alphaCell])
    (fun e bound => by
      rw [ramClear, writeCells_off _ _ _ _ _ (by unfold vectorLimbBase; omega) fun index small =>
        word_ne (by have := ok.fits; unfold accBase; omega) (by unfold vectorLimbBase; omega)
          (by have := ok.fits; unfold accBase vectorLimbBase; omega), ramGuard, cells e bound])
  refine ⟨after, ?_, ?_⟩
  · rw [switchStep_split, rtree_seqList_append, rtree_plain_some (plain_guard designated switch)
      runGuard, bindOpt_pure]
    show bindOpt (rtree (Replay.limbGate spec chunk switch) guarded)
      (rtree (Prog.seqList [BigInt.digitsOf vectorLimbBase spec.limbs spec.count vectorDigitBase,
        Replay.accumulate spec switch])) = _
    unfold Replay.limbGate
    rw [rtree_ite, guardReg, skipped, if_pos (show word 0 = 0 from rfl),
      rtree_plain_some (by unfold Replay.clearLimbs storeAt cst; plain_split) runClear,
      bindOpt_pure, rtree_plain_some (plain_tail spec switch) runTail]
  · obtain ⟨accs, frame, bitsAfter⟩ := tail
    refine ⟨fun e => ?_, fun address offAcc offVector => ?_, ?_⟩
    · rw [accs e, sampleLane_zero]
    · rw [frame address offAcc offVector, ramClear, writeCells_off _ _ _ _ _
        (by unfold vectorLimbBase; omega) fun index small => offVector index (by omega), ramGuard]
    · rw [bitsAfter, bitsClear, bitsGuard]

/-- **An asked switch**: its limbs are asked, packed, extracted and accumulated. -/
theorem agree_switchQuery (spec : Replay.LaneSpec) (ok : SpecOK spec) (designated : Bool)
    (chunk : Fin chunkCount) (switch alpha : Nat) (alphaSmall : alpha < 32)
    (switchSmall : switch < 32) (label : Block) (memory : Memory) (record : DesignatedRecord)
    (acc0 : Nat → BaseField)
    (asked : (alpha ^^^ switch) >>> (if designated then 1 else 0) ≠ 0)
    (alphaCell : memory.ram (word tmpAlpha) = word alpha)
    (hotCell : memory.ram (word (hotLabel switch)) = blockWord label)
    (cells : ∀ e, e < laneCount spec.lane → memory.ram (accCell spec e) = fieldWord (acc0 e)) :
    Agree (fun (result : Vector BaseField (laneCount spec.lane) × DesignatedRecord) after =>
        SwitchCells spec acc0 memory (fun e => result.1.get e)
          ((switch : BaseField) - (alpha : BaseField)) after ∧ result.2 = record)
      (rtree (Replay.switchStep spec designated chunk.val switch) memory)
      (FreeQuery.bind (FreeQuery.vector (limbCount spec.lane) fun limb =>
          Programs.askHash (scaleInput spec.lane chunk switch limb.val label)) fun limbs =>
        .pure (Vector.ofFn (sampleLane (laneCount spec.lane) (limbCount spec.lane) limbs.get),
          record)) := by
  have limbsSmall := limbCount_le spec.lane
  obtain ⟨guarded, runGuard, ramGuard, bitsGuard, guardReg⟩ :=
    det_guard designated switch alpha alphaSmall switchSmall memory alphaCell
  rw [switchStep_split, rtree_seqList_append, rtree_plain_some (plain_guard designated switch)
    runGuard, bindOpt_pure]
  show Agree _ (bindOpt (rtree (Replay.limbGate spec chunk.val switch) guarded) _) _
  unfold Replay.limbGate Replay.queryLimbs
  have nonzero : word ((alpha ^^^ switch) >>> (if designated then 1 else 0)) ≠ 0 := by
    intro zero
    apply asked
    have := congrArg BitVec.toNat zero
    rwa [word_small (lt_of_le_of_lt (Nat.shiftRight_le _ _) (lt_trans
      (Nat.xor_lt_two_pow (show alpha < 2 ^ 5 by omega) (show switch < 2 ^ 5 by omega))
      (by norm_num)))] at this
  rw [rtree_ite, guardReg, if_neg nonzero, rtree_loadAt_seq]
  set loaded := setReg (setReg guarded rAddr (word (hotLabel switch))) rA
    (guarded.ram (word (hotLabel switch))) with loadedDef
  have labelReg : loaded.registers rA = blockWord label := by
    rw [loadedDef, reg_same, ramGuard, hotCell]
  refine Agree.bindOpt (fun limbs limbed inv => ?_)
    (agree_limbs spec chunk switch label loaded switchSmall labelReg)
  obtain ⟨_, limbCells, limbFrame, limbBits⟩ := inv
  have offVecAt : ∀ address : Nat, (address < vectorLimbBase ∨ vectorLimbBase + 1024 ≤ address) →
      address < 2 ^ 256 → ∀ i, i < limbCount spec.lane →
        word address ≠ word (vectorLimbBase + i) :=
    fun address away small i bound => word_ne small (by unfold vectorLimbBase; omega) (by omega)
  obtain ⟨after, runTail, tail⟩ := det_switchTail spec ok switch alpha switchSmall alphaSmall limbed
    limbs.get acc0 (fun i => by rw [limbCells i]; rfl)
    (by rw [limbFrame _ (offVecAt _ (by unfold tmpAlpha tmpBase vectorLimbBase; omega)
        (by unfold tmpAlpha tmpBase; omega)), loadedDef]
        simp only [setReg_ram]
        rw [ramGuard, alphaCell])
    (fun e bound => by
      rw [limbFrame _ (offVecAt _ (by have := ok.fits; unfold accBase vectorLimbBase; omega)
        (by have := ok.fits; unfold accBase; omega)), loadedDef]
      simp only [setReg_ram]
      rw [ramGuard, cells e bound])
  obtain ⟨accs, frame, bitsAfter⟩ := tail
  refine agree_plain_leaf (plain_tail spec switch) runTail
    ⟨⟨fun e => ?_, fun address offAcc offVector => ?_, ?_⟩, rfl⟩
  · rw [accs e]
    simp only [Vector.get_ofFn]
  · rw [frame address offAcc offVector, limbFrame address fun i bound => offVector i (by omega),
      loadedDef]
    simp only [setReg_ram]
    rw [ramGuard]
  · rw [bitsAfter, limbBits, loadedDef]
    simp only [setReg_bits]
    rw [bitsGuard]

/-! ### The switches of a chunk -/

omit [FieldCertificate] in
/-- The plain guard is zero exactly at `α`. -/
theorem guard_plain : ∀ alpha, alpha < 32 → ∀ switch, switch < 32 →
    ((alpha ^^^ switch) >>> 0 = 0 ↔ switch = alpha) := fun alpha _ switch _ => by
  rw [Nat.shiftRight_zero]
  constructor
  · intro zero
    have cancel : alpha ^^^ (alpha ^^^ switch) = switch := by
      rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    rw [zero, Nat.xor_zero] at cancel
    exact cancel.symm
  · rintro rfl
    exact Nat.xor_self _

omit [FieldCertificate] in
/-- The designated guard is zero exactly at `α` and `α ⊕ 1`. -/
theorem guard_designated : ∀ alpha, alpha < 4 → ∀ switch, switch < 4 →
    ((alpha ^^^ switch) >>> 1 = 0 ↔ (switch = alpha ∨ switch = alpha ^^^ 1)) := by decide

omit [FieldCertificate] in
theorem ne_xor_one (value : Nat) : value ≠ value ^^^ 1 := by
  intro same
  have cancel : value ^^^ (value ^^^ 1) = 1 := by
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [← same, Nat.xor_self] at cancel
  exact absurd cancel (by decide)

/-- The record after one switch: the designated switch records `E*` at every limb. -/
def switchRecord (designated : Bool) (jstar : Nat) (label : Block) (record : DesignatedRecord)
    (switch : Nat) : DesignatedRecord :=
  if designated = true ∧ switch = jstar then fun _ => some label else record

/-- The switch step's abstract side: the evaluator's `evalMasksM` body. -/
abbrev maskProg (lane : Lane) (chunk : Fin chunkCount) (width : Nat) (hot : HotLabels width)
    (alpha switch : Fin (2 ^ width)) : Programs.M (Vector BaseField (laneCount lane)) :=
  if switch = alpha then pure (Vector.ofFn fun _ => 0)
  else Programs.switchMaskM lane chunk switch.val (hot switch)

/-- **One switch step** against the evaluator's `evalMasksM` body, intercepted. In the designated
chunk (`spec = pointXSpec`, chunk `0`) the switch `j* = α ⊕ 1` is skipped by the machine and
intercepted by the evaluator. -/
theorem agree_switchStep (bits : BitInput) (spec : Replay.LaneSpec) (ok : SpecOK spec)
    (designated : Bool) (chunk : Fin chunkCount) (width : Nat) (widthSmall : width ≤ 5)
    (alpha switch : Fin (2 ^ width)) (hot : HotLabels width) (memory : Memory)
    (record : DesignatedRecord) (acc0 : Nat → BaseField)
    (plainChunk : designated = false → spec.lane ≠ .pointX ∨ chunk ≠ chunkZero)
    (desChunk : designated = true → spec = Replay.pointXSpec ∧ chunk = chunkZero ∧ width = 2 ∧
      (designatedSwitch bits).val = alpha.val ^^^ 1)
    (alphaCell : memory.ram (word tmpAlpha) = word alpha.val)
    (hotCell : memory.ram (word (hotLabel switch.val)) = blockWord (hot switch))
    (cells : ∀ e, e < laneCount spec.lane → memory.ram (accCell spec e) = fieldWord (acc0 e)) :
    Agree (fun (result : Vector BaseField (laneCount spec.lane) × DesignatedRecord) after =>
        SwitchCells spec acc0 memory (fun e => result.1.get e)
          ((switch.val : BaseField) - (alpha.val : BaseField)) after ∧
        result.2 = switchRecord designated (alpha.val ^^^ 1) (hot switch) record switch.val)
      (rtree (Replay.switchStep spec designated chunk.val switch.val) memory)
      (interceptT bits (maskProg spec.lane chunk width hot alpha switch) record) := by
  have alphaSmall : alpha.val < 32 :=
    lt_of_lt_of_le alpha.isLt (Nat.pow_le_pow_right (by norm_num) widthSmall)
  have switchSmall : switch.val < 32 :=
    lt_of_lt_of_le switch.isLt (Nat.pow_le_pow_right (by norm_num) widthSmall)
  unfold maskProg
  by_cases atAlpha : switch = alpha
  · -- the active switch: skipped by both sides
    subst atAlpha
    have skipped : (switch.val ^^^ switch.val) >>> (if designated then 1 else 0) = 0 := by
      rw [Nat.xor_self]; exact Nat.zero_shiftRight _
    obtain ⟨after, run, post⟩ := rtree_switchSkip spec ok designated chunk.val switch.val switch.val
      alphaSmall switchSmall memory acc0 skipped alphaCell cells
    rw [if_pos rfl, run]
    refine .leaf ⟨⟨fun e => ?_, post.2.1, post.2.2⟩, ?_⟩
    · rw [post.1 e]
      simp only [Vector.get_ofFn]
    · unfold switchRecord
      rw [if_neg]
      rintro ⟨-, same⟩
      exact ne_xor_one _ same
  · rw [if_neg atAlpha]
    have different : switch.val ≠ alpha.val := fun same => atAlpha (Fin.ext same)
    cases designated with
    | true =>
        obtain ⟨specIs, chunkIs, widthIs, jstarIs⟩ := desChunk rfl
        subst specIs chunkIs widthIs
        have alpha4 : alpha.val < 4 := alpha.isLt
        have switch4 : switch.val < 4 := switch.isLt
        by_cases atStar : switch.val = alpha.val ^^^ 1
        · -- the designated switch: skipped by the machine, intercepted by the evaluator
          have skipped : (alpha.val ^^^ switch.val) >>> (if true = true then 1 else 0) = 0 := by
            rw [if_pos rfl]
            exact (guard_designated alpha.val alpha4 switch.val switch4).mpr (Or.inr atStar)
          obtain ⟨after, run, post⟩ := rtree_switchSkip Replay.pointXSpec ok true chunkZero.val
            switch.val alpha.val alphaSmall switchSmall memory acc0 skipped alphaCell cells
          have maskIs : Programs.switchMaskM Replay.pointXSpec.lane chunkZero switch.val
              (hot switch) = Programs.switchMaskM .pointX chunkZero (designatedSwitch bits).val
                (hot switch) := by
            rw [jstarIs, atStar]
            rfl
          rw [maskIs]
          show Agree _ (rtree (Replay.switchStep Replay.pointXSpec true chunkZero.val switch.val)
            memory) (@interceptT (Vector BaseField (laneCount .pointX)) bits
              (Programs.switchMaskM .pointX chunkZero (designatedSwitch bits).val (hot switch))
              record)
          rw [interceptT_designatedMask, run]
          refine .leaf ⟨⟨fun e => ?_, post.2.1, post.2.2⟩, ?_⟩
          · have zero : (Vector.ofFn (sampleLane pointElementCountX (limbCount .pointX)
                fun _ => ((0 : Block), (0 : Block)))).get e = 0 :=
              (Vector.get_ofFn _ e).trans (congrFun (sampleLane_zero _ _) e)
            rw [post.1 e]
            exact congrArg (fun value => fieldWord (acc0 e.val + value *
              ((switch.val : BaseField) - (alpha.val : BaseField)))) zero.symm
          · unfold switchRecord
            rw [if_pos ⟨rfl, atStar⟩]
        · have asked : (alpha.val ^^^ switch.val) >>> (if true = true then 1 else 0) ≠ 0 := by
            rw [if_pos rfl]
            intro zero
            rcases (guard_designated alpha.val alpha4 switch.val switch4).mp zero with same | same
            · exact different same
            · exact atStar same
          have clean : Clean bits (Programs.switchMaskM Replay.pointXSpec.lane chunkZero switch.val
              (hot switch)) := by
            unfold Programs.switchMaskM
            exact (Clean.vector _ fun limb => clean_askHash bits _ (not_isDesignated_scaleInput bits
              _ _ _ _ _ switchSmall (lt_trans limb.isLt (limbCount_lt _))
              (Or.inr (Or.inr (by rw [jstarIs]; exact atStar))))).bind fun _ => .pure _
          rw [interceptT_clean bits record clean]
          unfold Programs.switchMaskM
          simp only [TreeLaws.monad_bind, TreeLaws.monad_pure, TreeLaws.bind_assoc,
            TreeLaws.bind_pure_left]
          refine (agree_switchQuery Replay.pointXSpec ok true chunkZero switch.val alpha.val
            alphaSmall switchSmall (hot switch) memory record acc0 asked alphaCell hotCell
            cells).mono fun result after post => ⟨post.1, ?_⟩
          rw [post.2]
          unfold switchRecord
          rw [if_neg fun both => atStar both.2]
    | false =>
        have asked : (alpha.val ^^^ switch.val) >>> (if false = true then 1 else 0) ≠ 0 := by
          rw [if_neg (by decide)]
          intro zero
          exact different ((guard_plain alpha.val alphaSmall switch.val switchSmall).mp zero)
        have clean : Clean bits (Programs.switchMaskM spec.lane chunk switch.val (hot switch)) := by
          unfold Programs.switchMaskM
          exact (Clean.vector _ fun limb => clean_askHash bits _ (not_isDesignated_scaleInput bits
            _ _ _ _ _ switchSmall (lt_trans limb.isLt (limbCount_lt _))
            (by rcases plainChunk rfl with other | other
                · exact Or.inl other
                · exact Or.inr (Or.inl other)))).bind fun _ => .pure _
        rw [interceptT_clean bits record clean]
        unfold Programs.switchMaskM
        simp only [TreeLaws.monad_bind, TreeLaws.monad_pure, TreeLaws.bind_assoc,
          TreeLaws.bind_pure_left]
        refine (agree_switchQuery spec ok false chunk switch.val alpha.val alphaSmall switchSmall
          (hot switch) memory record acc0 asked alphaCell hotCell cells).mono
          fun result after post => ⟨post.1, ?_⟩
        rw [post.2]
        unfold switchRecord
        rw [if_neg fun both => absurd both.1 (by decide)]

/-- The invariant of the switch loop: every accumulator cell holds its start value plus the
processed switches' `Y_s[e] · (ι(s) − ι(α))`; the record is the expected one. -/
def SwInv (spec : Replay.LaneSpec) (acc0 : Nat → BaseField) (alpha : Nat) (start : Memory)
    (recordAt : Nat → DesignatedRecord) (count : Nat)
    (state : Vector (Vector BaseField (laneCount spec.lane)) count × DesignatedRecord)
    (memory : Memory) : Prop :=
  (∀ e : Fin (laneCount spec.lane), memory.ram (accCell spec e.val) = fieldWord (acc0 e.val +
      ∑ switch : Fin count, state.1[switch].get e * ((switch.val : BaseField) - (alpha : BaseField)))) ∧
    (∀ address, OffAcc spec address → OffVector address → memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧ state.2 = recordAt count

/-- **The switch loop of a chunk.** -/
theorem agree_switches (bits : BitInput) (spec : Replay.LaneSpec) (ok : SpecOK spec)
    (designated : Bool) (chunk : Fin chunkCount) (width : Nat) (widthSmall : width ≤ 5)
    (alpha : Fin (2 ^ width)) (hot : HotLabels width) (start : Memory)
    (recordAt : Nat → DesignatedRecord) (acc0 : Nat → BaseField)
    (plainChunk : designated = false → spec.lane ≠ .pointX ∨ chunk ≠ chunkZero)
    (desChunk : designated = true → spec = Replay.pointXSpec ∧ chunk = chunkZero ∧ width = 2 ∧
      (designatedSwitch bits).val = alpha.val ^^^ 1)
    (recordStep : ∀ switch : Fin (2 ^ width), recordAt (switch.val + 1) =
      switchRecord designated (alpha.val ^^^ 1) (hot switch) (recordAt switch.val) switch.val)
    (alphaCell : start.ram (word tmpAlpha) = word alpha.val)
    (hotCells : ∀ switch : Fin (2 ^ width),
      start.ram (word (hotLabel switch.val)) = blockWord (hot switch))
    (hotOff : ∀ switch : Fin (2 ^ width),
      OffAcc spec (word (hotLabel switch.val)) ∧ OffVector (word (hotLabel switch.val)))
    (alphaOff : OffAcc spec (word tmpAlpha) ∧ OffVector (word tmpAlpha))
    (cells : ∀ e, e < laneCount spec.lane → start.ram (accCell spec e) = fieldWord (acc0 e)) :
    Agree (SwInv spec acc0 alpha.val start recordAt (2 ^ width))
      (rtree (Prog.rep (2 ^ width) fun switch =>
        Replay.switchStep spec designated chunk.val switch) start)
      (interceptT bits (FreeQuery.vector (2 ^ width) (maskProg spec.lane chunk width hot alpha))
        (recordAt 0)) := by
  refine agree_rep_vector bits _ (SwInv spec acc0 alpha.val start recordAt) (2 ^ width) _ ?_
    (recordAt 0) start ⟨fun e => by
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      exact cells e.val e.isLt, fun _ _ _ => rfl, rfl, rfl⟩
  intro switch masks record memory holds
  obtain ⟨accs, frame, bitsSame, recordIs⟩ := holds
  subst recordIs
  have agree := agree_switchStep bits spec ok designated chunk width widthSmall alpha switch hot memory
    (recordAt switch.val)
    (fun e => if bound : e < laneCount spec.lane then acc0 e + ∑ earlier : Fin switch.val,
      masks[earlier].get ⟨e, bound⟩ * ((earlier.val : BaseField) - (alpha.val : BaseField)) else 0)
    plainChunk desChunk
    (by rw [frame _ alphaOff.1 alphaOff.2, alphaCell])
    (by rw [frame _ (hotOff switch).1 (hotOff switch).2, hotCells])
    (fun e bound => by rw [dif_pos bound]; exact accs ⟨e, bound⟩)
  refine agree.mono fun result after post => ?_
  obtain ⟨⟨accsAfter, frameAfter, bitsAfter⟩, recordAfter⟩ := post
  refine ⟨fun e => ?_, fun address offAcc offVector => ?_, bitsAfter.trans bitsSame, ?_⟩
  · rw [accsAfter e]
    simp only [dif_pos e.isLt]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [add_assoc]
    congr 3
    · refine Finset.sum_congr rfl fun earlier _ => ?_
      simp only [Fin.getElem_fin, Fin.val_castSucc, Vector.getElem_push_lt earlier.isLt]
    · simp only [Fin.getElem_fin, Fin.val_last, Vector.getElem_push_eq]
  · rw [frameAfter address offAcc offVector, frame address offAcc offVector]
  · rw [recordAfter, recordStep switch]

/-! ### The published-join terms -/

/-- **The published-join terms** `acc[e] += J[e] · ι(α)` (`ι(α)` in `rF`). -/
theorem det_joinTerms (spec : Replay.LaneSpec) (ok : SpecOK spec) (chunk : Nat) (chunkSmall : chunk < 52)
    (memory : Memory) (join : Nat → BaseField) (acc0 : Nat → BaseField) (alpha : BaseField)
    (factor : ((memory.registers rF).toNat : BaseField) = alpha)
    (joins : ∀ e, e < laneCount spec.lane →
      memory.ram (word (scaleCellBase + elementCount * chunk + spec.slot + e)) = fieldWord (join e))
    (cells : ∀ e, e < laneCount spec.lane → memory.ram (accCell spec e) = fieldWord (acc0 e)) :
    ∃ after, BigInt.det (Prog.rep (laneCount spec.lane) fun element =>
        Replay.joinTerm spec chunk element) memory = some after ∧
      (∀ e, e < laneCount spec.lane → after.ram (accCell spec e) =
        fieldWord (acc0 e + join e * alpha)) ∧
      (∀ address, OffAcc spec address → after.ram address = memory.ram address) ∧
      after.bits = memory.bits := by
  have fits := ok.fits
  obtain ⟨after, run, accs, frame, bitsSame, _⟩ := det_axpy
    (fun e => scaleCellBase + elementCount * chunk + spec.slot + e)
    (fun e => accBase + spec.slot + e) (laneCount spec.lane) memory join acc0 alpha
    (fun e bound => by rw [joins e bound, fieldWord_cast])
    (fun e bound => by rw [cells e bound, fieldWord_cast]) factor
    (fun e e' bound bound' different => accCell_ne spec (by omega) (by omega) different)
    (fun e e' bound bound' => word_ne
      (by unfold scaleCellBase fieldBase curveCellCount rowCellCount elementCount; omega)
      (by unfold accBase; omega)
      (by unfold scaleCellBase fieldBase curveCellCount rowCellCount elementCount accBase; omega))
  exact ⟨after, run, accs, fun address off => frame address fun e bound => off e bound, bitsSame⟩

omit [FieldCertificate] in
theorem plain_joinTerms (spec : Replay.LaneSpec) (chunk : Nat) :
    BigInt.IsPlain (Prog.rep (laneCount spec.lane) fun element => Replay.joinTerm spec chunk element) :=
  BigInt.plain_rep _ _ fun _ _ => by
    unfold Replay.joinTerm loadAt storeAt cst ar
    plain_split

/-! ### `evalScaleOf` in accumulation order -/

/-- **The evaluator's free fold** is the switch terms `Y_s · (ι(s) − ι(α))` plus the
published-join term. -/
theorem evalScaleOf_eq {count width : Nat} (masks : Fin (2 ^ width) → Vector BaseField count)
    (alpha : Fin (2 ^ width)) (join : Fin count → BaseField) (e : Fin count) :
    Programs.evalScaleOf width masks alpha join e =
      (∑ switch, (masks switch).get e * ((switch.val : BaseField) - (alpha.val : BaseField))) +
        join e * (alpha.val : BaseField) := by
  unfold Programs.evalScaleOf iota
  have split : ∑ switch : Fin (2 ^ width), (switch.val : BaseField) *
      (if switch = alpha then join e - ∑ other ∈ Finset.univ.erase alpha, (masks other).get e
        else (masks switch).get e) =
      (alpha.val : BaseField) * (join e - ∑ other ∈ Finset.univ.erase alpha, (masks other).get e) +
        ∑ switch ∈ Finset.univ.erase alpha, (switch.val : BaseField) * (masks switch).get e := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ alpha), if_pos rfl]
    congr 1
    exact Finset.sum_congr rfl fun switch member => by
      rw [if_neg (Finset.ne_of_mem_erase member)]
  have peel : ∑ switch : Fin (2 ^ width), (masks switch).get e *
      ((switch.val : BaseField) - (alpha.val : BaseField)) =
      (masks alpha).get e * ((alpha.val : BaseField) - (alpha.val : BaseField)) +
        ∑ switch ∈ Finset.univ.erase alpha,
          (masks switch).get e * ((switch.val : BaseField) - (alpha.val : BaseField)) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ alpha)).symm
  rw [split, peel, sub_self, mul_zero, zero_add]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have comm : ∑ switch ∈ Finset.univ.erase alpha, (switch.val : BaseField) * (masks switch).get e =
      ∑ switch ∈ Finset.univ.erase alpha, (masks switch).get e * (switch.val : BaseField) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [comm]
  ring

end

end Kriterion.ArgoMAC.PlanB.SimMachine
