/-
**The law of stage 1's serializer.**

`serialize` pushes the wire bits in reverse wire order; each `emitWord address width` pushes the
low `width` bits of `RAM[address]`, least significant on top. `memSem_serialize`: the serializer
is deterministic, leaves the RAM and the other stacks unchanged, and leaves stack `3` holding
`serialBits RAM` (curve and rows, bytes, fold joins, the `52` scale chunk words, each least
significant bit first) on top of the old stack. A chunk word is its `642` scale cells, the first
`641` as `254` bits and the last as `256` bits, then two explicit zero bits: the word's four zero
padding bits are the top bits of its last cell and the two pushed zeros (`chunkWordBits`,
`memSem_serializeChunk`).
-/

import Proof.Simulator.Stage1Cells

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

/-- **The serialized bits of one chunk word** (chunk `chunk`, counted from the bottom): the
chunk's first `641` scale cells as `254` bits each, then its last cell as `256` bits, then two
zero bits. -/
def chunkWordBits (ram : Word → Word) (chunk : Nat) : List Bool :=
  (List.ofFn fun index : Fin 641 =>
      bitRun (ram (word (scaleCellBase + 642 * chunk + index.val))) 0 254).flatten ++
    (bitRun (ram (word (scaleCellBase + 642 * chunk + 641))) 0 256 ++ [false, false])

/-- **The serialized bits of a RAM**: curve and rows (`256` bits each), the exception bytes
(`8`), the fold joins (`128`), the `52` chunk words (`chunkWordBits`), each least significant bit
first. -/
def serialBits (ram : Word → Word) : List Bool :=
  (List.ofFn fun index : Fin (curveCellCount + rowCellCount) =>
      bitRun (ram (word (fieldBase + index.val))) 0 256).flatten ++
    ((List.ofFn fun index : Fin exceptionByteCount =>
      bitRun (ram (word (exceptionBase + index.val))) 0 8).flatten ++
    ((List.ofFn fun index : Fin hotBlockCount =>
      bitRun (ram (word (hotBase + index.val))) 0 128).flatten ++
    (List.ofFn fun chunk : Fin 52 => chunkWordBits ram chunk.val).flatten))

omit [FieldCertificate] in
/-- One pushed zero bit on the response stack. -/
theorem emits_pushZero (memory : Memory) : Emits memory (pushOn memory 3 false) [false] :=
  ⟨rfl, by simp [pushOn], fun stack other => by simp [pushOn, Function.update_of_ne other]⟩

/-- A pushed bit, then the rest. -/
theorem memSem_push_seq (bit : Bool) (rest : Prog) (memory : Memory) :
    (Prog.seq (.op (.push 3 bit)) rest).memSem memory = rest.memSem (pushOn memory 3 bit) := by
  rw [memSem_seq]
  exact PMF.pure_bind _ _

/-- **One chunk word.** `serializeChunk r` emits chunk `51 − r`: two zero bits, its last cell
(`256` bits), then its other `641` cells from the top down, which leaves the word's bits in wire
order. -/
theorem memSem_serializeChunk (step : Nat) (small : step < 52) (memory : Memory) :
    ∃ after, (Stage1.serializeChunk step).memSem memory = PMF.pure (some after) ∧
      Emits memory after (chunkWordBits memory.ram (51 - step)) := by
  have lastCell : fieldBase + fieldCellCount - 1 - 642 * step =
      scaleCellBase + 642 * (51 - step) + 641 := by
    unfold fieldCellCount scaleCellBase curveCellCount rowCellCount scaleCellCount
    omega
  have blockCell : ∀ index : Nat,
      fieldBase + fieldCellCount - 1 - 642 * step - 1 + 1 - 641 + index =
        scaleCellBase + 642 * (51 - step) + index := by
    intro index
    unfold fieldCellCount scaleCellBase curveCellCount rowCellCount scaleCellCount
    omega
  set pushed := pushOn (pushOn memory 3 false) 3 false with pushedDef
  have emitsPushed : Emits memory pushed ([false] ++ [false]) :=
    (emits_pushZero memory).trans (emits_pushZero _)
  obtain ⟨middle, runLast, emitsLast⟩ :=
    memSem_emitWord (fieldBase + fieldCellCount - 1 - 642 * step) 256 le_rfl pushed
  obtain ⟨after, runBlock, emitsBlock⟩ := memSem_emitBlock 254 (by norm_num)
    (fieldBase + fieldCellCount - 1 - 642 * step - 1) 641
    (by unfold fieldCellCount curveCellCount rowCellCount scaleCellCount; omega) middle
  refine ⟨after, ?_, ?_⟩
  · unfold Stage1.serializeChunk
    rw [memSem_push_seq, memSem_push_seq, ← pushedDef, memSem_seq, runLast, PMF.pure_bind]
    exact runBlock
  · have joined := (emitsPushed.trans emitsLast).trans emitsBlock
    have pushedRam : pushed.ram = memory.ram := rfl
    have block : (List.ofFn fun index : Fin 641 =>
        bitRun (middle.ram (word (fieldBase + fieldCellCount - 1 - 642 * step - 1 + 1 - 641 +
          index.val))) 0 254) =
        List.ofFn fun index : Fin 641 =>
          bitRun (memory.ram (word (scaleCellBase + 642 * (51 - step) + index.val))) 0 254 := by
      congr 1
      funext index
      rw [emitsLast.1, pushedRam, blockCell index.val]
    rw [block, pushedRam, lastCell] at joined
    unfold chunkWordBits
    exact joined

/-- **The chunk words**: the first `count` steps emit the top `count` chunk words, in wire order. -/
theorem memSem_serializeChunks :
    ∀ (count : Nat), count ≤ 52 → ∀ memory : Memory,
      ∃ after, (Prog.rep count Stage1.serializeChunk).memSem memory = PMF.pure (some after) ∧
        Emits memory after (List.ofFn fun index : Fin count =>
          chunkWordBits memory.ram (52 - count + index.val)).flatten
  | 0, _, memory => ⟨memory, by rw [Prog.rep]; rfl, by simpa using Emits.refl memory⟩
  | count + 1, bound, memory => by
      obtain ⟨middle, run, emits⟩ := memSem_serializeChunks count (by omega) memory
      obtain ⟨after, step, emitsStep⟩ := memSem_serializeChunk count (by omega) middle
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
theorem memSem_serialize (memory : Memory) :
    ∃ after, Stage1.serialize.memSem memory = PMF.pure (some after) ∧
      Emits memory after (serialBits memory.ram) := by
  have hotTop : hotBase + hotBlockCount - 1 + 1 - hotBlockCount = hotBase :=
    top_sub _ _ (by decide)
  have byteTop : exceptionBase + exceptionByteCount - 1 + 1 - exceptionByteCount =
      exceptionBase := top_sub _ _ (by decide)
  have fieldTop : fieldBase + curveCellCount + rowCellCount - 1 + 1 -
      (curveCellCount + rowCellCount) = fieldBase := by
    rw [Nat.add_assoc]
    exact top_sub _ _ (by decide)
  obtain ⟨afterScale, runScale, emitsScale⟩ := memSem_serializeChunks 52 le_rfl memory
  obtain ⟨afterHot, runHot, emitsHot⟩ := memSem_emitBlock 128 (by norm_num)
    (hotBase + hotBlockCount - 1) hotBlockCount
    (block_le _ _ _ le_rfl (by unfold hotBlockCount; decide)) afterScale
  obtain ⟨afterBytes, runBytes, emitsBytes⟩ := memSem_emitBlock 8 (by norm_num)
    (exceptionBase + exceptionByteCount - 1) exceptionByteCount
    (block_le _ _ _ le_rfl (by unfold exceptionByteCount; decide)) afterHot
  obtain ⟨afterFields, runFields, emitsFields⟩ := memSem_emitBlock 256 (by norm_num)
    (fieldBase + curveCellCount + rowCellCount - 1) (curveCellCount + rowCellCount)
    (by rw [Nat.add_assoc]; exact block_le _ _ _ le_rfl (by decide))
    afterBytes
  refine ⟨afterFields, ?_, ?_⟩
  · unfold Stage1.serialize
    rw [memSem_seq, runScale, PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_seq, runHot, PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_seq, runBytes, PMF.pure_bind]
    simp only [kleisli]
    exact runFields
  · have all := ((emitsScale.trans emitsHot).trans emitsBytes).trans emitsFields
    rw [emitsBytes.1, emitsHot.1, emitsScale.1, hotTop, byteTop, fieldTop] at all
    convert all using 1
    unfold serialBits
    simp only [Nat.sub_self, Nat.zero_add]

end Serializer

end

end Kriterion.ArgoMAC.PlanB.SimMachine
