/-
**The replay's tree toolkit.**

* the straight-line tree steps (`rtree_cst_seq`, …) and the register reads (`reg_same`,
  `reg_ne`, `rtree_ar_val`);
* `rtree_plain`: a plain block (`BigInt.IsPlain`: no coin, no oracle, no point operation) is the
  pure tree of its deterministic result `BigInt.det`, so the replay's straight-line phases
  (digit extraction, accumulation, the fold's bookkeeping) are proved with `det`;
* one Davies–Meyer hash step (`agree_hashStep`: an index constant, a fixed forward query, the xor
  with the label), the fold's query step.
-/

import Proof.Simulator.ReplayBase

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Straight-line tree steps -/

theorem rtree_cst_seq (target : Register) (value : Nat) (rest : Prog) (memory : Memory) :
    rtree (.seq (cst target value) rest) memory = rtree rest (setReg memory target (word value)) :=
  rfl

theorem rtree_ar_seq (operation : Arithmetic) (target left right : Register) (rest : Prog)
    (memory : Memory) :
    rtree (.seq (ar operation target left right) rest) memory =
      rtree rest (setReg memory target
        (operation.eval (memory.registers left) (memory.registers right))) := rfl

theorem rtree_loadAt_seq (target : Register) (address : Nat) (rest : Prog) (memory : Memory) :
    rtree (.seq (loadAt target address) rest) memory =
      rtree rest (setReg (setReg memory rAddr (word address)) target (memory.ram (word address))) :=
  rfl

theorem rtree_storeAt_seq (address : Nat) (source : Register) (rest : Prog) (memory : Memory)
    (other : source ≠ rAddr) :
    rtree (.seq (storeAt address source) rest) memory =
      rtree rest (storeRam (setReg memory rAddr (word address)) (word address)
        (memory.registers source)) := by
  show rtree rest (storeRam (setReg memory rAddr (word address))
    ((setReg memory rAddr (word address)).registers rAddr)
    ((setReg memory rAddr (word address)).registers source)) = _
  simp only [setReg_registers, if_neg other, ↓reduceIte]

theorem rtree_storeAt (address : Nat) (source : Register) (memory : Memory)
    (other : source ≠ rAddr) :
    rtree (storeAt address source) memory =
      .pure (some (storeRam (setReg memory rAddr (word address)) (word address)
        (memory.registers source))) := by
  show FreeQuery.pure (some (storeRam (setReg memory rAddr (word address))
    ((setReg memory rAddr (word address)).registers rAddr)
    ((setReg memory rAddr (word address)).registers source))) = _
  simp only [setReg_registers, if_neg other, ↓reduceIte]

/-! ### Register reads -/

omit [FieldCertificate] in
theorem reg_same (memory : Memory) (target : Register) (value : Word) :
    (setReg memory target value).registers target = value := by
  rw [setReg_registers, if_pos rfl]

omit [FieldCertificate] in
theorem reg_ne (memory : Memory) (target other : Register) (value : Word) (different : other ≠ target) :
    (setReg memory target value).registers other = memory.registers other := by
  rw [setReg_registers, if_neg different]

theorem rtree_ar_val (operation : Arithmetic) (target left right : Register) (rest : Prog)
    (memory : Memory) (first second : Word) (hfirst : memory.registers left = first)
    (hsecond : memory.registers right = second) :
    rtree (.seq (ar operation target left right) rest) memory =
      rtree rest (setReg memory target (operation.eval first second)) := by
  rw [rtree_ar_seq, hfirst, hsecond]

theorem fieldMul_words (first second : BaseField) :
    Arithmetic.fieldMul.eval (fieldWord first) (fieldWord second) = fieldWord (first * second) := by
  rw [eval_fieldMul, fieldWord_cast, fieldWord_cast]

theorem fieldAdd_words (first second : BaseField) :
    Arithmetic.fieldAdd.eval (fieldWord first) (fieldWord second) = fieldWord (first + second) := by
  rw [eval_fieldAdd, fieldWord_cast, fieldWord_cast]

/-! ### Plain blocks are pure trees -/

/-- **A plain block is the pure tree of its deterministic result.** -/
theorem rtree_plain : ∀ (program : Prog), BigInt.IsPlain program → ∀ memory : Memory,
    rtree program memory = .pure (BigInt.det program memory)
  | .op operation, plain, memory => by
      cases operation <;> first | exact absurd plain id | rfl
  | .popBit _ _, _, _ => rfl
  | .skip _, _, _ => rfl
  | .abort _, _, _ => rfl
  | .seq first second, plain, memory => by
      rw [rtree_seq, rtree_plain first plain.1 memory]
      show bindOpt (.pure (BigInt.det first memory)) (rtree second) =
        .pure ((BigInt.det first memory).bind (BigInt.det second))
      cases BigInt.det first memory with
      | none => rfl
      | some next => exact rtree_plain second plain.2 next
  | .ite source whenSet whenClear, plain, memory => by
      show (if memory.registers source = 0 then rtree whenClear memory else rtree whenSet memory) =
        .pure (if memory.registers source = 0 then BigInt.det whenClear memory
          else BigInt.det whenSet memory)
      by_cases zero : memory.registers source = 0
      · rw [if_pos zero, if_pos zero]
        exact rtree_plain whenClear plain.2 memory
      · rw [if_neg zero, if_neg zero]
        exact rtree_plain whenSet plain.1 memory

/-- A plain block that ends in `after`, followed by any block. -/
theorem rtree_plain_seq {first : Prog} (plain : BigInt.IsPlain first) {memory after : Memory}
    (run : BigInt.det first memory = some after) (rest : Prog) :
    rtree (.seq first rest) memory = rtree rest after := by
  rw [rtree_seq, rtree_plain first plain memory, run]
  rfl

/-- A plain block that ends in `after`. -/
theorem rtree_plain_some {program : Prog} (plain : BigInt.IsPlain program) {memory after : Memory}
    (run : BigInt.det program memory = some after) :
    rtree program memory = .pure (some after) := by
  rw [rtree_plain program plain memory, run]

/-- A plain block that ends in `after`, against a pure abstract value. -/
theorem agree_plain_leaf {β : Type} {Post : β → Memory → Prop} {program : Prog}
    (plain : BigInt.IsPlain program) {memory after : Memory}
    (run : BigInt.det program memory = some after) {value : β} (post : Post value after) :
    Agree Post (rtree program memory) (.pure value) := by
  rw [rtree_plain_some plain run]
  exact .leaf post

theorem rtree_ite (source : Register) (whenSet whenClear : Prog) (memory : Memory) :
    rtree (.ite source whenSet whenClear) memory =
      if memory.registers source = 0 then rtree whenClear memory else rtree whenSet memory := rfl

theorem rtree_skip (count : Nat) (memory : Memory) :
    rtree (.skip count) memory = .pure (some memory) := rfl

/-- `seqList` of an append, on trees. -/
theorem rtree_seqList_append (first second : List Prog) (memory : Memory) :
    rtree (Prog.seqList (first ++ second)) memory =
      bindOpt (rtree (Prog.seqList first) memory) (rtree (Prog.seqList second)) := by
  induction first generalizing memory with
  | nil =>
      show rtree (Prog.seqList second) memory = bindOpt (.pure (some memory)) _
      rfl
  | cons head rest ih =>
      show rtree (.seq head (Prog.seqList (rest ++ second))) memory =
        bindOpt (rtree (.seq head (Prog.seqList rest)) memory) _
      rw [rtree_seq, rtree_seq, bindOpt_assoc]
      congr 1
      funext middle
      exact ih middle

/-! ### Memory bookkeeping -/

omit [FieldCertificate] in
theorem writePair_ram (memory : Memory) (first second : Register) (values : Word × Word) :
    (writePair memory first second values).ram = memory.ram := rfl

omit [FieldCertificate] in
theorem writePair_bits (memory : Memory) (first second : Register) (values : Word × Word) :
    (writePair memory first second values).bits = memory.bits := rfl

omit [FieldCertificate] in
theorem writePair_registers (memory : Memory) (first second : Register) (values : Word × Word)
    (index : Register) :
    (writePair memory first second values).registers index =
      if index = second then values.2 else if index = first then values.1 else
        memory.registers index := by
  simp only [writePair, Function.update_apply]

omit [FieldCertificate] in
theorem storeRam_registers (memory : Memory) (address value : Word) :
    (storeRam memory address value).registers = memory.registers := rfl

omit [FieldCertificate] in
theorem storeRam_bits (memory : Memory) (address value : Word) :
    (storeRam memory address value).bits = memory.bits := rfl

omit [FieldCertificate] in
theorem storeRam_ram (memory : Memory) (address value : Word) :
    (storeRam memory address value).ram = Function.update memory.ram address value := rfl

/-! ### One hash step -/

/-- The memory after one hash step: the index constant, the answer, the xor into `target`. -/
def hashMem (memory : Memory) (index : Nat) (target : Register) (answer label : Block) : Memory :=
  setReg (writePair (setReg memory rIndex (word index)) rFirst rSecond (blockWord answer, 0))
    target (blockWord (answer ^^^ label))

omit [FieldCertificate] in
theorem hashMem_ram (memory : Memory) (index : Nat) (target : Register) (answer label : Block) :
    (hashMem memory index target answer label).ram = memory.ram := rfl

omit [FieldCertificate] in
theorem hashMem_bits (memory : Memory) (index : Nat) (target : Register) (answer label : Block) :
    (hashMem memory index target answer label).bits = memory.bits := rfl

omit [FieldCertificate] in
theorem hashMem_target (memory : Memory) (index : Nat) (target : Register) (answer label : Block) :
    (hashMem memory index target answer label).registers target = blockWord (answer ^^^ label) := by
  simp only [hashMem, setReg_registers, ↓reduceIte]

omit [FieldCertificate] in
theorem hashMem_other (memory : Memory) (index : Nat) (target : Register) (answer label : Block)
    (register : Register) (notTarget : register ≠ target) (notIndex : register ≠ rIndex)
    (notFirst : register ≠ rFirst) (notSecond : register ≠ rSecond) :
    (hashMem memory index target answer label).registers register = memory.registers register := by
  simp only [hashMem, setReg_registers, writePair_registers, if_neg notTarget, if_neg notSecond,
    if_neg notFirst, if_neg notIndex]

/-- **One Davies–Meyer hash step** against the evaluator's `hashM`. -/
theorem agree_hashStep {β : Type} {Post : β → Memory → Prop} (index : PlanB.FixedIndex)
    (target : Register) (rest : Prog) (memory : Memory) (label : Block)
    (input : memory.registers rInput = blockWord label)
    (next : Block → FreeQuery Programs.Spec β)
    (each : ∀ answer, Agree Post (rtree rest (hashMem memory (ordF0 index) target answer label))
      (next (answer ^^^ label))) :
    Agree Post (rtree (.seq (cst rIndex (ordF0 index))
        (.seq (.op (.query 0 rIndex rInput rFirst rSecond))
          (.seq (ar .xor target rFirst rInput) rest))) memory)
      (FreeQuery.bind (Programs.hashM index label) next) := by
  rw [rtree_cst_seq]
  have decode : @queryFromRegisters PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
      (Fintype.ofFinite _) 0 ((setReg memory rIndex (word (ordF0 index))).registers rIndex)
      ((setReg memory rIndex (word (ordF0 index))).registers rInput) =
        some (.fixedForward index label) := by
    rw [setReg_registers, if_pos rfl, setReg_registers, if_neg (by decide), input, query_fixed,
      blockWord_block]
  refine Agree.query 0 rIndex rInput rFirst rSecond _ _ decode
    (rtree (.seq (ar .xor target rFirst rInput) rest)) _ fun answer => ?_
  rw [rtree_ar_seq]
  have same : setReg (writePair (setReg memory rIndex (word (ordF0 index))) rFirst rSecond
      (answerWords (.fixedForward index label) answer)) target
      (Arithmetic.xor.eval
        ((writePair (setReg memory rIndex (word (ordF0 index))) rFirst rSecond
          (answerWords (.fixedForward index label) answer)).registers rFirst)
        ((writePair (setReg memory rIndex (word (ordF0 index))) rFirst rSecond
          (answerWords (.fixedForward index label) answer)).registers rInput)) =
      hashMem memory (ordF0 index) target answer label := by
    unfold hashMem
    congr 1
    rw [writePair_registers, writePair_registers, if_neg (by decide), if_pos rfl, if_neg (by decide),
      if_neg (by decide), setReg_registers, if_neg (by decide), input]
    exact blockWord_xor answer label
  rw [same]
  exact each answer

end

end Kriterion.ArgoMAC.PlanB.SimMachine
