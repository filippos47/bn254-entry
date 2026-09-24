/-
**The opening, the non-collectors** (`Opening.nonCollectors`).

The designated vector's `182` free coordinates `Y*[5d]`, `Y*[5d + 2]` are drawn in the machine's
order, draw `2d + s` being the free coordinate `(d, s)` (element `ncElement (2d + s) = 5d + 2s`):
each is a field cell (bounded rejection below `p`), stored in its designated cell and added to
its element's value, `acc[e] += κ · Y*[e]` (`memSem_nonCollectorOne`). All `182` are
`optionProduct 182 fieldCellLaw` (`memSem_nonCollectors`); afterwards every free designated cell
holds its draw (`ncFold_designated`), every free accumulator its value plus `κ` times the draw
(`ncFold_acc`), and every other cell is unchanged (`ncFold_off`).
-/

import Proof.Simulator.OpeningSolve

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-- The registers a non-collector clears. -/
def ncScratch : List Register := [rAcc, rOut, rFlag, rBit, rAddr, rSel, rA, rB]

/-- The RAM after the non-collector `Y` of element `e`: `Y` in the designated cell,
`acc[e] + κ · Y` in the accumulator. -/
def ncRam (element : Nat) (ram : Word → Word) (value : Word) : Word → Word :=
  Function.update (Function.update ram (word (designatedCell element)) value)
    (word (Opening.xCell element))
    (fieldWord (wordField (ram (word (Opening.xCell element))) +
      wordField (ram (word tmpKappa)) * wordField value))

/-- The memory one non-collector leaves. -/
def ncMem (element : Nat) (memory : Memory) (value : BaseField) : Memory :=
  clearRegs (withRam memory (ncRam element memory.ram (fieldWord value))) ncScratch

/-- The element of draw `i`: `5 ⌊i / 2⌋ + 2 (i mod 2)`. -/
def ncElement (index : Nat) : Nat := 5 * (index / 2) + 2 * (index % 2)

/-! ### One non-collector -/

omit [FieldCertificate] in
theorem plain_storeNonCollector (element : Nat) :
    BigInt.IsPlain (Opening.storeNonCollector element) := by
  unfold Opening.storeNonCollector loadAt storeAt cst ar
  plain_split

theorem det_storeNonCollector (element : Nat) (small : element < 455) (memory : Memory) :
    ∃ after, BigInt.det (Opening.storeNonCollector element) memory = some after ∧
      after.ram = ncRam element memory.ram (memory.registers rOut) ∧ after.bits = memory.bits ∧
      ∀ index, index ≠ rAddr → index ≠ rA → index ≠ rB →
        after.registers index = memory.registers index := by
  have kappaNe : word tmpKappa ≠ word (designatedCell element) := by addr_ne
  have accNe : word (Opening.xCell element) ≠ word (designatedCell element) := by addr_ne
  refine ⟨_, rfl, ?_, by reg_eval, fun index notAddr notA notB => by
    reg_eval
    simp only [notAddr, notA, notB, if_false]⟩
  reg_eval
  unfold ncRam
  rw [Function.update_of_ne kappaNe, Function.update_of_ne accNe, eval_fieldAdd, eval_fieldMul,
    fieldWord_cast]
  rfl

/-- What follows the attempts of a non-collector: on success the store, then the scratch. -/
def ncTail (element : Nat) (memory : Memory) : PMF (Option Memory) :=
  if memory.registers rFlag = 0 then PMF.pure none
  else PMF.pure (some (clearRegs (withRam memory (ncRam element memory.ram (memory.registers rOut)))
    ncScratch))

theorem memSem_ncContinuation (element : Nat) (small : element < 455) (memory : Memory) :
    (Prog.seq (.ite rFlag (Opening.storeNonCollector element) (.abort rSel))
      (zeroRegs ncScratch)).memSem memory = ncTail element memory := by
  rw [memSem_seq]
  unfold ncTail
  by_cases zero : memory.registers rFlag = 0
  · rw [if_pos zero]
    simp only [Prog.memSem, if_pos zero, PMF.pure_bind]
    rfl
  · rw [if_neg zero]
    simp only [Prog.memSem, if_neg zero]
    obtain ⟨after, run, ram, bits, regs⟩ := det_storeNonCollector element small memory
    rw [BigInt.memSem_det _ (plain_storeNonCollector element), run, PMF.pure_bind]
    show (zeroRegs ncScratch).memSem after = _
    rw [memSem_zeroRegs]
    refine congrArg (fun final => PMF.pure (some final)) ?_
    rw [clearRegs_eq_iff]
    refine ⟨ram, bits, fun index outside => regs index ?_ ?_ ?_⟩ <;>
      (intro same; apply outside; rw [same]; decide)

theorem ncTail_clear (element : Nat) (memory : Memory) :
    ncTail element (clearRegs memory (attemptScratch [rAddr])) = ncTail element memory := by
  have flagSame : (clearRegs memory (attemptScratch [rAddr])).registers rFlag =
      memory.registers rFlag := by
    rw [clearRegs_registers, if_neg (by simp [attemptScratch]; decide)]
  have outSame : (clearRegs memory (attemptScratch [rAddr])).registers rOut =
      memory.registers rOut := by
    rw [clearRegs_registers, if_neg (by simp [attemptScratch]; decide)]
  unfold ncTail
  rw [flagSame, outSame, (clearRegs_other _ _).1]
  split
  · rfl
  · refine congrArg (fun final => PMF.pure (some final)) ?_
    rw [clearRegs_eq_iff]
    refine ⟨rfl, (clearRegs_other _ _).2, fun index outside => ?_⟩
    simp only [withRam_registers]
    rw [clearRegs_registers, if_neg]
    intro inside
    apply outside
    simp only [attemptScratch, List.mem_cons] at inside
    simp only [ncScratch, List.mem_cons]
    rcases inside with h | h | h | h | h | h <;> simp [h]

/-- **One non-collector is a field cell**, stored in its designated cell and added to its
element's value. -/
theorem memSem_nonCollectorOne (element : Nat) (small : element < 455) (memory : Memory) :
    (Opening.nonCollectorOne element).memSem memory =
      fieldCellLaw.map (Option.map (ncMem element memory)) := by
  have scratchJunk : attemptScratch [rAddr] = [rAcc, rBit, rAddr, rSel, rAddr] := rfl
  have outOut : rOut ∉ attemptScratch [rAddr] := by rw [scratchJunk]; decide
  have flagOut : rFlag ∉ attemptScratch [rAddr] := by rw [scratchJunk]; decide
  set start := setReg (setReg memory rOut (word 0)) rFlag (word 0) with startDef
  have startFlag : start.registers rFlag = bitWord false := by
    rw [startDef, setReg_registers, if_pos rfl]; rfl
  have shape : (Opening.nonCollectorOne element).memSem memory =
      ((Prog.rep attempts fun _ => attempt fieldWidth (testBelow pNat)).memSem start).bind
        (kleisli (ncTail element)) := by
    unfold Opening.nonCollectorOne bounded rejection
    rw [memSem_seq, memSem_seq, PMF.bind_bind, memSem_cst_seq, memSem_cst_seq]
    have tailIs : ncTail element = (Prog.seq (.ite rFlag (Opening.storeNonCollector element)
        (.abort rSel)) (zeroRegs ncScratch)).memSem :=
      funext fun final => (memSem_ncContinuation element small final).symm
    rw [tailIs]
    refine congrArg (PMF.bind _) (funext fun result => ?_)
    rw [kleisli_bind]
    refine congrArg (kleisli · result) (funext fun final => ?_)
    rw [memSem_seq]
    rfl
  rw [shape]
  have tailClear : ((Prog.rep attempts fun _ => attempt fieldWidth (testBelow pNat)).memSem
      start).bind (kleisli (ncTail element)) =
      (((Prog.rep attempts fun _ => attempt fieldWidth (testBelow pNat)).memSem start).map
        (Option.map fun final => clearRegs final (attemptScratch [rAddr]))).bind
        (kleisli (ncTail element)) := by
    rw [PMF.bind_map]
    refine congrArg (PMF.bind _) (funext fun result => ?_)
    cases result with
    | none => rfl
    | some final => exact (ncTail_clear element final).symm
  rw [tailClear, rep_attempt_law fieldWidth (by unfold fieldWidth; omega) (testBelow pNat)
      (fun value => decide (value < pNat)) [rAddr] (isTest_testBelow pNat (by unfold pNat; norm_num))
      (by decide) (by decide) (by decide) attempts start ⟨false, startFlag⟩,
    attemptsLaw_eq_rejectLaw fieldWidth _ (attemptScratch [rAddr]) outOut flagOut attempts _
      (clearRegs_idem _ _) (by rw [clearRegs_registers, if_neg flagOut, startFlag]; rfl),
    PMF.bind_map, fieldCellLaw, PMF.map_comp, ← PMF.bind_pure_comp]
  apply PMF.bind_congr
  intro kept member
  cases kept with
  | none =>
      simp only [Function.comp_apply, kleisli, keptMem, ncTail, Option.map_none]
      rw [if_pos (by rw [clearRegs_registers, if_neg flagOut, startFlag]; rfl)]
  | some value =>
      have good := rejectLaw_support _ _ _ _ ((PMF.mem_support_iff _ _).mpr member)
      simp only [decide_eq_true_eq] at good
      simp only [Function.comp_apply, kleisli, keptMem, ncTail, Option.map_some]
      have flagOne : (clearRegs (setReg (setReg (clearRegs start (attemptScratch [rAddr])) rOut
          (BitVec.ofNat 256 value)) rFlag 1) (attemptScratch [rAddr])).registers rFlag = 1 := by
        rw [clearRegs_registers, if_neg flagOut, setReg_registers, if_pos rfl]
      rw [if_neg (by rw [flagOne]; decide)]
      refine congrArg (fun final => PMF.pure (some final)) ?_
      unfold ncMem
      rw [clearRegs_eq_iff]
      have outIs : (clearRegs (setReg (setReg (clearRegs start (attemptScratch [rAddr])) rOut
          (BitVec.ofNat 256 value)) rFlag 1) (attemptScratch [rAddr])).registers rOut =
          fieldWord (value : BaseField) := by
        rw [clearRegs_registers, if_neg outOut, setReg_registers,
          if_neg (show rOut ≠ rFlag by decide), setReg_registers, if_pos rfl,
          fieldWord_natCast good.1]
      refine ⟨?_, ?_, fun index outside => ?_⟩
      · simp only [withRam_ram]
        rw [outIs, (clearRegs_other _ _).1]
        rfl
      · simp only [withRam_bits]
        rw [(clearRegs_other _ _).2]
        rfl
      · have notOut : index ≠ rOut := fun same => outside (by rw [same]; decide)
        have notFlag : index ≠ rFlag := fun same => outside (by rw [same]; decide)
        have notScratch : index ∉ attemptScratch [rAddr] := by
          intro inside
          apply outside
          rw [scratchJunk] at inside
          simp only [ncScratch, List.mem_cons] at inside ⊢
          rcases inside with h | h | h | h | h | h <;> simp [h]
        simp only [withRam_registers, clearRegs_registers, setReg_registers, notOut, notFlag,
          notScratch, if_false, startDef]

/-! ### All non-collectors -/

omit [FieldCertificate] in
theorem ncElement_lt (index : Nat) (small : index < digitCount * 2) : ncElement index < 455 := by
  unfold ncElement digitCount at *
  omega

/-- The non-collector steps from draw `offset` on. -/
def ncStep (offset index : Nat) : Memory → BaseField → Memory := ncMem (ncElement (index + offset))

/-- **The non-collectors**: `182` independent field cells, draw `i` at element `ncElement i`. -/
theorem memSem_nonCollectors (memory : Memory) :
    Opening.nonCollectors.memSem memory =
      (optionProduct (digitCount * 2) fun _ => fieldCellLaw).map
        (Option.map (foldStore (ncStep 0) (digitCount * 2) memory)) := by
  unfold Opening.nonCollectors
  rw [memSem_rep_congr _ (fun digit => Prog.rep 2 fun slot =>
      if slot = 0 then Opening.nonCollectorOne (5 * digit) else
        Opening.nonCollectorOne (5 * digit + 2)) 91
      (fun digit _ memory => memSem_seq_rep_two _ _ memory),
    memSem_rep_nest 2 _ (by norm_num) 91]
  exact memSem_rep_law_idx (fun _ => True) (91 * 2) (fun _ => fieldCellLaw) _ (ncStep 0)
    (fun index bound memory _ => by
      have element := ncElement_lt index bound
      rcases Nat.mod_two_eq_zero_or_one index with even | odd
      · rw [if_pos even]
        have same : 5 * (index / 2) = ncElement index := by unfold ncElement; omega
        rw [same]
        exact memSem_nonCollectorOne _ element memory
      · rw [if_neg (by omega)]
        have same : 5 * (index / 2) + 2 = ncElement index := by unfold ncElement; omega
        rw [same]
        exact memSem_nonCollectorOne _ element memory)
    (fun _ _ _ _ _ => trivial) memory trivial


/-! ### What the non-collectors leave -/

theorem ncMem_ram (element : Nat) (memory : Memory) (value : BaseField) :
    (ncMem element memory value).ram = ncRam element memory.ram (fieldWord value) := by
  unfold ncMem
  rw [(clearRegs_other _ _).1]
  rfl

theorem ncMem_bits (element : Nat) (memory : Memory) (value : BaseField) :
    (ncMem element memory value).bits = memory.bits := by
  unfold ncMem
  rw [(clearRegs_other _ _).2]
  rfl


theorem ncStep_succ (offset : Nat) :
    (fun index => ncStep offset (index + 1)) = ncStep (offset + 1) := by
  funext index
  unfold ncStep
  rw [show index + 1 + offset = index + (offset + 1) by omega]

omit [FieldCertificate] in
theorem ncElement_ne {first second : Nat} (different : first ≠ second) :
    ncElement first ≠ ncElement second := by
  unfold ncElement
  omega

/-- The two cells a draw writes. -/
def NcAway (element : Nat) (target : Word) : Prop :=
  target ≠ word (designatedCell element) ∧ target ≠ word (Opening.xCell element)

theorem ncRam_off (element : Nat) (ram : Word → Word) (value : Word) (target : Word)
    (away : NcAway element target) : ncRam element ram value target = ram target := by
  unfold ncRam
  rw [Function.update_of_ne away.2, Function.update_of_ne away.1]

theorem ncFold_off : ∀ (count offset : Nat) (memory : Memory) (values : Fin count → BaseField)
    (target : Word), (∀ index, index < count → NcAway (ncElement (index + offset)) target) →
    (foldStore (ncStep offset) count memory values).ram target = memory.ram target
  | 0, _, _, _, _, _ => by rw [foldStore]
  | count + 1, offset, memory, values, target, away => by
      rw [foldStore, ncStep_succ, ncFold_off count (offset + 1) _ _ target (fun index bound => by
          rw [show index + (offset + 1) = index + 1 + offset by omega]
          exact away (index + 1) (by omega)),
        ncStep, ncMem_ram, ncRam_off _ _ _ _ (by simpa using away 0 (by omega))]

theorem ncFold_designated : ∀ (count offset : Nat), offset + count ≤ digitCount * 2 →
    ∀ (memory : Memory) (values : Fin count → BaseField) (index : Fin count),
      (foldStore (ncStep offset) count memory values).ram
          (word (designatedCell (ncElement (index.val + offset)))) = fieldWord (values index)
  | 0, _, _, _, _, index => index.elim0
  | count + 1, offset, fits, memory, values, index => by
      rw [foldStore, ncStep_succ]
      cases index using Fin.cases with
      | zero =>
          have element := ncElement_lt offset (by omega)
          simp only [Fin.val_zero, Nat.zero_add]
          rw [ncFold_off count (offset + 1) _ _ _ (fun later bound => ⟨?_, ?_⟩)]
          · rw [ncStep, Nat.zero_add, ncMem_ram]
            unfold ncRam
            rw [Function.update_of_ne (by addr_ne), Function.update_self]
          · have other := ncElement_lt (later + (offset + 1)) (by omega)
            have different := ncElement_ne (show later + (offset + 1) ≠ offset by omega)
            exact word_ne (by addr_arith) (by addr_arith) (by unfold designatedCell; omega)
          · have other := ncElement_lt (later + (offset + 1)) (by omega)
            exact word_ne (by addr_arith) (by addr_arith) (by addr_arith)
      | succ index =>
          have := ncFold_designated count (offset + 1) (by omega)
            (ncStep offset 0 memory (values 0)) (fun later => values later.succ) index
          rw [show index.val + (offset + 1) = index.succ.val + offset by
            simp only [Fin.val_succ]; omega] at this
          exact this

theorem ncFold_acc : ∀ (count offset : Nat), offset + count ≤ digitCount * 2 →
    ∀ (memory : Memory) (values : Fin count → BaseField) (index : Fin count),
      (foldStore (ncStep offset) count memory values).ram
          (word (Opening.xCell (ncElement (index.val + offset)))) =
        fieldWord (wordField (memory.ram (word (Opening.xCell (ncElement (index.val + offset))))) +
          wordField (memory.ram (word tmpKappa)) * values index)
  | 0, _, _, _, _, index => index.elim0
  | count + 1, offset, fits, memory, values, index => by
      rw [foldStore, ncStep_succ]
      have element := ncElement_lt offset (by omega)
      have kappaAway : NcAway (ncElement offset) (word tmpKappa) :=
        ⟨by addr_ne, by addr_ne⟩
      cases index using Fin.cases with
      | zero =>
          simp only [Fin.val_zero, Nat.zero_add]
          rw [ncFold_off count (offset + 1) _ _ _ (fun later bound => ⟨?_, ?_⟩)]
          · rw [ncStep, Nat.zero_add, ncMem_ram]
            unfold ncRam
            rw [Function.update_self, wordField_fieldWord]
          · have other := ncElement_lt (later + (offset + 1)) (by omega)
            exact word_ne (by addr_arith) (by addr_arith) (by addr_arith)
          · have other := ncElement_lt (later + (offset + 1)) (by omega)
            have different := ncElement_ne (show later + (offset + 1) ≠ offset by omega)
            exact word_ne (by addr_arith) (by addr_arith) (by unfold Opening.xCell; omega)
      | succ index =>
          have := ncFold_acc count (offset + 1) (by omega)
            (ncStep offset 0 memory (values 0)) (fun later => values later.succ) index
          rw [show index.val + (offset + 1) = index.succ.val + offset by
            simp only [Fin.val_succ]; omega] at this
          rw [this, ncStep, Nat.zero_add, ncMem_ram, ncRam_off _ _ _ _ kappaAway]
          have other := ncElement_lt (index.succ.val + offset) (by omega)
          have different := ncElement_ne (show index.succ.val + offset ≠ offset by
            simp only [Fin.val_succ]; omega)
          rw [ncRam_off _ _ _ _ ⟨word_ne (by addr_arith) (by addr_arith) (by addr_arith),
            word_ne (by addr_arith) (by addr_arith) (by unfold Opening.xCell; omega)⟩]

theorem ncFold_bits (count offset : Nat) (memory : Memory) (values : Fin count → BaseField) :
    (foldStore (ncStep offset) count memory values).bits = memory.bits :=
  foldStore_bits _ (fun _ _ _ => ncMem_bits _ _ _) count memory values

end

end Kriterion.ArgoMAC.PlanB.SimMachine
