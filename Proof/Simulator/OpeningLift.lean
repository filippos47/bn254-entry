/-
**The opening, step 2 (continued): the randomisers and the homogeneous lift**
(`Opening.lambdas`, `Opening.lifts`).

* `memSem_lambdas`: the `91` randomisers are `optionProduct 91 lambdaLaw = boundedSamplers.lift`,
  `λ_d` stored at `openLambda d`;
* `memSem_liftOne`: the machine's field instructions compute exactly P3's
  `liftRow D_d λ_d = (λ² x, λ³ y, λ)` (and `(λ², λ³, 0)` at `O`), stored at `openRow d`;
* `memSem_lifts`: all `91` rows.
-/

import Proof.Simulator.OpeningHorner

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

/-- Evaluate a register read through a chain of `setReg` / `storeRam`. -/
macro "regs" : tactic =>
  `(tactic| (simp only [setReg_registers, storeRam_registers]; simp (config := { decide := true }) only [if_true, if_false]))

noncomputable section

variable [FieldCertificate]

/-! ### The randomisers -/

/-- The test `1 ≤ rAcc < p` has junk `rAddr` only. -/
theorem isTest_testPositiveBelow :
    IsTestJ (testPositiveBelow pNat) (fun value => decide (1 ≤ value ∧ value < pNat)) [rAddr] := by
  intro memory
  have pSmall : pNat < 2 ^ 256 := by decide
  have pLarge : 1 < pNat := by decide
  refine ⟨setReg memory rAddr (word (pNat - 1)), ?_, clearRegs_setReg_mem _ _ (by simp) _⟩
  set value := memory.registers rAcc with valueDef
  unfold testPositiveBelow
  rw [memSem_cst_seq, memSem_ar_val _ _ _ _ _ _ value (word 1)
      (by rw [reg_ne _ _ _ _ (by decide)]) (reg_same _ _ _), memSem_cst_seq,
    memSem_ar _ _ _ _ _ (Arithmetic.sub.eval value (word 1)) (word (pNat - 1))
      (by rw [reg_ne _ _ _ _ (by decide), reg_same]) (reg_same _ _ _), less_word,
    word_small (show pNat - 1 < 2 ^ 256 by omega)]
  have accept : decide ((Arithmetic.sub.eval value (word 1)).toNat < pNat - 1) =
      decide (1 ≤ value.toNat ∧ value.toNat < pNat) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_iff, eval_sub, BitVec.toNat_sub, word_small (show 1 < 2 ^ 256 by norm_num)]
    have bound := value.isLt
    constructor
    · intro below
      by_cases zero : value.toNat = 0
      · rw [zero] at below
        omega
      · omega
    · intro ⟨one, below⟩
      omega
  rw [accept, setReg_comm _ (show rBit ≠ rAddr by decide), setReg_same, setReg_same]

/-- **A randomiser cell**: bounded rejection on `[1, p)`, stored at `openLambda d`. -/
theorem memSem_lambdaOne_raw (digit : Nat) (memory : Memory) :
    (Opening.lambdaOne digit).memSem memory =
      (rejectLaw fieldWidth (fun value => decide (1 ≤ value ∧ value < pNat)) attempts).map fun kept =>
        kept.map fun value => clearRegs (storeRam memory (word (openLambda digit))
          (BitVec.ofNat 256 value)) samplerScratch := by
  have scratchJunk : attemptScratch [rAddr] = [rAcc, rBit, rAddr, rSel, rAddr] := rfl
  have outOut : rOut ∉ attemptScratch [rAddr] := by rw [scratchJunk]; decide
  have flagOut : rFlag ∉ attemptScratch [rAddr] := by rw [scratchJunk]; decide
  set start := setReg (setReg memory rOut (word 0)) rFlag (word 0) with startDef
  have startFlag : start.registers rFlag = bitWord false := by
    rw [startDef, setReg_registers, if_pos rfl]; rfl
  have shape : (Opening.lambdaOne digit).memSem memory =
      ((Prog.rep attempts fun _ => attempt fieldWidth (testPositiveBelow pNat)).memSem start).bind
        (kleisli (cellTail (openLambda digit))) := by
    unfold Opening.lambdaOne bounded rejection
    rw [memSem_seq, memSem_seq, PMF.bind_bind, memSem_cst_seq, memSem_cst_seq]
    have tailIs : cellTail (openLambda digit) = (Prog.seq (.ite rFlag
        (storeAt (openLambda digit) rOut) (.abort rSel)) (zeroRegs samplerScratch)).memSem :=
      funext fun final => (memSem_cellContinuation (openLambda digit) final).symm
    rw [tailIs]
    refine congrArg (PMF.bind _) (funext fun result => ?_)
    rw [kleisli_bind]
    refine congrArg (kleisli · result) (funext fun final => ?_)
    rw [memSem_seq]
  rw [shape]
  have tailClear : ((Prog.rep attempts fun _ => attempt fieldWidth (testPositiveBelow pNat)).memSem
      start).bind (kleisli (cellTail (openLambda digit))) =
      (((Prog.rep attempts fun _ => attempt fieldWidth (testPositiveBelow pNat)).memSem start).map
        (Option.map fun final => clearRegs final (attemptScratch [rAddr]))).bind
        (kleisli (cellTail (openLambda digit))) := by
    rw [PMF.bind_map]
    refine congrArg (PMF.bind _) (funext fun result => ?_)
    cases result with
    | none => rfl
    | some final => exact (cellTail_clear (openLambda digit) final).symm
  rw [tailClear, rep_attempt_law fieldWidth (by unfold fieldWidth; omega) (testPositiveBelow pNat)
      (fun value => decide (1 ≤ value ∧ value < pNat)) [rAddr] isTest_testPositiveBelow
      (by decide) (by decide) (by decide) attempts start ⟨false, startFlag⟩,
    attemptsLaw_eq_rejectLaw fieldWidth _ (attemptScratch [rAddr]) outOut flagOut attempts _
      (clearRegs_idem _ _) (by rw [clearRegs_registers, if_neg flagOut, startFlag]; rfl),
    PMF.bind_map]
  rw [PMF.map]
  refine congrArg (PMF.bind _) (funext fun kept => ?_)
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

/-- The memory one randomiser leaves. -/
def lamMem (digit : Nat) (memory : Memory) (lam : NonZeroBase) : Memory :=
  clearRegs (storeRam memory (word (openLambda digit)) (fieldWord lam.value)) samplerScratch

/-- **A randomiser is `lambdaLaw`**, stored at `openLambda d`. -/
theorem memSem_lambdaOne (digit : Nat) (memory : Memory) :
    (Opening.lambdaOne digit).memSem memory = lambdaLaw.map (Option.map (lamMem digit memory)) := by
  rw [memSem_lambdaOne_raw, lambdaLaw, PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  apply PMF.bind_congr
  intro drawn member
  cases drawn with
  | none => rfl
  | some value =>
      have good := rejectLaw_support _ _ _ _ ((PMF.mem_support_iff _ _).mpr member)
      simp only [decide_eq_true_eq] at good
      have nonzero : ((value : Nat) : BaseField) ≠ 0 := by
        intro zero
        have := congrArg ZMod.val zero
        rw [ZMod.val_natCast_of_lt (by unfold baseFieldModulus; unfold pNat at good; omega),
          ZMod.val_zero] at this
        omega
      simp only [Function.comp_apply, Option.map_some, Option.bind_some, dif_pos nonzero, lamMem]
      rw [fieldWord_natCast good.1.2]

/-- **The randomisers are `boundedSamplers.lift`**, `λ_d` at `openLambda d`. -/
theorem memSem_lambdas (memory : Memory) :
    Opening.lambdas.memSem memory =
      liftLaw.map (Option.map (foldStore lamMem 91 memory)) :=
  memSem_rep_law lambdaLaw 91 _ _ (fun index memory => memSem_lambdaOne index memory) memory

omit [FieldCertificate] in
theorem lamMem_ram (digit : Nat) (memory : Memory) (lam : NonZeroBase) :
    (lamMem digit memory lam).ram =
      Function.update memory.ram (word (openLambda digit)) (fieldWord lam.value) := by
  unfold lamMem
  rw [(clearRegs_other _ _).1]
  rfl

omit [FieldCertificate] in
theorem lamMem_bits (digit : Nat) (memory : Memory) (lam : NonZeroBase) :
    (lamMem digit memory lam).bits = memory.bits := by
  unfold lamMem
  rw [(clearRegs_other _ _).2]
  rfl

theorem lamFold_bits (memory : Memory) (lams : Fin 91 → NonZeroBase) :
    (foldStore lamMem 91 memory lams).bits = memory.bits :=
  foldStore_bits _ lamMem_bits _ _ _

omit [FieldCertificate] in
theorem lamFold_sameOff (memory : Memory) (lams : Fin 91 → NonZeroBase) :
    SameOff memory.ram (foldStore lamMem 91 memory lams).ram :=
  foldStore_invariant (fun later => SameOff memory.ram later.ram) _ 91
    (fun index bound later lam previous => previous.trans (by
      rw [lamMem_ram]
      have step := sameOff_update later.ram (openCell_word (400 + index) (by omega)) (fieldWord lam.value)
      rw [← Nat.add_assoc] at step
      exact step)) memory lams (SameOff.refl _)

theorem lamFold_at (memory : Memory) (lams : Fin 91 → NonZeroBase) (index : Fin 91) :
    (foldStore lamMem 91 memory lams).ram (word (openLambda index)) = fieldWord (lams index).value :=
  foldStore_ram_at lamMem (fun index => word (openLambda index)) (fun lam => fieldWord lam.value)
    lamMem_ram 91
    (fun first second firstBound secondBound different => word_ne
      (by unfold openLambda openBase; omega) (by unfold openLambda openBase; omega)
      (by unfold openLambda; omega)) memory lams index

theorem lamFold_off (memory : Memory) (lams : Fin 91 → NonZeroBase) (target : Word)
    (away : ∀ index, index < 91 → target ≠ word (openLambda index)) :
    (foldStore lamMem 91 memory lams).ram target = memory.ram target :=
  foldStore_ram_off lamMem (fun index => word (openLambda index)) (fun lam => fieldWord lam.value)
    lamMem_ram 91 memory lams target away

/-! ### The homogeneous lift -/

/-- A homogeneous row's three words. -/
def rowWords (row : FieldMacToECMac.HomogeneousValue) : Word × Word × Word :=
  (fieldWord row.x, fieldWord row.y, fieldWord row.z)

/-- The machine's lift formula on a point register's words `(tag, x, y)`. -/
def liftFormula (words : Word × Word × Word) (lam : BaseField) : Word × Word × Word :=
  let tag : BaseField := ((words.1.toNat : Nat) : BaseField)
  let x : BaseField := ((words.2.1.toNat : Nat) : BaseField)
  let y : BaseField := ((words.2.2.toNat : Nat) : BaseField)
  (fieldWord (((x - 1) * tag + 1) * (lam * lam)), fieldWord (((y - 1) * tag + 1) * (lam * lam * lam)),
    fieldWord (tag * lam))

/-- The machine's lift formula on a point's words is `liftRow`. -/
theorem liftWords (point : Point) (lam : BaseField) :
    rowWords (liftRow point lam) = liftFormula (pointWords point) lam := by
  cases point with
  | zero =>
      simp only [rowWords, liftRow, pointWords, liftFormula]
      have zero : (((0 : Word).toNat : Nat) : BaseField) = 0 := by
        rw [show (0 : Word).toNat = 0 from rfl, Nat.cast_zero]
      rw [zero]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> congr 1 <;> ring
  | some x y valid =>
      simp only [rowWords, liftRow, pointWords, liftFormula]
      have one : (((1 : Word).toNat : Nat) : BaseField) = 1 := by
        rw [show (1 : Word).toNat = 1 from rfl, Nat.cast_one]
      rw [one, field_val_lt, field_val_lt, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> congr 1 <;> ring

omit [FieldCertificate] in
/-- The registers a lift clears. -/
def liftScratch : List Register := [rAcc, rAddr, rA, rB, rC, rD, rE, rF]

/-- **One lifted row** `W_d = liftRow D_d λ_d`, stored at `openRow d` (exact). -/
theorem memSem_liftOne (digit : Nat) (memory : Memory) (point : Point) (lam : BaseField)
    (lamCell : memory.ram (word (openLambda digit)) = fieldWord lam)
    (pointCells : (memory.ram (word (openPoint digit)), memory.ram (word (openPoint digit + 1)),
      memory.ram (word (openPoint digit + 2))) = pointWords point) :
    (Opening.liftOne digit).memSem memory =
      PMF.pure (some (clearRegs (withRam memory (putPoint memory.ram (openRow digit)
        (rowWords (liftRow point lam)))) liftScratch)) := by
  have tagCell := congrArg (fun words => words.1) pointCells
  have xCell := congrArg (fun words => words.2.1) pointCells
  have yCell := congrArg (fun words => words.2.2) pointCells
  simp only at tagCell xCell yCell
  rw [liftWords]
  set tag := (pointWords point).1 with tagDef
  set xw := (pointWords point).2.1 with xwDef
  set yw := (pointWords point).2.2 with ywDef
  unfold Opening.liftOne Opening.loadPoint
  simp only [Prog.seqList]
  rw [memSem_loadAt_seq, lamCell,
    memSem_ar_val _ _ _ _ _ _ (fieldWord lam) (fieldWord lam) (by regs) (by regs), fieldMul_words,
    memSem_ar_val _ _ _ _ _ _ (fieldWord (lam * lam)) (fieldWord lam) (by regs) (by regs),
    fieldMul_words, memSem_seq, memSem_loadAt_seq, memSem_loadAt_seq, memSem_loadAt_seq,
    memSem_skip, PMF.pure_bind]
  simp only [kleisli, setReg_ram]
  rw [tagCell, xCell, yCell, memSem_cst_seq,
    memSem_ar_val _ _ _ _ _ _ xw (word 1) (by regs) (by regs), eval_fieldSub,
    word_small (show 1 < 2 ^ 256 by norm_num), Nat.cast_one,
    memSem_ar_val _ _ _ _ _ _ (fieldWord ((xw.toNat : BaseField) - 1)) tag (by regs) (by regs),
    eval_fieldMul, fieldWord_cast,
    memSem_ar_val _ _ _ _ _ _ (fieldWord (((xw.toNat : BaseField) - 1) * (tag.toNat : BaseField)))
      (word 1) (by regs) (by regs), eval_fieldAdd, fieldWord_cast,
    word_small (show 1 < 2 ^ 256 by norm_num), Nat.cast_one,
    memSem_ar_val _ _ _ _ _ _ yw (word 1) (by regs) (by regs), eval_fieldSub,
    word_small (show 1 < 2 ^ 256 by norm_num), Nat.cast_one,
    memSem_ar_val _ _ _ _ _ _ (fieldWord ((yw.toNat : BaseField) - 1)) tag (by regs) (by regs),
    eval_fieldMul, fieldWord_cast,
    memSem_ar_val _ _ _ _ _ _ (fieldWord (((yw.toNat : BaseField) - 1) * (tag.toNat : BaseField)))
      (word 1) (by regs) (by regs), eval_fieldAdd, fieldWord_cast,
    word_small (show 1 < 2 ^ 256 by norm_num), Nat.cast_one,
    memSem_ar_val _ _ _ _ _ _
      (fieldWord (((xw.toNat : BaseField) - 1) * (tag.toNat : BaseField) + 1))
      (fieldWord (lam * lam)) (by regs) (by regs), fieldMul_words,
    memSem_ar_val _ _ _ _ _ _
      (fieldWord (((yw.toNat : BaseField) - 1) * (tag.toNat : BaseField) + 1))
      (fieldWord (lam * lam * lam)) (by regs) (by regs), fieldMul_words,
    memSem_ar_val _ _ _ _ _ _ tag (fieldWord lam) (by regs) (by regs), eval_fieldMul,
    fieldWord_cast,
    memSem_storeAt_seq _ _ _ _ (by decide), memSem_storeAt_seq _ _ _ _ (by decide),
    memSem_storeAt_seq _ _ _ _ (by decide), memSem_zeroRegs_seq, memSem_skip]
  refine congrArg (fun final => PMF.pure (some final)) ?_
  apply clearRegs_withRam_eq
  · simp only [storeRam_ram, setReg_ram, putPoint, liftFormula]
    regs
    rfl
  · simp only [storeRam_bits, setReg_bits]
  · intro index outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨n0, n4, n6, n7, n8, n9, n10, n11⟩ := outside
    simp only [storeRam_registers, setReg_registers, if_neg n0, if_neg n4, if_neg n6, if_neg n7,
      if_neg n8, if_neg n9, if_neg n10, if_neg n11]

/-- **The `91` lifted rows** `W_d = liftRow D_d λ_d` at `openRow d`, nothing else changed off
the opening's cells. -/
theorem memSem_lifts (memory : Memory) (points : Nat → Point) (lams : Nat → BaseField)
    (lamCells : ∀ digit, digit < 91 → memory.ram (word (openLambda digit)) = fieldWord (lams digit))
    (pointCells : ∀ digit, digit < 91 → (memory.ram (word (openPoint digit)),
      memory.ram (word (openPoint digit + 1)), memory.ram (word (openPoint digit + 2))) =
        pointWords (points digit)) :
    ∀ count, count ≤ 91 → ∃ after,
      (Prog.rep count Opening.liftOne).memSem memory = PMF.pure (some after) ∧
      after.bits = memory.bits ∧ SameOff memory.ram after.ram ∧
      (∀ digit, digit < count → ∀ position, position < 3 →
        after.ram (word (openRow digit + position)) =
          wordAt (rowWords (liftRow (points digit) (lams digit))) position) ∧
      (∀ target, (∀ digit, digit < count → ∀ position, position < 3 →
        target ≠ word (openRow digit + position)) → after.ram target = memory.ram target)
  | 0, _ => ⟨memory, by rw [Prog.rep]; rfl, rfl, SameOff.refl _, fun _ bound => absurd bound (by omega),
      fun _ _ => rfl⟩
  | count + 1, bound => by
      obtain ⟨previous, runPrevious, bitsPrevious, samePrevious, rowsPrevious, offPrevious⟩ :=
        memSem_lifts memory points lams lamCells pointCells count (by omega)
      have lamCell : previous.ram (word (openLambda count)) = fieldWord (lams count) := by
        rw [offPrevious _ (fun digit below position inside => word_ne
          (by unfold openLambda openBase; omega) (by unfold openRow openBase; omega)
          (by unfold openLambda openRow; omega)), lamCells count (by omega)]
      have pointCell : (previous.ram (word (openPoint count)),
          previous.ram (word (openPoint count + 1)), previous.ram (word (openPoint count + 2))) =
            pointWords (points count) := by
        rw [offPrevious (word (openPoint count)) (fun digit below position inside => word_ne
            (by unfold openPoint openBase; omega) (by unfold openRow openBase; omega)
            (by unfold openPoint openRow; omega)),
          offPrevious (word (openPoint count + 1)) (fun digit below position inside => word_ne
            (by unfold openPoint openBase; omega) (by unfold openRow openBase; omega)
            (by unfold openPoint openRow; omega)),
          offPrevious (word (openPoint count + 2)) (fun digit below position inside => word_ne
            (by unfold openPoint openBase; omega) (by unfold openRow openBase; omega)
            (by unfold openPoint openRow; omega)), pointCells count (by omega)]
      have ramNext : (clearRegs (withRam previous (putPoint previous.ram (openRow count)
          (rowWords (liftRow (points count) (lams count))))) liftScratch).ram =
          putPoint previous.ram (openRow count) (rowWords (liftRow (points count) (lams count))) := by
        rw [(clearRegs_other _ _).1]; rfl
      refine ⟨clearRegs (withRam previous (putPoint previous.ram (openRow count)
          (rowWords (liftRow (points count) (lams count))))) liftScratch, ?_, ?_, ?_, ?_, ?_⟩
      · rw [memSem_rep_succ, runPrevious, PMF.pure_bind]
        exact memSem_liftOne count previous (points count) (lams count) lamCell pointCell
      · rw [(clearRegs_other _ _).2, withRam_bits, bitsPrevious]
      · rw [ramNext]
        have step := sameOff_putPoint previous.ram (500 + 3 * count) (by omega)
          (rowWords (liftRow (points count) (lams count)))
        rw [show openBase + (500 + 3 * count) = openRow count by unfold openRow; omega] at step
        exact samePrevious.trans step
      · intro digit below position inside
        rw [ramNext]
        by_cases same : digit = count
        · subst same
          exact putPoint_at _ _ _ _ (by unfold openRow openBase; omega) inside
        · rw [putPoint_off _ _ _ _ (fun position' inside' => word_ne
              (by unfold openRow openBase; omega) (by unfold openRow openBase; omega)
              (by unfold openRow; omega)),
            rowsPrevious digit (by omega) position inside]
      · intro target away
        rw [ramNext, putPoint_off _ _ _ _ (fun position inside => away count (by omega) position inside),
          offPrevious target (fun digit below position inside => away digit (by omega) position inside)]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
