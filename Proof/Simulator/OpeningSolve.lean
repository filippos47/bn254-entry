/-
**The opening, step 3: the collector solve** (`Opening.solve`).

For each digit the machine evaluates the three rows `X, S, Z` on the replayed (designated-free)
accumulators, exactly as `Biquadratic.evaluate{X,Y,Z}` (P3's `evaluateGamma`, the designated-free rows
of `evaluateHomogeneous`), and stores `y*_c = κ · (W_d.c − row_c) · s_c` in the designated
vector's cell of collector `c` (`collectorCell d c`: elements `4d + 1`, `4d + 2`, `4d + 3`,
`memSem_solveDigit`): P3's `collectorTargets`. The scale `s_c` inverts the collector's coefficient
in its row: `1` for `X` and `Z`, `(x · x)⁻¹` for the sign row, whose collector `rowY_cubic` rides
on `x²` (`Opening.finishScaled`, `solveWords`).

* `memSem_addScaled`, `memSem_addCell`, `memSem_finishTarget`, `memSem_finishScaled`: the row
  blocks;
* `run_solvePrefix`, `run_rowX`, `run_rowY`, `run_rowZ`: a digit, in four parts;
* `memSem_solve`: all `91` digits.
-/

import Proof.Simulator.OpeningLift

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

/-- The slot of collector `c` inside its digit: `1, 2, 3` (`rowX_x9`, `rowY_cubic`, `rowZ_x9`). -/
def collectorSlot (collector : Nat) : Nat := collector + 1

/-- The designated vector's cell of collector `c` of digit `d`. -/
def collectorCell (digit collector : Nat) : Nat := designatedCell (4 * digit + collectorSlot collector)

/-- Evaluate a register read through a chain of `setReg` / `storeRam`, then close by `rfl`. -/
macro "regv" : tactic =>
  `(tactic| ((simp only [setReg_registers, storeRam_registers]); (try simp (config := { decide := true }) only [if_true, if_false]); (try rfl)))

/-- Arithmetic on the concrete addresses of the machine's layout. -/
macro "addr_arith" : tactic =>
  `(tactic| ((try simp only [Opening.rowCell, Opening.xCell, Opening.yCell, openRow, openPoint, openLambda, openTau, designatedCell, designatedBase, collectorCell, collectorSlot, fieldBase, curveCellCount, accBase, openBase, requestBase, reqX, reqY, reqTag0, reqQX, reqQY, tmpBase, tmpKappa, tmpJStar, hotLabelBase, designatedLabel, labelBase]) <;> omega))

/-- Two distinct concrete addresses of the machine's layout. -/
macro "addr_ne" : tactic => `(tactic| (apply word_ne <;> addr_arith))

noncomputable section

variable [FieldCertificate]

/-! ### The row blocks -/

/-- `rAcc += RAM[cell] · R[factor]`. -/
theorem memSem_addScaled (cell : Nat) (factor : Register) (memory : Memory)
    (notSel : factor ≠ rSel) (notAddr : factor ≠ rAddr) :
    ∃ after, (Opening.addScaled cell factor).memSem memory = PMF.pure (some after) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      after.registers rAcc = fieldWord (wordField (memory.registers rAcc) +
        wordField (memory.ram (word cell)) * wordField (memory.registers factor)) ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  unfold Opening.addScaled
  simp only [Prog.seqList]
  rw [memSem_loadAt_seq,
    memSem_ar_val _ _ _ _ _ _ (memory.ram (word cell)) (memory.registers factor) (by regv)
      (by simp only [setReg_registers, if_neg notSel, if_neg notAddr]),
    eval_fieldMul,
    memSem_ar_val _ _ _ _ _ _ (memory.registers rAcc) (fieldWord (wordField (memory.ram (word cell)) *
      wordField (memory.registers factor))) (by regv) (by regv), eval_fieldAdd, fieldWord_cast,
    memSem_skip]
  refine ⟨_, rfl, rfl, rfl, by regv, fun index h0 h5 h4 => ?_⟩
  simp only [setReg_registers, if_neg h0, if_neg h5, if_neg h4]

/-- `rAcc += RAM[cell]`. -/
theorem memSem_addCell (cell : Nat) (memory : Memory) :
    ∃ after, (Opening.addCell cell).memSem memory = PMF.pure (some after) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      after.registers rAcc = fieldWord (wordField (memory.registers rAcc) +
        wordField (memory.ram (word cell))) ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  unfold Opening.addCell
  simp only [Prog.seqList]
  rw [memSem_loadAt_seq,
    memSem_ar_val _ _ _ _ _ _ (memory.registers rAcc) (memory.ram (word cell)) (by regv) (by regv),
    eval_fieldAdd, memSem_skip]
  refine ⟨_, rfl, rfl, rfl, by regv, fun index h0 h5 h4 => ?_⟩
  simp only [setReg_registers, if_neg h0, if_neg h5, if_neg h4]

/-- `RAM[target] = (RAM[row] − rAcc) · rF`. -/
theorem memSem_finishTarget (row target : Nat) (memory : Memory) :
    ∃ after, (Opening.finishTarget row target).memSem memory = PMF.pure (some after) ∧
      after.ram = Function.update memory.ram (word target)
        (fieldWord ((wordField (memory.ram (word row)) - wordField (memory.registers rAcc)) *
          wordField (memory.registers rF))) ∧
      after.bits = memory.bits ∧
      ∀ index, index ≠ rSel → index ≠ rAddr → after.registers index = memory.registers index := by
  unfold Opening.finishTarget
  simp only [Prog.seqList]
  rw [memSem_loadAt_seq,
    memSem_ar_val _ _ _ _ _ _ (memory.ram (word row)) (memory.registers rAcc) (by regv) (by regv),
    eval_fieldSub,
    memSem_ar_val _ _ _ _ _ _ (fieldWord (wordField (memory.ram (word row)) -
      wordField (memory.registers rAcc))) (memory.registers rF) (by regv) (by regv), eval_fieldMul,
    fieldWord_cast, memSem_storeAt_seq _ _ _ _ (by decide), memSem_skip]
  refine ⟨_, rfl, ?_, rfl, fun index h5 h4 => ?_⟩
  · simp only [storeRam_ram, setReg_ram]
    regv
  · simp only [storeRam_registers, setReg_registers, if_neg h5, if_neg h4]

/-- `Arithmetic.fieldInv` on words (the inverse of `0` is `0`). -/
theorem eval_fieldInv (first second : Word) :
    Arithmetic.fieldInv.eval first second = fieldWord ((first.toNat : BaseField)⁻¹) := rfl

/-- `RAM[target] = (RAM[row] − rAcc) · rF · rC⁻¹`: the sign row's finish, whose collector has
coefficient `rC = x · x`. It overwrites `rAcc` with `rC⁻¹`. -/
theorem memSem_finishScaled (row target : Nat) (memory : Memory) :
    ∃ after, (Opening.finishScaled row target).memSem memory = PMF.pure (some after) ∧
      after.ram = Function.update memory.ram (word target)
        (fieldWord ((wordField (memory.ram (word row)) - wordField (memory.registers rAcc)) *
          wordField (memory.registers rF) * (wordField (memory.registers rC))⁻¹)) ∧
      after.bits = memory.bits ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  unfold Opening.finishScaled
  simp only [Prog.seqList]
  rw [memSem_loadAt_seq,
    memSem_ar_val _ _ _ _ _ _ (memory.ram (word row)) (memory.registers rAcc) (by regv) (by regv),
    eval_fieldSub,
    memSem_ar_val _ _ _ _ _ _ (fieldWord (wordField (memory.ram (word row)) -
      wordField (memory.registers rAcc))) (memory.registers rF) (by regv) (by regv), eval_fieldMul,
    fieldWord_cast,
    memSem_ar_val _ _ _ _ _ _ (memory.registers rC) (memory.registers rC) (by regv) (by regv),
    eval_fieldInv,
    memSem_ar_val _ _ _ _ _ _ (fieldWord ((wordField (memory.ram (word row)) -
      wordField (memory.registers rAcc)) * wordField (memory.registers rF)))
      (fieldWord (wordField (memory.registers rC))⁻¹) (by regv) (by regv), eval_fieldMul,
    fieldWord_cast, fieldWord_cast, memSem_storeAt_seq _ _ _ _ (by decide), memSem_skip]
  refine ⟨_, rfl, ?_, rfl, fun index h0 h5 h4 => ?_⟩
  · simp only [storeRam_ram, setReg_ram]
    regv
  · simp only [storeRam_registers, setReg_registers, if_neg h0, if_neg h5, if_neg h4]

/-! ### Row steps on field values -/

omit [FieldCertificate] in
theorem wordField_fieldWord (value : BaseField) : wordField (fieldWord value) = value :=
  fieldWord_cast value

/-- An `addScaled` step on field values. -/
theorem step_addScaled (cell : Nat) (factor : Register) (memory : Memory) (acc value scale : BaseField)
    (notSel : factor ≠ rSel) (notAddr : factor ≠ rAddr)
    (hacc : wordField (memory.registers rAcc) = acc) (hvalue : wordField (memory.ram (word cell)) = value)
    (hscale : wordField (memory.registers factor) = scale) :
    ∃ after, (Opening.addScaled cell factor).memSem memory = PMF.pure (some after) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      wordField (after.registers rAcc) = acc + value * scale ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  obtain ⟨after, run, ram, bits, accIs, frame⟩ := memSem_addScaled cell factor memory notSel notAddr
  exact ⟨after, run, ram, bits, by rw [accIs, wordField_fieldWord, hacc, hvalue, hscale], frame⟩

/-- An `addCell` step on field values. -/
theorem step_addCell (cell : Nat) (memory : Memory) (acc value : BaseField)
    (hacc : wordField (memory.registers rAcc) = acc) (hvalue : wordField (memory.ram (word cell)) = value) :
    ∃ after, (Opening.addCell cell).memSem memory = PMF.pure (some after) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      wordField (after.registers rAcc) = acc + value ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  obtain ⟨after, run, ram, bits, accIs, frame⟩ := memSem_addCell cell memory
  exact ⟨after, run, ram, bits, by rw [accIs, wordField_fieldWord, hacc, hvalue], frame⟩

/-- The solve's fixed registers, as field values. -/
def SolveRegs (memory : Memory) (x y kappaValue : BaseField) : Prop :=
  wordField (memory.registers rA) = x ∧ wordField (memory.registers rB) = y ∧
    wordField (memory.registers rC) = x * x ∧ wordField (memory.registers rF) = kappaValue

theorem SolveRegs.frame {memory after : Memory} {x y kappaValue : BaseField}
    (holds : SolveRegs memory x y kappaValue)
    (same : ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
      after.registers index = memory.registers index) : SolveRegs after x y kappaValue := by
  obtain ⟨a, b, c, f⟩ := holds
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [same _ (by decide) (by decide) (by decide)] <;> assumption

/-- **The `X` row** of a digit and its collector target `y*_0 = (W.x − X) · κ`:
`X = gX + x7 · x + x9 + y10`. -/
theorem run_rowX (digit : Nat) (rest : Prog) (memory : Memory) (x y kappaValue : BaseField)
    (regsHold : SolveRegs memory x y kappaValue)
    (c0 v7 v9 v10 target : BaseField)
    (h0 : wordField (memory.ram (word (Opening.rowCell digit 0))) = c0)
    (h7 : wordField (memory.ram (word (Opening.xCell (4 * digit)))) = v7)
    (h9 : wordField (memory.ram (word (Opening.xCell (4 * digit + 1)))) = v9)
    (h10 : wordField (memory.ram (word (Opening.yCell (3 * digit)))) = v10)
    (hw : wordField (memory.ram (word (openRow digit))) = target) :
    ∃ after, (Prog.seq (loadAt rAcc (Opening.rowCell digit 0))
        (Prog.seq (Opening.addScaled (Opening.xCell (4 * digit)) rA)
        (Prog.seq (Opening.addCell (Opening.xCell (4 * digit + 1)))
        (Prog.seq (Opening.addCell (Opening.yCell (3 * digit)))
        (Prog.seq (Opening.finishTarget (openRow digit) (designatedCell (4 * digit + 1)))
          rest))))).memSem memory = rest.memSem after ∧
      after.ram = Function.update memory.ram (word (designatedCell (4 * digit + 1)))
        (fieldWord ((target - (c0 + v7 * x + v9 + v10)) * kappaValue)) ∧
      after.bits = memory.bits ∧ SolveRegs after x y kappaValue ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  obtain ⟨ra, rb, rc, rf⟩ := regsHold
  rw [memSem_loadAt_seq]
  set m1 := setReg (setReg memory rAddr (word (Opening.rowCell digit 0))) rAcc
    (memory.ram (word (Opening.rowCell digit 0))) with m1Def
  have frame1 : ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
      m1.registers index = memory.registers index := fun index h0' _ h4' => by
    rw [m1Def]; simp only [setReg_registers, if_neg h0', if_neg h4']
  have regs1 : SolveRegs m1 x y kappaValue := SolveRegs.frame ⟨ra, rb, rc, rf⟩ frame1
  have ram1 : m1.ram = memory.ram := by rw [m1Def]; rfl
  obtain ⟨m2, run2, ram2, bits2, acc2, frame2⟩ := step_addScaled _ rA m1 c0 v7 x (by decide)
    (by decide) (by rw [m1Def, reg_same, h0]) (by rw [ram1]; exact h7) regs1.1
  rw [memSem_pure_seq run2]
  have regs2 := regs1.frame frame2
  obtain ⟨m3, run3, ram3, bits3, acc3, frame3⟩ := step_addCell _ m2 _ v9 acc2
    (by rw [ram2, ram1]; exact h9)
  rw [memSem_pure_seq run3]
  have regs3 := regs2.frame frame3
  obtain ⟨m4, run4, ram4, bits4, acc4, frame4⟩ := step_addCell _ m3 _ v10 acc3
    (by rw [ram3, ram2, ram1]; exact h10)
  rw [memSem_pure_seq run4]
  have regs4 := regs3.frame frame4
  obtain ⟨m5, run5, ram5, bits5, frame5⟩ :=
    memSem_finishTarget (openRow digit) (designatedCell (4 * digit + 1)) m4
  rw [memSem_pure_seq run5]
  have ramChain : m4.ram = memory.ram := by rw [ram4, ram3, ram2, ram1]
  refine ⟨m5, rfl, ?_, ?_, regs4.frame fun index _ h5 h4 => frame5 index h5 h4, ?_⟩
  · rw [ram5, acc4, regs4.2.2.2, ramChain, hw]
  · rw [bits5, bits4, bits3, bits2, m1Def]; rfl
  · intro index h0' h5 h4
    rw [frame5 index h5 h4, frame4 index h0' h5 h4, frame3 index h0' h5 h4, frame2 index h0' h5 h4,
      frame1 index h0' h5 h4]

/-- **The `Y` row** of a digit and its collector target `y*_1 = (W.y − Y) · κ · (x · x)⁻¹`: the
collector `rowY_cubic` enters the row with coefficient `x²`. The row reads `y10`, then
`gY · x²`, `cubic · x²` (the running sum without `j*`) and `y8 · y`. -/
theorem run_rowY (digit : Nat) (rest : Prog) (memory : Memory) (x y kappaValue : BaseField)
    (regsHold : SolveRegs memory x y kappaValue)
    (c4 vc v8 v10 target : BaseField)
    (h4 : wordField (memory.ram (word (Opening.rowCell digit 1))) = c4)
    (hc : wordField (memory.ram (word (Opening.xCell (4 * digit + 2)))) = vc)
    (h8 : wordField (memory.ram (word (Opening.yCell (3 * digit + 1)))) = v8)
    (h10 : wordField (memory.ram (word (Opening.yCell (3 * digit + 2)))) = v10)
    (hw : wordField (memory.ram (word (openRow digit + 1))) = target) :
    ∃ after, (Prog.seq (loadAt rAcc (Opening.yCell (3 * digit + 2)))
        (Prog.seq (Opening.addScaled (Opening.rowCell digit 1) rC)
        (Prog.seq (Opening.addScaled (Opening.xCell (4 * digit + 2)) rC)
        (Prog.seq (Opening.addScaled (Opening.yCell (3 * digit + 1)) rB)
        (Prog.seq (Opening.finishScaled (openRow digit + 1) (designatedCell (4 * digit + 2)))
          rest))))).memSem memory = rest.memSem after ∧
      after.ram = Function.update memory.ram (word (designatedCell (4 * digit + 2)))
        (fieldWord ((target - (v10 + c4 * (x * x) + vc * (x * x) + v8 * y)) *
          kappaValue * (x * x)⁻¹)) ∧
      after.bits = memory.bits ∧ SolveRegs after x y kappaValue ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  obtain ⟨ra, rb, rc, rf⟩ := regsHold
  rw [memSem_loadAt_seq]
  set m1 := setReg (setReg memory rAddr (word (Opening.yCell (3 * digit + 2)))) rAcc
    (memory.ram (word (Opening.yCell (3 * digit + 2)))) with m1Def
  have frame1 : ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
      m1.registers index = memory.registers index := fun index h0' _ h4' => by
    rw [m1Def]; simp only [setReg_registers, if_neg h0', if_neg h4']
  have regs1 : SolveRegs m1 x y kappaValue := SolveRegs.frame ⟨ra, rb, rc, rf⟩ frame1
  have ram1 : m1.ram = memory.ram := by rw [m1Def]; rfl
  obtain ⟨m2, run2, ram2, bits2, acc2, frame2⟩ := step_addScaled _ rC m1 v10 c4 (x * x)
    (by decide) (by decide) (by rw [m1Def, reg_same, h10]) (by rw [ram1]; exact h4) regs1.2.2.1
  rw [memSem_pure_seq run2]
  have regs2 := regs1.frame frame2
  obtain ⟨m3, run3, ram3, bits3, acc3, frame3⟩ := step_addScaled _ rC m2 _ vc (x * x) (by decide)
    (by decide) acc2 (by rw [ram2, ram1]; exact hc) regs2.2.2.1
  rw [memSem_pure_seq run3]
  have regs3 := regs2.frame frame3
  obtain ⟨m4, run4, ram4, bits4, acc4, frame4⟩ := step_addScaled _ rB m3 _ v8 y (by decide)
    (by decide) acc3 (by rw [ram3, ram2, ram1]; exact h8) regs3.2.1
  rw [memSem_pure_seq run4]
  have regs4 := regs3.frame frame4
  obtain ⟨m5, run5, ram5, bits5, frame5⟩ :=
    memSem_finishScaled (openRow digit + 1) (designatedCell (4 * digit + 2)) m4
  rw [memSem_pure_seq run5]
  have ramChain : m4.ram = memory.ram := by
    rw [ram4, ram3, ram2, ram1]
  refine ⟨m5, rfl, ?_, ?_, regs4.frame fun index h0' h5' h4' => frame5 index h0' h5' h4', ?_⟩
  · rw [ram5, acc4, regs4.2.2.2, regs4.2.2.1, ramChain, hw]
  · rw [bits5, bits4, bits3, bits2, m1Def]; rfl
  · intro index h0' h5' h4'
    rw [frame5 index h0' h5' h4', frame4 index h0' h5' h4',
      frame3 index h0' h5' h4', frame2 index h0' h5' h4', frame1 index h0' h5' h4']

/-- **The `Z` row** of a digit and its collector target `y*_2 = (W.z − Z) · κ`:
`Z = gZ + x9`. -/
theorem run_rowZ (digit : Nat) (rest : Prog) (memory : Memory) (x y kappaValue : BaseField)
    (regsHold : SolveRegs memory x y kappaValue)
    (c0 v9 target : BaseField)
    (h0 : wordField (memory.ram (word (Opening.rowCell digit 2))) = c0)
    (h9 : wordField (memory.ram (word (Opening.xCell (4 * digit + 3)))) = v9)
    (hw : wordField (memory.ram (word (openRow digit + 2))) = target) :
    ∃ after, (Prog.seq (loadAt rAcc (Opening.rowCell digit 2))
        (Prog.seq (Opening.addCell (Opening.xCell (4 * digit + 3)))
        (Prog.seq (Opening.finishTarget (openRow digit + 2) (designatedCell (4 * digit + 3)))
          rest))).memSem memory = rest.memSem after ∧
      after.ram = Function.update memory.ram (word (designatedCell (4 * digit + 3)))
        (fieldWord ((target - (c0 + v9)) * kappaValue)) ∧
      after.bits = memory.bits ∧ SolveRegs after x y kappaValue ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  obtain ⟨ra, rb, rc, rf⟩ := regsHold
  rw [memSem_loadAt_seq]
  set m1 := setReg (setReg memory rAddr (word (Opening.rowCell digit 2))) rAcc
    (memory.ram (word (Opening.rowCell digit 2))) with m1Def
  have frame1 : ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
      m1.registers index = memory.registers index := fun index h0' _ h4' => by
    rw [m1Def]; simp only [setReg_registers, if_neg h0', if_neg h4']
  have regs1 : SolveRegs m1 x y kappaValue := SolveRegs.frame ⟨ra, rb, rc, rf⟩ frame1
  have ram1 : m1.ram = memory.ram := by rw [m1Def]; rfl
  obtain ⟨m2, run2, ram2, bits2, acc2, frame2⟩ := step_addCell _ m1 c0 v9
    (by rw [m1Def, reg_same, h0]) (by rw [ram1]; exact h9)
  rw [memSem_pure_seq run2]
  have regs2 := regs1.frame frame2
  obtain ⟨m3, run3, ram3, bits3, frame3⟩ :=
    memSem_finishTarget (openRow digit + 2) (designatedCell (4 * digit + 3)) m2
  rw [memSem_pure_seq run3]
  refine ⟨m3, rfl, ?_, ?_, regs2.frame fun index _ h5' h4' => frame3 index h5' h4', ?_⟩
  · rw [ram3, acc2, regs2.2.2.2, ram2, ram1, hw]
  · rw [bits3, bits2, m1Def]; rfl
  · intro index h0' h5' h4'
    rw [frame3 index h5' h4', frame2 index h0' h5' h4', frame1 index h0' h5' h4']

/-- **The solve's prefix**: `x, y, x²` and `κ` into `rA, rB, rC, rF`. -/
theorem run_solvePrefix (rest : Prog) (memory : Memory) (x y kappaValue : BaseField)
    (hx : wordField (memory.ram (word reqX)) = x) (hy : wordField (memory.ram (word reqY)) = y)
    (hk : wordField (memory.ram (word tmpKappa)) = kappaValue) :
    ∃ after, (Prog.seq (loadAt rA reqX) (Prog.seq (loadAt rB reqY)
        (Prog.seq (ar .fieldMul rC rA rA) (Prog.seq (loadAt rF tmpKappa) rest)))).memSem memory =
        rest.memSem after ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧ SolveRegs after x y kappaValue ∧
      ∀ index, index ≠ rAddr → index ≠ rA → index ≠ rB → index ≠ rC →
        index ≠ rF → after.registers index = memory.registers index := by
  rw [memSem_loadAt_seq, memSem_loadAt_seq]
  simp only [setReg_ram]
  rw [memSem_ar_val _ _ _ _ _ _ (memory.ram (word reqX)) (memory.ram (word reqX)) (by regv)
      (by regv), eval_fieldMul, memSem_loadAt_seq]
  simp only [setReg_ram]
  refine ⟨_, rfl, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, fun index n4 n6 n7 n8 n11 => ?_⟩
  · simp only [setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    exact hx
  · simp only [setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    exact hy
  · simp only [setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    rw [wordField_fieldWord, ← hx]; rfl
  · simp only [setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    exact hk
  · simp only [setReg_registers, if_neg n4, if_neg n6, if_neg n7, if_neg n8, if_neg n11]

/-! ### One digit -/

omit [FieldCertificate] in
/-- A row constant by its position in `Opening.rowCell` order (the `Wire` order of `RowGamma`). -/
def gammaConst (gamma : RowGamma) : Nat → BaseField
  | 0 => gamma.gX
  | 1 => gamma.gY
  | _ => gamma.gZ

/-- The three collector targets as words: `κ · (W.c − row.c)` for `X` and `Z`, and
`κ · (W.y − row.y) · (x · x)⁻¹` for the sign row, whose collector `rowY_cubic` has coefficient
`x²`. -/
def solveWords (kappaValue x : BaseField) (target row : FieldMacToECMac.HomogeneousValue) :
    Word × Word × Word :=
  (fieldWord (kappaValue * (target.x - row.x)),
    fieldWord (kappaValue * (target.y - row.y) * (x * x)⁻¹),
    fieldWord (kappaValue * (target.z - row.z)))

omit [FieldCertificate] in
/-- The registers a digit's solve clears. -/
def solveScratch : List Register := [rAcc, rAddr, rSel, rA, rB, rC, rD, rE, rF]

omit [FieldCertificate] in
/-- The three collector cells of digit `d`, written. -/
def putTargets (ram : Word → Word) (digit : Nat) (words : Word × Word × Word) : Word → Word :=
  Function.update (Function.update (Function.update ram (word (collectorCell digit 0)) words.1)
    (word (collectorCell digit 1)) words.2.1) (word (collectorCell digit 2)) words.2.2

theorem putTargets_at (ram : Word → Word) (digit : Nat) (small : digit < 91)
    (words : Word × Word × Word) (collector : Nat) (inside : collector < 3) :
    putTargets ram digit words (word (collectorCell digit collector)) = wordAt words collector := by
  unfold putTargets
  have ne01 : word (collectorCell digit 0) ≠ word (collectorCell digit 1) := by addr_ne
  have ne02 : word (collectorCell digit 0) ≠ word (collectorCell digit 2) := by addr_ne
  have ne12 : word (collectorCell digit 1) ≠ word (collectorCell digit 2) := by addr_ne
  rcases (show collector = 0 ∨ collector = 1 ∨ collector = 2 by omega) with same | same | same <;>
    subst same
  · rw [Function.update_of_ne ne02, Function.update_of_ne ne01, Function.update_self]; rfl
  · rw [Function.update_of_ne ne12, Function.update_self]; rfl
  · rw [Function.update_self]; rfl

omit [FieldCertificate] in
theorem putTargets_off (ram : Word → Word) (digit : Nat) (words : Word × Word × Word)
    (target : Word) (away : ∀ collector, collector < 3 → target ≠ word (collectorCell digit collector)) :
    putTargets ram digit words target = ram target := by
  unfold putTargets
  rw [Function.update_of_ne (away 2 (by omega)), Function.update_of_ne (away 1 (by omega)),
    Function.update_of_ne (away 0 (by omega))]

omit [FieldCertificate] in
theorem sameOff_putTargets (ram : Word → Word) (digit : Nat) (small : digit < 91)
    (words : Word × Word × Word) : SameOff ram (putTargets ram digit words) := by
  unfold putTargets
  refine ((sameOff_update _ ?_ _).trans (sameOff_update _ ?_ _)).trans (sameOff_update _ ?_ _) <;>
    exact openCell_designated _ (by unfold collectorSlot; omega)

/-- **One digit of the solve**: the rows `evaluateGamma` on the replayed values, and the
three collector targets `κ · (W_d.c − row_c)` at `collectorCell d c` (exact). -/
theorem memSem_solveDigit (digit : Nat) (small : digit < 91) (memory : Memory)
    (input : AffineInput) (kappaValue : BaseField) (gamma : RowGamma) (values : Biquadratic.Values)
    (target : FieldMacToECMac.HomogeneousValue)
    (hx : wordField (memory.ram (word reqX)) = input.x)
    (hy : wordField (memory.ram (word reqY)) = input.y)
    (hk : wordField (memory.ram (word tmpKappa)) = kappaValue)
    (hg : ∀ k, k < 3 → wordField (memory.ram (word (Opening.rowCell digit k))) = gammaConst gamma k)
    (hvx : ∀ element : XElement,
      wordField (memory.ram (word (Opening.xCell (4 * digit + element.slot.val)))) =
        values (.inl element))
    (hvy : ∀ element : YElement,
      wordField (memory.ram (word (Opening.yCell (3 * digit + element.slot.val)))) =
        values (.inr element))
    (hw : ∀ position, position < 3 →
      memory.ram (word (openRow digit + position)) = wordAt (rowWords target) position) :
    (Opening.solveDigit digit).memSem memory =
      PMF.pure (some (clearRegs (withRam memory (putTargets memory.ram digit
        (solveWords kappaValue input.x target (FieldMacToECMac.evaluateGamma gamma input values))))
          solveScratch)) := by
  have hwx : wordField (memory.ram (word (openRow digit))) = target.x := by
    have := hw 0 (by omega); rw [Nat.add_zero] at this; rw [this]; exact wordField_fieldWord _
  have hwy : wordField (memory.ram (word (openRow digit + 1))) = target.y := by
    rw [hw 1 (by omega)]; exact wordField_fieldWord _
  have hwz : wordField (memory.ram (word (openRow digit + 2))) = target.z := by
    rw [hw 2 (by omega)]; exact wordField_fieldWord _
  unfold Opening.solveDigit
  simp only [Prog.seqList]
  obtain ⟨pre, runPre, ramPre, bitsPre, regsPre, framePre⟩ :=
    run_solvePrefix _ memory input.x input.y kappaValue hx hy hk
  rw [runPre]
  obtain ⟨rowX, runX, ramX, bitsX, regsX, frameX⟩ := run_rowX digit _ pre input.x input.y kappaValue
    regsPre (gammaConst gamma 0)
    (values (.inl .rowX_x7)) (values (.inl .rowX_x9)) (values (.inr .rowX_y10)) target.x
    (by rw [ramPre]; exact hg 0 (by omega))
    (by rw [ramPre]; exact hvx .rowX_x7) (by rw [ramPre]; exact hvx .rowX_x9)
    (by rw [ramPre]; exact hvy .rowX_y10) (by rw [ramPre]; exact hwx)
  rw [runX]
  have readX : ∀ address, address < 2 ^ 256 → address ≠ designatedCell (4 * digit + 1) →
      rowX.ram (word address) = memory.ram (word address) := by
    intro address bound different
    rw [ramX, Function.update_of_ne (word_ne bound (by addr_arith) different),
      ramPre]
  obtain ⟨rowY, runY, ramY, bitsY, regsY, frameY⟩ := run_rowY digit _ rowX input.x input.y
    kappaValue regsX (gammaConst gamma 1) (values (.inl .rowY_cubic)) (values (.inr .rowY_y8))
    (values (.inr .rowY_y10)) target.y
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hg 1 (by omega))
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hvx .rowY_cubic)
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hvy .rowY_y8)
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hvy .rowY_y10)
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hwy)
  rw [runY]
  have readY : ∀ address, address < 2 ^ 256 → address ≠ designatedCell (4 * digit + 1) →
      address ≠ designatedCell (4 * digit + 2) → rowY.ram (word address) = memory.ram (word address) := by
    intro address bound different0 different1
    rw [ramY, Function.update_of_ne (word_ne bound (by addr_arith) different1),
      readX address bound different0]
  obtain ⟨rowZ, runZ, ramZ, bitsZ, _, frameZ⟩ := run_rowZ digit _ rowY input.x input.y
    kappaValue regsY (gammaConst gamma 2) (values (.inl .rowZ_x9)) target.z
    (by rw [readY _ (by addr_arith) (by addr_arith) (by addr_arith)]; exact hg 2 (by omega))
    (by rw [readY _ (by addr_arith) (by addr_arith) (by addr_arith)]; exact hvx .rowZ_x9)
    (by rw [readY _ (by addr_arith) (by addr_arith) (by addr_arith)]; exact hwz)
  rw [runZ, memSem_zeroRegs_seq, memSem_skip]
  refine congrArg (fun final => PMF.pure (some final)) ?_
  apply clearRegs_withRam_eq
  · rw [ramZ, ramY, ramX, ramPre]
    unfold putTargets solveWords
    rw [show collectorCell digit 0 = designatedCell (4 * digit + 1) from rfl,
      show collectorCell digit 1 = designatedCell (4 * digit + 2) from rfl,
      show collectorCell digit 2 = designatedCell (4 * digit + 3) from rfl]
    have eX : (target.x - (gammaConst gamma 0 + values (.inl .rowX_x7) * input.x +
        values (.inl .rowX_x9) + values (.inr .rowX_y10))) * kappaValue =
        kappaValue * (target.x - (FieldMacToECMac.evaluateGamma gamma input values).x) := by
      simp only [FieldMacToECMac.evaluateGamma, Biquadratic.evaluateX, gammaConst]
      ring
    have eY : (target.y - (values (.inr .rowY_y10) + gammaConst gamma 1 * (input.x * input.x) +
        values (.inl .rowY_cubic) * (input.x * input.x) + values (.inr .rowY_y8) * input.y)) *
          kappaValue * (input.x * input.x)⁻¹ =
        kappaValue * (target.y - (FieldMacToECMac.evaluateGamma gamma input values).y) *
          (input.x * input.x)⁻¹ := by
      simp only [FieldMacToECMac.evaluateGamma, Biquadratic.evaluateY, gammaConst]
      ring
    have eZ : (target.z - (gammaConst gamma 2 + values (.inl .rowZ_x9))) * kappaValue =
        kappaValue * (target.z - (FieldMacToECMac.evaluateGamma gamma input values).z) := by
      simp only [FieldMacToECMac.evaluateGamma, Biquadratic.evaluateZ, gammaConst]
      ring
    rw [eX, eY, eZ]
  · rw [bitsZ, bitsY, bitsX, bitsPre]
  · intro index outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨n0, n4, n5, n6, n7, n8, n9, n10, n11⟩ := outside
    rw [frameZ index n0 n5 n4, frameY index n0 n5 n4, frameX index n0 n5 n4,
      framePre index n4 n6 n7 n8 n11]

/-! ### All digits -/

/-- **The solve**: the `273` collector targets `κ · (W_d.c − row_{d,c}) · s_c` (`solveWords`) at
`collectorCell d c`, nothing else changed off the opening's cells. -/
theorem memSem_solve (memory : Memory) (input : AffineInput) (kappaValue : BaseField)
    (gammas : Fin 91 → RowGamma) (values : Fin 91 → Biquadratic.Values)
    (targets : Fin 91 → FieldMacToECMac.HomogeneousValue)
    (hx : wordField (memory.ram (word reqX)) = input.x)
    (hy : wordField (memory.ram (word reqY)) = input.y)
    (hk : wordField (memory.ram (word tmpKappa)) = kappaValue)
    (hg : ∀ (digit : Fin 91) k, k < 3 →
      wordField (memory.ram (word (Opening.rowCell digit k))) = gammaConst (gammas digit) k)
    (hvx : ∀ (digit : Fin 91) (element : XElement),
      wordField (memory.ram (word (Opening.xCell (4 * digit.val + element.slot.val)))) =
        values digit (.inl element))
    (hvy : ∀ (digit : Fin 91) (element : YElement),
      wordField (memory.ram (word (Opening.yCell (3 * digit.val + element.slot.val)))) =
        values digit (.inr element))
    (hw : ∀ (digit : Fin 91) position, position < 3 →
      memory.ram (word (openRow digit + position)) = wordAt (rowWords (targets digit)) position) :
    ∀ count, count ≤ 91 → ∃ after,
      (Prog.rep count Opening.solveDigit).memSem memory = PMF.pure (some after) ∧
      after.bits = memory.bits ∧ SameOff memory.ram after.ram ∧
      (∀ digit : Fin 91, digit.val < count → ∀ position, position < 3 →
        after.ram (word (collectorCell digit position)) =
          wordAt (solveWords kappaValue input.x (targets digit)
            (FieldMacToECMac.evaluateGamma (gammas digit) input (values digit))) position) ∧
      (∀ target, (∀ digit, digit < count → ∀ position, position < 3 →
        target ≠ word (collectorCell digit position)) → after.ram target = memory.ram target)
  | 0, _ => ⟨memory, by rw [Prog.rep]; rfl, rfl, SameOff.refl _,
      fun _ bound => absurd bound (by omega), fun _ _ => rfl⟩
  | count + 1, bound => by
      obtain ⟨previous, runPrevious, bitsPrevious, samePrevious, targetsPrevious, offPrevious⟩ :=
        memSem_solve memory input kappaValue gammas values targets hx hy hk hg hvx hvy hw count
          (by omega)
      have read : ∀ address, address < 2 ^ 256 →
          (∀ digit, digit < count → ∀ position, position < 3 →
            address ≠ collectorCell digit position) →
          previous.ram (word address) = memory.ram (word address) := fun address small away =>
        offPrevious _ fun digit below position inside =>
          word_ne small (by addr_arith) (away digit below position inside)
      set here : Fin 91 := ⟨count, by omega⟩ with hereDef
      have run := memSem_solveDigit count (by omega) previous input kappaValue (gammas here)
        (values here) (targets here)
        (by rw [read _ (by addr_arith) (fun digit below position inside => by addr_arith)]; exact hx)
        (by rw [read _ (by addr_arith) (fun digit below position inside => by addr_arith)]; exact hy)
        (by rw [read _ (by addr_arith) (fun digit below position inside => by addr_arith)]; exact hk)
        (fun k inside => by
          rw [read _ (by addr_arith) (fun digit below position inside' => by addr_arith)]
          exact hg here k inside)
        (fun element => by
          have slot : element.slot.val < 4 := element.slot.isLt
          rw [read _ (by addr_arith) (fun digit below position inside' => by addr_arith)]
          exact hvx here element)
        (fun element => by
          have slot : element.slot.val < 3 := element.slot.isLt
          rw [read _ (by addr_arith) (fun digit below position inside' => by addr_arith)]
          exact hvy here element)
        (fun position inside => by
          rw [read _ (by addr_arith) (fun digit below position' inside' => by addr_arith)]
          exact hw here position inside)
      set written := putTargets previous.ram count (solveWords kappaValue input.x (targets here)
        (FieldMacToECMac.evaluateGamma (gammas here) input (values here))) with writtenDef
      have ramNext : (clearRegs (withRam previous written) solveScratch).ram = written := by
        rw [(clearRegs_other _ _).1]; rfl
      refine ⟨clearRegs (withRam previous written) solveScratch, ?_, ?_, ?_, ?_, ?_⟩
      · rw [memSem_rep_succ, runPrevious, PMF.pure_bind]
        exact run
      · rw [(clearRegs_other _ _).2, withRam_bits, bitsPrevious]
      · rw [ramNext, writtenDef]
        exact samePrevious.trans (sameOff_putTargets previous.ram count (by omega) _)
      · intro digit below position inside
        rw [ramNext, writtenDef]
        by_cases same : digit.val = count
        · have digitIs : digit = here := Fin.ext same
          subst digitIs
          exact putTargets_at _ _ (by omega) _ _ inside
        · rw [putTargets_off _ _ _ _ (fun position' inside' => word_ne (by addr_arith)
              (by addr_arith) (by addr_arith)), targetsPrevious digit (by omega) position inside]
      · intro target away
        rw [ramNext, writtenDef,
          putTargets_off _ _ _ _ (fun position inside => away count (by omega) position inside),
          offPrevious target (fun digit below position inside => away digit (by omega) position inside)]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
