/-
**The opening, step 2: Horner and the head clamp** (`Opening.horner`).

The machine computes `H = pointHorner β (D_1 … D_90)` by `P ← D_d + β · P` from `d = 90` down,
with `β · P` a double-and-add over the `192` bits of `betaNat = radix.val` (kept symbolic), and
then the head `D_0 = Q − β · H`, aborting when `β · H = O`. This is exactly P3's head
`digitPoints target tail 0 = target − radix • pointHorner radix (freeOffsetPoints tail)`, and the
abort is exactly `tailLaw`'s clamp check `clampedFirst tail = 0` (`memSem_horner`).

* `readWords`, `pointWords`: a point register's three words; `readWords (pointWords p) = some p`;
* `memSem_betaMul`: `P ← betaNat • P` (and `Q ←` the old `P`);
* `memSem_hornerSteps`: the Horner loop against `pointHorner radix`.
-/

import Proof.Simulator.OpeningTail

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Point words -/

/-- A point register's three words, decoded as `readPoint` decodes them. -/
def readWords (words : Word × Word × Word) : Option Point :=
  if words.1 = 0 then some 0
  else if words.1 = 1 ∧ words.2.1.toNat < baseFieldModulus ∧ words.2.2.toNat < baseFieldModulus then
    decodePoint ⟨words.2.1.toNat, words.2.2.toNat⟩
  else none

theorem readPoint_eq (registers : Register → Word) (source : PointRegisters) :
    readPoint registers source =
      readWords (registers source.tag, registers source.x, registers source.y) := rfl

omit [FieldCertificate] in
theorem field_val_lt (value : BaseField) : (BitVec.ofNat 256 value.val).toNat = value.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans value.val_lt (by unfold baseFieldModulus; norm_num))]

/-- **A point's words decode to the point.** -/
theorem readWords_pointWords (point : Point) : readWords (pointWords point) = some point := by
  cases point with
  | zero => rfl
  | some x y valid =>
      unfold readWords pointWords
      have one : (1 : Word) ≠ 0 := by decide
      simp only [one, if_false, field_val_lt, ZMod.val_lt, and_self, if_true,
        ZMod.natCast_zmod_val]
      have onCurve : OnCurve ⟨x, y⟩ := (equation_iff_onCurve ⟨x, y⟩).mp valid.1
      unfold decodePoint
      rw [dif_pos ((validate_eq_true_iff _).mpr onCurve)]

theorem pointWords_tag_eq_zero (point : Point) : (pointWords point).1 = 0 ↔ point = 0 := by
  cases point with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some x y valid =>
      have one : (pointWords (.some x y valid)).1 = 1 := rfl
      rw [one]
      exact ⟨fun zero => absurd zero (by decide), fun zero => absurd zero (by simp)⟩

/-- The words an offset is stored as are its point's words. -/
theorem offsetWords_eq (offset : FieldMacToECMac.AffineOffset) :
    offsetWords offset = pointWords offset.point := by
  have valid : validate offset.coordinates = true := (validate_eq_true_iff _).mpr offset.onCurve
  obtain ⟨proof, decoded⟩ : ∃ proof, decodePoint offset.coordinates =
      some (.some offset.coordinates.x offset.coordinates.y proof) :=
    ⟨_, by unfold decodePoint; rw [dif_pos valid]⟩
  have point : offset.point = .some offset.coordinates.x offset.coordinates.y proof :=
    Option.get_of_mem _ decoded
  rw [point]
  rfl

/-- Registers holding a point's words. -/
def HoldsPoint (memory : Memory) (target : PointRegisters) (point : Point) : Prop :=
  (memory.registers target.tag, memory.registers target.x, memory.registers target.y) =
    pointWords point

/-- **A point addition on decoded registers.** -/
theorem memSem_pointAdd_seq (target left right : PointRegisters) (rest : Prog) (memory : Memory)
    (first second : Point) (hfirst : readPoint memory.registers left = some first)
    (hsecond : readPoint memory.registers right = some second) :
    (Prog.seq (.op (.pointAdd target left right)) rest).memSem memory =
      rest.memSem (writePointMem memory target (first + second)) := by
  apply memSem_pure_seq
  show (match readPoint memory.registers left, readPoint memory.registers right with
    | some a, some b => PMF.pure (some (writePointMem memory target (a + b)))
    | _, _ => PMF.pure none) = _
  rw [hfirst, hsecond]

theorem writePoint_eq (registers : Register → Word) (target : PointRegisters) (point : Point) :
    writePoint registers target point =
      Function.update (Function.update (Function.update registers target.tag (pointWords point).1)
        target.x (pointWords point).2.1) target.y (pointWords point).2.2 := by
  cases point <;> rfl

theorem memSem_pointAdd (target left right : PointRegisters) (memory : Memory)
    (first second : Point) (hfirst : readPoint memory.registers left = some first)
    (hsecond : readPoint memory.registers right = some second) :
    (Prog.op (.pointAdd target left right)).memSem memory =
      PMF.pure (some (writePointMem memory target (first + second))) := by
  show (match readPoint memory.registers left, readPoint memory.registers right with
    | some a, some b => PMF.pure (some (writePointMem memory target (a + b)))
    | _, _ => PMF.pure none) = _
  rw [hfirst, hsecond]

/-- The point registers `P` (`R6 … R8`). -/
theorem holds_writeP (memory : Memory) (point : Point) :
    HoldsPoint (writePointMem memory pointP point) pointP point := by
  unfold HoldsPoint writePointMem
  simp only [writePoint_eq, Function.update_apply]
  simp (config := { decide := true }) only [if_true, if_false]

theorem writeP_other (memory : Memory) (point : Point) (index : Register)
    (outside : index ∉ [6, 7, 8]) :
    (writePointMem memory pointP point).registers index = memory.registers index := by
  unfold writePointMem
  simp only [writePoint_eq, Function.update_apply]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  obtain ⟨n6, n7, n8⟩ := outside
  simp only [n6, n7, n8, if_false]

theorem writeP_ram (memory : Memory) (point : Point) :
    (writePointMem memory pointP point).ram = memory.ram := rfl

theorem writeP_bits (memory : Memory) (point : Point) :
    (writePointMem memory pointP point).bits = memory.bits := rfl

theorem read_of_holds {memory : Memory} {target : PointRegisters} {point : Point}
    (holds : HoldsPoint memory target point) : readPoint memory.registers target = some point := by
  rw [readPoint_eq, show (memory.registers target.tag, memory.registers target.x,
    memory.registers target.y) = pointWords point from holds, readWords_pointWords]

/-! ### `P ← betaNat • P` -/

omit [FieldCertificate] in
theorem betaNat_lt : betaNat < 2 ^ 192 := by decide

omit [FieldCertificate] in
theorem beta_step (rounds : Nat) (small : rounds < 192) :
    betaNat / 2 ^ (192 - (rounds + 1)) =
      2 * (betaNat / 2 ^ (192 - rounds)) + (if betaNat.testBit (191 - rounds) then 1 else 0) := by
  have shape : 192 - rounds = (192 - (rounds + 1)) + 1 := by omega
  have index : 191 - rounds = 192 - (rounds + 1) := by omega
  rw [shape, index, pow_succ, ← Nat.div_div_eq_div_mul, Nat.testBit_eq_decide_div_mod_eq]
  generalize betaNat / 2 ^ (192 - (rounds + 1)) = value
  have := Nat.div_add_mod value 2
  rcases Nat.mod_two_eq_zero_or_one value with zero | one
  · rw [zero]; simp; omega
  · rw [one]; simp; omega

theorem writeP_writeP (memory : Memory) (first second : Point) :
    writePointMem (writePointMem memory pointP first) pointP second =
      writePointMem memory pointP second := by
  unfold writePointMem
  congr 1
  funext index
  simp only [writePoint_eq, Function.update_apply]
  split_ifs <;> rfl

/-- The double-and-add rounds, the top `rounds` bits of `betaNat`. -/
theorem memSem_betaRounds (base : Memory) (point : Point)
    (hQ : readPoint base.registers pointQ = some point) :
    ∀ rounds, rounds ≤ 192 →
      (Prog.rep rounds fun round => Opening.betaRound (191 - round)).memSem
          (writePointMem base pointP 0) =
        PMF.pure (some (writePointMem base pointP ((betaNat / 2 ^ (192 - rounds)) • point)))
  | 0, _ => by
      rw [Prog.rep, Nat.sub_zero, Nat.div_eq_of_lt betaNat_lt, zero_nsmul]
      rfl
  | rounds + 1, bound => by
      rw [memSem_rep_succ, memSem_betaRounds base point hQ rounds (by omega), PMF.pure_bind]
      show (Opening.betaRound (191 - rounds)).memSem _ = _
      set current := (betaNat / 2 ^ (192 - rounds)) • point with currentDef
      unfold Opening.betaRound
      rw [memSem_pointAdd_seq _ _ _ _ _ current current (read_of_holds (holds_writeP _ _))
        (read_of_holds (holds_writeP _ _)), writeP_writeP, beta_step rounds (by omega)]
      have hQ' : readPoint (writePointMem base pointP (current + current)).registers pointQ =
          some point := by
        rw [readPoint_eq, writeP_other _ _ _ (by decide), writeP_other _ _ _ (by decide),
          writeP_other _ _ _ (by decide), ← readPoint_eq, hQ]
      split
      · rw [memSem_pointAdd _ _ _ _ (current + current) point
          (read_of_holds (holds_writeP _ _)) hQ', writeP_writeP, add_nsmul, two_mul,
          add_nsmul, one_nsmul]
      · rw [memSem_skip, add_zero, two_mul, add_nsmul]

/-- **`P ← betaNat • P`**, with `Q ← P`; only the point registers change. -/
theorem memSem_betaMul (memory : Memory) (point : Point)
    (hP : readPoint memory.registers pointP = some point) :
    ∃ after, Opening.betaMul.memSem memory = PMF.pure (some after) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      HoldsPoint after pointP (betaNat • point) ∧
      readPoint after.registers pointQ = some point ∧
      ∀ index, index ∉ [6, 7, 8, 9, 10, 11] → after.registers index = memory.registers index := by
  unfold Opening.betaMul Opening.copyPoint Opening.clearP
  simp only [Prog.seqList]
  rw [memSem_pure_seq (first := Prog.seq (ar .and pointQ.tag pointP.tag pointP.tag)
      (Prog.seq (ar .and pointQ.x pointP.x pointP.x) (Prog.seq (ar .and pointQ.y pointP.y pointP.y)
        (.skip 0)))) (after := setReg (setReg (setReg memory 9 (memory.registers 6))
          10 (memory.registers 7)) 11 (memory.registers 8)) (by
      rw [memSem_ar_val _ _ _ _ _ _ (memory.registers 6) (memory.registers 6) rfl rfl,
        memSem_ar_val _ _ _ _ _ _ (memory.registers 7) (memory.registers 7)
          (by rw [reg_ne _ _ _ _ (by decide)]) (by rw [reg_ne _ _ _ _ (by decide)]),
        memSem_ar_val _ _ _ _ _ _ (memory.registers 8) (memory.registers 8)
          (by rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide)])
          (by rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide)]),
        memSem_skip]
      simp only [Arithmetic.eval, BitVec.and_self])]
  set copied := setReg (setReg (setReg memory 9 (memory.registers 6)) 10 (memory.registers 7)) 11
    (memory.registers 8) with copiedDef
  have cleared : setReg (setReg (setReg copied 6 (word 0)) 7 (word 0)) 8 (word 0) =
      writePointMem copied pointP 0 := by
    unfold writePointMem setReg
    rw [writePoint_eq]
    rfl
  rw [memSem_pure_seq (first := Prog.seq (cst 6 0) (Prog.seq (cst 7 0) (Prog.seq (cst 8 0)
      (.skip 0)))) (by rw [memSem_cst_seq, memSem_cst_seq, memSem_cst_seq, memSem_skip, cleared])]
  have hQ : readPoint copied.registers pointQ = some point := by
    rw [readPoint_eq, copiedDef]
    simp only [reg_same, reg_ne _ _ _ _ (show (10 : Register) ≠ 11 by decide),
      reg_ne _ _ _ _ (show (9 : Register) ≠ 11 by decide),
      reg_ne _ _ _ _ (show (9 : Register) ≠ 10 by decide)]
    exact hP
  rw [memSem_pure_seq (memSem_betaRounds copied point hQ 192 le_rfl), memSem_skip, Nat.sub_self,
    pow_zero, Nat.div_one]
  refine ⟨_, rfl, rfl, rfl, holds_writeP _ _, ?_, fun index outside => ?_⟩
  · rw [readPoint_eq, writeP_other _ _ _ (by decide), writeP_other _ _ _ (by decide),
      writeP_other _ _ _ (by decide), ← readPoint_eq, hQ]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨n6, n7, n8, n9, n10, n11⟩ := outside
    rw [writeP_other _ _ _ (by simp [n6, n7, n8]), copiedDef, reg_ne _ _ _ _ n11,
      reg_ne _ _ _ _ n10, reg_ne _ _ _ _ n9]

/-! ### One Horner step -/

theorem memSem_loadPoint (address : Nat) (memory : Memory) :
    ∃ after, (Opening.loadPoint pointQ address).memSem memory = PMF.pure (some after) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      readPoint after.registers pointQ = readWords (memory.ram (word address),
        memory.ram (word (address + 1)), memory.ram (word (address + 2))) ∧
      ∀ index, index ∉ [4, 9, 10, 11] → after.registers index = memory.registers index := by
  unfold Opening.loadPoint
  simp only [Prog.seqList]
  rw [memSem_loadAt_seq, memSem_loadAt_seq, memSem_loadAt_seq, memSem_skip]
  refine ⟨_, rfl, rfl, rfl, ?_, fun index outside => ?_⟩
  · rw [readPoint_eq]
    simp only [setReg_ram]
    rw [reg_ne _ _ _ _ (show (9 : Register) ≠ 11 by decide), reg_ne _ _ _ _ (by decide),
      reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), reg_same,
      reg_ne _ _ _ _ (show (10 : Register) ≠ 11 by decide), reg_ne _ _ _ _ (by decide), reg_same,
      reg_same]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨n4, n9, n10, n11⟩ := outside
    simp only [setReg_registers, n4, n9, n10, n11, if_false]

/-- **One Horner step** `P ← D + β · P`, `D` read from its cell. -/
theorem memSem_hornerStep (digit : Nat) (memory : Memory) (current point : Point)
    (hP : readPoint memory.registers pointP = some current)
    (cell : readWords (memory.ram (word (openPoint digit)), memory.ram (word (openPoint digit + 1)),
      memory.ram (word (openPoint digit + 2))) = some point) :
    ∃ after, (Opening.hornerStep digit).memSem memory = PMF.pure (some after) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      HoldsPoint after pointP (point + betaNat • current) ∧
      ∀ index, index ∉ [4, 6, 7, 8, 9, 10, 11] → after.registers index = memory.registers index := by
  obtain ⟨multiplied, runMul, ramMul, bitsMul, holdsMul, _, regsMul⟩ :=
    memSem_betaMul memory current hP
  obtain ⟨loaded, runLoad, ramLoad, bitsLoad, readLoad, regsLoad⟩ :=
    memSem_loadPoint (openPoint digit) multiplied
  unfold Opening.hornerStep
  simp only [Prog.seqList]
  rw [memSem_pure_seq runMul, memSem_pure_seq runLoad]
  have readP : readPoint loaded.registers pointP = some (betaNat • current) := by
    rw [readPoint_eq, regsLoad _ (by decide), regsLoad _ (by decide), regsLoad _ (by decide),
      ← readPoint_eq]
    exact read_of_holds holdsMul
  have readQ : readPoint loaded.registers pointQ = some point := by
    rw [readLoad, ramMul, cell]
  rw [memSem_pointAdd_seq _ _ _ _ _ point (betaNat • current) readQ readP, memSem_skip]
  refine ⟨_, rfl, by rw [writeP_ram, ramLoad, ramMul], by rw [writeP_bits, bitsLoad, bitsMul],
    holds_writeP _ _, fun index outside => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  obtain ⟨n4, n6, n7, n8, n9, n10, n11⟩ := outside
  rw [writeP_other _ _ _ (by simp [n6, n7, n8]), regsLoad _ (by simp [n4, n9, n10, n11]),
    regsMul _ (by simp [n6, n7, n8, n9, n10, n11])]

/-! ### The Horner loop -/

variable [GroupCertificate]

omit [FieldCertificate] in
theorem radix_val : radix.val = betaNat := by rfl

theorem radix_smul (point : Point) : radix • point = betaNat • point := by
  rw [show radix • point = radix.val • point from rfl, radix_val]

theorem pointHorner_cons (head : Point) (rest : List Point) :
    pointHorner radix (head :: rest) = head + betaNat • pointHorner radix rest := by
  rw [pointHorner, radix_smul]

/-- **The Horner loop**, digits `90, 89, …` down: the Horner value of the last `steps` points. -/
theorem memSem_hornerSteps (memory : Memory) (points : Fin 90 → Point)
    (cells : ∀ index : Fin 90, readWords (memory.ram (word (openPoint (index.val + 1))),
      memory.ram (word (openPoint (index.val + 1) + 1)),
      memory.ram (word (openPoint (index.val + 1) + 2))) = some (points index))
    (start : readPoint memory.registers pointP = some 0) :
    ∀ steps, steps ≤ 90 → ∃ after,
      (Prog.rep steps fun index => Opening.hornerStep (90 - index)).memSem memory =
        PMF.pure (some after) ∧ after.ram = memory.ram ∧ after.bits = memory.bits ∧
      readPoint after.registers pointP =
        some (pointHorner radix ((List.ofFn points).drop (90 - steps))) ∧
      ∀ index, index ∉ [4, 6, 7, 8, 9, 10, 11] → after.registers index = memory.registers index
  | 0, _ => by
      refine ⟨memory, by rw [Prog.rep]; rfl, rfl, rfl, ?_, fun _ _ => rfl⟩
      rw [start, Nat.sub_zero, List.drop_of_length_le (by simp)]
      rfl
  | steps + 1, bound => by
      obtain ⟨previous, runPrevious, ramPrevious, bitsPrevious, readPrevious, regsPrevious⟩ :=
        memSem_hornerSteps memory points cells start steps (by omega)
      have digitIs : openPoint (90 - steps) = openPoint ((⟨89 - steps, by omega⟩ : Fin 90).val + 1) := by
        show openPoint (90 - steps) = openPoint (89 - steps + 1)
        congr 1
        omega
      obtain ⟨next, runNext, ramNext, bitsNext, holdsNext, regsNext⟩ :=
        memSem_hornerStep (90 - steps) previous _ (points ⟨89 - steps, by omega⟩) readPrevious
          (by rw [ramPrevious, digitIs]; exact cells _)
      refine ⟨next, ?_, by rw [ramNext, ramPrevious], by rw [bitsNext, bitsPrevious], ?_,
        fun index outside => by rw [regsNext index outside, regsPrevious index outside]⟩
      · rw [memSem_rep_succ, runPrevious, PMF.pure_bind]
        exact runNext
      · rw [read_of_holds holdsNext, show 90 - (steps + 1) = 89 - steps by omega,
          List.drop_eq_getElem_cons (i := 89 - steps) (l := List.ofFn points)
            (by rw [List.length_ofFn]; omega), show 89 - steps + 1 = 90 - steps by omega,
          pointHorner_cons, List.getElem_ofFn]

/-! ### The head clamp -/

omit [GroupCertificate] in
theorem negY_curve (x y : BaseField) : curve.toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, curve]

omit [GroupCertificate] in
/-- The words of a finite point with its `y` negated decode to its negative. -/
theorem readWords_neg (x y : BaseField) (valid : curve.toAffine.Nonsingular x y) :
    readWords ((1 : Word), fieldWord x, fieldWord (-y)) =
      some (-(WeierstrassCurve.Affine.Point.some x y valid)) := by
  have onCurve : OnCurve ⟨x, -y⟩ := by
    have base := (equation_iff_onCurve ⟨x, y⟩).mp valid.1
    unfold OnCurve at base ⊢
    rw [neg_sq]
    exact base
  rw [WeierstrassCurve.Affine.Point.neg_some]
  unfold readWords
  have one : (1 : Word) ≠ 0 := by decide
  simp only [one, if_false, fieldWord_toNat, ZMod.val_lt, and_self, if_true, ZMod.natCast_zmod_val]
  unfold decodePoint
  rw [dif_pos ((validate_eq_true_iff _).mpr onCurve)]
  simp only [negY_curve]

omit [FieldCertificate] [GroupCertificate] in
/-- The registers the head clears. -/
def headScratch : List Register := [0, 4, 6, 7, 8, 9, 10, 11]

omit [GroupCertificate] in
/-- **The head clamp** `D_0 = Q − β · H`, `H` in `P`: abort when `β · H = O`. -/
theorem memSem_head (memory : Memory) (hash target : Point)
    (hP : readPoint memory.registers pointP = some hash)
    (request : readWords (memory.ram (word reqTag0), memory.ram (word reqQX),
      memory.ram (word reqQY)) = some target) :
    Opening.head.memSem memory =
      if betaNat • hash = 0 then PMF.pure none
      else PMF.pure (some (clearRegs (withRam memory (putPoint memory.ram (openPoint 0)
        (pointWords (target - betaNat • hash)))) headScratch)) := by
  obtain ⟨multiplied, runMul, ramMul, bitsMul, holdsMul, _, regsMul⟩ :=
    memSem_betaMul memory hash hP
  unfold Opening.head
  simp only [Prog.seqList]
  rw [memSem_pure_seq runMul]
  have tagIs : multiplied.registers 6 = (pointWords (betaNat • hash)).1 :=
    congrArg (fun words => words.1) holdsMul
  have branch : (Prog.ite 6 (Prog.seq (cst rAcc 0) (Prog.seq (ar .fieldSub 8 rAcc 8)
      (Prog.seq (loadAt 9 reqTag0) (Prog.seq (loadAt 10 reqQX) (Prog.seq (loadAt 11 reqQY)
      (Prog.seq (.op (.pointAdd pointP pointQ pointP)) (Prog.seq (Opening.storePoint (openPoint 0) pointP)
      (Prog.seq (zeroRegs [0, 4, 6, 7, 8, 9, 10, 11]) (.skip 0))))))))) (.abort rSel)).memSem
        multiplied = if multiplied.registers 6 = 0 then PMF.pure none else
        (Prog.seq (cst rAcc 0) (Prog.seq (ar .fieldSub 8 rAcc 8)
      (Prog.seq (loadAt 9 reqTag0) (Prog.seq (loadAt 10 reqQX) (Prog.seq (loadAt 11 reqQY)
      (Prog.seq (.op (.pointAdd pointP pointQ pointP)) (Prog.seq (Opening.storePoint (openPoint 0) pointP)
      (Prog.seq (zeroRegs [0, 4, 6, 7, 8, 9, 10, 11]) (.skip 0))))))))).memSem multiplied := rfl
  rw [memSem_seq, branch, tagIs]
  by_cases zero : betaNat • hash = 0
  · rw [if_pos ((pointWords_tag_eq_zero _).mpr zero), if_pos zero, PMF.pure_bind]
    rfl
  rw [if_neg (fun tag => zero ((pointWords_tag_eq_zero _).mp tag)), if_neg zero]
  obtain ⟨x, y, valid, point⟩ : ∃ x y valid,
      betaNat • hash = WeierstrassCurve.Affine.Point.some x y valid := by
    cases h : betaNat • hash with
    | zero => exact absurd h zero
    | some x y valid => exact ⟨x, y, valid, rfl⟩
  have words : (multiplied.registers 6, multiplied.registers 7, multiplied.registers 8) =
      ((1 : Word), fieldWord x, fieldWord y) := by
    rw [show (multiplied.registers 6, multiplied.registers 7, multiplied.registers 8) =
      pointWords (betaNat • hash) from holdsMul, point]
    rfl
  simp only [Prod.mk.injEq] at words
  obtain ⟨tag6, x7, y8⟩ := words
  rw [memSem_cst_seq,
    memSem_ar_val _ _ _ _ _ _ (word 0) (fieldWord y) (reg_same _ _ _)
      (by rw [reg_ne _ _ _ _ (by decide), y8]), fieldSub_zero,
    memSem_loadAt_seq, memSem_loadAt_seq, memSem_loadAt_seq]
  simp only [setReg_ram]
  set loaded := setReg (setReg (setReg (setReg (setReg (setReg (setReg (setReg multiplied rAcc
    (word 0)) 8 (fieldWord (-y))) rAddr (word reqTag0)) 9 (multiplied.ram (word reqTag0))) rAddr
    (word reqQX)) 10 (multiplied.ram (word reqQX))) rAddr (word reqQY)) 11
    (multiplied.ram (word reqQY)) with loadedDef
  have readQ : readPoint loaded.registers pointQ = some target := by
    rw [readPoint_eq, loadedDef]
    simp only [setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    rw [ramMul, request]
  have readP : readPoint loaded.registers pointP = some (-(betaNat • hash)) := by
    rw [readPoint_eq, loadedDef]
    simp only [setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    rw [tag6, x7, point, readWords_neg]
  rw [memSem_pointAdd_seq _ _ _ _ _ target (-(betaNat • hash)) readQ readP]
  set added := writePointMem loaded pointP (target + -(betaNat • hash)) with addedDef
  have holds : HoldsPoint added pointP (target + -(betaNat • hash)) := holds_writeP _ _
  unfold Opening.storePoint
  simp only [Prog.seqList]
  rw [memSem_seq, memSem_storeAt_seq _ _ _ _ (by decide), memSem_storeAt_seq _ _ _ _ (by decide),
    memSem_storeAt_seq _ _ _ _ (by decide), memSem_skip, PMF.pure_bind]
  simp only [kleisli]
  rw [memSem_zeroRegs_seq, memSem_skip, PMF.pure_bind]
  simp only [kleisli]
  rw [memSem_skip]
  have h6 : added.registers 6 = (pointWords (target - betaNat • hash)).1 := by
    rw [sub_eq_add_neg]; exact congrArg (fun words => words.1) holds
  have h7 : added.registers 7 = (pointWords (target - betaNat • hash)).2.1 := by
    rw [sub_eq_add_neg]; exact congrArg (fun words => words.2.1) holds
  have h8 : added.registers 8 = (pointWords (target - betaNat • hash)).2.2 := by
    rw [sub_eq_add_neg]; exact congrArg (fun words => words.2.2) holds
  refine congrArg (fun final => PMF.pure (some final)) ?_
  apply clearRegs_withRam_eq
  · simp only [storeRam_ram, setReg_ram, storeRam_registers, setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    rw [h6, h7, h8, addedDef, writeP_ram, loadedDef]
    simp only [setReg_ram, ramMul]
    rfl
  · simp only [storeRam_bits, setReg_bits, addedDef, writeP_bits, loadedDef, bitsMul]
  · intro index outside
    simp only [headScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨n0, n4, n6, n7, n8, n9, n10, n11⟩ := outside
    simp only [storeRam_registers, setReg_registers, if_neg n4]
    rw [addedDef, writeP_other _ _ _ (by simp [n6, n7, n8]), loadedDef]
    simp only [setReg_registers, if_neg n0, if_neg n4, if_neg n8, if_neg n9, if_neg n10, if_neg n11]
    exact regsMul index (by simp [n6, n7, n8, n9, n10, n11])

/-! ### Horner and the head -/

omit [FieldCertificate] [GroupCertificate] in
theorem wordAt_triple (words : Word × Word × Word) :
    (wordAt words 0, wordAt words 1, wordAt words 2) = words := rfl

omit [GroupCertificate] in
theorem freeOffsetPoints_ofFn (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    FieldMacToECMac.freeOffsetPoints (Vector.ofFn points) = List.ofFn fun index => (points index).point := by
  unfold FieldMacToECMac.freeOffsetPoints
  rw [Vector.toList_ofFn, List.map_ofFn]
  rfl

/-- **Horner and the head clamp**: `D_0 = Q − radix • pointHorner radix (tail)` at `openPoint 0`,
aborting exactly when the tail's clamp `clampedFirst` vanishes (`tailLaw`'s check). -/
theorem memSem_horner (memory : Memory) (points : Fin 90 → FieldMacToECMac.AffineOffset)
    (target : Point)
    (cells : ∀ (index : Fin 90) (position : Nat), position < 3 →
      memory.ram (word (openPoint (index.val + 1) + position)) =
        wordAt (offsetWords (points index)) position)
    (request : readWords (memory.ram (word reqTag0), memory.ram (word reqQX),
      memory.ram (word reqQY)) = some target) :
    Opening.horner.memSem memory =
      if FieldMacToECMac.clampedFirst (Vector.ofFn points) = 0 then PMF.pure none
      else PMF.pure (some (clearRegs (withRam memory (putPoint memory.ram (openPoint 0)
        (pointWords (target - radix • pointHorner radix
          (FieldMacToECMac.freeOffsetPoints (Vector.ofFn points)))))) headScratch)) := by
  set cleared := setReg (setReg (setReg memory 6 (word 0)) 7 (word 0)) 8 (word 0) with clearedDef
  have clearRun : Opening.clearP.memSem memory = PMF.pure (some cleared) := by
    unfold Opening.clearP
    simp only [Prog.seqList]
    rw [memSem_cst_seq, memSem_cst_seq, memSem_cst_seq, memSem_skip]
  have start : readPoint cleared.registers pointP = some 0 := by
    rw [readPoint_eq, clearedDef]
    simp only [setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    rfl
  have pointCells : ∀ index : Fin 90, readWords (cleared.ram (word (openPoint (index.val + 1))),
      cleared.ram (word (openPoint (index.val + 1) + 1)),
      cleared.ram (word (openPoint (index.val + 1) + 2))) = some (points index).point := by
    intro index
    have zero := cells index 0 (by omega)
    rw [Nat.add_zero] at zero
    simp only [clearedDef, setReg_ram]
    rw [zero, cells index 1 (by omega), cells index 2 (by omega), wordAt_triple, offsetWords_eq,
      readWords_pointWords]
  obtain ⟨looped, runLoop, ramLoop, bitsLoop, readLoop, regsLoop⟩ :=
    memSem_hornerSteps cleared (fun index => (points index).point) pointCells start 90 le_rfl
  rw [Nat.sub_self, List.drop_zero] at readLoop
  have requestLoop : readWords (looped.ram (word reqTag0), looped.ram (word reqQX),
      looped.ram (word reqQY)) = some target := by
    rw [ramLoop]
    exact request
  unfold Opening.horner
  simp only [Prog.seqList]
  rw [memSem_pure_seq clearRun, memSem_pure_seq runLoop, memSem_seq,
    memSem_head looped _ target readLoop requestLoop]
  have clampIs : FieldMacToECMac.clampedFirst (Vector.ofFn points) = 0 ↔
      betaNat • pointHorner radix (List.ofFn fun index => (points index).point) = 0 := by
    rw [FieldMacToECMac.clampedFirst, freeOffsetPoints_ofFn, neg_eq_zero, radix_smul]
  rw [freeOffsetPoints_ofFn, radix_smul]
  by_cases zero : betaNat • pointHorner radix (List.ofFn fun index => (points index).point) = 0
  · rw [if_pos zero, if_pos (clampIs.mpr zero), PMF.pure_bind]
    rfl
  · rw [if_neg zero, if_neg (fun clamp => zero (clampIs.mp clamp)), PMF.pure_bind]
    simp only [kleisli]
    rw [memSem_skip]
    refine congrArg (fun final => PMF.pure (some final)) ?_
    apply clearRegs_withRam_eq
    · simp only [withRam_ram, ramLoop, clearedDef, setReg_ram]
    · simp only [withRam_bits, bitsLoop, clearedDef, setReg_bits]
    · intro index outside
      simp only [headScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
      obtain ⟨n0, n4, n6, n7, n8, n9, n10, n11⟩ := outside
      simp only [withRam_registers]
      rw [regsLoop index (by simp [n4, n6, n7, n8, n9, n10, n11]), clearedDef]
      simp only [setReg_registers, if_neg n6, if_neg n7, if_neg n8]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
