/-
**The machine big-integer routines compute what they claim** (task T9a).

Every block is plain, so its law is the point mass at `det` (`memSem_det`); the lemmas here
compute `det` of each block symbolically and connect the words to the natural-number facts of
`BigIntArith`:

* `det_mulHi`: `bY ← ⌊x · p / 2^256⌋`;
* `det_henselLimb`, `det_exactDivP`: the limbs of `Q = (V − r)/p` for `p Q + r = V`;
* `det_hornerLimb`, `det_limbsToField`: `V mod p`;
* `det_digitLoop`, `memSem_digitsOf`: all digits `Y_e = (V / p^e) mod p`;
* `det_macLimb`, `det_macPass`, `det_macPasses`: big-integer Horner (the sampler's encoder);
* `det_packLimb`: packing a hash answer into a limb.
-/

import Proof.Simulator.BigIntDet

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine Blocks

namespace BigInt

/-- Resolve register reads through a chain of `setReg` / `storeRam`. -/
macro "reg_eval" : tactic =>
  `(tactic| simp (config := { decide := true }) only [regs_setReg, regs_storeRam, ram_setReg,
    ram_storeRam, bits_setReg, bits_storeRam, ↓reduceIte])

/-- The memory with its RAM replaced. -/
def setRam (memory : Memory) (ram : Word → Word) : Memory := { memory with ram := ram }

@[simp] theorem ram_setRam (memory : Memory) (ram : Word → Word) : (setRam memory ram).ram = ram := rfl
@[simp] theorem bits_setRam (memory : Memory) (ram : Word → Word) :
    (setRam memory ram).bits = memory.bits := rfl
@[simp] theorem regs_setRam (memory : Memory) (ram : Word → Word) :
    (setRam memory ram).registers = memory.registers := rfl

/-- The four `mulHi` constants are loaded. -/
def Consts (memory : Memory) : Prop :=
  memory.registers bMask = word mask128 ∧ memory.registers bC128 = word 128 ∧
    memory.registers bP0 = word pLow ∧ memory.registers bP1 = word pHigh

/-- Consts survive writes to other registers. -/
theorem consts_of_regs {before after : Memory} (consts : Consts before)
    (same : ∀ index, index ≠ bBeta → index ≠ bZ → index ≠ rAddr → index ≠ bK → index ≠ bV →
      index ≠ bQ0 → index ≠ bX → index ≠ bY → index ≠ bCarry →
      after.registers index = before.registers index) : Consts after := by
  obtain ⟨h1, h2, h3, h4⟩ := consts
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h1]
  · rw [same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h2]
  · rw [same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h3]
  · rw [same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h4]

theorem not_mem_scratch {index : Register} (outside : index ∉ scratch) :
    index ≠ bBeta ∧ index ≠ bMask ∧ index ≠ bC128 ∧ index ≠ bZ ∧ index ≠ rAddr ∧ index ≠ bP0 ∧
      index ≠ bP1 ∧ index ≠ bK ∧ index ≠ bV ∧ index ≠ bQ0 ∧ index ≠ bX ∧ index ≠ bY ∧
        index ≠ bCarry := by
  simp only [scratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  exact outside

/-! ### Setup -/

theorem det_setup (memory : Memory) :
    ∃ after, det setup memory = some after ∧ Consts after ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧ ∀ index, index ∉ scratch → after.registers index = memory.registers index := by
  refine ⟨_, rfl, ⟨?_, ?_, ?_, ?_⟩, by reg_eval, by reg_eval, fun index outside => ?_⟩
  all_goals (try reg_eval)
  obtain ⟨_, n1, n2, _, _, n5, n6, _⟩ := not_mem_scratch outside
  simp (config := { decide := true }) only [n1, n2, n5, n6, ↓reduceIte]

/-! ### The high word -/

/-- **`mulHi`**: `bY ← ⌊x · p / 2^256⌋`, clobbering only `bV`, `bQ0`, `bX`, `bZ`, `bY`. -/
theorem det_mulHi (memory : Memory) (consts : Consts memory) (x : Nat) (small : x < 2 ^ 256)
    (loaded : memory.registers bV = word x) :
    ∃ after, det mulHi memory = some after ∧ after.ram = memory.ram ∧ after.bits = memory.bits ∧
      after.registers bY = word (x * pNat / 2 ^ 256) ∧
      ∀ index, index ≠ bV → index ≠ bQ0 → index ≠ bX → index ≠ bZ → index ≠ bY →
        after.registers index = memory.registers index := by
  obtain ⟨hMask, hC, hP0, hP1⟩ := consts
  refine ⟨_, rfl, by reg_eval, by reg_eval, ?_, fun index n1 n2 n3 n4 n5 => ?_⟩
  · reg_eval
    rw [loaded, hMask, hC, hP0, hP1]
    simp only [eval_and_mask, eval_shr128, eval_mul_word, eval_add_word, Nat.mod_eq_of_lt small]
    rw [hiWord_eq x small]
  · simp (config := { decide := true }) only [regs_setReg, n1, n2, n3, n4, n5, ↓reduceIte]

/-! ### Hensel exact division -/

/-- The Hensel quotient limb the machine computes from borrow `b` and limb `v`. -/
def henselQ (b v : Nat) : Nat := (v + (2 ^ 256 - b)) * pinvNat % 2 ^ 256

theorem det_henselPre (address : Nat) (memory : Memory) (b v : Nat) (bSmall : b < 2 ^ 256)
    (vSmall : v < 2 ^ 256) (key : memory.registers bK = word pinvNat)
    (borrowIn : memory.registers bCarry = word b) (limbIn : memory.ram (word address) = word v) :
    ∃ after, det (henselPre address) memory = some after ∧
      after.registers bV = word (henselQ b v) ∧
      after.registers bBeta = word (if v < b then 1 else 0) ∧
      after.ram = Function.update memory.ram (word address) (word (henselQ b v)) ∧
      after.bits = memory.bits ∧
      ∀ index, index ≠ rAddr → index ≠ bV → index ≠ bBeta →
        after.registers index = memory.registers index := by
  have value : Arithmetic.mul.eval (Arithmetic.sub.eval (word v) (word b)) (word pinvNat) =
      word (henselQ b v) := by
    rw [eval_sub_word, eval_mul_word, Nat.mod_eq_of_lt vSmall, Nat.mod_eq_of_lt bSmall, henselQ,
      word_mod]
  refine ⟨_, rfl, ?_, ?_, ?_, by reg_eval, fun index n1 n2 n3 => ?_⟩
  · reg_eval
    rw [limbIn, borrowIn, key, value]
  · reg_eval
    rw [limbIn, borrowIn, eval_less_word, Nat.mod_eq_of_lt vSmall, Nat.mod_eq_of_lt bSmall]
  · reg_eval
    rw [limbIn, borrowIn, key, value]
  · simp (config := { decide := true }) only [regs_setReg, regs_storeRam, n1, n2, n3, ↓reduceIte]

/-- **One Hensel limb.** -/
theorem det_henselLimb (address : Nat) (memory : Memory) (consts : Consts memory) (b v : Nat)
    (bSmall : b < 2 ^ 256) (vSmall : v < 2 ^ 256) (key : memory.registers bK = word pinvNat)
    (borrowIn : memory.registers bCarry = word b) (limbIn : memory.ram (word address) = word v) :
    ∃ after, det (henselLimb address) memory = some after ∧ Consts after ∧
      after.registers bK = word pinvNat ∧
      after.registers bCarry = word (henselQ b v * pNat / 2 ^ 256 + (if v < b then 1 else 0)) ∧
      after.ram = Function.update memory.ram (word address) (word (henselQ b v)) ∧
      after.bits = memory.bits ∧
      ∀ index, index ∉ scratch → after.registers index = memory.registers index := by
  obtain ⟨first, firstDet, firstV, firstBeta, firstRam, firstBits, firstSame⟩ :=
    det_henselPre address memory b v bSmall vSmall key borrowIn limbIn
  have firstConsts : Consts first := consts_of_regs consts fun index n0 _ n4 _ n8 _ _ _ _ =>
    firstSame index n4 n8 n0
  obtain ⟨second, secondDet, secondRam, secondBits, secondY, secondSame⟩ :=
    det_mulHi first firstConsts (henselQ b v) (Nat.mod_lt _ (Nat.two_pow_pos _)) firstV
  have secondBeta : second.registers bBeta = word (if v < b then 1 else 0) := by
    rw [secondSame _ (by decide) (by decide) (by decide) (by decide) (by decide), firstBeta]
  refine ⟨setReg second bCarry (word (henselQ b v * pNat / 2 ^ 256 + (if v < b then 1 else 0))),
    ?_, ?_, ?_, ?_, ?_, ?_, fun index outside => ?_⟩
  · simp only [henselLimb, Prog.seqList, det_seq, firstDet, secondDet, Option.bind_some]
    simp only [det, ar, opDet, Option.bind_some, secondY, secondBeta, eval_add_word]
  · exact consts_of_regs firstConsts fun index _ _ _ _ n8 n9 n10 _ n12 => by
      rw [regs_setReg, if_neg n12, secondSame index n8 n9 n10 (by assumption) (by assumption)]
  · rw [regs_setReg, if_neg (by decide), secondSame _ (by decide) (by decide) (by decide) (by decide)
      (by decide), firstSame _ (by decide) (by decide) (by decide), key]
  · rw [regs_setReg, if_pos rfl]
  · rw [ram_setReg, secondRam, firstRam]
  · rw [bits_setReg, secondBits, firstBits]
  · obtain ⟨n0, _, _, n3, n4, _, _, _, n8, n9, n10, n11, n12⟩ := not_mem_scratch outside
    rw [regs_setReg, if_neg n12, secondSame index n8 n9 n10 n3 n11, firstSame index n4 n8 n0]

/-- The Hensel invariant after `index` limbs. -/
def HenselHolds (memory : Memory) (base quotient remainder index : Nat) (current : Memory) : Prop :=
  Consts current ∧ current.registers bK = word pinvNat ∧
    current.registers bCarry = word (borrow quotient remainder index) ∧
    current.ram = writeCells memory.ram base index (limb quotient) ∧ current.bits = memory.bits ∧
    ∀ register, register ∉ scratch → current.registers register = memory.registers register

/-- **Exact division by `p`**: the `count` limbs of `V` at `base` become those of `Q`, for
`p Q + r = V`, `r < p` in `bCarry`. -/
theorem det_exactDivP (base count : Nat) (small : base + count < 2 ^ 256) (memory : Memory)
    (consts : Consts memory) (value quotient remainder : Nat)
    (exact : pNat * quotient + remainder = value) (remainderSmall : remainder < pNat)
    (borrowIn : memory.registers bCarry = word remainder)
    (limbsIn : ∀ index, index < count → memory.ram (word (base + index)) = word (limb value index)) :
    ∃ after, det (exactDivP base count) memory = some after ∧ Consts after ∧
      after.ram = writeCells memory.ram base count (limb quotient) ∧ after.bits = memory.bits ∧
      ∀ register, register ∉ scratch → after.registers register = memory.registers register := by
  have start : HenselHolds memory base quotient remainder 0 (setReg memory bK (word pinvNat)) := by
    refine ⟨consts_of_regs consts fun index _ _ _ n7 _ _ _ _ _ => by rw [regs_setReg, if_neg n7],
      by rw [regs_setReg, if_pos rfl], ?_, by rw [ram_setReg, writeCells_zero], rfl,
      fun register outside => ?_⟩
    · rw [regs_setReg, if_neg (by decide), borrowIn, borrow_zero]
    · rw [regs_setReg, if_neg (not_mem_scratch outside).2.2.2.2.2.2.2.1]
  obtain ⟨after, reach, holds⟩ := det_rep_inv (HenselHolds memory base quotient remainder)
    (fun index => henselLimb (base + index)) count (fun index bound current holds => by
      obtain ⟨cConsts, cKey, cBorrow, cRam, cBits, cSame⟩ := holds
      have limbHere : current.ram (word (base + index)) = word (limb value index) := by
        rw [cRam, writeCells_out _ _ _ _ _ (by omega) (Or.inr le_rfl), limbsIn index bound]
      have step := hensel_step value quotient remainder index exact remainderSmall
      obtain ⟨next, nextDet, nConsts, nKey, nBorrow, nRam, nBits, nSame⟩ :=
        det_henselLimb (base + index) current cConsts _ _
          (lt_trans (borrow_lt quotient remainder index remainderSmall) pNat_lt_word)
          (limb_lt value index) cKey cBorrow limbHere
      refine ⟨next, nextDet, nConsts, nKey, ?_, ?_, by rw [nBits, cBits], fun register outside => ?_⟩
      · rw [nBorrow, henselQ, step.1, step.2]
      · rw [nRam, cRam, henselQ, step.1, writeCells_succ _ _ _ _ (by omega)]
      · rw [nSame register outside, cSame register outside])
    (setReg memory bK (word pinvNat)) start
  obtain ⟨aConsts, _, _, aRam, aBits, aSame⟩ := holds
  refine ⟨after, ?_, aConsts, aRam, aBits, aSame⟩
  simp only [exactDivP, Prog.seqList, det_seq, det, cst, opDet, Option.bind_some]
  rw [reach]
  rfl

/-! ### Field Horner -/

theorem det_hornerLimb (address : Nat) (memory : Memory) (acc v : Nat) (accSmall : acc < pNat)
    (vSmall : v < 2 ^ 256) (key : memory.registers bK = word c256)
    (accIn : memory.registers bCarry = word acc) (limbIn : memory.ram (word address) = word v) :
    ∃ after, det (hornerLimb address) memory = some after ∧
      after.registers bCarry = word ((acc * c256 % pNat + v) % pNat) ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧
      ∀ index, index ≠ rAddr → index ≠ bV → index ≠ bCarry →
        after.registers index = memory.registers index := by
  have h1 : acc % 2 ^ 256 = acc := Nat.mod_eq_of_lt (lt_trans accSmall pNat_lt_word)
  have h2 : c256 % 2 ^ 256 = c256 := Nat.mod_eq_of_lt (lt_trans c256_lt_p pNat_lt_word)
  have h3 : acc * c256 % pNat % 2 ^ 256 = acc * c256 % pNat :=
    Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ pNat_pos) pNat_lt_word)
  have h4 : v % 2 ^ 256 = v := Nat.mod_eq_of_lt vSmall
  refine ⟨_, rfl, ?_, by reg_eval, by reg_eval, fun index n1 n2 n3 => ?_⟩
  · reg_eval
    rw [accIn, key, limbIn, eval_fieldMul_word, h1, h2, eval_fieldAdd_word, h3, h4]
  · simp (config := { decide := true }) only [regs_setReg, n1, n2, n3, ↓reduceIte]

/-- The field-Horner invariant after `step` limbs (from the top). -/
def HornerHolds (memory : Memory) (value count step : Nat) (current : Memory) : Prop :=
  current.registers bK = word c256 ∧
    current.registers bCarry = word (value / 2 ^ (256 * (count - step)) % pNat) ∧
    current.ram = memory.ram ∧ current.bits = memory.bits ∧
    ∀ index, index ≠ rAddr → index ≠ bV → index ≠ bCarry → index ≠ bK →
      current.registers index = memory.registers index

/-- **`V mod p`** from the `count` limbs of `V < 2^(256 count)` at `base`, into `bCarry`. -/
theorem det_limbsToField (base count : Nat) (memory : Memory) (value : Nat)
    (valueSmall : value < 2 ^ (256 * count))
    (limbsIn : ∀ index, index < count → memory.ram (word (base + index)) = word (limb value index)) :
    ∃ after, det (limbsToField base count) memory = some after ∧
      after.registers bCarry = word (value % pNat) ∧ after.ram = memory.ram ∧
      after.bits = memory.bits ∧
      ∀ index, index ≠ rAddr → index ≠ bV → index ≠ bCarry → index ≠ bK →
        after.registers index = memory.registers index := by
  have start : HornerHolds memory value count 0 (setReg (setReg memory bK (word c256)) bCarry (word 0)) := by
    refine ⟨by reg_eval, ?_, rfl, rfl, fun index n1 n2 n3 n4 => ?_⟩
    · rw [Nat.sub_zero, div_top value count valueSmall, Nat.zero_mod]
      reg_eval
    · simp (config := { decide := true }) only [regs_setReg, n3, n4, ↓reduceIte]
  obtain ⟨after, reach, holds⟩ := det_rep_inv (HornerHolds memory value count)
    (fun step => hornerLimb (base + (count - 1 - step))) count (fun step bound current holds => by
      obtain ⟨cKey, cAcc, cRam, cBits, cSame⟩ := holds
      obtain ⟨next, nextDet, nAcc, nRam, nBits, nSame⟩ := det_hornerLimb (base + (count - 1 - step))
        current _ (limb value (count - 1 - step)) (Nat.mod_lt _ pNat_pos) (limb_lt _ _) cKey cAcc
        (by rw [cRam, limbsIn _ (by omega)])
      refine ⟨next, nextDet, by rw [nSame _ (by decide) (by decide) (by decide), cKey], ?_,
        by rw [nRam, cRam], by rw [nBits, cBits], fun index n1 n2 n3 n4 => by
          rw [nSame index n1 n2 n3, cSame index n1 n2 n3 n4]⟩
      rw [nAcc, show count - step = count - 1 - step + 1 by omega,
        show count - (step + 1) = count - 1 - step by omega, horner_step])
    _ start
  obtain ⟨_, aAcc, aRam, aBits, aSame⟩ := holds
  refine ⟨after, ?_, by rw [aAcc, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one], aRam, aBits,
    aSame⟩
  simp only [limbsToField, Prog.seqList, det_seq, det, cst, opDet, Option.bind_some]
  rw [reach]
  rfl

/-! ### Digit extraction -/

/-- **One digit**: `r = V mod p` to `cell`, then the limbs of `V / p`. -/
theorem det_digitStep (base count cell : Nat) (small : base + count < 2 ^ 256)
    (cellSmall : cell < 2 ^ 256) (apart : cell < base ∨ base + count ≤ cell) (memory : Memory)
    (consts : Consts memory) (value : Nat) (valueSmall : value < 2 ^ (256 * count))
    (limbsIn : ∀ index, index < count → memory.ram (word (base + index)) = word (limb value index)) :
    ∃ after, det (digitStep base count cell) memory = some after ∧ Consts after ∧
      after.ram = writeCells (Function.update memory.ram (word cell) (word (value % pNat))) base count
        (limb (value / pNat)) ∧ after.bits = memory.bits ∧
      ∀ register, register ∉ scratch → after.registers register = memory.registers register := by
  obtain ⟨first, firstDet, firstAcc, firstRam, firstBits, firstSame⟩ :=
    det_limbsToField base count memory value valueSmall limbsIn
  have firstConsts : Consts first := consts_of_regs consts fun index _ _ n4 n7 n8 _ _ _ n12 =>
    firstSame index n4 n8 n12 n7
  set second := storeRam (setReg first rAddr (word cell)) (word cell) (word (value % pNat)) with hSecond
  have secondDet : det (storeAt cell bCarry) first = some second := by
    rw [hSecond, ← firstAcc]; rfl
  have secondConsts : Consts second := consts_of_regs firstConsts fun index _ _ n4 _ _ _ _ _ _ => by
    rw [hSecond, regs_storeRam, regs_setReg, if_neg n4]
  obtain ⟨third, thirdDet, thirdConsts, thirdRam, thirdBits, thirdSame⟩ :=
    det_exactDivP base count small second secondConsts value (value / pNat) (value % pNat)
      (Nat.div_add_mod value pNat) (Nat.mod_lt _ pNat_pos)
      (by rw [hSecond, regs_storeRam, regs_setReg, if_neg (by decide), firstAcc])
      (fun index bound => by
        rw [hSecond, ram_storeRam, ram_setReg, Function.update_of_ne, firstRam, limbsIn index bound]
        intro same
        have := congrArg BitVec.toNat same
        rw [toNat_word_of_lt (by omega), toNat_word_of_lt cellSmall] at this
        omega)
  refine ⟨third, ?_, thirdConsts, ?_, ?_, fun register outside => ?_⟩
  · rw [digitStep, Prog.seqList, Prog.seqList, Prog.seqList, Prog.seqList, det_seq_some firstDet,
      det_seq_some secondDet, det_seq_some thirdDet]
    rfl
  · rw [thirdRam, hSecond, ram_storeRam, ram_setReg, firstRam]
  · rw [thirdBits, hSecond, bits_storeRam, bits_setReg, firstBits]
  · obtain ⟨_, _, _, _, n4, _, _, n7, n8, _, _, _, n12⟩ := not_mem_scratch outside
    rw [thirdSame register outside, hSecond, regs_storeRam, regs_setReg, if_neg n4,
      firstSame register n4 n8 n12 n7]

/-- The digit-loop invariant after `digit` digits. -/
def DigitHolds (memory : Memory) (base count digitBase value digit : Nat) (current : Memory) : Prop :=
  Consts current ∧
    current.ram = writeCells (writeCells memory.ram base count (limb (value / pNat ^ digit)))
      digitBase digit (fun e => value / pNat ^ e % pNat) ∧
    current.bits = memory.bits ∧
    ∀ register, register ∉ scratch → current.registers register = memory.registers register

/-- **The digit loop**: `Y_e = (V / p^e) mod p` at `digitBase + e` for `e < digits`, and the
limbs of `V / p^digits`. -/
theorem det_digitLoop (base count digits digitBase : Nat) (layout : base + count ≤ digitBase)
    (small : digitBase + digits < 2 ^ 256) (memory : Memory) (consts : Consts memory) (value : Nat)
    (valueSmall : value < 2 ^ (256 * count))
    (limbsIn : ∀ index, index < count → memory.ram (word (base + index)) = word (limb value index)) :
    ∃ after, det (digitLoop base count digits digitBase) memory = some after ∧ Consts after ∧
      after.ram = writeCells (writeCells memory.ram base count (limb (value / pNat ^ digits)))
        digitBase digits (fun e => value / pNat ^ e % pNat) ∧
      after.bits = memory.bits ∧
      ∀ register, register ∉ scratch → after.registers register = memory.registers register := by
  have start : DigitHolds memory base count digitBase value 0 memory := by
    refine ⟨consts, ?_, rfl, fun _ _ => rfl⟩
    rw [writeCells_zero, Nat.pow_zero, Nat.div_one, writeCells_self _ _ _ _ limbsIn]
  obtain ⟨after, reach, holds⟩ := det_rep_inv (DigitHolds memory base count digitBase value)
    (fun digit => digitStep base count (digitBase + digit)) digits (fun digit bound current holds => by
      obtain ⟨cConsts, cRam, cBits, cSame⟩ := holds
      have currentSmall : value / pNat ^ digit < 2 ^ (256 * count) :=
        lt_of_le_of_lt (Nat.div_le_self _ _) valueSmall
      obtain ⟨next, nextDet, nConsts, nRam, nBits, nSame⟩ := det_digitStep base count (digitBase + digit)
        (by omega) (by omega) (Or.inr (by omega)) current cConsts (value / pNat ^ digit) currentSmall
        (fun index inside => by
          rw [cRam, writeCells_out _ _ _ _ _ (by omega) (Or.inl (by omega)),
            writeCells_in _ _ _ _ _ inside (by omega)])
      refine ⟨next, nextDet, nConsts, ?_, by rw [nBits, cBits], fun register outside => by
        rw [nSame register outside, cSame register outside]⟩
      rw [nRam, cRam, div_pow_succ,
        show word (value / pNat ^ digit % pNat) =
          word ((fun e => value / pNat ^ e % pNat) digit) from rfl,
        ← writeCells_succ (writeCells memory.ram base count (limb (value / pNat ^ digit))) digitBase
          digit _ (by omega),
        writeCells_comm (writeCells memory.ram base count (limb (value / pNat ^ digit))) digitBase
          (digit + 1) base count _ _ (Or.inr layout), writeCells_writeCells])
    memory start
  exact ⟨after, reach, holds⟩

theorem plain_mulHi : IsPlain mulHi := by
  simp only [mulHi, Prog.seqList, IsPlain, OpIsPlain, ar, and_self]

theorem plain_setup : IsPlain setup := by
  simp only [setup, Prog.seqList, IsPlain, OpIsPlain, cst, and_self]

theorem plain_digitsOf (base count digits digitBase : Nat) :
    IsPlain (digitsOf base count digits digitBase) := by
  refine ⟨plain_setup, plain_rep _ _ fun _ _ => ?_, plain_zeroRegs _, trivial⟩
  refine ⟨?_, ⟨trivial, trivial⟩, ?_, trivial⟩
  · exact ⟨trivial, trivial, plain_rep _ _ fun _ _ => ⟨⟨trivial, trivial⟩, trivial, trivial, trivial⟩,
      trivial⟩
  · exact ⟨trivial, plain_rep _ _ fun _ _ =>
      ⟨⟨⟨trivial, trivial⟩, trivial, trivial, trivial, ⟨trivial, trivial⟩, trivial⟩, plain_mulHi,
        trivial, trivial⟩, trivial⟩

/-- **Digit extraction** (A1 §4 item 1): from the `count` limbs of `V < 2^(256 count)` at
`base`, the machine leaves `Y_e = (V / p^e) mod p` at `digitBase + e` for every `e < digits`,
the limbs of `V / p^digits` at `base`, and nothing else changed but the cleared scratch. -/
theorem memSem_digitsOf [BN254.FieldCertificate] (base count digits digitBase : Nat)
    (layout : base + count ≤ digitBase) (small : digitBase + digits < 2 ^ 256) (memory : Memory)
    (value : Nat) (valueSmall : value < 2 ^ (256 * count))
    (limbsIn : ∀ index, index < count → memory.ram (word (base + index)) = word (limb value index)) :
    (digitsOf base count digits digitBase).memSem memory =
      PMF.pure (some (clearRegs (setRam memory
        (writeCells (writeCells memory.ram base count (limb (value / pNat ^ digits))) digitBase digits
          (fun e => value / pNat ^ e % pNat))) scratch)) := by
  rw [memSem_det _ (plain_digitsOf base count digits digitBase)]
  obtain ⟨first, firstDet, firstConsts, firstRam, firstBits, firstSame⟩ := det_setup memory
  obtain ⟨second, secondDet, _, secondRam, secondBits, secondSame⟩ :=
    det_digitLoop base count digits digitBase layout small first firstConsts value valueSmall
      (fun index bound => by rw [firstRam, limbsIn index bound])
  rw [digitsOf, Prog.seqList, Prog.seqList, Prog.seqList, Prog.seqList, det_seq_some firstDet,
    det_seq_some secondDet, det_seq, det_zeroRegs, Option.bind_some]
  show PMF.pure (some (clearRegs second scratch)) = _
  congr 2
  rw [clearRegs_eq_iff]
  refine ⟨by rw [secondRam, firstRam, ram_setRam], by rw [secondBits, firstBits, bits_setRam],
    fun register outside => ?_⟩
  rw [secondSame register outside, firstSame register outside, regs_setRam]

/-! ### Multiply-accumulate -/

theorem det_macPre (address : Nat) (memory : Memory) (e : Nat)
    (key : memory.registers bK = word pNat) (limbIn : memory.ram (word address) = word e) :
    ∃ after, det (macPre address) memory = some after ∧ after.registers bV = word e ∧
      after.registers bBeta = word (e * pNat) ∧ after.ram = memory.ram ∧ after.bits = memory.bits ∧
      ∀ index, index ≠ rAddr → index ≠ bV → index ≠ bBeta →
        after.registers index = memory.registers index := by
  refine ⟨_, rfl, ?_, ?_, by reg_eval, by reg_eval, fun index n1 n2 n3 => ?_⟩
  · reg_eval; rw [limbIn]
  · reg_eval; rw [limbIn, key, eval_mul_word]
  · simp (config := { decide := true }) only [regs_setReg, n1, n2, n3, ↓reduceIte]

theorem det_macPost (address : Nat) (memory : Memory) (lo c hi : Nat)
    (loIn : memory.registers bBeta = word lo) (cIn : memory.registers bCarry = word c)
    (hiIn : memory.registers bY = word hi) :
    ∃ after, det (macPost address) memory = some after ∧
      after.registers bCarry =
        word (hi + (if (lo + c) % 2 ^ 256 < c % 2 ^ 256 then 1 else 0)) ∧
      after.ram = Function.update memory.ram (word address) (word (lo + c)) ∧
      after.bits = memory.bits ∧
      ∀ index, index ≠ rAddr → index ≠ bBeta → index ≠ bX → index ≠ bCarry →
        after.registers index = memory.registers index := by
  refine ⟨_, rfl, ?_, ?_, by reg_eval, fun index n1 n2 n3 n4 => ?_⟩
  · reg_eval
    rw [loIn, cIn, hiIn, eval_add_word, eval_less_word, eval_add_word]
  · reg_eval
    rw [loIn, cIn, eval_add_word]
  · simp (config := { decide := true }) only [regs_setReg, regs_storeRam, n1, n2, n3, n4, ↓reduceIte]

/-- **One multiply-accumulate limb**: `E_j ← (e · p + c) mod 2^256`, carry `← ⌊e p / 2^256⌋ +
[overflow]`. -/
theorem det_macLimb (address : Nat) (memory : Memory) (consts : Consts memory) (e c : Nat)
    (eSmall : e < 2 ^ 256) (cSmall : c < 2 ^ 256) (key : memory.registers bK = word pNat)
    (cIn : memory.registers bCarry = word c) (limbIn : memory.ram (word address) = word e) :
    ∃ after, det (macLimb address) memory = some after ∧ Consts after ∧
      after.registers bK = word pNat ∧
      after.registers bCarry =
        word (e * pNat / 2 ^ 256 + (if (e * pNat + c) % 2 ^ 256 < c then 1 else 0)) ∧
      after.ram = Function.update memory.ram (word address) (word (e * pNat + c)) ∧
      after.bits = memory.bits ∧
      ∀ index, index ∉ scratch → after.registers index = memory.registers index := by
  obtain ⟨first, firstDet, firstV, firstBeta, firstRam, firstBits, firstSame⟩ :=
    det_macPre address memory e key limbIn
  have firstConsts : Consts first := consts_of_regs consts fun index n0 _ n4 _ n8 _ _ _ _ =>
    firstSame index n4 n8 n0
  obtain ⟨second, secondDet, secondRam, secondBits, secondY, secondSame⟩ :=
    det_mulHi first firstConsts e eSmall firstV
  obtain ⟨third, thirdDet, thirdCarry, thirdRam, thirdBits, thirdSame⟩ :=
    det_macPost address second (e * pNat) c (e * pNat / 2 ^ 256)
      (by rw [secondSame _ (by decide) (by decide) (by decide) (by decide) (by decide), firstBeta])
      (by rw [secondSame _ (by decide) (by decide) (by decide) (by decide) (by decide),
        firstSame _ (by decide) (by decide) (by decide), cIn])
      secondY
  have keep : ∀ index, index ≠ bBeta → index ≠ bZ → index ≠ rAddr → index ≠ bV → index ≠ bQ0 →
      index ≠ bX → index ≠ bY → index ≠ bCarry → third.registers index = memory.registers index :=
    fun index n0 n3 n4 n8 n9 n10 n11 n12 => by
      rw [thirdSame index n4 n0 n10 n12, secondSame index n8 n9 n10 n3 n11, firstSame index n4 n8 n0]
  refine ⟨third, ?_, consts_of_regs consts fun index n0 n3 n4 _ n8 n9 n10 n11 n12 =>
    keep index n0 n3 n4 n8 n9 n10 n11 n12, by rw [keep _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), key], ?_, ?_, ?_,
    fun index outside => ?_⟩
  · rw [macLimb, Prog.seqList, Prog.seqList, Prog.seqList, Prog.seqList, det_seq_some firstDet,
      det_seq_some secondDet, det_seq_some thirdDet]
    rfl
  · rw [thirdCarry, Nat.mod_eq_of_lt cSmall]
  · rw [thirdRam, secondRam, firstRam]
  · rw [thirdBits, secondBits, firstBits]
  · obtain ⟨n0, _, _, n3, n4, _, _, _, n8, n9, n10, n11, n12⟩ := not_mem_scratch outside
    exact keep index n0 n3 n4 n8 n9 n10 n11 n12

/-- The invariant of one Horner pass after `index` limbs. -/
def MacHolds (memory : Memory) (base value digit index : Nat) (current : Memory) : Prop :=
  Consts current ∧ current.registers bK = word pNat ∧
    current.registers bCarry = word (borrow value digit index) ∧
    current.ram = writeCells memory.ram base index (limb (pNat * value + digit)) ∧
    current.bits = memory.bits ∧
    ∀ register, register ∉ scratch → current.registers register = memory.registers register

/-- **One Horner pass** `E ← p · E + y` over the `count` limbs at `base`, `y < p` read from
`cell`. -/
theorem det_macPass (base count cell : Nat) (small : base + count < 2 ^ 256) (memory : Memory)
    (consts : Consts memory) (key : memory.registers bK = word pNat) (value digit : Nat)
    (digitSmall : digit < pNat) (cellIn : memory.ram (word cell) = word digit)
    (limbsIn : ∀ index, index < count → memory.ram (word (base + index)) = word (limb value index)) :
    ∃ after, det (macPass base count cell) memory = some after ∧ Consts after ∧
      after.registers bK = word pNat ∧
      after.ram = writeCells memory.ram base count (limb (pNat * value + digit)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ∉ scratch → after.registers register = memory.registers register := by
  set loaded := setReg (setReg memory rAddr (word cell)) bCarry (word digit) with hLoaded
  have loadDet : det (loadAt bCarry cell) memory = some loaded := by
    rw [hLoaded, ← cellIn]; rfl
  have start : MacHolds memory base value digit 0 loaded := by
    refine ⟨consts_of_regs consts fun index _ _ n4 _ _ _ _ _ n12 => by
        rw [hLoaded, regs_setReg, if_neg n12, regs_setReg, if_neg n4],
      by rw [hLoaded, regs_setReg, if_neg (by decide), regs_setReg, if_neg (by decide), key],
      by rw [hLoaded, regs_setReg, if_pos rfl, borrow_zero],
      by rw [hLoaded, ram_setReg, ram_setReg, writeCells_zero], rfl, fun register outside => ?_⟩
    obtain ⟨_, _, _, _, n4, _, _, _, _, _, _, _, n12⟩ := not_mem_scratch outside
    rw [hLoaded, regs_setReg, if_neg n12, regs_setReg, if_neg n4]
  obtain ⟨after, reach, holds⟩ := det_rep_inv (MacHolds memory base value digit)
    (fun index => macLimb (base + index)) count (fun index bound current holds => by
      obtain ⟨cConsts, cKey, cCarry, cRam, cBits, cSame⟩ := holds
      have step := mac_step value digit index digitSmall
      obtain ⟨next, nextDet, nConsts, nKey, nCarry, nRam, nBits, nSame⟩ :=
        det_macLimb (base + index) current cConsts (limb value index) (borrow value digit index)
          (limb_lt _ _) (lt_trans (borrow_lt value digit index digitSmall) pNat_lt_word) cKey cCarry
          (by rw [cRam, writeCells_out _ _ _ _ _ (by omega) (Or.inr le_rfl), limbsIn index bound])
      refine ⟨next, nextDet, nConsts, nKey, by rw [nCarry, step.2], ?_, by rw [nBits, cBits],
        fun register outside => by rw [nSame register outside, cSame register outside]⟩
      rw [nRam, cRam, ← word_mod (limb value index * pNat + borrow value digit index), step.1,
        writeCells_succ _ _ _ _ (by omega)])
    loaded start
  obtain ⟨aConsts, aKey, _, aRam, aBits, aSame⟩ := holds
  refine ⟨after, ?_, aConsts, aKey, aRam, aBits, aSame⟩
  rw [macPass, Prog.seqList, Prog.seqList, Prog.seqList, det_seq_some loadDet, det_seq, reach]
  rfl

/-- The invariant of the Horner passes after `step` digits. -/
def PassesHolds (memory : Memory) (base count start digits : Nat) (digitValues : Nat → Nat)
    (step : Nat) (current : Memory) : Prop :=
  Consts current ∧ current.registers bK = word pNat ∧
    current.ram = writeCells memory.ram base count (limb (hornerValue start digitValues digits step)) ∧
    current.bits = memory.bits ∧
    ∀ register, register ∉ scratch → current.registers register = memory.registers register

/-- **The Horner passes**: the `count` limbs of `E₀` at `base` become those of
`E₀ · p^digits + Σ_e Y_e p^e`, the digits `Y_e < p` read from `yBase + e`. -/
theorem det_macPasses (base count digits yBase : Nat) (small : base + count < 2 ^ 256)
    (ySmall : yBase + digits < 2 ^ 256) (apart : base + count ≤ yBase ∨ yBase + digits ≤ base)
    (memory : Memory) (consts : Consts memory) (start : Nat) (digitValues : Nat → Nat)
    (digitsSmall : ∀ e, e < digits → digitValues e < pNat)
    (cellsIn : ∀ e, e < digits → memory.ram (word (yBase + e)) = word (digitValues e))
    (limbsIn : ∀ index, index < count → memory.ram (word (base + index)) = word (limb start index)) :
    ∃ after, det (macPasses base count digits yBase) memory = some after ∧ Consts after ∧
      after.ram = writeCells memory.ram base count
        (limb (start * pNat ^ digits + encNat digitValues digits)) ∧
      after.bits = memory.bits ∧
      ∀ register, register ∉ scratch → after.registers register = memory.registers register := by
  have startHolds : PassesHolds memory base count start digits digitValues 0
      (setReg memory bK (word pNat)) := by
    refine ⟨consts_of_regs consts fun index _ _ _ n7 _ _ _ _ _ => by rw [regs_setReg, if_neg n7],
      by rw [regs_setReg, if_pos rfl], ?_, rfl, fun register outside => ?_⟩
    · rw [ram_setReg, hornerValue, writeCells_self _ _ _ _ limbsIn]
    · rw [regs_setReg, if_neg (not_mem_scratch outside).2.2.2.2.2.2.2.1]
  obtain ⟨after, reach, holds⟩ := det_rep_inv (PassesHolds memory base count start digits digitValues)
    (fun step => macPass base count (yBase + (digits - 1 - step))) digits
    (fun step bound current holds => by
      obtain ⟨cConsts, cKey, cRam, cBits, cSame⟩ := holds
      obtain ⟨next, nextDet, nConsts, nKey, nRam, nBits, nSame⟩ := det_macPass base count
        (yBase + (digits - 1 - step)) small current cConsts cKey
        (hornerValue start digitValues digits step) (digitValues (digits - 1 - step))
        (digitsSmall _ (by omega))
        (by rw [cRam, writeCells_out _ _ _ _ _ (by omega) (by omega), cellsIn _ (by omega)])
        (fun index inside => by rw [cRam, writeCells_in _ _ _ _ _ inside (by omega)])
      refine ⟨next, nextDet, nConsts, nKey, ?_, by rw [nBits, cBits], fun register outside => by
        rw [nSame register outside, cSame register outside]⟩
      rw [nRam, cRam, writeCells_writeCells]
      rfl)
    (setReg memory bK (word pNat)) startHolds
  obtain ⟨aConsts, _, aRam, aBits, aSame⟩ := holds
  refine ⟨after, ?_, aConsts, by rw [aRam, hornerValue_eq], aBits, aSame⟩
  rw [macPasses, Prog.seqList, Prog.seqList, Prog.seqList,
    det_seq_some (rfl : det (cst bK pNat) memory = some (setReg memory bK (word pNat))), det_seq, reach]
  rfl

theorem plain_macPasses (base count digits yBase : Nat) : IsPlain (macPasses base count digits yBase) :=
  ⟨trivial, plain_rep _ _ fun _ _ => ⟨⟨trivial, trivial⟩, plain_rep _ _ fun _ _ =>
    ⟨⟨⟨trivial, trivial⟩, trivial, trivial⟩, plain_mulHi,
      ⟨trivial, ⟨trivial, trivial⟩, trivial, trivial, trivial⟩, trivial⟩, trivial⟩, trivial⟩

/-! ### Packing a hash answer -/

/-- **Packing a hash answer** `(a.1, a.2)` from `rFirst`, `rSecond` (both below `2^128`): the limb
`a.1 + 2^128 · a.2` is stored at `address`. -/
theorem det_packLimb (address : Nat) (memory : Memory) (first second : Nat)
    (firstIn : memory.registers rFirst = word first) (secondIn : memory.registers rSecond = word second) :
    ∃ after, det (packLimb address) memory = some after ∧
      after.ram = Function.update memory.ram (word address) (word (first + 2 ^ 128 * second)) ∧
      after.bits = memory.bits ∧
      ∀ index, index ≠ rAddr → index ≠ rFirst → index ≠ rSecond →
        after.registers index = memory.registers index := by
  refine ⟨_, rfl, ?_, by reg_eval, fun index n1 n2 n3 => ?_⟩
  · reg_eval
    rw [firstIn, secondIn, eval_shl128, eval_add_word, Nat.mul_comm second]
  · simp (config := { decide := true }) only [regs_setReg, regs_storeRam, n1, n2, n3, ↓reduceIte]

end BigInt

end Kriterion.ArgoMAC.PlanB.SimMachine
