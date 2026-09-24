/-
**Deterministic evaluation of plain machine blocks** (task T9a toolkit).

The big-integer routines are coin-free and oracle-free except the preimage sampler's draws, so
their memory law (`Prog.memSem`) is a point mass. `det` computes that point as an `Option Memory`
(abort = `none`) by plain structural recursion; `memSem_det` shows `memSem = PMF.pure ∘ det` for
every `IsPlain` program. Straight-line blocks then reduce by `simp` on `det`, never by executing
code, and `det_rep_inv` threads an invariant through an unrolled `rep`.

Also here: the unconditional word laws of the arithmetic operations the routines use
(`eval_add_word`, `eval_mul_word`, `eval_sub_word`, `eval_and_mask`, `eval_shr128`,
`eval_less_word`, `eval_fieldMul_word`, `eval_fieldAdd_word`, `eval_shl128`), and `writeCells`, a
block of RAM cells replaced by the words of a function.
-/

import Proof.Simulator.Rejection
import Proof.Simulator.BigIntArith

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine Blocks

namespace BigInt

/-! ### The deterministic law -/

/-- The point law of a plain operation (`none` for coins, oracles and point additions, which
`IsPlain` excludes). -/
def opDet (operation : Op) (memory : Memory) : Option Memory :=
  match operation with
  | .constant target value => some (setReg memory target value)
  | .arith operation target left right =>
      some (setReg memory target (operation.eval (memory.registers left) (memory.registers right)))
  | .load target address => some (setReg memory target (memory.ram (memory.registers address)))
  | .store address source =>
      some (storeRam memory (memory.registers address) (memory.registers source))
  | .push stack bit => some (pushOn memory stack bit)
  | .pushBit stack source => some (pushOn memory stack ((memory.registers source).getLsbD 0))
  | _ => none

/-- The point law of a program: the memory it leaves, `none` on an abort. -/
def det : Prog → Memory → Option Memory
  | .op operation, memory => opDet operation memory
  | .popBit stack target, memory => some (popInto memory stack target)
  | .skip _, memory => some memory
  | .abort _, _ => none
  | .seq first second, memory => (det first memory).bind (det second)
  | .ite source whenSet whenClear, memory =>
      if memory.registers source = 0 then det whenClear memory else det whenSet memory

/-- An operation with a point law. -/
def OpIsPlain : Op → Prop
  | .constant .. | .arith .. | .load .. | .store .. | .push .. | .pushBit .. => True
  | _ => False

/-- A program built from operations with point laws. -/
def IsPlain : Prog → Prop
  | .op operation => OpIsPlain operation
  | .popBit _ _ | .skip _ | .abort _ => True
  | .seq first second => IsPlain first ∧ IsPlain second
  | .ite _ whenSet whenClear => IsPlain whenSet ∧ IsPlain whenClear

/-- **A plain program's memory law is the point mass at `det`.** -/
theorem memSem_det [BN254.FieldCertificate] : ∀ (program : Prog), IsPlain program →
    ∀ memory, program.memSem memory = PMF.pure (det program memory)
  | .op operation, plain, memory => by
      cases operation <;> first | exact absurd plain id | rfl
  | .popBit _ _, _, _ => rfl
  | .skip _, _, _ => rfl
  | .abort _, _, _ => rfl
  | .seq first second, plain, memory => by
      simp only [Prog.memSem, det]
      rw [memSem_det first plain.1 memory, PMF.pure_bind]
      cases det first memory with
      | none => rfl
      | some next => exact memSem_det second plain.2 next
  | .ite source whenSet whenClear, plain, memory => by
      simp only [Prog.memSem, det]
      split
      · exact memSem_det whenClear plain.2 memory
      · exact memSem_det whenSet plain.1 memory

/-- **A plain program issues no oracle operation** (`IsPlain` excludes the oracle operations, and
the coins and point additions besides), so the lazy oracle passes through it untouched
(`sem_noOracle`). -/
theorem IsPlain.noOracle : ∀ {program : Prog}, IsPlain program → program.NoOracle
  | .op operation, plain => by cases operation <;> first | rfl | exact absurd plain id
  | .popBit _ _, _ | .skip _, _ | .abort _, _ => trivial
  | .seq _ _, plain => ⟨plain.1.noOracle, plain.2.noOracle⟩
  | .ite _ _ _, plain => ⟨plain.1.noOracle, plain.2.noOracle⟩

theorem plain_rep (count : Nat) (body : Nat → Prog)
    (plain : ∀ index, index < count → IsPlain (body index)) : IsPlain (Prog.rep count body) := by
  induction count with
  | zero => rw [Prog.rep]; trivial
  | succ count ih =>
      rw [Prog.rep]
      exact ⟨ih fun index bound => plain index (by omega), plain count (by omega)⟩

theorem plain_zeroRegs (registers : List Register) : IsPlain (zeroRegs registers) := by
  induction registers with
  | nil => trivial
  | cons register rest ih => exact ⟨trivial, ih⟩

/-! ### Equations -/

theorem det_seq (first second : Prog) (memory : Memory) :
    det (.seq first second) memory = (det first memory).bind (det second) := rfl

theorem det_seq_some {first second : Prog} {memory middle : Memory}
    (step : det first memory = some middle) :
    det (.seq first second) memory = det second middle := by
  rw [det_seq, step, Option.bind_some]

/-- A `seqList` of a concatenation runs its two parts in turn. -/
theorem det_seqList_append (first second : List Prog) (memory : Memory) :
    det (Prog.seqList (first ++ second)) memory =
      (det (Prog.seqList first) memory).bind (det (Prog.seqList second)) := by
  induction first generalizing memory with
  | nil => rfl
  | cons head tail ih =>
      rw [List.cons_append, Prog.seqList, Prog.seqList, det_seq, det_seq, Option.bind_assoc]
      congr 1
      funext middle
      exact ih middle

theorem det_rep_zero (body : Nat → Prog) (memory : Memory) :
    det (Prog.rep 0 body) memory = some memory := by rw [Prog.rep]; rfl

theorem det_rep_succ (count : Nat) (body : Nat → Prog) (memory : Memory) :
    det (Prog.rep (count + 1) body) memory =
      (det (Prog.rep count body) memory).bind (det (body count)) := by
  rw [Prog.rep]; rfl

/-- **An invariant through an unrolled `rep`.** -/
theorem det_rep_inv (holds : Nat → Memory → Prop) (body : Nat → Prog) :
    ∀ count, (∀ index, index < count → ∀ memory, holds index memory →
        ∃ after, det (body index) memory = some after ∧ holds (index + 1) after) →
      ∀ memory, holds 0 memory → ∃ after, det (Prog.rep count body) memory = some after ∧
        holds count after
  | 0, _, memory, start => ⟨memory, det_rep_zero body memory, start⟩
  | count + 1, step, memory, start => by
      obtain ⟨middle, reach, middleHolds⟩ := det_rep_inv holds body count
        (fun index bound => step index (by omega)) memory start
      obtain ⟨after, last, afterHolds⟩ := step count (by omega) middle middleHolds
      exact ⟨after, by rw [det_rep_succ, reach, Option.bind_some, last], afterHolds⟩

theorem clearRegs_cons' (memory : Memory) (register : Register) (rest : List Register) :
    clearRegs (setReg memory register 0) rest = clearRegs memory (register :: rest) := by
  apply memory_ext
  · rw [(clearRegs_other _ _).2, (clearRegs_other _ _).2]; rfl
  · funext index
    simp only [clearRegs_registers, setReg_registers, List.mem_cons]
    by_cases same : index = register <;> by_cases inRest : index ∈ rest <;> simp [same, inRest]
  · rw [(clearRegs_other _ _).1, (clearRegs_other _ _).1]; rfl

theorem det_zeroRegs (registers : List Register) (memory : Memory) :
    det (zeroRegs registers) memory = some (clearRegs memory registers) := by
  induction registers generalizing memory with
  | nil => rfl
  | cons register rest ih =>
      simp only [zeroRegs, det, cst, opDet, Option.bind_some, ih]
      rw [show word 0 = 0 from rfl, clearRegs_cons']

/-! ### Memory projections -/

@[simp] theorem regs_setReg (memory : Memory) (target : Register) (value : Word) (index : Register) :
    (setReg memory target value).registers index =
      if index = target then value else memory.registers index := setReg_registers _ _ _ _
@[simp] theorem ram_setReg (memory : Memory) (target : Register) (value : Word) :
    (setReg memory target value).ram = memory.ram := rfl
@[simp] theorem bits_setReg (memory : Memory) (target : Register) (value : Word) :
    (setReg memory target value).bits = memory.bits := rfl
@[simp] theorem regs_storeRam (memory : Memory) (address value : Word) :
    (storeRam memory address value).registers = memory.registers := rfl
@[simp] theorem ram_storeRam (memory : Memory) (address value : Word) :
    (storeRam memory address value).ram = Function.update memory.ram address value := rfl
@[simp] theorem bits_storeRam (memory : Memory) (address value : Word) :
    (storeRam memory address value).bits = memory.bits := rfl

/-! ### Words -/

theorem toNat_word (value : Nat) : (word value).toNat = value % 2 ^ 256 := BitVec.toNat_ofNat _ _

theorem toNat_word_of_lt {value : Nat} (small : value < 2 ^ 256) : (word value).toNat = value := by
  rw [toNat_word, Nat.mod_eq_of_lt small]

theorem word_mod (value : Nat) : word (value % 2 ^ 256) = word value := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_word, toNat_word, Nat.mod_mod]

theorem word_toNat (value : Word) : word value.toNat = value := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_word, Nat.mod_eq_of_lt value.isLt]

theorem eval_add_word (first second : Nat) :
    Arithmetic.add.eval (word first) (word second) = word (first + second) := by
  apply BitVec.eq_of_toNat_eq
  show (word first + word second).toNat = _
  rw [BitVec.toNat_add, toNat_word, toNat_word, toNat_word, ← Nat.add_mod]

theorem eval_mul_word (first second : Nat) :
    Arithmetic.mul.eval (word first) (word second) = word (first * second) := by
  apply BitVec.eq_of_toNat_eq
  show (word first * word second).toNat = _
  rw [BitVec.toNat_mul, toNat_word, toNat_word, toNat_word, ← Nat.mul_mod]

theorem eval_sub_word (first second : Nat) :
    Arithmetic.sub.eval (word first) (word second) =
      word (first % 2 ^ 256 + (2 ^ 256 - second % 2 ^ 256)) := by
  apply BitVec.eq_of_toNat_eq
  show (word first - word second).toNat = _
  rw [BitVec.toNat_sub, toNat_word, toNat_word, toNat_word]
  have := Nat.mod_lt second (Nat.two_pow_pos 256)
  rw [Nat.add_comm (2 ^ 256 - second % 2 ^ 256)]

theorem eval_and_mask (value : Nat) :
    Arithmetic.and.eval (word value) (word mask128) = word (value % 2 ^ 128) := by
  apply BitVec.eq_of_toNat_eq
  show (word value &&& word mask128).toNat = _
  have maskSmall : mask128 < 2 ^ 256 := by unfold mask128; omega
  rw [BitVec.toNat_and, toNat_word, toNat_word, Nat.mod_eq_of_lt maskSmall, mask128_eq,
    Nat.and_two_pow_sub_one_eq_mod, toNat_word, Nat.mod_mod_of_dvd _ (by norm_num),
    Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (Nat.two_pow_pos 128)) (by norm_num))]

theorem eval_shr128 (value : Nat) :
    Arithmetic.shiftRight.eval (word value) (word 128) = word (value % 2 ^ 256 / 2 ^ 128) := by
  apply BitVec.eq_of_toNat_eq
  show (word value >>> (word 128).toNat).toNat = _
  rw [BitVec.toNat_ushiftRight, toNat_word, toNat_word_of_lt (by norm_num), Nat.shiftRight_eq_div_pow,
    toNat_word, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (Nat.two_pow_pos 256)))]

theorem eval_shl128 (value : Nat) :
    Arithmetic.shiftLeft.eval (word value) (word 128) = word (value * 2 ^ 128) := by
  apply BitVec.eq_of_toNat_eq
  show (word value <<< (word 128).toNat).toNat = _
  rw [BitVec.toNat_shiftLeft, toNat_word, toNat_word_of_lt (by norm_num), Nat.shiftLeft_eq,
    toNat_word, Nat.mod_mul_mod]

theorem eval_less_word (first second : Nat) :
    Arithmetic.less.eval (word first) (word second) =
      word (if first % 2 ^ 256 < second % 2 ^ 256 then 1 else 0) := by
  show (if (word first).toNat < (word second).toNat then 1 else 0) = _
  rw [toNat_word, toNat_word]
  split <;> rfl

theorem eval_fieldMul_word (first second : Nat) :
    Arithmetic.fieldMul.eval (word first) (word second) =
      word (first % 2 ^ 256 * (second % 2 ^ 256) % pNat) := by
  show BitVec.ofNat 256 (((word first).toNat : BN254.BaseField) *
    ((word second).toNat : BN254.BaseField)).val = _
  rw [toNat_word, toNat_word, ← Nat.cast_mul, ZMod.val_natCast]
  rfl

theorem eval_fieldAdd_word (first second : Nat) :
    Arithmetic.fieldAdd.eval (word first) (word second) =
      word ((first % 2 ^ 256 + second % 2 ^ 256) % pNat) := by
  show BitVec.ofNat 256 (((word first).toNat : BN254.BaseField) +
    ((word second).toNat : BN254.BaseField)).val = _
  rw [toNat_word, toNat_word, ← Nat.cast_add, ZMod.val_natCast]
  rfl

/-! ### Blocks of RAM cells -/

/-- `ram` with the `count` cells from `base` replaced by the words `f 0, …, f (count − 1)`. -/
def writeCells (ram : Word → Word) (base count : Nat) (f : Nat → Nat) : Word → Word :=
  fun address => if base ≤ address.toNat ∧ address.toNat < base + count then
    word (f (address.toNat - base)) else ram address

theorem writeCells_zero (ram : Word → Word) (base : Nat) (f : Nat → Nat) :
    writeCells ram base 0 f = ram := by
  funext address
  simp only [writeCells, Nat.add_zero]
  rw [if_neg (by omega)]

theorem writeCells_succ (ram : Word → Word) (base count : Nat) (f : Nat → Nat)
    (small : base + count < 2 ^ 256) :
    writeCells ram base (count + 1) f =
      Function.update (writeCells ram base count f) (word (base + count)) (word (f count)) := by
  funext address
  simp only [writeCells, Function.update_apply]
  by_cases hit : address = word (base + count)
  · subst hit
    rw [if_pos rfl, toNat_word_of_lt small, if_pos (by omega), Nat.add_sub_cancel_left]
  · rw [if_neg hit]
    have other : address.toNat ≠ base + count := by
      intro same; apply hit; rw [← same, word_toNat]
    by_cases inside : base ≤ address.toNat ∧ address.toNat < base + count
    · rw [if_pos (by omega), if_pos inside]
    · rw [if_neg (by omega), if_neg inside]

theorem writeCells_in (ram : Word → Word) (base count : Nat) (f : Nat → Nat) (index : Nat)
    (inside : index < count) (small : base + count ≤ 2 ^ 256) :
    writeCells ram base count f (word (base + index)) = word (f index) := by
  simp only [writeCells]
  rw [toNat_word_of_lt (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem writeCells_out (ram : Word → Word) (base count : Nat) (f : Nat → Nat) (address : Nat)
    (small : address < 2 ^ 256) (outside : address < base ∨ base + count ≤ address) :
    writeCells ram base count f (word address) = ram (word address) := by
  simp only [writeCells]
  rw [toNat_word_of_lt small, if_neg (by omega)]

/-- A later block over the same cells wins. -/
theorem writeCells_writeCells (ram : Word → Word) (base count : Nat) (f g : Nat → Nat) :
    writeCells (writeCells ram base count f) base count g = writeCells ram base count g := by
  funext address
  simp only [writeCells]
  split <;> rfl

/-- Disjoint blocks commute. -/
theorem writeCells_comm (ram : Word → Word) (base count other width : Nat) (f g : Nat → Nat)
    (disjoint : base + count ≤ other ∨ other + width ≤ base) :
    writeCells (writeCells ram base count f) other width g =
      writeCells (writeCells ram other width g) base count f := by
  funext address
  simp only [writeCells]
  by_cases first : base ≤ address.toNat ∧ address.toNat < base + count
  · rw [if_pos first, if_neg (by omega), if_pos first]
  · rw [if_neg first]
    split <;> rfl

/-- A single-cell update inside or outside a block. -/
theorem update_writeCells_out (ram : Word → Word) (base count address : Nat) (f : Nat → Nat)
    (value : Word) (small : address < 2 ^ 256) (outside : address < base ∨ base + count ≤ address) :
    Function.update (writeCells ram base count f) (word address) value =
      writeCells (Function.update ram (word address) value) base count f := by
  funext cell
  simp only [writeCells, Function.update_apply]
  by_cases hit : cell = word address
  · subst hit
    rw [if_pos rfl, toNat_word_of_lt small, if_neg (by omega), if_pos rfl]
  · rw [if_neg hit]
    split <;> rfl

/-- A block that already holds the words of `f` is unchanged by writing them. -/
theorem writeCells_self (ram : Word → Word) (base count : Nat) (f : Nat → Nat)
    (holds : ∀ index, index < count → ram (word (base + index)) = word (f index)) :
    writeCells ram base count f = ram := by
  funext address
  simp only [writeCells]
  split
  · rename_i inside
    rw [← holds _ (by omega), Nat.add_sub_cancel' inside.1, word_toNat]
  · rfl

/-- A cell update inside a block is overwritten by the block. -/
theorem writeCells_update_in (ram : Word → Word) (base count address : Nat) (f : Nat → Nat)
    (value : Word) (small : address < 2 ^ 256) (inside : base ≤ address ∧ address < base + count) :
    writeCells (Function.update ram (word address) value) base count f = writeCells ram base count f := by
  funext cell
  simp only [writeCells, Function.update_apply]
  split
  · rfl
  · rename_i outside
    rw [if_neg]
    intro same
    apply outside
    rw [same, toNat_word_of_lt small]
    exact inside

/-- A block inside a larger block is overwritten by it. -/
theorem writeCells_writeCells_sub (ram : Word → Word) (inner count base width : Nat) (f g : Nat → Nat)
    (sub : base ≤ inner ∧ inner + count ≤ base + width) :
    writeCells (writeCells ram inner count f) base width g = writeCells ram base width g := by
  funext cell
  simp only [writeCells]
  split
  · rfl
  · rw [if_neg (by omega)]

/-- Two memories that agree outside a block agree after writing it. -/
theorem writeCells_agree (first second : Word → Word) (base count : Nat) (f : Nat → Nat)
    (agree : ∀ address : Word, ¬ (base ≤ address.toNat ∧ address.toNat < base + count) →
      first address = second address) :
    writeCells first base count f = writeCells second base count f := by
  funext cell
  simp only [writeCells]
  split
  · rfl
  · rename_i outside; exact agree cell outside

end BigInt

end Kriterion.ArgoMAC.PlanB.SimMachine
