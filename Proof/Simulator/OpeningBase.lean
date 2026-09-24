/-
**The opening's toolkit** (stage 2, part 2: `Opening.program`).

* straight-line memory laws (`memSem_pure_seq`, `memSem_cst_seq`, `memSem_ar_val`,
  `memSem_loadAt`, `memSem_storeAt`, …): the opening is oracle-free until its programs, so its
  blocks are read through `Prog.memSem`;
* `withRam`, `putPoint`, `pointWords`: how a phase leaves its memory (a RAM update, the scratch
  registers cleared);
* `OpenCell`, `SameOff`: the opening's own cells (the region `openBase + [0, 2^12)` of digit
  points, randomisers and lifted rows, the designated vector's cells and the preimage sampler's
  region) and "unchanged off them"; the non-collectors also add to the accumulators, which
  `OpeningFree` tracks cell by cell.
-/

import Proof.Simulator.ReplayFold

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Straight-line memory laws -/

theorem memSem_pure_seq {first rest : Prog} {memory after : Memory}
    (step : first.memSem memory = PMF.pure (some after)) :
    (Prog.seq first rest).memSem memory = rest.memSem after := by
  rw [memSem_seq, step, PMF.pure_bind]
  rfl

theorem memSem_skip (count : Nat) (memory : Memory) :
    (Prog.skip count).memSem memory = PMF.pure (some memory) := rfl

theorem memSem_cst (target : Register) (value : Nat) (memory : Memory) :
    (cst target value).memSem memory = PMF.pure (some (setReg memory target (word value))) := rfl

theorem memSem_cst_seq (target : Register) (value : Nat) (rest : Prog) (memory : Memory) :
    (Prog.seq (cst target value) rest).memSem memory =
      rest.memSem (setReg memory target (word value)) :=
  memSem_pure_seq (memSem_cst target value memory)

theorem memSem_ar_val (operation : Arithmetic) (target left right : Register) (rest : Prog)
    (memory : Memory) (first second : Word) (hfirst : memory.registers left = first)
    (hsecond : memory.registers right = second) :
    (Prog.seq (ar operation target left right) rest).memSem memory =
      rest.memSem (setReg memory target (operation.eval first second)) := by
  rw [← hfirst, ← hsecond]
  exact memSem_pure_seq rfl

theorem memSem_ar (operation : Arithmetic) (target left right : Register) (memory : Memory)
    (first second : Word) (hfirst : memory.registers left = first)
    (hsecond : memory.registers right = second) :
    (ar operation target left right).memSem memory =
      PMF.pure (some (setReg memory target (operation.eval first second))) := by
  rw [← hfirst, ← hsecond]
  rfl

theorem memSem_loadAt (target : Register) (address : Nat) (memory : Memory) :
    (loadAt target address).memSem memory =
      PMF.pure (some (setReg (setReg memory rAddr (word address)) target
        (memory.ram (word address)))) := by
  rw [loadAt, memSem_cst_seq]
  rfl

theorem memSem_loadAt_seq (target : Register) (address : Nat) (rest : Prog) (memory : Memory) :
    (Prog.seq (loadAt target address) rest).memSem memory =
      rest.memSem (setReg (setReg memory rAddr (word address)) target
        (memory.ram (word address))) :=
  memSem_pure_seq (memSem_loadAt target address memory)

theorem memSem_storeAt (address : Nat) (source : Register) (memory : Memory)
    (other : source ≠ rAddr) :
    (storeAt address source).memSem memory =
      PMF.pure (some (storeRam (setReg memory rAddr (word address)) (word address)
        (memory.registers source))) := by
  rw [storeAt, memSem_cst_seq]
  show PMF.pure (some (storeRam (setReg memory rAddr (word address))
    ((setReg memory rAddr (word address)).registers rAddr)
    ((setReg memory rAddr (word address)).registers source))) = _
  simp only [setReg_registers, if_neg other, ↓reduceIte]

theorem memSem_storeAt_seq (address : Nat) (source : Register) (rest : Prog) (memory : Memory)
    (other : source ≠ rAddr) :
    (Prog.seq (storeAt address source) rest).memSem memory =
      rest.memSem (storeRam (setReg memory rAddr (word address)) (word address)
        (memory.registers source)) :=
  memSem_pure_seq (memSem_storeAt address source memory other)

theorem memSem_zeroRegs_seq (registers : List Register) (rest : Prog) (memory : Memory) :
    (Prog.seq (zeroRegs registers) rest).memSem memory =
      rest.memSem (clearRegs memory registers) :=
  memSem_pure_seq (memSem_zeroRegs registers memory)

theorem memSem_rep_succ (count : Nat) (body : Nat → Prog) (memory : Memory) :
    (Prog.rep (count + 1) body).memSem memory =
      ((Prog.rep count body).memSem memory).bind (kleisli (body count).memSem) := by
  rw [Prog.rep, memSem_seq]

/-! ### Memories after a phase -/

/-- The memory with its RAM replaced. -/
def withRam (memory : Memory) (ram : Word → Word) : Memory := { memory with ram := ram }

omit [FieldCertificate] in
@[simp] theorem withRam_ram (memory : Memory) (ram : Word → Word) :
    (withRam memory ram).ram = ram := rfl

omit [FieldCertificate] in
@[simp] theorem withRam_bits (memory : Memory) (ram : Word → Word) :
    (withRam memory ram).bits = memory.bits := rfl

omit [FieldCertificate] in
@[simp] theorem withRam_registers (memory : Memory) (ram : Word → Word) :
    (withRam memory ram).registers = memory.registers := rfl

omit [FieldCertificate] in
/-- A memory is determined, up to the cleared registers, by its RAM, stacks and other
registers. -/
theorem clearRegs_withRam_eq (after memory : Memory) (registers : List Register)
    (ram : Word → Word) (sameRam : after.ram = ram) (sameBits : after.bits = memory.bits)
    (sameRegs : ∀ index, index ∉ registers → after.registers index = memory.registers index) :
    clearRegs after registers = clearRegs (withRam memory ram) registers := by
  rw [clearRegs_eq_iff]
  exact ⟨sameRam, sameBits, sameRegs⟩

/-- The three words of a point register, as `writePoint` lays them out. -/
def pointWords (point : Point) : Word × Word × Word :=
  match point with
  | .zero => (0, 0, 0)
  | .some x y _ => (1, BitVec.ofNat 256 x.val, BitVec.ofNat 256 y.val)

omit [FieldCertificate] in
/-- Three consecutive RAM words. -/
def putPoint (ram : Word → Word) (base : Nat) (words : Word × Word × Word) : Word → Word :=
  Function.update (Function.update (Function.update ram (word base) words.1)
    (word (base + 1)) words.2.1) (word (base + 2)) words.2.2

/-! ### The opening's own cells -/

/-- The opening's own cells: its region `openBase + [0, 2^12)`, the `455` cells of the designated
vector and the preimage sampler's region `samplerBase + [0, 2^11)`. -/
def OpenCell (address : Word) : Prop :=
  (openBase ≤ address.toNat ∧ address.toNat < openBase + 2 ^ 12) ∨
    (designatedBase ≤ address.toNat ∧ address.toNat < designatedBase + 455) ∨
    (samplerBase ≤ address.toNat ∧ address.toNat < samplerBase + 2 ^ 11)

omit [FieldCertificate] in
theorem openCell_word (offset : Nat) (small : offset < 2 ^ 12) :
    OpenCell (word (openBase + offset)) := by
  left
  rw [word_small (by unfold openBase; omega)]
  omega

omit [FieldCertificate] in
theorem openCell_designated (element : Nat) (small : element < 455) :
    OpenCell (word (designatedCell element)) := by
  right; left
  unfold designatedCell
  rw [word_small (by unfold designatedBase; omega)]
  omega

omit [FieldCertificate] in
/-- A cell below the opening's region is not one of the opening's cells. -/
theorem not_openCell (address : Nat) (below : address < openBase) : ¬ OpenCell (word address) := by
  have small : address < 2 ^ 256 := by unfold openBase at below; omega
  unfold OpenCell
  rw [word_small small]
  unfold openBase designatedBase samplerBase at *
  omega

omit [FieldCertificate] in
/-- `after` agrees with `before` off the opening's own cells. -/
def SameOff (before after : Word → Word) : Prop :=
  ∀ address, ¬ OpenCell address → after address = before address

omit [FieldCertificate] in
theorem SameOff.refl (ram : Word → Word) : SameOff ram ram := fun _ _ => rfl

omit [FieldCertificate] in
theorem SameOff.trans {first second third : Word → Word} (one : SameOff first second)
    (two : SameOff second third) : SameOff first third :=
  fun address outside => (two address outside).trans (one address outside)

omit [FieldCertificate] in
theorem sameOff_update (ram : Word → Word) {address : Word} (inside : OpenCell address)
    (value : Word) : SameOff ram (Function.update ram address value) := by
  intro other outside
  rw [Function.update_of_ne (fun same => outside (by rw [same]; exact inside))]

omit [FieldCertificate] in
theorem sameOff_putPoint (ram : Word → Word) (offset : Nat) (small : offset + 2 < 2 ^ 12)
    (words : Word × Word × Word) : SameOff ram (putPoint ram (openBase + offset) words) := by
  unfold putPoint
  refine ((sameOff_update _ (openCell_word _ (by omega)) _).trans
    (sameOff_update _ ?_ _)).trans (sameOff_update _ ?_ _)
  · rw [Nat.add_assoc]; exact openCell_word _ (by omega)
  · rw [Nat.add_assoc]; exact openCell_word _ (by omega)

omit [FieldCertificate] in
/-- The word at position `j` of a point triple. -/
def wordAt (words : Word × Word × Word) : Nat → Word
  | 0 => words.1
  | 1 => words.2.1
  | _ => words.2.2

theorem putPoint_at (ram : Word → Word) (base : Nat) (words : Word × Word × Word) (index : Nat)
    (small : base + 2 < 2 ^ 256) (inside : index < 3) :
    putPoint ram base words (word (base + index)) = wordAt words index := by
  unfold putPoint
  have ne01 : word base ≠ word (base + 1) := word_ne (by omega) (by omega) (by omega)
  have ne02 : word base ≠ word (base + 2) := word_ne (by omega) (by omega) (by omega)
  have ne12 : word (base + 1) ≠ word (base + 2) := word_ne (by omega) (by omega) (by omega)
  rcases (show index = 0 ∨ index = 1 ∨ index = 2 by omega) with same | same | same <;> subst same
  · simp only [Nat.add_zero]
    rw [Function.update_of_ne ne02, Function.update_of_ne ne01, Function.update_self]; rfl
  · rw [Function.update_of_ne ne12, Function.update_self]; rfl
  · rw [Function.update_self]; rfl

omit [FieldCertificate] in
theorem putPoint_off (ram : Word → Word) (base : Nat) (words : Word × Word × Word) (target : Word)
    (away : ∀ index, index < 3 → target ≠ word (base + index)) :
    putPoint ram base words target = ram target := by
  unfold putPoint
  rw [Function.update_of_ne (away 2 (by omega)), Function.update_of_ne (away 1 (by omega)),
    Function.update_of_ne (by simpa using away 0 (by omega))]

omit [FieldCertificate] in
/-- A property every step keeps holds after a fold of stores. -/
theorem foldStore_invariant {α : Type} (holds : Memory → Prop) :
    ∀ (step : Nat → Memory → α → Memory) (count : Nat),
      (∀ index, index < count → ∀ memory value, holds memory → holds (step index memory value)) →
      ∀ (memory : Memory) (values : Fin count → α), holds memory →
        holds (foldStore step count memory values)
  | _, 0, _, memory, _, start => by rw [foldStore]; exact start
  | step, count + 1, keeps, memory, values, start => by
      rw [foldStore]
      exact foldStore_invariant holds (fun index => step (index + 1)) count
        (fun index bound => keeps (index + 1) (by omega)) _ _
        (keeps 0 (by omega) memory (values 0) start)

omit [FieldCertificate] in
/-- Addresses a fold of point stores does not write keep their contents. -/
theorem foldStore_putPoint_off {α : Type} (step : Nat → Memory → α → Memory) (base : Nat → Nat)
    (encode : α → Word × Word × Word)
    (stores : ∀ index memory value,
      (step index memory value).ram = putPoint memory.ram (base index) (encode value)) :
    ∀ (count : Nat) (memory : Memory) (values : Fin count → α) (target : Word),
      (∀ index, index < count → ∀ position, position < 3 → target ≠ word (base index + position)) →
      (foldStore step count memory values).ram target = memory.ram target
  | 0, memory, _, _, _ => by rw [foldStore]
  | count + 1, memory, values, target, away => by
      rw [foldStore, foldStore_putPoint_off (fun index => step (index + 1)) (fun index => base (index + 1))
        encode (fun index => stores (index + 1)) count _ _ target
        (fun index bound => away (index + 1) (by omega)), stores,
        putPoint_off _ _ _ _ (away 0 (by omega))]

/-- The cells a fold of point stores writes hold the stored words. -/
theorem foldStore_putPoint_at {α : Type} (step : Nat → Memory → α → Memory) (base : Nat → Nat)
    (encode : α → Word × Word × Word)
    (stores : ∀ index memory value,
      (step index memory value).ram = putPoint memory.ram (base index) (encode value)) :
    ∀ (count : Nat),
      (∀ index, index < count → base index + 2 < 2 ^ 256) →
      (∀ first second, first < count → second < count → first ≠ second →
        ∀ position position', position < 3 → position' < 3 →
          word (base first + position) ≠ word (base second + position')) →
      ∀ (memory : Memory) (values : Fin count → α) (index : Fin count) (position : Nat),
        position < 3 →
        (foldStore step count memory values).ram (word (base index + position)) =
          wordAt (encode (values index)) position
  | 0, _, _, _, _, index, _, _ => index.elim0
  | count + 1, small, distinct, memory, values, index, position, inside => by
      rw [foldStore]
      cases index using Fin.cases with
      | zero =>
          show (foldStore (fun index => step (index + 1)) count (step 0 memory (values 0))
            fun index => values index.succ).ram (word (base 0 + position)) = _
          rw [foldStore_putPoint_off (fun index => step (index + 1)) (fun index => base (index + 1))
            encode (fun index => stores (index + 1)) count _ _ _
            (fun later bound position' inside' =>
              distinct 0 (later + 1) (by omega) (by omega) (by omega) position position' inside inside'),
            stores, putPoint_at _ _ _ _ (small 0 (by omega)) inside]
      | succ index =>
          have := foldStore_putPoint_at (fun index => step (index + 1)) (fun index => base (index + 1))
            encode (fun index => stores (index + 1)) count
            (fun index bound => small (index + 1) (by omega))
            (fun first second firstBound secondBound different =>
              distinct (first + 1) (second + 1) (by omega) (by omega) (by omega))
            (step 0 memory (values 0)) (fun index => values index.succ) index position inside
          simpa only [Fin.val_succ] using this

/-! ### Reps: congruence, splitting, nesting, index-dependent draws -/

/-- Two `rep`s with the same body laws have the same law. -/
theorem memSem_rep_congr (body body' : Nat → Prog) :
    ∀ (count : Nat), (∀ index, index < count → ∀ memory,
      (body index).memSem memory = (body' index).memSem memory) →
      ∀ memory, (Prog.rep count body).memSem memory = (Prog.rep count body').memSem memory
  | 0, _, memory => by rw [Prog.rep, Prog.rep]
  | count + 1, same, memory => by
      rw [memSem_rep_succ, memSem_rep_succ,
        memSem_rep_congr body body' count (fun index bound => same index (by omega)) memory]
      refine congrArg (PMF.bind _) (funext fun result => ?_)
      cases result with
      | none => rfl
      | some final => exact same count (by omega) final

/-- A sequence of two blocks is a `rep` of two. -/
theorem memSem_seq_rep_two (first second : Prog) (memory : Memory) :
    (Prog.seq first second).memSem memory =
      (Prog.rep 2 fun index => if index = 0 then first else second).memSem memory := by
  rw [memSem_rep_succ, memSem_rep_succ, Prog.rep, memSem_skip, PMF.pure_bind, memSem_seq]
  rfl

omit [FieldCertificate] in
theorem rep_congr (count : Nat) (body body' : Nat → Prog) (same : ∀ index, index < count → body index = body' index) :
    Prog.rep count body = Prog.rep count body' := by
  induction count with
  | zero => rw [Prog.rep, Prog.rep]
  | succ count ih =>
      rw [Prog.rep, Prog.rep, ih fun index bound => same index (by omega), same count (by omega)]

/-- A `rep` split after `first` bodies. -/
theorem memSem_rep_add (first : Nat) (body : Nat → Prog) :
    ∀ (second : Nat) (memory : Memory), (Prog.rep (first + second) body).memSem memory =
      ((Prog.rep first body).memSem memory).bind
        (kleisli (Prog.rep second fun index => body (first + index)).memSem)
  | 0, memory => by
      rw [Nat.add_zero]
      conv_lhs => rw [← PMF.bind_pure ((Prog.rep first body).memSem memory)]
      refine congrArg (PMF.bind _) (funext fun result => ?_)
      cases result <;> (rw [Prog.rep]; rfl)
  | second + 1, memory => by
      rw [← Nat.add_assoc, memSem_rep_succ, memSem_rep_add first body second memory, PMF.bind_bind]
      refine congrArg (PMF.bind _) (funext fun result => ?_)
      rw [kleisli_bind]
      refine congrArg (kleisli · result) (funext fun final => ?_)
      rw [memSem_rep_succ]

/-- **A nested `rep` is a flat one**, index `i ↦ (i / inner, i % inner)`. -/
theorem memSem_rep_nest (inner : Nat) (body : Nat → Nat → Prog) (innerPos : 0 < inner) :
    ∀ (outer : Nat) (memory : Memory),
      (Prog.rep outer fun digit => Prog.rep inner (body digit)).memSem memory =
        (Prog.rep (outer * inner) fun index => body (index / inner) (index % inner)).memSem memory
  | 0, memory => by rw [Nat.zero_mul, Prog.rep, Prog.rep]
  | outer + 1, memory => by
      rw [Nat.succ_mul, memSem_rep_succ, memSem_rep_add (outer * inner) _ inner,
        memSem_rep_nest inner body innerPos outer memory]
      refine congrArg (PMF.bind _) (funext fun result => ?_)
      rw [rep_congr inner (body outer) (fun index => body ((outer * inner + index) / inner)
        ((outer * inner + index) % inner)) (fun index bound => by
          congr 1
          · rw [Nat.add_comm, Nat.add_mul_div_right _ _ innerPos, Nat.div_eq_of_lt bound, Nat.zero_add]
          · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt bound])]

/-- **A `rep` of independent, index-dependent draws** under an invariant the stores keep. -/
theorem memSem_rep_law_idx {α : Type} (holds : Memory → Prop) :
    ∀ (count : Nat) (law : Nat → PMF (Option α)) (body : Nat → Prog)
      (step : Nat → Memory → α → Memory),
      (∀ index, index < count → ∀ memory, holds memory →
        (body index).memSem memory = (law index).map (Option.map (step index memory))) →
      (∀ index, index < count → ∀ memory value, holds memory → holds (step index memory value)) →
      ∀ memory, holds memory → (Prog.rep count body).memSem memory =
        (optionProduct count fun index => law index.val).map
          (Option.map (foldStore step count memory))
  | 0, law, body, step, _, _, memory, _ => by
      rw [Prog.rep]
      simp only [Prog.memSem, optionProduct, PMF.pure_map, Option.map_some]
      rw [foldStore]
  | count + 1, law, body, step, each, keeps, memory, start => by
      rw [memSem_rep_front, each 0 (by omega) memory start, PMF.bind_map]
      simp only [optionProduct]
      rw [PMF.map_bind]
      refine congrArg (PMF.bind _) (funext fun drawn => ?_)
      cases drawn with
      | none => simp [kleisli, PMF.pure_map]
      | some value =>
          simp only [Function.comp_apply, Option.map_some, kleisli]
          rw [memSem_rep_law_idx holds count (fun index => law (index + 1))
            (fun index => body (index + 1)) (fun index => step (index + 1))
            (fun index bound memory hm => each (index + 1) (by omega) memory hm)
            (fun index bound memory value hm => keeps (index + 1) (by omega) memory value hm)
            (step 0 memory value) (keeps 0 (by omega) memory value start), PMF.map_comp]
          refine congrArg (PMF.map · _) (funext fun values => ?_)
          cases values with
          | none => rfl
          | some values =>
              simp only [Function.comp_apply, Option.map_some]
              rw [foldStore]
              simp only [Fin.cons_zero, Fin.cons_succ]

omit [FieldCertificate] in
end

end Kriterion.ArgoMAC.PlanB.SimMachine
