/-
**The laws of stage 1's unrolled cell blocks.**

`Prog.rep` appends at the back, `optionProduct` peels at the front; `memSem_rep_front` peels a
`rep` at the front, and `memSem_rep_law` turns a `rep` of independent draws, each stored by a
`step`, into `optionProduct` followed by `foldStore`. Instances:

* `memSem_fields`: the `42,052` field cells, as `fieldCellLaw` draws;
* `memSem_words`: the byte, fold-join and key cells, as `wordLaw` draws.

`foldStore_ram_at` / `foldStore_ram_off` read the RAM a fold of stores leaves.
-/

import Proof.Simulator.CutoffSamplers
import Proof.Simulator.Emit

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

section Reps

variable [FieldCertificate]

/-- **A `rep` peeled at the front.** -/
theorem memSem_rep_front (count : Nat) (body : Nat → Prog) (memory : Memory) :
    (Prog.rep (count + 1) body).memSem memory =
      ((body 0).memSem memory).bind
        (kleisli (Prog.rep count fun index => body (index + 1)).memSem) := by
  induction count generalizing memory with
  | zero =>
      have right : ((body 0).memSem memory).bind
          (kleisli (Prog.rep 0 fun index => body (index + 1)).memSem) = (body 0).memSem memory := by
        conv_rhs => rw [← PMF.bind_pure ((body 0).memSem memory)]
        congr 1
        funext result
        cases result <;> (rw [Prog.rep.eq_1]; rfl)
      rw [right, Prog.rep.eq_2, memSem_seq, Prog.rep.eq_1]
      simp only [Prog.memSem, PMF.pure_bind]
      rfl
  | succ count ih =>
      rw [Prog.rep, memSem_seq, ih, PMF.bind_bind]
      conv_rhs => rw [Prog.rep]
      congr 1
      funext result
      rw [kleisli_bind]
      congr 1

/-- A fold of stores, one per draw, front first. -/
def foldStore {α : Type} (step : Nat → Memory → α → Memory) :
    (count : Nat) → Memory → (Fin count → α) → Memory
  | 0, memory, _ => memory
  | count + 1, memory, values =>
      foldStore (fun index => step (index + 1)) count (step 0 memory (values 0))
        (fun index => values index.succ)

/-- **A `rep` of independent draws.** If every body draws from `law` and stores by `step`, the
`rep` draws independently and folds the stores. -/
theorem memSem_rep_law {α : Type} (law : PMF (Option α)) :
    ∀ (count : Nat) (body : Nat → Prog) (step : Nat → Memory → α → Memory),
      (∀ index memory, (body index).memSem memory = law.map (Option.map (step index memory))) →
      ∀ memory, (Prog.rep count body).memSem memory =
        (optionProduct count fun _ => law).map (Option.map (foldStore step count memory))
  | 0, body, step, _, memory => by
      rw [Prog.rep]
      simp only [Prog.memSem, optionProduct, PMF.pure_map, Option.map_some]
      rfl
  | count + 1, body, step, each, memory => by
      rw [memSem_rep_front, each 0 memory, PMF.bind_map]
      simp only [optionProduct]
      rw [PMF.map_bind]
      congr 1
      funext drawn
      cases drawn with
      | none => simp [kleisli, PMF.pure_map]
      | some value =>
          simp only [Function.comp_apply, Option.map_some, kleisli]
          rw [memSem_rep_law law count (fun index => body (index + 1))
            (fun index => step (index + 1)) (fun index memory => each (index + 1) memory),
            PMF.map_comp]
          congr 1
          funext values
          cases values with
          | none => rfl
          | some values =>
              simp only [Function.comp_apply, Option.map_some, foldStore, Fin.cons_zero,
                Fin.cons_succ]

/-! ### The RAM a fold of stores leaves -/

omit [FieldCertificate] in
/-- A fold of stores does not touch the stacks. -/
theorem foldStore_bits {α : Type} (step : Nat → Memory → α → Memory)
    (keeps : ∀ index memory value, (step index memory value).bits = memory.bits) :
    ∀ (count : Nat) (memory : Memory) (values : Fin count → α),
      (foldStore step count memory values).bits = memory.bits
  | 0, _, _ => rfl
  | count + 1, memory, values => by
      rw [foldStore, foldStore_bits _ (fun index => keeps (index + 1)), keeps]

/-- Addresses a fold of stores does not write keep their contents. -/
theorem foldStore_ram_off {α : Type} (step : Nat → Memory → α → Memory) (address : Nat → Word)
    (encode : α → Word)
    (stores : ∀ index memory value,
      (step index memory value).ram = Function.update memory.ram (address index) (encode value)) :
    ∀ (count : Nat) (memory : Memory) (values : Fin count → α) (target : Word),
      (∀ index, index < count → target ≠ address index) →
      (foldStore step count memory values).ram target = memory.ram target
  | 0, _, _, _, _ => rfl
  | count + 1, memory, values, target, away => by
      rw [foldStore, foldStore_ram_off _ (fun index => address (index + 1)) encode
        (fun index => stores (index + 1)) count _ _ target
        (fun index bound => away (index + 1) (by omega)), stores,
        Function.update_of_ne (away 0 (by omega))]

/-- The address a fold stores at holds the stored draw. -/
theorem foldStore_ram_at {α : Type} (step : Nat → Memory → α → Memory) (address : Nat → Word)
    (encode : α → Word)
    (stores : ∀ index memory value,
      (step index memory value).ram = Function.update memory.ram (address index) (encode value)) :
    ∀ (count : Nat),
      (∀ first second, first < count → second < count → first ≠ second →
        address first ≠ address second) →
      ∀ (memory : Memory) (values : Fin count → α) (index : Fin count),
        (foldStore step count memory values).ram (address index) = encode (values index)
  | 0, _, _, _, index => index.elim0
  | count + 1, distinct, memory, values, index => by
      rw [foldStore]
      cases index using Fin.cases with
      | zero =>
          show (foldStore (fun index => step (index + 1)) count (step 0 memory (values 0))
            fun index => values index.succ).ram (address 0) = encode (values 0)
          rw [foldStore_ram_off _ (fun index => address (index + 1)) encode
            (fun index => stores (index + 1)) count _ _ _
            (fun later bound => distinct 0 (later + 1) (by omega) (by omega) (by omega)), stores,
            Function.update_self]
      | succ index =>
          have := foldStore_ram_at (fun index => step (index + 1)) (fun index => address (index + 1))
            encode (fun index => stores (index + 1)) count
            (fun first second firstBound secondBound different =>
              distinct (first + 1) (second + 1) (by omega) (by omega) (by omega))
            (step 0 memory (values 0)) (fun index => values index.succ) index
          simpa only [Fin.val_succ] using this

/- `foldStore` is sealed: a fold over `10^5` draws must never be unfolded by a defeq check; its
equation lemmas remain available. -/
attribute [irreducible] foldStore

/-- `word` is injective below `2 ^ 256`. -/
theorem word_injective {first second : Nat} (firstSmall : first < 2 ^ 256)
    (secondSmall : second < 2 ^ 256) (same : word first = word second) : first = second := by
  have := congrArg BitVec.toNat same
  simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt firstSmall,
    Nat.mod_eq_of_lt secondSmall] at this
  exact this

/-! ### The cells -/

/-- The store of one field cell. -/
def cellStep (base : Nat) (index : Nat) (memory : Memory) (value : BaseField) : Memory :=
  clearRegs (storeRam memory (word (base + index)) (BitVec.ofNat 256 value.val)) samplerScratch

/-- The store of one word cell. -/
def wordStep (base : Nat) (index : Nat) (memory : Memory) (value : Nat) : Memory :=
  clearRegs (storeRam memory (word (base + index)) (BitVec.ofNat 256 value)) [rAcc, rBit, rAddr]

/-- **A field cell, as a field element.** -/
theorem memSem_fieldCell_field (address : Nat) (memory : Memory) :
    (Stage1.fieldCell address).memSem memory =
      fieldCellLaw.map (Option.map fun value : BaseField =>
        clearRegs (storeRam memory (word address) (BitVec.ofNat 256 value.val)) samplerScratch) := by
  rw [memSem_fieldCell, fieldCellLaw, PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  apply PMF.bind_congr
  intro drawn member
  cases drawn with
  | none => rfl
  | some value =>
      have good := rejectLaw_support _ _ _ _ member
      simp only [decide_eq_true_eq] at good
      simp only [Function.comp_apply, Option.map_some]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (show value < baseFieldModulus from good.1)]

/-- **A word cell.** -/
theorem memSem_wordCell (width address : Nat) (small : width ≤ 256) (memory : Memory) :
    (Stage1.wordCell width address).memSem memory =
      (wordLaw width).map fun value : Nat =>
        some (clearRegs (storeRam memory (word address) (BitVec.ofNat 256 value))
          [rAcc, rBit, rAddr]) := by
  unfold Stage1.wordCell
  rw [memSem_seq, memSem_sampleWord, PMF.bind_map, wordLaw, PMF.map_comp, ← PMF.bind_pure_comp]
  congr 1
  funext value
  simp only [Function.comp_apply, kleisli]
  rw [memSem_seq]
  simp only [storeAt, cst, Prog.memSem, Op.memSem, PMF.pure_bind, kleisli, memSem_zeroRegs]
  congr 2
  rw [clearRegs_eq_iff]
  refine ⟨?_, ?_, fun index outside => ?_⟩
  · simp only [storeRam, setReg_registers, if_pos rfl, (clearRegs_other _ _).1]
    rw [show (wordMem (setReg memory rAcc 0) width value.val).registers rAcc =
      BitVec.ofNat 256 value.val from wordMem_acc memory width value.val]
    rfl
  · rfl
  · simp only [storeRam, setReg_registers]
    have notAddr : index ≠ rAddr := fun same => outside (by simp [same])
    have notAcc : index ≠ rAcc := fun same => outside (by simp [same])
    have notBit : index ≠ rBit := fun same => outside (by simp [same])
    rw [if_neg notAddr]
    exact wordMem_other memory width value.val index notAcc notBit

/-- **The field cells.** -/
theorem memSem_fields (base count : Nat) (memory : Memory) :
    (Prog.rep count fun index => Stage1.fieldCell (base + index)).memSem memory =
      (optionProduct count fun _ => fieldCellLaw).map
        (Option.map (foldStore (cellStep base) count memory)) :=
  memSem_rep_law fieldCellLaw count _ (cellStep base)
    (fun index memory => memSem_fieldCell_field (base + index) memory) memory

/-- **The word cells.** -/
theorem memSem_words (width base count : Nat) (small : width ≤ 256) (memory : Memory) :
    (Prog.rep count fun index => Stage1.wordCell width (base + index)).memSem memory =
      (optionProduct count fun _ => (wordLaw width).map some).map
        (Option.map (foldStore (wordStep base) count memory)) := by
  refine memSem_rep_law _ count _ (wordStep base) (fun index memory => ?_) memory
  rw [memSem_wordCell width (base + index) small, PMF.map_comp]
  rfl

theorem cellStep_ram (base index : Nat) (memory : Memory) (value : BaseField) :
    (cellStep base index memory value).ram =
      Function.update memory.ram (word (base + index)) (BitVec.ofNat 256 value.val) := by
  simp only [cellStep, (clearRegs_other _ _).1, storeRam]

theorem cellStep_bits (base index : Nat) (memory : Memory) (value : BaseField) :
    (cellStep base index memory value).bits = memory.bits := by
  simp only [cellStep, (clearRegs_other _ _).2, storeRam]

theorem wordStep_ram (base index : Nat) (memory : Memory) (value : Nat) :
    (wordStep base index memory value).ram =
      Function.update memory.ram (word (base + index)) (BitVec.ofNat 256 value) := by
  simp only [wordStep, (clearRegs_other _ _).1, storeRam]

theorem wordStep_bits (base index : Nat) (memory : Memory) (value : Nat) :
    (wordStep base index memory value).bits = memory.bits := by
  simp only [wordStep, (clearRegs_other _ _).2, storeRam]

end Reps

end

end Kriterion.ArgoMAC.PlanB.SimMachine
