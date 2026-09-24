/-
**Phase 3, P4b — chunk `0` of a lane in the refill run: the fold.**

Chunk `0` is `firstChunkBits = 2` wide (the ragged-first profile). For a width-2 chunk, the
evaluator's fold asks exactly two questions: the two halves `i₀ = hot(lane, chunk, 1, e, false)`,
`i₁ = …true` of the inactive level-1 gate `e = (α mod 2) xor 1`, both at the level-1 label
`W = join 0 xor bitLabel 0` (`runRefillT_evalFold_two`). Every one-hot label it returns is a fixed
block XOR the fold material `a₀ xor a₁` of the two answers (`foldLabels_linear`), in particular
`E*`. The switch masks that follow are hash queries (`Masks.lean`).
-/

import Proof.Privacy.Phase3.Lazy.DetRun

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### The fold of a width-2 chunk, as a program -/

/-- The inactive level-1 gate of a chunk with cleartext value `value`. -/
def inactiveEntry (value : Nat) : Nat := 1 - value % 2

/-- The one-hot labels of a width-2 chunk, as a function of the fold material. -/
def foldLabels (value : Nat) (bitLabel join : Nat → Block) (material : Block) :
    Fin (2 ^ 2) → Block :=
  extendLevel 1 (fun _ => join 0 ^^^ bitLabel 0) fun entry =>
    if entry = activeAt value 1 then join 1 ^^^ bitLabel 1 ^^^ material else material

/-- **Every one-hot label is a fixed block XOR the fold material.** -/
theorem foldLabels_linear (value : Nat) (bitLabel join : Nat → Block) (material : Block)
    (entry : Fin (2 ^ 2)) :
    foldLabels value bitLabel join material entry =
      foldLabels value bitLabel join 0 entry ^^^ material := by
  unfold foldLabels extendLevel
  dsimp only
  split_ifs <;> simp [BitVec.xor_assoc]

section Program

variable {α : Type}

theorem vector_one (f : Fin 1 → FreeQuery Programs.Spec α) :
    FreeQuery.vector 1 f =
      f 0 >>= fun value => (Pure.pure (#v[].push value) : FreeQuery Programs.Spec (Vector α 1)) :=
  rfl

theorem vector_two (f : Fin (2 ^ 1) → FreeQuery Programs.Spec α) :
    FreeQuery.vector (2 ^ 1) f =
      f ⟨0, by decide⟩ >>= fun first => f ⟨1, by decide⟩ >>= fun second =>
        (Pure.pure ((#v[].push first).push second) : FreeQuery Programs.Spec (Vector α 2)) := by
  show (f ⟨0, by decide⟩ >>= fun value =>
      (Pure.pure (#v[].push value) : FreeQuery Programs.Spec (Vector α 1))) >>= (fun values =>
    f ⟨1, by decide⟩ >>= fun value => Pure.pure (values.push value)) = _
  rw [fq_bind_assoc]
  rfl

theorem xorFoldExcept_two_zero (family : Fin (2 ^ 1) → Block) :
    xorFoldExcept ⟨0, by decide⟩ family = family ⟨1, by decide⟩ := by
  simp [xorFoldExcept, Fin.foldl_succ]

theorem xorFoldExcept_two_one (family : Fin (2 ^ 1) → Block) :
    xorFoldExcept ⟨1, by decide⟩ family = family ⟨0, by decide⟩ := by
  simp [xorFoldExcept, Fin.foldl_succ]

variable (lane : Lane) (chunk : Fin chunkCount) (value : Nat) (bitLabel join : Nat → Block)

/-- **The first level of the fold asks nothing**: both level-1 labels are `join 0 xor bitLabel 0`. -/
theorem evalFoldM_one :
    Programs.evalFoldM lane chunk value bitLabel join 1 =
      Pure.pure (fun _ => join 0 ^^^ bitLabel 0) := by
  show Programs.evalStepM lane chunk 0 (bitLabel 0) (join 0) (activeAt value 0) (fun _ => 0) >>=
    (fun right => (Pure.pure (extendLevel 0 (fun _ => 0) right) :
      FreeQuery Programs.Spec (Fin (2 ^ 1) → Block))) = _
  have only : (0 : Fin 1) = activeAt value 0 := Subsingleton.elim _ _
  unfold Programs.evalStepM
  show (FreeQuery.vector 1 (fun entry : Fin 1 => if entry = activeAt value 0 then
      (Pure.pure 0 : FreeQuery Programs.Spec Block) else
      Programs.foldMaskM lane chunk 0 entry.val ((fun _ => 0) entry)) >>= _) >>= _ = _
  rw [vector_one, if_pos only]
  show (Pure.pure (extendLevel 0 (fun _ => 0) fun entry : Fin 1 =>
    if entry = activeAt value 0 then join 0 ^^^ bitLabel 0 ^^^
      xorFoldExcept (activeAt value 0) (#v[].push (0 : Block)).get
    else (#v[].push (0 : Block)).get entry) : FreeQuery Programs.Spec (Fin (2 ^ 1) → Block)) = _
  congr 1
  funext entry
  have zero : ∀ e : Fin 1, e = activeAt value 0 := fun e => Subsingleton.elim _ _
  have fold : xorFoldExcept (activeAt value 0) (#v[].push (0 : Block)).get = 0 := by
    rw [← only]
    exact xorFoldExcept_one _
  unfold extendLevel
  dsimp only
  split
  · rw [if_pos (zero _), fold]
    simp
  · rw [if_pos (zero _), fold]
    simp

/-- **The fold of a width-2 chunk is one fold gate**: the material of the inactive level-1 gate at
the level-1 label, then the labels. -/
theorem evalFoldM_two :
    Programs.evalFoldM lane chunk value bitLabel join 2 =
      Programs.foldMaskM lane chunk 1 (inactiveEntry value) (join 0 ^^^ bitLabel 0) >>=
        fun material => Pure.pure (foldLabels value bitLabel join material) := by
  show Programs.evalFoldM lane chunk value bitLabel join 1 >>= (fun previous =>
    Programs.evalStepM lane chunk 1 (bitLabel 1) (join 1) (activeAt value 1) previous >>=
      fun right => (Pure.pure (extendLevel 1 previous right) :
        FreeQuery Programs.Spec (Fin (2 ^ 2) → Block))) = _
  rw [evalFoldM_one, fq_pure_bind]
  unfold foldLabels
  rcases Nat.mod_two_eq_zero_or_one value with even | odd
  · have active : activeAt value 1 = ⟨0, by decide⟩ := Fin.ext (by simp [activeAt, even])
    have inactive : inactiveEntry value = 1 := by simp [inactiveEntry, even]
    rw [active, inactive]
    unfold Programs.evalStepM
    rw [fq_bind_assoc, vector_two, if_pos rfl, if_neg (by decide), fq_pure_bind, fq_bind_assoc]
    refine congrArg _ (funext fun material => ?_)
    show (Pure.pure (extendLevel 1 (fun _ => join 0 ^^^ bitLabel 0) fun entry =>
      if entry = ⟨0, by decide⟩ then join 1 ^^^ bitLabel 1 ^^^
        xorFoldExcept ⟨0, by decide⟩ ((#v[].push (0 : Block)).push material).get
      else ((#v[].push (0 : Block)).push material).get entry) :
        FreeQuery Programs.Spec (Fin (2 ^ 2) → Block)) = _
    congr 2
    funext gate
    split
    · rw [xorFoldExcept_two_zero]
      rfl
    · rename_i notZero
      have one : gate = ⟨1, by decide⟩ := by
        apply Fin.ext
        have bound := gate.isLt
        have nonzero : gate.val ≠ 0 := fun same => notZero (Fin.ext same)
        simp only [pow_one] at bound
        show gate.val = 1
        omega
      rw [one]
      rfl
  · have active : activeAt value 1 = ⟨1, by decide⟩ := Fin.ext (by simp [activeAt, odd])
    have inactive : inactiveEntry value = 0 := by simp [inactiveEntry, odd]
    rw [active, inactive]
    unfold Programs.evalStepM
    rw [fq_bind_assoc, vector_two, if_neg (by decide), fq_bind_assoc]
    refine congrArg _ (funext fun material => ?_)
    rw [if_pos rfl, fq_pure_bind]
    show (Pure.pure (extendLevel 1 (fun _ => join 0 ^^^ bitLabel 0) fun entry =>
      if entry = ⟨1, by decide⟩ then join 1 ^^^ bitLabel 1 ^^^
        xorFoldExcept ⟨1, by decide⟩ ((#v[].push material).push (0 : Block)).get
      else ((#v[].push material).push (0 : Block)).get entry) :
        FreeQuery Programs.Spec (Fin (2 ^ 2) → Block)) = _
    congr 2
    funext gate
    split
    · rw [xorFoldExcept_two_one]
      rfl
    · rename_i notOne
      have zero : gate = ⟨0, by decide⟩ := by
        apply Fin.ext
        have bound := gate.isLt
        have nonone : gate.val ≠ 1 := fun same => notOne (Fin.ext same)
        simp only [pow_one] at bound
        show gate.val = 0
        omega
      rw [zero]
      rfl

end Program

/-! ### The fold in the refill run -/

section Run

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
  (bits : BitInput) (draw : Cell → PMF (Block × Block))

/-- **The fold gate in the run**: two lazy forward queries at the gate's halves, at its label. -/
theorem runRefillT_foldMaskM {β : Type} (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat)
    (label : Block) (k : Block → FreeQuery Programs.Spec β) (oracle : LState) (record : Record)
    (touched : Set Cell) :
    runRefillT bits draw (Programs.foldMaskM lane chunk step entry label >>= k) oracle record
        touched =
      (forwardAnswer (hotIndexNat lane chunk step entry false) label oracle).bind fun first =>
        (forwardAnswer (hotIndexNat lane chunk step entry true) label first.2).bind fun second =>
          runRefillT bits draw (k (first.1 ^^^ second.1)) second.2 record
            (touch (.fixedForward (hotIndexNat lane chunk step entry true) label)
              (touch (.fixedForward (hotIndexNat lane chunk step entry false) label) touched)) := by
  show runRefillT bits draw (.query (.fixedForward (hotIndexNat lane chunk step entry false) label)
      fun (first : Block) => .query (.fixedForward (hotIndexNat lane chunk step entry true) label)
        fun (second : Block) => k ((first ^^^ label) ^^^ (second ^^^ label))) oracle record
    touched = _
  refine (runRefillT_lazy bits draw _ _ oracle record touched rfl rfl).trans ?_
  refine congrArg _ (funext fun first => ?_)
  refine (runRefillT_lazy bits draw _ _ _ record _ rfl rfl).trans ?_
  refine congrArg _ (funext fun second => ?_)
  have cancel : ∀ a b : Block, (a ^^^ label) ^^^ (b ^^^ label) = a ^^^ b := by
    intro a b
    rw [BitVec.xor_assoc, BitVec.xor_comm label, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]
  exact congrArg (fun x => runRefillT bits draw (k x) second.2 record _)
    (cancel first.1 second.1)

/-- **(a) The fold of a width-2 chunk in the refill run**: two lazy queries at the halves of the
inactive level-1 gate, at the label `W = join 0 xor bitLabel 0`; the labels are
`foldLabels (a₀ xor a₁)`. -/
theorem runRefillT_evalFold_two {β : Type} (lane : Lane) (chunk : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) (k : (Fin (2 ^ 2) → Block) → FreeQuery Programs.Spec β)
    (oracle : LState) (record : Record) (touched : Set Cell) :
    runRefillT bits draw (Programs.evalFoldM lane chunk value bitLabel join 2 >>= k) oracle record
        touched =
      (forwardAnswer (hotIndexNat lane chunk 1 (inactiveEntry value) false)
          (join 0 ^^^ bitLabel 0) oracle).bind fun first =>
        (forwardAnswer (hotIndexNat lane chunk 1 (inactiveEntry value) true)
            (join 0 ^^^ bitLabel 0) first.2).bind fun second =>
          runRefillT bits draw (k (foldLabels value bitLabel join (first.1 ^^^ second.1)))
            second.2 record
            (touch (.fixedForward (hotIndexNat lane chunk 1 (inactiveEntry value) true)
                (join 0 ^^^ bitLabel 0))
              (touch (.fixedForward (hotIndexNat lane chunk 1 (inactiveEntry value) false)
                (join 0 ^^^ bitLabel 0)) touched)) := by
  rw [evalFoldM_two, fq_bind_assoc]
  exact runRefillT_foldMaskM bits draw lane chunk 1 _ _ _ oracle record touched

end Run

end

end Kriterion.ArgoMAC.Phase3.Lazy
