/-
**Phase 3, P1r — `LawOn`, step (E), part 7: the garbler's published value on a table, with the
hidden fold material at every paid fold step and the hidden gadget answer at any position.**

A lane publishes one fold join per paid fold step (`LawsOff.foldJoin`: the two gate halves of every
entry of the step, and the step's zero label). The evaluator asks every entry of the step but the
active parent; so the active parent's first gate half hides the join (`foldJoin_splitW`). A digit's
digest hides its gadget answer at any position the view does not read (`pos`, `digest_splitW`).
Here the hidden indices take one gate half per (lane, paid fold step) and a gadget position per
digit (`hidW pos`, injective, `hidW_injective`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnETape

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState)
open scoped ENNReal

noncomputable section

/-! ### 1. The flat fold slots -/

/-- **A flat fold slot is its chunk's base plus its offset**, a paid step of its chunk. -/
theorem slot_decompose (slot : Fin foldStepCount) :
    slot.val = foldBase (slotChunk slot) + slotOffset slot ∧
      slotOffset slot < chunkWidth (slotChunk slot) - 1 :=
  slot_eq_foldBase_add slot

/-- A slot's step is paid: below its chunk's width. -/
theorem slot_step_lt (slot : Fin foldStepCount) : slotOffset slot + 1 < chunkWidth (slotChunk slot) := by
  have small := (slot_decompose slot).2
  have positive := chunkWidth_pos (slotChunk slot)
  omega

variable [FieldCertificate] [GroupCertificate] (input : AffineInput)
  (pos : Fin digitCount → Coord × Fin PlanB.coordinateBits)

/-! ### 2. Hidden indices -/

/-- The active parent's entry at a slot's step, as an entry of the step. -/
def activeAtSlot (lane : Lane) (slot : Fin foldStepCount) : Nat :=
  activeEntry input lane (slotChunk slot) (slotOffset slot + 1)

theorem activeAtSlot_lt (lane : Lane) (slot : Fin foldStepCount) :
    activeAtSlot input lane slot < 2 ^ (slotOffset slot + 1) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- **The hidden coins' indices**: the active parent's first gate half per (lane, paid fold step),
the gadget at `pos d` per digit. -/
def hidW : HiddenIdx → FixedIndex
  | .inl p => hotIndexNat p.1 (slotChunk p.2) (slotOffset p.2 + 1) (activeAtSlot input p.1 p.2) false
  | .inr d => .gadget d (pos d).1 (pos d).2

theorem hotIndexNat_slot (lane : Lane) (slot : Fin foldStepCount) (entry : Nat)
    (small : entry < 2 ^ (slotOffset slot + 1)) (half : Bool) :
    hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry half =
      .hot lane (slotChunk slot) ⟨slotOffset slot + 1, lt_of_lt_of_le (slot_step_lt slot)
        (chunkWidth_le _)⟩ ⟨entry, lt_of_lt_of_le small (Nat.pow_le_pow_right (by norm_num)
          (le_trans (slot_step_lt slot).le (chunkWidth_le _)))⟩ half := by
  unfold hotIndexNat
  have le := chunkWidth_le (slotChunk slot)
  have step := slot_step_lt slot
  have foldSmall : slotOffset slot + 1 < chunkBits := by omega
  have entrySmall : entry < 2 ^ chunkBits :=
    lt_of_lt_of_le small (Nat.pow_le_pow_right (by norm_num) foldSmall.le)
  simp only [FixedIndex.hot.injEq, Fin.mk.injEq, true_and, and_true]
  exact ⟨Nat.mod_eq_of_lt foldSmall, Nat.mod_eq_of_lt entrySmall⟩

theorem hidW_injective : Function.Injective (hidW input pos) := by
  rintro (⟨ℓ, s⟩ | d) (⟨ℓ', s'⟩ | d') same
  · simp only [hidW] at same
    rw [hotIndexNat_slot _ _ _ (activeAtSlot_lt input ℓ s), hotIndexNat_slot _ _ _ (activeAtSlot_lt input ℓ' s')]
      at same
    simp only [FixedIndex.hot.injEq, Fin.mk.injEq] at same
    obtain ⟨rfl, chunk, offset, -⟩ := same
    rw [slot_ext chunk (by omega)]
  · simp only [hidW] at same
    rw [hotIndexNat_slot _ _ _ (activeAtSlot_lt input ℓ s)] at same
    cases same
  · simp only [hidW] at same
    rw [hotIndexNat_slot _ _ _ (activeAtSlot_lt input ℓ' s')] at same
    cases same
  · simp only [hidW, FixedIndex.gadget.injEq] at same
    rw [same.1]

/-- The fixed-key answers with the hidden ones zeroed. -/
def zeroW (rest : {i : FixedIndex // i ∉ Set.range (hidW input pos)} → Block) : FixedIndex → Block :=
  (splitAlong (hidW input pos) (hidW_injective input pos)).symm (fun _ => 0, rest)

theorem zeroW_hidden (rest : {i : FixedIndex // i ∉ Set.range (hidW input pos)} → Block) (h : HiddenIdx) :
    zeroW input pos rest (hidW input pos h) = 0 :=
  splitAlong_symm_image _ _ _ _ h

theorem zeroW_rest (v : FixedIndex → Block) (i : FixedIndex) (notHidden : i ∉ Set.range (hidW input pos)) :
    zeroW input pos (splitAlong (hidW input pos) (hidW_injective input pos) v).2 i = v i :=
  splitAlong_symm_rest _ _ _ _ ⟨i, notHidden⟩

theorem hot_not_hiddenW (lane : Lane) (slot : Fin foldStepCount) (entry : Nat)
    (small : entry < 2 ^ (slotOffset slot + 1)) (half : Bool)
    (off : ¬ (entry = activeAtSlot input lane slot ∧ half = false)) :
    hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry half ∉ Set.range (hidW input pos) := by
  rintro ⟨(⟨ℓ, s⟩ | d), same⟩
  · simp only [hidW] at same
    rw [hotIndexNat_slot _ _ _ (activeAtSlot_lt input ℓ s), hotIndexNat_slot _ _ _ small] at same
    simp only [FixedIndex.hot.injEq, Fin.mk.injEq] at same
    obtain ⟨rfl, chunk, offset, entryEq, halfEq⟩ := same
    have slotEq : s = slot := slot_ext chunk (by omega)
    subst slotEq
    exact off ⟨entryEq.symm, halfEq.symm⟩
  · simp only [hidW] at same
    rw [hotIndexNat_slot _ _ _ small] at same
    cases same

theorem gadget_not_hiddenW (output : Fin digitCount) (κ : Coord) (p : Fin PlanB.coordinateBits)
    (off : (κ, p) ≠ pos output) : FixedIndex.gadget output κ p ∉ Set.range (hidW input pos) := by
  rintro ⟨(⟨ℓ, s⟩ | d), same⟩
  · simp only [hidW] at same
    rw [hotIndexNat_slot _ _ _ (activeAtSlot_lt input ℓ s)] at same
    cases same
  · simp only [hidW, FixedIndex.gadget.injEq] at same
    obtain ⟨rfl, coordEq, position⟩ := same
    exact off (Prod.ext coordEq.symm position.symm)

/-! ### 3. The fold joins and the digests -/

theorem xorFold_hidden {n : Nat} (skip : Fin n) (a mac w : Fin n → Block) (hw : w skip = 0)
    (agree : ∀ i, i ≠ skip → w i = a i) :
    xorFold (fun i => a i ^^^ mac i) = a skip ^^^ xorFold (fun i => w i ^^^ mac i) := by
  rw [xorFold_split skip (fun i => a i ^^^ mac i), xorFold_split skip (fun i => w i ^^^ mac i),
    Programs.xorFoldExcept_congr skip (fun i => w i ^^^ mac i) (fun i => a i ^^^ mac i)
      (fun i off => by rw [agree i off]), hw]
  refine xor_bits _ _ fun j => ?_
  simp only [BitVec.getLsbD_xor]
  cases (a skip).getLsbD j <;> simp

/-- **A fold join is its hidden gate half XOR the rest.** -/
theorem foldJoin_splitW (v : FixedIndex → Block) (lane : Lane) (slot : Fin foldStepCount) (zero : Block) :
    foldJoin v lane slot zero = v (hidW input pos (.inl (lane, slot))) ^^^
      foldJoin (zeroW input pos (splitAlong (hidW input pos) (hidW_injective input pos) v).2)
        lane slot zero := by
  set w := zeroW input pos (splitAlong (hidW input pos) (hidW_injective input pos) v).2
  let skip : Fin (2 ^ (slotOffset slot + 1)) := ⟨activeAtSlot input lane slot, activeAtSlot_lt input lane slot⟩
  have hiddenZero : w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) skip.val false) = 0 :=
    zeroW_hidden input pos _ (.inl (lane, slot))
  have restTrue : ∀ entry : Fin (2 ^ (slotOffset slot + 1)),
      w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry.val true) =
        v (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry.val true) := fun entry =>
    zeroW_rest input pos v _ (hot_not_hiddenW input pos lane slot entry.val entry.isLt true
      (fun both => by cases both.2))
  have restFalse : ∀ entry : Fin (2 ^ (slotOffset slot + 1)), entry ≠ skip →
      w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry.val false) =
        v (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry.val false) := fun entry off =>
    zeroW_rest input pos v _ (hot_not_hiddenW input pos lane slot entry.val entry.isLt false
      (fun both => off (Fin.ext both.1)))
  unfold foldJoin
  have folded := xorFold_hidden skip
    (fun entry => v (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry.val false))
    (fun entry => v (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry.val true))
    (fun entry => w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry.val false))
    hiddenZero restFalse
  have trueHalves : (fun entry : Fin (2 ^ (slotOffset slot + 1)) =>
      w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry.val false) ^^^
        w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry.val true)) =
      fun entry => w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry.val false) ^^^
        v (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry.val true) :=
    funext fun entry => by rw [restTrue entry]
  rw [trueHalves]
  beta_reduce at folded
  rw [folded, BitVec.xor_assoc]
  rfl

/-- **A digest is its hidden gadget answer XOR the rest.** -/
theorem digest_splitW (v : FixedIndex → Block) (output : Fin digitCount) (mac : InputMac) :
    digest v output mac = v (hidW input pos (.inr output)) ^^^
      digest (zeroW input pos (splitAlong (hidW input pos) (hidW_injective input pos) v).2)
        output mac := by
  set w := zeroW input pos (splitAlong (hidW input pos) (hidW_injective input pos) v).2
  have atHidden : w (hidW input pos (.inr output)) = 0 := zeroW_hidden input pos _ (.inr output)
  have rest : ∀ (κ : Coord) (i : Fin coordinateBitCount), (κ, i) ≠ pos output →
      w (.gadget output κ i) = v (.gadget output κ i) := fun κ i off =>
    zeroW_rest input pos v _ (gadget_not_hiddenW input pos output κ i off)
  unfold digest
  rcases hpos : pos output with ⟨κ, p⟩
  have hidEq : hidW input pos (.inr output) = .gadget output κ p := by
    show FixedIndex.gadget output (pos output).1 (pos output).2 = _
    rw [hpos]
  rw [hidEq] at atHidden ⊢
  let p' : Fin coordinateBitCount := ⟨p.val, p.isLt⟩
  have sameIdx : ∀ κ' : Coord, (FixedIndex.gadget output κ' p' : FixedIndex) = .gadget output κ' p :=
    fun _ => rfl
  cases κ with
  | x =>
      have hx := xorFold_hidden p' (fun i => v (.gadget output .x i)) (fun i => mac.x.get i)
        (fun i => w (.gadget output .x i)) (by show w (.gadget output .x p') = 0; rw [sameIdx]; exact atHidden)
        (fun i off => rest .x i (by
          rw [hpos]
          intro same
          exact off (Fin.ext (congrArg (fun q : Coord × Fin PlanB.coordinateBits => q.2.val) same))))
      have ys : (fun index : Fin coordinateBitCount => w (.gadget output .y index) ^^^ mac.y.get index) =
          fun index => v (.gadget output .y index) ^^^ mac.y.get index :=
        funext fun index => by rw [rest .y index (by rw [hpos]; intro same; cases congrArg Prod.fst same)]
      beta_reduce at hx
      rw [hx, ys]
      show (v (.gadget output .x p) ^^^ _) ^^^ _ = _
      exact BitVec.xor_assoc _ _ _
  | y =>
      have hy := xorFold_hidden p' (fun i => v (.gadget output .y i)) (fun i => mac.y.get i)
        (fun i => w (.gadget output .y i)) (by show w (.gadget output .y p') = 0; rw [sameIdx]; exact atHidden)
        (fun i off => rest .y i (by
          rw [hpos]
          intro same
          exact off (Fin.ext (congrArg (fun q : Coord × Fin PlanB.coordinateBits => q.2.val) same))))
      have xs : (fun index : Fin coordinateBitCount => w (.gadget output .x index) ^^^ mac.x.get index) =
          fun index => v (.gadget output .x index) ^^^ mac.x.get index :=
        funext fun index => by rw [rest .x index (by rw [hpos]; intro same; cases congrArg Prod.fst same)]
      beta_reduce at hy
      rw [hy, xs]
      show _ ^^^ (v (.gadget output .y p) ^^^ _) = v (.gadget output .y p) ^^^ (_ ^^^ _)
      refine xor_bits _ _ fun j => ?_
      simp only [BitVec.getLsbD_xor]
      cases (v (.gadget output .y p)).getLsbD j <;> simp <;> rfl

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
