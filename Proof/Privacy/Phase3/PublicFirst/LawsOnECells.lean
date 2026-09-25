/-
**Phase 3, P1r — `LawOn`, step (E), part 7: the garbler's published value on a table, with the
hidden fold material at every paid fold step and the hidden gadget answer at any position.**

A lane publishes one fold join per paid fold step (`LawsOff.foldJoin`: the two gate halves of every
entry of the step, and the step's zero label). The evaluator asks every entry of the step but the
active parent; so the active parent's first gate half hides the join (`foldJoin_splitW`). A digit's
two digests read its two hidden gadget answers (`pos`: two distinct gadget indices per digit) as
far as their bits agree with the indices' (`readW`, `digest_splitW`). Here the hidden indices take
one gate half per (lane, paid fold step) and two gadget indices per digit (`hidW pos`, injective,
`hidW_injective`).
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

/-- **Two distinct gadget indices (position and bit) per digit.** -/
abbrev PosPair := {pos : Fin digitCount → Bool → Coord × Fin PlanB.coordinateBits × Bool //
  ∀ d, pos d false ≠ pos d true}

variable [FieldCertificate] [GroupCertificate] (input : AffineInput) (pos : PosPair)

/-! ### 2. Hidden indices -/

/-- The active parent's entry at a slot's step, as an entry of the step. -/
def activeAtSlot (lane : Lane) (slot : Fin foldStepCount) : Nat :=
  activeEntry input lane (slotChunk slot) (slotOffset slot + 1)

theorem activeAtSlot_lt (lane : Lane) (slot : Fin foldStepCount) :
    activeAtSlot input lane slot < 2 ^ (slotOffset slot + 1) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- **The hidden coins' indices**: the active parent's first gate half per (lane, paid fold step),
the two gadget indices `pos d` per digit. -/
def hidW : HiddenIdx → FixedIndex
  | .inl p => hotIndexNat p.1 (slotChunk p.2) (slotOffset p.2 + 1) (activeAtSlot input p.1 p.2) false
  | .inr q => .gadget q.1 (pos.1 q.1 q.2).1 (pos.1 q.1 q.2).2.1 (pos.1 q.1 q.2).2.2

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
  rintro (⟨ℓ, s⟩ | ⟨d, b⟩) (⟨ℓ', s'⟩ | ⟨d', b'⟩) same
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
    obtain ⟨rfl, coordEq, positionEq, bitEq⟩ := same
    have posEq : pos.1 d b = pos.1 d b' := Prod.ext coordEq (Prod.ext positionEq bitEq)
    cases b <;> cases b'
    · rfl
    · exact absurd posEq (pos.2 d)
    · exact absurd posEq.symm (pos.2 d)
    · rfl

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
  rintro ⟨(⟨ℓ, s⟩ | ⟨d, b⟩), same⟩
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
    (b : Bool) (off : ∀ kind, (κ, p, b) ≠ pos.1 output kind) :
    FixedIndex.gadget output κ p b ∉ Set.range (hidW input pos) := by
  rintro ⟨(⟨ℓ, s⟩ | ⟨d, kind⟩), same⟩
  · simp only [hidW] at same
    rw [hotIndexNat_slot _ _ _ (activeAtSlot_lt input ℓ s)] at same
    cases same
  · simp only [hidW, FixedIndex.gadget.injEq] at same
    obtain ⟨rfl, coordEq, position, bitEq⟩ := same
    exact off kind (Prod.ext coordEq.symm (Prod.ext position.symm bitEq.symm))

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

/-- **A digit's hidden answer of a kind, as a point's digest reads it**: the answer if the point's
bit at the index's position is the index's bit, else nothing. -/
def readW (v : FixedIndex → Block) (d : Fin digitCount) (point : AffineInput) (kind : Bool) : Block :=
  if (inputBits point (pos.1 d kind).1).getLsb (pos.1 d kind).2.1 = (pos.1 d kind).2.2 then
    v (hidW input pos (.inr (d, kind)))
  else 0

/-- **A digest is the hidden answers it reads XOR the rest.** -/
theorem digest_splitW (v : FixedIndex → Block) (d : Fin digitCount) (point : AffineInput)
    (mac : InputMac) :
    digest v d point mac = readW input pos v d point false ^^^ (readW input pos v d point true ^^^
      digest (zeroW input pos (splitAlong (hidW input pos) (hidW_injective input pos) v).2)
        d point mac) := by
  have apart : hidW input pos (.inr (d, true)) ≠ hidW input pos (.inr (d, false)) := fun same =>
    Bool.noConfusion (congrArg Prod.snd (Sum.inr.inj (hidW_injective input pos same)))
  have firstIdx : hidW input pos (.inr (d, false)) =
      .gadget d (pos.1 d false).1 (pos.1 d false).2.1 (pos.1 d false).2.2 := rfl
  have step1 := digest_update v (Function.update v (hidW input pos (.inr (d, false))) 0) d point mac
    (pos.1 d false).1 (pos.1 d false).2.1 (pos.1 d false).2.2
    (fun κ' p' b' off => Function.update_of_ne (fun same => by
      rw [firstIdx] at same
      obtain ⟨-, h1, h2, h3⟩ := FixedIndex.gadget.inj same
      exact off (Prod.ext h1 (Prod.ext h2 h3))) _ _)
    (by rw [← firstIdx]; exact Function.update_self _ _ _)
  have step2 := digest_update (Function.update v (hidW input pos (.inr (d, false))) 0)
    (zeroW input pos (splitAlong (hidW input pos) (hidW_injective input pos) v).2) d point mac
    (pos.1 d true).1 (pos.1 d true).2.1 (pos.1 d true).2.2
    (fun κ' p' b' off => by
      by_cases atFirst : (κ', p', b') = pos.1 d false
      · have index : (FixedIndex.gadget d κ' p' b' : FixedIndex) = hidW input pos (.inr (d, false)) := by
          rw [firstIdx, ← atFirst]
        rw [index, Function.update_self]
        exact zeroW_hidden input pos _ (.inr (d, false))
      · have notHidden := gadget_not_hiddenW input pos d κ' p' b' (fun kind => by
          cases kind
          · exact atFirst
          · exact off)
        rw [zeroW_rest input pos v _ notHidden,
          Function.update_of_ne (fun same => notHidden ⟨.inr (d, false), same.symm⟩)])
    (zeroW_hidden input pos _ (.inr (d, true)))
  have secondSame : Function.update v (hidW input pos (.inr (d, false))) 0
      (.gadget d (pos.1 d true).1 (pos.1 d true).2.1 (pos.1 d true).2.2) =
      v (.gadget d (pos.1 d true).1 (pos.1 d true).2.1 (pos.1 d true).2.2) :=
    Function.update_of_ne apart _ _
  unfold readW
  rw [step1, step2, secondSame]
  rfl

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
