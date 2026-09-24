/-
**Phase 3, P1r — `LawOn`, step (E), part 9: the garbler's side (C's output) on the view.**

The garbler's side after (C) (`realTarget`): uniform coins, an answer table `A ~ tableLaw` and fresh
answers `w` at the gadget positions the garbler's designed entries do not plant (`FreshQ`: a digit
without exceptional input, or a position where `u` disagrees with the digit's exceptional input),
the shadow run on the table `freshen A w`. Off `Exact0` (no digit's exceptional input is `u`) it is
bounded below by `realCore`, which drops the `Exact0` outcomes. Here (per coins):

* `real_view`: the table law expanded, the kernel on the view (`xvW`: the fixed-key view from `A`,
  from `w` at the fresh gadget positions), the published value `tablePub` of the coins, the pads at
  the table's hash of the bridge input, the table's fixed-key answers and limbs;
* the hidden indices of the garbler's published value (`hidW` at fresh gadget positions, `posOf`)
  are off the view (`viewHot_not_hidden`, `planted_not_hidden`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnERegroup

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState uniformMaskTape)
open scoped ENNReal

noncomputable section

/-- The hash off the scale range at the bridge input of a key. -/
def bridgeOf (H : OtherTable) (t : BaseField) : Block × Block :=
  H ⟨bridgeInput t, bridgeInput_not_lt t⟩

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (input : AffineInput)

/-! ### 1. The planted gadget positions, `Exact0`, the garbler's side -/

/-- A gadget coordinate as an EncPRF coordinate. -/
def toEnc : Coord → EncPRF.Coordinate
  | .x => .x
  | .y => .y

/-- **A planted gadget position**: its digit has an exceptional input, which agrees with `u` there
(the garbler's designed gadget entries). -/
def Planted (K : FieldMacToECMac.SuccessfulOffsets) (d : Fin digitCount) (κ : Coord)
    (p : Fin PlanB.coordinateBits) : Prop :=
  ∃ phi, digitEndomorphismBase (outputKeyOf scalar K d).digit = some phi ∧
    inputBit (BitInput.ofAffine (Exception.exceptionalInput phi (outputKeyOf scalar K d).offset.coordinates))
        (toEnc κ) p = inputBit (BitInput.ofAffine input) (toEnc κ) p

/-- **`E₀`: some nonzero digit's exceptional input is `u`.** -/
def Exact0 (K : FieldMacToECMac.SuccessfulOffsets) : Prop :=
  ∃ o, RevealsAt scalar K (BitInput.ofAffine input) (fun _ _ => False) o

/-- A fresh gadget index (the garbler's designed entries leave it empty). -/
def FreshQ (K : FieldMacToECMac.SuccessfulOffsets) : FixedIndex → Prop
  | .gadget d κ p => ¬ Planted scalar input K d κ p
  | _ => False

open Classical in
/-- **The table with fresh answers at the fresh gadget indices.** -/
def freshen (K : FieldMacToECMac.SuccessfulOffsets) (A : Table) (w : FixedIndex → Block) : Table :=
  (A.1, A.2.1, fun i => if FreshQ scalar input K i then w i else A.2.2.1 i, A.2.2.2)

variable (parameter : ℕ)

/-- **The garbler's side after (C)**: the shadow on the table with fresh answers at the fresh gadget
indices. -/
def realTarget (Ψ : Public → LamportSignature → LState → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' coins, PMF.uniformOfFintype Coins coins * ∑' A, tableLaw A *
    ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
      Ψ ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
        (Scheme.scheme.encode ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 input)
        (plantAll (transcript (tableAnswer (freshen scalar input coins.offsets A w))
          (shadowOnM ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 (BitInput.ofAffine input)
            (coins.inputMacKey.encode (BitInput.ofAffine input)))) LazyOracle.empty)

open Classical in
/-- The garbler's side off `Exact0`. -/
def realCore (Ψ : Public → LamportSignature → LState → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' coins, PMF.uniformOfFintype Coins coins * if Exact0 scalar input coins.offsets then 0 else
    ∑' A, tableLaw A * ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
      Ψ ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
        (Scheme.scheme.encode ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 input)
        (plantAll (transcript (tableAnswer (freshen scalar input coins.offsets A w))
          (shadowOnM ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 (BitInput.ofAffine input)
            (coins.inputMacKey.encode (BitInput.ofAffine input)))) LazyOracle.empty)

omit parameter in
theorem realCore_le (Ψ : Public → LamportSignature → LState → ℝ≥0∞) :
    realCore scalar input Ψ ≤ realTarget scalar input Ψ := by
  unfold realCore realTarget
  refine ENNReal.tsum_le_tsum fun coins => mul_le_mul' le_rfl ?_
  split_ifs
  · exact zero_le
  · exact le_rfl

/-! ### 2. The view of the garbler's side -/

open Classical in
/-- **The view's fixed-key answers on `freshen`**: the table's, the fresh answers at the fresh
gadget positions. -/
def xvW (K : FieldMacToECMac.SuccessfulOffsets) (v w : FixedIndex → Block) : VO input → Block :=
  fun i => if FreshQ scalar input K i.1 then w i.1 else v i.1

theorem freshen_view (K : FieldMacToECMac.SuccessfulOffsets) (A : Table) (w : FixedIndex → Block) :
    (fun i : VO input => (freshen scalar input K A w).2.2.1 i.1) = xvW scalar input K A.2.2.1 w := rfl

omit parameter in
theorem tablePads_bridge (A : Table) (coins : Coins) :
    tablePads A coins = padsOf A.1 (bridgeOf A.2.1 coins.bridgeKey) := by
  rw [tablePads_eq]
  exact congrArg (padsOf A.1) (tableAnswer_other A ⟨bridgeInput coins.bridgeKey, bridgeInput_not_lt _⟩)

/-- **The garbler's side, per coins, on the view.** -/
theorem real_view (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (coins : Coins) :
    ∑' A, tableLaw A * ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
      Ψ ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
        (Scheme.scheme.encode ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 input)
        (plantAll (transcript (tableAnswer (freshen scalar input coins.offsets A w))
          (shadowOnM ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 (BitInput.ofAffine input)
            (coins.inputMacKey.encode (BitInput.ofAffine input)))) LazyOracle.empty) =
      ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
        ∑' H, PMF.uniformOfFintype OtherTable H *
          ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v * ∑' T, uniformMaskTape T *
            ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
              onKW input Ψ (tablePub scalar coins (padsOf E (bridgeOf H coins.bridgeKey)) v T)
                coins.inputMacKey E H (xvW scalar input coins.offsets v w) (fun s limb => T ⟨s.1, limb⟩) := by
  have pointwise : ∀ (A : Table) (w : FixedIndex → Block),
      Ψ ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
        (Scheme.scheme.encode ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 input)
        (plantAll (transcript (tableAnswer (freshen scalar input coins.offsets A w))
          (shadowOnM ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 (BitInput.ofAffine input)
            (coins.inputMacKey.encode (BitInput.ofAffine input)))) LazyOracle.empty) =
      onKW input Ψ (tablePub scalar coins (padsOf A.1 (bridgeOf A.2.1 coins.bridgeKey)) A.2.2.1 A.2.2.2)
        coins.inputMacKey A.1 A.2.1 (xvW scalar input coins.offsets A.2.2.1 w)
        (fun s limb => A.2.2.2 ⟨s.1, limb⟩) := by
    intro A w
    have second : ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 = coins.inputMacKey := by
      rw [garbleM_table]
    rw [garbleM_tablePub, second, tablePads_bridge]
    show onK input Ψ _ coins.inputMacKey (freshen scalar input coins.offsets A w) = _
    rw [onK_view, freshen_view, onKV_tape]
    rfl
  simp only [pointwise]
  unfold tableLaw
  rw [tsum_productPMF]
  refine tsum_congr fun E => congrArg _ ?_
  rw [tsum_productPMF]
  refine tsum_congr fun H => congrArg _ ?_
  rw [tsum_productPMF]

/-! ### 3. The hidden gadget positions: fresh ones -/

open Classical in
/-- A fresh position of each digit (`(x, 0)` if there is none). -/
def posOf (K : FieldMacToECMac.SuccessfulOffsets) (d : Fin digitCount) : Coord × Fin PlanB.coordinateBits :=
  if h : ∃ q : Coord × Fin PlanB.coordinateBits, ¬ Planted scalar input K d q.1 q.2 then Classical.choose h
  else (.x, ⟨0, by unfold PlanB.coordinateBits; omega⟩)

theorem inputBit_toEnc (bits : BitInput) (c : EncPRF.Coordinate) (p : Fin coordinateBitCount) :
    inputBit bits (toEnc (Pipeline.gadgetCoord c)) p = inputBit bits c p := by
  cases c <;> rfl

/-- **Off `Exact0` every digit has a fresh position.** -/
theorem posOf_fresh (K : FieldMacToECMac.SuccessfulOffsets) (off : ¬ Exact0 scalar input K)
    (d : Fin digitCount) : ¬ Planted scalar input K d (posOf scalar input K d).1 (posOf scalar input K d).2 := by
  unfold posOf
  split_ifs with h
  · exact Classical.choose_spec h
  · push Not at h
    intro planted
    obtain ⟨phi, found, _⟩ := planted
    refine off ⟨d, phi, found, fun c p => Or.inl ?_⟩
    obtain ⟨phi', found', agree⟩ := h (Pipeline.gadgetCoord c, p)
    rw [found] at found'
    cases Option.some.inj found'
    rw [← inputBit_toEnc, ← inputBit_toEnc (BitInput.ofAffine input)]
    exact agree

variable (K : FieldMacToECMac.SuccessfulOffsets)

/-- The hidden gadget positions at fixed offsets. -/
abbrev posK : Fin digitCount → Coord × Fin PlanB.coordinateBits := posOf scalar input K

omit parameter in
/-- **A fold gate of the view is not hidden**: the view asks every entry but the active parent. -/
theorem viewHot_not_hidden (i : FixedIndex) (view : ViewIdx input i)
    (notGadget : ∀ o κ p, i ≠ .gadget o κ p) : i ∉ Set.range (hidW input (posK scalar input K)) := by
  rintro ⟨(⟨ℓ, s⟩ | d), same⟩
  · simp only [hidW] at same
    rw [hotIndexNat_slot _ _ _ (activeAtSlot_lt input ℓ s)] at same
    subst same
    exact view.2.2.2 rfl
  · exact notGadget _ _ _ same.symm

omit parameter in
/-- Off `Exact0` a planted gadget index is not hidden. -/
theorem planted_not_hidden (off : ¬ Exact0 scalar input K) (d : Fin digitCount) (κ : Coord)
    (p : Fin PlanB.coordinateBits) (planted : Planted scalar input K d κ p) :
    FixedIndex.gadget d κ p ∉ Set.range (hidW input (posK scalar input K)) := by
  rintro ⟨(⟨ℓ, s⟩ | d'), same⟩
  · simp only [hidW] at same
    rw [hotIndexNat_slot _ _ _ (activeAtSlot_lt input ℓ s)] at same
    cases same
  · simp only [hidW, FixedIndex.gadget.injEq] at same
    obtain ⟨rfl, coordEq, position⟩ := same
    refine posOf_fresh scalar input K off d' ?_
    rw [coordEq, position]
    exact planted

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
