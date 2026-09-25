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

/-- **A planted gadget index**: its digit has an exceptional input (the garbler asks both bits of
every position), and its bit is `u`'s (the garbler's designed gadget entries). -/
def Planted (K : FieldMacToECMac.SuccessfulOffsets) (d : Fin digitCount) (κ : Coord)
    (p : Fin PlanB.coordinateBits) (b : Bool) : Prop :=
  (∃ phi, digitEndomorphismBase (outputKeyOf scalar K d).digit = some phi) ∧
    (inputBits input κ).getLsb p = b

/-- **`E₀`: some nonzero digit's exceptional input is `u`.** -/
def Exact0 (K : FieldMacToECMac.SuccessfulOffsets) : Prop :=
  ∃ o, RevealsAt scalar K (BitInput.ofAffine input) (fun _ _ => False) o

/-- A fresh gadget index (the garbler's designed entries leave it empty). -/
def FreshQ (K : FieldMacToECMac.SuccessfulOffsets) : FixedIndex → Prop
  | .gadget d κ p b => ¬ Planted scalar input K d κ p b
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

/-! ### 3. The hidden gadget indices -/

/-- A position where an input's bit differs from `u`'s. -/
abbrev DiffAt (point : AffineInput) (q : Coord × Fin PlanB.coordinateBits) : Prop :=
  (inputBits point q.1).getLsb q.2 ≠ (inputBits input q.1).getLsb q.2

/-- The origin position `(x, 0)`. -/
def pos₀ : Coord × Fin PlanB.coordinateBits := (.x, ⟨0, by unfold PlanB.coordinateBits; omega⟩)

/-- The position `(x, 1)`. -/
def pos₁ : Coord × Fin PlanB.coordinateBits := (.x, ⟨1, by unfold PlanB.coordinateBits; omega⟩)

/-- A position other than `q`. -/
def otherPos (q : Coord × Fin PlanB.coordinateBits) : Coord × Fin PlanB.coordinateBits :=
  if q = pos₀ then pos₁ else pos₀

theorem otherPos_ne (q : Coord × Fin PlanB.coordinateBits) : otherPos q ≠ q := by
  unfold otherPos
  split_ifs with origin
  · rw [origin]
    intro same
    cases congrArg (fun q : Coord × Fin PlanB.coordinateBits => q.2.val) same
  · exact fun same => origin same.symm

open Classical in
/-- **A digit's two hidden positions** at fixed offsets: a position where only the doubling input
differs from `u`, then one where the sign-zero input does; or a position where only the sign-zero
input differs, and one where the doubling input does. -/
def positionsOf (K : FieldMacToECMac.SuccessfulOffsets) (d : Fin digitCount) :
    (Coord × Fin PlanB.coordinateBits) × (Coord × Fin PlanB.coordinateBits) :=
  match digitEndomorphismBase (outputKeyOf scalar K d).digit with
  | none => (pos₀, pos₁)
  | some phi =>
    if h : ∃ q, DiffAt input (Exception.exceptionalInput phi (outputKeyOf scalar K d).offset.coordinates) q ∧
        ¬ DiffAt input (Exception.tripleInput phi (outputKeyOf scalar K d).offset.coordinates) q then
      (Classical.choose h,
        if h₂ : ∃ q, DiffAt input (Exception.tripleInput phi (outputKeyOf scalar K d).offset.coordinates) q
        then Classical.choose h₂ else otherPos (Classical.choose h))
    else if h' : ∃ q, DiffAt input (Exception.tripleInput phi (outputKeyOf scalar K d).offset.coordinates) q ∧
        ¬ DiffAt input (Exception.exceptionalInput phi (outputKeyOf scalar K d).offset.coordinates) q then
      (if h₁ : ∃ q, DiffAt input (Exception.exceptionalInput phi (outputKeyOf scalar K d).offset.coordinates) q
        then Classical.choose h₁ else otherPos (Classical.choose h'),
        Classical.choose h')
    else (pos₀, pos₁)

theorem positionsOf_ne (K : FieldMacToECMac.SuccessfulOffsets) (d : Fin digitCount) :
    (positionsOf scalar input K d).1 ≠ (positionsOf scalar input K d).2 := by
  unfold positionsOf
  split
  · exact fun same => by cases congrArg (fun q : Coord × Fin PlanB.coordinateBits => q.2.val) same
  · rename_i phi found
    split_ifs with h h₂ h' h₁
    · intro same
      simp only at same
      exact (Classical.choose_spec h).2 (same ▸ Classical.choose_spec h₂)
    · exact (otherPos_ne _).symm
    · intro same
      simp only at same
      exact (Classical.choose_spec h').2 (same.symm ▸ Classical.choose_spec h₁)
    · exact otherPos_ne _
    · exact fun same => by cases congrArg (fun q : Coord × Fin PlanB.coordinateBits => q.2.val) same

/-- The hidden index at a position: the position and the bit `u` does not have there. -/
def flipAt (q : Coord × Fin PlanB.coordinateBits) : Coord × Fin PlanB.coordinateBits × Bool :=
  (q.1, q.2, !(inputBits input q.1).getLsb q.2)

theorem flipAt_injective (q q' : Coord × Fin PlanB.coordinateBits) (same : flipAt input q = flipAt input q') :
    q = q' := by
  have first := congrArg Prod.fst same
  have second := congrArg (fun t => t.2.1) same
  exact Prod.ext first second

variable (K : FieldMacToECMac.SuccessfulOffsets)

/-- **The hidden gadget indices at fixed offsets**: each digit's two positions, at the bits `u` does
not have. -/
def posK : PosPair :=
  ⟨fun d kind => flipAt input (bif kind then (positionsOf scalar input K d).2
      else (positionsOf scalar input K d).1),
    fun d same => positionsOf_ne scalar input K d (flipAt_injective input _ _ same)⟩

/-- Off `Exact0`, every exceptional input of a nonzero digit differs from `u` somewhere. -/
theorem exists_diff (off : ¬ Exact0 scalar input K) (d : Fin digitCount) (phi : BaseField)
    (found : digitEndomorphismBase (outputKeyOf scalar K d).digit = some phi) (kind : Bool) :
    ∃ q, DiffAt input (kindInput phi (outputKeyOf scalar K d).offset.coordinates kind) q := by
  by_contra none
  push Not at none
  apply off
  refine ⟨d, phi, found, kind, fun c p => Or.inl ?_⟩
  cases c
  · exact none (.x, p)
  · exact none (.y, p)

/-- A hidden index is read by an input's digest iff the input differs from `u` there. -/
theorem reads_flip (point : AffineInput) (q : Coord × Fin PlanB.coordinateBits) :
    (inputBits point (flipAt input q).1).getLsb (flipAt input q).2.1 = (flipAt input q).2.2 ↔
      DiffAt input point q := by
  unfold flipAt DiffAt
  dsimp only
  cases (inputBits point q.1).getLsb q.2 <;> cases (inputBits input q.1).getLsb q.2 <;> simp

/-- **Off `Exact0` the hidden pair of every digit is valid.** -/
theorem posK_valid (off : ¬ Exact0 scalar input K) (d : Fin digitCount) :
    ValidPair (posK scalar input K) (outputKeyOf scalar K d) d := by
  intro phi found
  have diff₁ := exists_diff scalar input K off d phi found false
  have diff₂ := exists_diff scalar input K off d phi found true
  simp only [kindInput] at diff₁ diff₂
  have apartInputs := exceptionalInput_ne_triple phi
    (digitEndomorphismBasePowSix _ _ found) _ (outputKeyOf scalar K d).offset.onCurve
  set e₁ := Exception.exceptionalInput phi (outputKeyOf scalar K d).offset.coordinates with e₁Def
  set e₂ := Exception.tripleInput phi (outputKeyOf scalar K d).offset.coordinates with e₂Def
  have positionsEq : positionsOf scalar input K d =
      if h : ∃ q, DiffAt input e₁ q ∧ ¬ DiffAt input e₂ q then
        (Classical.choose h,
          if h₂ : ∃ q, DiffAt input e₂ q then Classical.choose h₂ else otherPos (Classical.choose h))
      else if h' : ∃ q, DiffAt input e₂ q ∧ ¬ DiffAt input e₁ q then
        (if h₁ : ∃ q, DiffAt input e₁ q then Classical.choose h₁ else otherPos (Classical.choose h'),
          Classical.choose h')
      else (pos₀, pos₁) := by
    unfold positionsOf
    rw [found]
  unfold ReadsAt posK
  simp only [cond_false, cond_true, reads_flip]
  rw [positionsEq]
  by_cases h : ∃ q, DiffAt input e₁ q ∧ ¬ DiffAt input e₂ q
  · rw [dif_pos h, dif_pos diff₂]
    exact ⟨(Classical.choose_spec h).1, Classical.choose_spec diff₂,
      fun both => (Classical.choose_spec h).2 both.1⟩
  · rw [dif_neg h]
    by_cases h' : ∃ q, DiffAt input e₂ q ∧ ¬ DiffAt input e₁ q
    · rw [dif_pos h', dif_pos diff₁]
      exact ⟨Classical.choose_spec diff₁, (Classical.choose_spec h').1,
        fun both => (Classical.choose_spec h').2 both.2⟩
    · exfalso
      push Not at h h'
      refine apartInputs (affine_eq_of_bits fun q => ?_)
      by_cases first : DiffAt input e₁ q
      · have second := h q first
        unfold DiffAt at first second
        revert first second
        cases (inputBits e₁ q.1).getLsb q.2 <;> cases (inputBits e₂ q.1).getLsb q.2 <;>
          cases (inputBits input q.1).getLsb q.2 <;> simp
      · have second : ¬ DiffAt input e₂ q := fun hit => first (h' q hit)
        unfold DiffAt at first second
        push Not at first second
        rw [first, second]

omit parameter in
/-- **A fold gate of the view is not hidden**: the view asks every entry but the active parent. -/
theorem viewHot_not_hidden (i : FixedIndex) (view : ViewIdx input i)
    (notGadget : ∀ o κ p b, i ≠ .gadget o κ p b) : i ∉ Set.range (hidW input (posK scalar input K)) := by
  rintro ⟨(⟨ℓ, s⟩ | ⟨d, kind⟩), same⟩
  · simp only [hidW] at same
    rw [hotIndexNat_slot _ _ _ (activeAtSlot_lt input ℓ s)] at same
    subst same
    exact view.2.2.2 rfl
  · exact notGadget _ _ _ _ same.symm

omit parameter in
/-- A planted gadget index is not hidden: the hidden ones carry the bit `u` does not have. -/
theorem planted_not_hidden (d : Fin digitCount) (κ : Coord) (p : Fin PlanB.coordinateBits) (b : Bool)
    (planted : Planted scalar input K d κ p b) :
    FixedIndex.gadget d κ p b ∉ Set.range (hidW input (posK scalar input K)) := by
  rintro ⟨(⟨ℓ, s⟩ | ⟨d', kind⟩), same⟩
  · simp only [hidW] at same
    rw [hotIndexNat_slot _ _ _ (activeAtSlot_lt input ℓ s)] at same
    cases same
  · simp only [hidW, FixedIndex.gadget.injEq] at same
    obtain ⟨rfl, coordEq, position, bitEq⟩ := same
    have flip : ((posK scalar input K).1 d' kind).2.2 =
        !(inputBits input ((posK scalar input K).1 d' kind).1).getLsb ((posK scalar input K).1 d' kind).2.1 :=
      rfl
    rw [flip, coordEq, position] at bitEq
    have bitIs := planted.2
    rw [← bitEq] at bitIs
    cases h : (inputBits input κ).getLsb p <;> simp [h] at bitIs

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
