/-
**Phase 3, P1m — (B1) the fixed-key conjunct on the curve.**

A level-1 fold input of system A is the source's own label of a chunk's first bit
(`hotCurveIn_le`); over the uniform Lamport key that label is a uniform block (`uniform_label`), so
its mass is `1/2^128` (`hotCurve_key_le`). With the per-index bounds of `BoundsFixedOn.lean` and the
outputs of `BoundsFixedDesig.lean`:

* `designed_fixed_onCurve` — on the curve, `Pr[x ∈ fixedIn_i] + Pr[y ∈ fixedOut_i] ≤ 4/2^128`
  (input `≤ 1/(2^128 − 1) ≤ 2/2^128`, output `≤ 1/2^128`).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsHashOn

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### The label of one key position is uniform -/

section KeyLabel

/-- The key of a coordinate. -/
def keyCoord (key : InputMacKey) : Coord → CoordinateMacKey
  | .x => key.x
  | .y => key.y

/-- A key is its two coordinate keys, the chosen one first. -/
def keySplit : Coord → (InputMacKey ≃ CoordinateMacKey × CoordinateMacKey)
  | .x => ⟨fun key => (key.x, key.y), fun pair => ⟨pair.1, pair.2⟩, fun _ => rfl, fun _ => rfl⟩
  | .y => ⟨fun key => (key.y, key.x), fun pair => ⟨pair.2, pair.1⟩, fun _ => rfl, fun _ => rfl⟩

/-- A vector is its entries. -/
def vecEquiv (α : Type) (n : ℕ) : Vector α n ≃ (Fin n → α) where
  toFun v i := v[i]
  invFun f := Vector.ofFn f
  left_inv v := by
    ext i h
    simp
  right_inv f := by
    funext i
    simp

/-- A bit key is its two labels. -/
def bitKeyEquiv : BitAdaptor.Key ≃ Block × Block :=
  ⟨fun key => (key.falseLabel, key.trueLabel), fun pair => ⟨pair.1, pair.2⟩, fun _ => rfl,
    fun _ => rfl⟩

/-- The rest of a key, once one label pair is taken out. -/
abbrev KeyRest (p : Fin coordinateBitCount) : Type :=
  ({j // j ≠ p} → BitAdaptor.Key) × CoordinateMacKey

/-- **A key is one label pair and the rest.** -/
def labelSplit (κ : Coord) (p : Fin coordinateBitCount) :
    InputMacKey ≃ (Block × Block) × KeyRest p :=
  (keySplit κ).trans ((((vecEquiv _ _).trans (Equiv.funSplitAt p _)).prodCongr
    (Equiv.refl _)).trans ((Equiv.prodAssoc _ _ _).trans (bitKeyEquiv.prodCongr (Equiv.refl _))))

theorem labelSplit_fst (κ : Coord) (p : Fin coordinateBitCount) (key : InputMacKey) :
    (labelSplit κ p key).1 = ((keyCoord key κ)[p].falseLabel, (keyCoord key κ)[p].trueLabel) := by
  cases κ <;> rfl

instance keyRestFinite (p : Fin coordinateBitCount) : Finite (KeyRest p) :=
  Finite.of_injective (fun rest => (labelSplit .x p).symm ((0, 0), rest)) fun a b same => by
    have := congrArg (fun key => (labelSplit .x p key).2) same
    simpa using this

noncomputable instance keyRestFintype (p : Fin coordinateBitCount) : Fintype (KeyRest p) :=
  Fintype.ofFinite _

instance keyRestNonempty (p : Fin coordinateBitCount) : Nonempty (KeyRest p) :=
  ⟨(labelSplit .x p defaultKey).2⟩

/-- **The selected label of one position of a uniform key is a uniform block.** -/
theorem uniform_label (κ : Coord) (p : Fin coordinateBitCount) (b : Bool) :
    (PMF.uniformOfFintype InputMacKey).map (fun key => BitAdaptor.encode (keyCoord key κ)[p] b) =
      PMF.uniformOfFintype Block := by
  cases b with
  | false =>
    have split : (fun key => BitAdaptor.encode (keyCoord key κ)[p] false) =
        Prod.fst ∘ Prod.fst ∘ labelSplit κ p := by
      funext key
      simp only [Function.comp_apply, labelSplit_fst]
      rfl
    rw [split, ← PMF.map_comp, ← PMF.map_comp, Kriterion.ArgoMAC.Phase3.Glue.uniform_equiv,
      Kriterion.ArgoMAC.Phase3.Glue.uniform_map_fst, Kriterion.ArgoMAC.Phase3.Glue.uniform_map_fst]
  | true =>
    have split : (fun key => BitAdaptor.encode (keyCoord key κ)[p] true) =
        Prod.snd ∘ Prod.fst ∘ labelSplit κ p := by
      funext key
      simp only [Function.comp_apply, labelSplit_fst]
      rfl
    rw [split, ← PMF.map_comp, ← PMF.map_comp, Kriterion.ArgoMAC.Phase3.Glue.uniform_equiv,
      Kriterion.ArgoMAC.Phase3.Glue.uniform_map_fst, Kriterion.ArgoMAC.Phase3.Glue.uniform_map_snd]

/-- **A uniform key's label hits one block with mass `1/2^128`.** -/
theorem key_label_le (κ : Coord) (p : Fin coordinateBitCount) (b : Bool) (P : Block → Prop)
    (unique : ∀ u v, P u → P v → u = v) :
    ∑' key, PMF.uniformOfFintype InputMacKey key *
      ind (P (BitAdaptor.encode (keyCoord key κ)[p] b)) ≤ delta := by
  rw [← tsum_map_mul (PMF.uniformOfFintype InputMacKey)
    (fun key => BitAdaptor.encode (keyCoord key κ)[p] b) (fun w => ind (P w)), uniform_label]
  unfold ind
  classical
  refine le_trans (uniform_single_le (X := Block) P unique) (le_of_eq ?_)
  rw [Kriterion.ArgoMAC.Security.PGS.card_block]

end KeyLabel

/-! ### The source's own label -/

section Own

theorem restore_selected_mac (input : AffineInput) (mac : InputMac) :
    (Lamport.restore input (Lamport.selectedLabels mac)).inputMac = mac := by
  apply InputMac.ext
  · apply Vector.ext
    intro index bound
    simp only [Lamport.restore, Lamport.selectedLabels, Vector.getElem_ofFn]
    rw [dif_pos (show index < 254 from bound)]
    rfl
  · apply Vector.ext
    intro index bound
    simp only [Lamport.restore, Lamport.selectedLabels, Vector.getElem_ofFn]
    rw [dif_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rfl

theorem restoredMac_join (pub : PubPart) (key : InputMacKey) (input : AffineInput) :
    restoredMac (joinSource pub key) input = key.encode (BitInput.ofAffine input) :=
  restore_selected_mac input _

theorem macLabels_encode (key : InputMacKey) (bits : BitInput) (κ : Coord)
    (p : Fin coordinateBitCount) :
    Pipeline.macLabels (key.encode bits) κ p =
      BitAdaptor.encode (keyCoord key κ)[p] ((Pipeline.coordBits bits κ).getLsb p) := by
  cases κ <;>
    simp [Pipeline.macLabels, InputMacKey.encode, encodeCoordinate, keyCoord, Pipeline.coordBits]

/-- **A system-A level-1 fold input, averaged over the key**: `≤ 1/2^128`. -/
theorem hotCurve_key_le (pub : PubPart) (input : AffineInput) (κ : Coord) (c : Fin chunkCount)
    (x : Block) :
    ∑' key, PMF.uniformOfFintype InputMacKey key *
      ind (Pipeline.macLabels (restoredMac (joinSource pub key) input) κ (firstBit c) = x) ≤
      delta := by
  simp only [restoredMac_join, macLabels_encode]
  exact key_label_le κ (firstBit c) _ (fun w => w = x) fun u v hu hv => hu.trans hv.symm

end Own

/-! ### The conjunct on the curve -/

section Conjunct

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

theorem delta_le_two : delta ≤ 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ :=
  le_mul_of_one_le_left zero_le (by norm_num)

theorem epsOne_le : epsOne ≤ 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  have split : ((2 ^ 128 : ℕ) : ℝ≥0∞) = 2 * ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
    push_cast
    ring
  show ((2 ^ 128 - 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ _
  rw [split, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← mul_assoc,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  exact ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (by norm_num))

theorem lane_cases (lane : Lane) :
    (lane = .curveX ∨ lane = .curveY) ∨ (lane = .pointX ∨ lane = .pointY) := by
  cases lane <;> simp

/-- The labels of a system-A lane are MAC labels of one coordinate. -/
theorem curve_labels {lane : Lane} (curve : lane = .curveX ∨ lane = .curveY) :
    ∃ κ : Coord, ∀ mac pads, laneLabels mac pads lane = Pipeline.macLabels mac κ := by
  rcases curve with rfl | rfl
  · exact ⟨.x, fun _ _ => rfl⟩
  · exact ⟨.y, fun _ _ => rfl⟩

/-- The labels of a system-B lane are whitened MAC labels of one coordinate. -/
theorem point_labels {lane : Lane} (point : lane = .pointX ∨ lane = .pointY) :
    ∃ κ : Coord, ∀ mac pads,
      laneLabels mac pads lane = Pipeline.macLabels (Programs.whitenMacOf pads mac) κ := by
  rcases point with rfl | rfl
  · exact ⟨.x, fun _ _ => rfl⟩
  · exact ⟨.y, fun _ _ => rfl⟩

/-- **The input half on the curve**: `≤ 2/2^128`. -/
theorem designed_fixedIn_onCurve (scalar : NonZeroScalar) (pub : PubPart) (input : AffineInput)
    (target : Point) (onCurve : Scheme.scheme.function scalar input = some target) (i : FixedIndex)
    (x : Block) :
    (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.fixedIn i x} ≤
      2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [keyedPoints_measure_eq, onCurve]
  cases i with
  | hot lane c f e h =>
    by_cases present : 1 ≤ f.val ∧ f.val < chunkWidth c ∧ e.val < 2 ^ f.val
    · obtain ⟨one, small, lt⟩ := present
      by_cases first : f.val = 1
      · rcases lane_cases lane with curve | point
        · obtain ⟨κ, labelsEq⟩ := curve_labels curve
          exact le_trans (ENNReal.tsum_le_tsum fun key => mul_le_mul' le_rfl
            (hotCurveIn_le scalar designedOff (joinSource pub key) input target lane κ labelsEq c f
              e h x first)) (le_trans (hotCurve_key_le pub input κ c x) delta_le_two)
        · obtain ⟨κ, labelsEq⟩ := point_labels point
          exact tsum_le_of_support _ _ _ fun key _ => le_trans
            (hotPointIn_le scalar designedOff (joinSource pub key) input target lane κ labelsEq c f
              e h x first) epsOne_le
      · exact tsum_le_of_support _ _ _ fun key _ => le_trans
          (hotLevelIn_le scalar designedOff (joinSource pub key) input target lane c f e h x
            (by omega) small lt) delta_le_two
    · exact tsum_le_of_support _ _ _ fun key _ => le_trans
        (hotAbsent_le scalar designedOff (joinSource pub key) input target lane c f e h x present)
        zero_le
  | gadget d κ pos b =>
    exact tsum_le_of_support _ _ _ fun key _ => le_trans
      (gadgetIn_le scalar designedOff (joinSource pub key) input target d κ pos b x) epsOne_le

/-- **The output half on the curve**: `≤ 1/2^128 ≤ 2/2^128`. -/
theorem designed_fixedOut_onCurve (scalar : NonZeroScalar) (pub : PubPart) (input : AffineInput)
    (target : Point) (onCurve : Scheme.scheme.function scalar input = some target) (i : FixedIndex)
    (y : Block) :
    (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.fixedOut i y} ≤
      2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  refine keyedPoints_le_of_source _ _ _ _ _ _ fun source => ?_
  rw [onCurve]
  exact le_trans (fixedOut_onCurve_le scalar designedOff source input target i y) delta_le_two

/-- **The fixed-key conjunct of `PerPairBound (designedShadow scalar) scalar (4/2^128)`, on the
curve.** -/
theorem designed_fixed_onCurve (scalar : NonZeroScalar) (pub : PubPart) (input : AffineInput)
    (target : Point) (onCurve : Scheme.scheme.function scalar input = some target) (i : FixedIndex)
    (x y : Block) :
    (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.fixedIn i x} +
      (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.fixedOut i y} ≤
        4 / 2 ^ 128 := by
  rw [← two_inv_add_two_inv]
  exact add_le_add (designed_fixedIn_onCurve scalar pub input target onCurve i x)
    (designed_fixedOut_onCurve scalar pub input target onCurve i y)

end Conjunct

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
