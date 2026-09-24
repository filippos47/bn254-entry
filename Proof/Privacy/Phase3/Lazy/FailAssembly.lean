/-
**Phase 3, P4b — (d) the key-averaged failure bound, and the restated `AbortBound.perQuery`.**

Per tape and per key the installation of `I^U` fails with mass at most (`opening_bound`,
`pointPart_bound`)

  `1[W_c ∈ dom(i₁ᶜ)] + κ_c·M_c + E_pads[1[W ∈ dom(i₁)]] + κ_p·D`,

`κ = 1/(2^128 − n(i₁))`, `M_c` the stage-1 hash entries at the `curveX` chunk-0 cells, `D` those at
the designated inputs. Averaged over the key, the two fold hits cost `n(i₁ᶜ)/2^128` and
`n(i₁)/2^128` (`key_sum_le`, (c)). Every coefficient is at most `1/(2^128 − q)`, and the four
families are disjoint abort sites (`families_le_abortUse`: the two level-1 fold indices, the
`curveX` chunk-0 cells, the designated `pointX` chunk-0 cells), so

  `Σ_key failMass ≤ 1/(2^128 − q) · Σ_{abort sites} n = abortQueryCharge q · abortUse`.

There is no output charge: a hash program needs only a fresh input.

**`keyAveragedFailBound : KeyAveragedFailBound`** and, with `abortBound_perQuery'_of`,
**`abortBound_perQuery' : AbortPerQuery' openedHybrid idealUniformHybrid`**.
-/

import Proof.Privacy.Phase3.Lazy.KeyAverage
import Proof.Privacy.Phase3.Lazy.AbortPerQuery

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.Phase3 (openedHybrid)
open scoped ENNReal

noncomputable section

/-- The wire adapter restores the selected labels. -/
theorem restore_selectedLabels (input : AffineInput) (mac : InputMac) :
    Lamport.restore input (Lamport.selectedLabels mac) = ⟨BitInput.ofAffine input, mac⟩ := by
  apply congrArg (Garbling.Labels.mk (BitInput.ofAffine input))
  apply InputMac.ext
  · apply Vector.ext
    intro index bound
    simp only [Lamport.selectedLabels, Vector.getElem_ofFn]
    rw [dif_pos (show index < 254 from bound)]
    rfl
  · apply Vector.ext
    intro index bound
    simp only [Lamport.selectedLabels, Vector.getElem_ofFn]
    rw [dif_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rfl

theorem zero_xor_block (a : Block) : (0 : Block) ^^^ a = a := BitVec.zero_xor

section Assembly

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]
  (stage : LState) (table : Public) (bits : BitInput) (tape : Tape)

open Classical in
/-- **(c) The fold hits of both lanes, averaged over the key.** -/
theorem key_sum_le :
    ∑' key, PMF.uniformOfFintype InputMacKey key *
      ((if (stage.fixed (foldIndex .curveX bits true)).knownInput
          (curveLabel table (key.encode bits)).toFin then 1 else 0) +
        expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
            (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage noRecord ∅)
          (fun q => if (stage.fixed (foldIndex .pointX bits true)).knownInput
            (pointLabel table (key.encode bits) q.1).toFin then 1 else 0)) ≤
      ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * ((stage.fixed (foldIndex .curveX bits true)).used +
        (stage.fixed (foldIndex .pointX bits true)).used) := by
  rw [key_resample]
  set bit := bits.xBits.getLsb ⟨0, by decide⟩
  have inner : ∀ key : InputMacKey,
      ∑' pair, PMF.uniformOfFintype BitAdaptor.Key pair *
        ((if (stage.fixed (foldIndex .curveX bits true)).knownInput
            (curveLabel table ((setX0 key pair).encode bits)).toFin then 1 else 0) +
          expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
              (curveRest table bits ((setX0 key pair).encode bits) (curveMasks bits tape)) stage
              noRecord ∅)
            (fun q => if (stage.fixed (foldIndex .pointX bits true)).knownInput
              (pointLabel table ((setX0 key pair).encode bits) q.1).toFin then 1 else 0)) ≤
        ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * ((stage.fixed (foldIndex .curveX bits true)).used +
          (stage.fixed (foldIndex .pointX bits true)).used) := by
    intro key
    simp only [curveLabel_eq, pointLabel_eq, encode_setX0_zero, curveRest_setX0]
    set μ := runRefillT bits (fun cell => PMF.pure (tape cell))
      (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage noRecord ∅
    simp only [mul_add]
    rw [ENNReal.tsum_add]
    refine add_le_add ?_ ?_
    · have mapped := tsum_map_mul (PMF.uniformOfFintype BitAdaptor.Key)
        (fun pair => BitAdaptor.encode pair bit)
        (fun a : Block => if (stage.fixed (foldIndex .curveX bits true)).knownInput a.toFin
          then (1 : ℝ≥0∞) else 0)
      rw [uniform_encode] at mapped
      rw [← mapped]
      have shifted := uniform_known_sum (stage.fixed (foldIndex .curveX bits true)) 0
      simp only [zero_xor_block] at shifted
      exact shifted.le
    · rw [tsum_congr fun pair => (expectO_mul_left μ _ _).symm, ← expectO_tsum]
      refine (expectO_mono μ fun q => ?_).trans (expectO_const_le μ _)
      have mapped := tsum_map_mul (PMF.uniformOfFintype BitAdaptor.Key)
        (fun pair => BitAdaptor.encode pair bit)
        (fun a : Block => if (stage.fixed (foldIndex .pointX bits true)).knownInput
          ((q.1 .x ⟨0, by decide⟩).1 ^^^ a).toFin then (1 : ℝ≥0∞) else 0)
      rw [uniform_encode] at mapped
      rw [← mapped]
      exact (uniform_known_sum _ _).le
  calc _ ≤ ∑' key, PMF.uniformOfFintype InputMacKey key *
          (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * ((stage.fixed (foldIndex .curveX bits true)).used +
            (stage.fixed (foldIndex .pointX bits true)).used)) :=
        ENNReal.tsum_le_tsum fun key => mul_le_mul_of_nonneg_left (inner key) zero_le
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ### The four families are disjoint abort sites -/

/-- The stage-1 entries at one index, as an extended real. -/
abbrev entries (index : FixedIndex) : ℝ≥0∞ := ((stage.fixed index).used : ℝ≥0∞)

theorem isFoldAbort_fold (lane : Lane) (inLanes : lane = .pointX ∨ lane = .curveX) :
    IsFoldAbort (foldIndex lane bits true) := by
  refine ⟨inLanes, rfl, ?_⟩
  simp [chunkBits]

/-- The two level-1 fold halves `i₁ᶜ` and `i₁` hold at most the fold sites' entries. -/
theorem folds_le :
    entries stage (foldIndex .curveX bits true) + entries stage (foldIndex .pointX bits true) ≤
      ∑ index : {index : FixedIndex // IsFoldAbort index},
        ((stage.fixed index.val).used : ℝ≥0∞) := by
  classical
  set first : {index : FixedIndex // IsFoldAbort index} :=
    ⟨foldIndex .curveX bits true, isFoldAbort_fold bits .curveX (Or.inr rfl)⟩
  set second : {index : FixedIndex // IsFoldAbort index} :=
    ⟨foldIndex .pointX bits true, isFoldAbort_fold bits .pointX (Or.inl rfl)⟩
  have different : first ≠ second := by
    intro same
    have := congrArg Subtype.val same
    simp [first, second, foldIndex, hotIndexNat] at this
  calc entries stage (foldIndex .curveX bits true) + entries stage (foldIndex .pointX bits true)
      = ∑ index ∈ ({first, second} : Finset _), ((stage.fixed index.val).used : ℝ≥0∞) := by
        rw [Finset.sum_pair different]
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- The `curveX` chunk-0 cells and the designated cells, as abort cells. -/
def abortCellOf :
    (Fin (2 ^ chunkWidth chunkZero) × Fin (limbCount .curveX)) ⊕ Fin (limbCount .pointX) →
      {cell : Cell // IsCellAbort cell}
  | .inl site => ⟨maskCell .curveX chunkZero site.1 site.2, Or.inr rfl, rfl⟩
  | .inr limb => ⟨maskCell .pointX chunkZero (designatedSwitch bits) limb, Or.inl rfl, rfl⟩

theorem abortCellOf_injective : Function.Injective (abortCellOf bits) := by
  rintro (⟨switch, limb⟩ | limb) (⟨switch', limb'⟩ | limb') same <;>
    have cellEq := congrArg Subtype.val same
  · simp only [abortCellOf] at cellEq
    exact congrArg Sum.inl (maskCell_injective .curveX chunkZero (a₁ := (switch, limb))
      (a₂ := (switch', limb')) cellEq)
  · simp [abortCellOf, maskCell] at cellEq
  · simp [abortCellOf, maskCell] at cellEq
  · simp only [abortCellOf] at cellEq
    exact congrArg Sum.inr (congrArg Prod.snd (maskCell_injective .pointX chunkZero
      (a₁ := (designatedSwitch bits, limb)) (a₂ := (designatedSwitch bits, limb')) cellEq))

/-- The `curveX` chunk-0 entries and the designated entries hold at most the abort cells'
entries. -/
theorem cells_le :
    maskCharge stage .curveX + slotCharge stage bits ≤
      ∑ cell : {cell : Cell // IsCellAbort cell},
        (hashCount (cellInput cell.val) stage : ℝ≥0∞) := by
  classical
  calc maskCharge stage .curveX + slotCharge stage bits
      = ∑ site, (hashCount (cellInput (abortCellOf bits site).val) stage : ℝ≥0∞) := by
        rw [Fintype.sum_sum_type, maskCharge, slotCharge, Fintype.sum_prod_type]
        rfl
    _ = ∑ cell ∈ Finset.univ.map ⟨abortCellOf bits, abortCellOf_injective bits⟩,
          (hashCount (cellInput cell.val) stage : ℝ≥0∞) := by
        rw [Finset.sum_map]
        rfl
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **The four families are disjoint abort sites**: their entries sum to at most `abortUse`. -/
theorem families_le_abortUse :
    entries stage (foldIndex .curveX bits true) + entries stage (foldIndex .pointX bits true) +
        maskCharge stage .curveX + slotCharge stage bits ≤ (abortUse stage : ℝ≥0∞) := by
  rw [add_assoc]
  refine (add_le_add (folds_le stage bits) (cells_le stage bits)).trans (le_of_eq ?_)
  unfold abortUse
  push_cast
  rw [Fintype.sum_sum_type]
  rfl

/-! ### The charges -/

theorem charge_eq (queries : ℕ) (small : queries < 2 ^ 100) :
    ENNReal.ofReal (abortQueryCharge queries) = (((2 ^ 128 - queries : ℕ) : ℝ≥0∞))⁻¹ := by
  have le : queries ≤ 2 ^ 128 := by omega
  have cast : ((2 ^ 128 - queries : ℕ) : ℝ) = 2 ^ 128 - (queries : ℝ) := by
    rw [Nat.cast_sub le]
    push_cast
    ring
  have pos : (0 : ℝ) < 2 ^ 128 - queries := lt_of_lt_of_le (by positivity) (room_le queries small)
  unfold abortQueryCharge
  rw [one_div, ENNReal.ofReal_inv_of_pos pos, ← cast, ENNReal.ofReal_natCast]

theorem freshCharge_le_kappa (state : SparsePermutation (2 ^ 128)) (queries : ℕ)
    (used : state.used ≤ queries) :
    freshCharge state ≤ (((2 ^ 128 - queries : ℕ) : ℝ≥0∞))⁻¹ :=
  ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (Nat.sub_le_sub_left used _))

theorem inv_two_pow_le_kappa (queries : ℕ) :
    ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤ (((2 ^ 128 - queries : ℕ) : ℝ≥0∞))⁻¹ :=
  ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (Nat.sub_le _ _))

/-- **The per-tape bound, charged.** -/
theorem bound_le_charge (queries : ℕ) (small : queries < 2 ^ 100)
    (usedLe : ∀ index, (stage.fixed index).used ≤ queries) :
    ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * (entries stage (foldIndex .curveX bits true) +
        entries stage (foldIndex .pointX bits true)) +
      (freshCharge (stage.fixed (foldIndex .curveX bits true)) * maskCharge stage .curveX +
        freshCharge (stage.fixed (foldIndex .pointX bits true)) * slotCharge stage bits) ≤
      ENNReal.ofReal (abortQueryCharge queries) * (abortUse stage : ℝ≥0∞) := by
  set κ := (((2 ^ 128 - queries : ℕ) : ℝ≥0∞))⁻¹
  rw [charge_eq queries small]
  calc _ ≤ κ * (entries stage (foldIndex .curveX bits true) +
          entries stage (foldIndex .pointX bits true)) +
        (κ * maskCharge stage .curveX + κ * slotCharge stage bits) :=
        add_le_add (mul_le_mul_of_nonneg_right (inv_two_pow_le_kappa queries) zero_le)
          (add_le_add (mul_le_mul_of_nonneg_right (freshCharge_le_kappa _ _ (usedLe _)) zero_le)
            (mul_le_mul_of_nonneg_right (freshCharge_le_kappa _ _ (usedLe _)) zero_le))
    _ = κ * (entries stage (foldIndex .curveX bits true) +
          entries stage (foldIndex .pointX bits true) + maskCharge stage .curveX +
          slotCharge stage bits) := by ring
    _ ≤ κ * (abortUse stage : ℝ≥0∞) :=
        mul_le_mul_of_nonneg_left (families_le_abortUse stage bits) zero_le

end Assembly

section Final

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **The per-tape key average.** -/
theorem perTape_le (stage : LState) (table : Public) (bits : BitInput) (tape : Tape) :
    ∑' key, PMF.uniformOfFintype InputMacKey key *
      ((if (stage.fixed (foldIndex .curveX bits true)).knownInput
          (curveLabel table (key.encode bits)).toFin then 1 else 0) +
        freshCharge (stage.fixed (foldIndex .curveX bits true)) * maskCharge stage .curveX +
        expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
          (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage noRecord ∅)
          (fun q => pointBound stage table bits (key.encode bits) q.1)) ≤
      ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * (entries stage (foldIndex .curveX bits true) +
          entries stage (foldIndex .pointX bits true)) +
        (freshCharge (stage.fixed (foldIndex .curveX bits true)) * maskCharge stage .curveX +
          freshCharge (stage.fixed (foldIndex .pointX bits true)) * slotCharge stage bits) := by
  classical
  set C := freshCharge (stage.fixed (foldIndex .curveX bits true)) * maskCharge stage .curveX +
    freshCharge (stage.fixed (foldIndex .pointX bits true)) * slotCharge stage bits
  have each : ∀ key : InputMacKey,
      ((if (stage.fixed (foldIndex .curveX bits true)).knownInput
          (curveLabel table (key.encode bits)).toFin then 1 else 0) +
        freshCharge (stage.fixed (foldIndex .curveX bits true)) * maskCharge stage .curveX +
        expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
          (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage noRecord ∅)
          (fun q => pointBound stage table bits (key.encode bits) q.1)) ≤
      ((if (stage.fixed (foldIndex .curveX bits true)).knownInput
          (curveLabel table (key.encode bits)).toFin then 1 else 0) +
        expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
            (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage noRecord ∅)
          (fun q => if (stage.fixed (foldIndex .pointX bits true)).knownInput
            (pointLabel table (key.encode bits) q.1).toFin then 1 else 0)) + C := by
    intro key
    set μ := runRefillT bits (fun cell => PMF.pure (tape cell))
      (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage noRecord ∅
    unfold pointBound
    rw [expectO_add]
    have constant := expectO_const_le μ (freshCharge (stage.fixed (foldIndex .pointX bits true)) *
      slotCharge stage bits)
    calc _ ≤ (if (stage.fixed (foldIndex .curveX bits true)).knownInput
          (curveLabel table (key.encode bits)).toFin then (1 : ℝ≥0∞) else 0) +
          freshCharge (stage.fixed (foldIndex .curveX bits true)) * maskCharge stage .curveX +
          (expectO μ (fun q => if (stage.fixed (foldIndex .pointX bits true)).knownInput
            (pointLabel table (key.encode bits) q.1).toFin then 1 else 0) +
          freshCharge (stage.fixed (foldIndex .pointX bits true)) * slotCharge stage bits) :=
          add_le_add le_rfl (add_le_add le_rfl constant)
      _ = _ := by ring
  calc _ ≤ ∑' key, PMF.uniformOfFintype InputMacKey key *
        (((if (stage.fixed (foldIndex .curveX bits true)).knownInput
            (curveLabel table (key.encode bits)).toFin then 1 else 0) +
          expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
              (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage noRecord ∅)
            (fun q => if (stage.fixed (foldIndex .pointX bits true)).knownInput
              (pointLabel table (key.encode bits) q.1).toFin then 1 else 0)) + C) :=
        ENNReal.tsum_le_tsum fun key => mul_le_mul_of_nonneg_left (each key) zero_le
    _ = ∑' key, PMF.uniformOfFintype InputMacKey key *
        ((if (stage.fixed (foldIndex .curveX bits true)).knownInput
            (curveLabel table (key.encode bits)).toFin then 1 else 0) +
          expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
              (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage noRecord ∅)
            (fun q => if (stage.fixed (foldIndex .pointX bits true)).knownInput
              (pointLabel table (key.encode bits) q.1).toFin then 1 else 0)) + C := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ _ := add_le_add (key_sum_le stage table bits tape) le_rfl

/-- **(d) The key-averaged failure bound**: `abortQueryCharge q = 1/(2^128 − q)` per stage-1 entry
at an abort site. -/
theorem keyAveragedFailBound : KeyAveragedFailBound := by
  intro _ _ _ _ source input target oracle queries small usedLe
  set bits := BitInput.ofAffine input
  set table := source.publicValue
  set bound := ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * (entries oracle (foldIndex .curveX bits true) +
      entries oracle (foldIndex .pointX bits true)) +
    (freshCharge (oracle.fixed (foldIndex .curveX bits true)) * maskCharge oracle .curveX +
      freshCharge (oracle.fixed (foldIndex .pointX bits true)) * slotCharge oracle bits)
  set A : Tape → InputMac → ℝ≥0∞ := fun tape mac =>
    (if (oracle.fixed (foldIndex .curveX bits true)).knownInput
        (curveLabel table mac).toFin then 1 else 0) +
      freshCharge (oracle.fixed (foldIndex .curveX bits true)) * maskCharge oracle .curveX +
      expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
        (curveRest table bits mac (curveMasks bits tape)) oracle noRecord ∅)
        (fun q => pointBound oracle table bits mac q.1)
  have perKey : ∀ key : InputMacKey,
      failMass table input (Lamport.selectedLabels (key.encode bits)) target oracle ≤
        ∑' tape, uniformMaskTape tape * A tape (key.encode bits) := by
    intro key
    have base := failMass_le_runs oracle table input target
      (Lamport.selectedLabels (key.encode bits))
    rw [restore_selectedLabels] at base
    exact base.trans (ENNReal.tsum_le_tsum fun tape => mul_le_mul_of_nonneg_left
      (opening_bound oracle table bits (key.encode bits) tape) zero_le)
  calc ∑' key, PMF.uniformOfFintype InputMacKey key *
        failMass table input (Lamport.selectedLabels (key.encode bits)) target oracle
      ≤ ∑' key, PMF.uniformOfFintype InputMacKey key *
          ∑' tape, uniformMaskTape tape * A tape (key.encode bits) :=
        ENNReal.tsum_le_tsum fun key => mul_le_mul_of_nonneg_left (perKey key) zero_le
    _ = ∑' tape, uniformMaskTape tape *
          ∑' key, PMF.uniformOfFintype InputMacKey key * A tape (key.encode bits) := by
        simp only [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun tape => tsum_congr fun key => by ring
    _ ≤ ∑' tape, uniformMaskTape tape * bound :=
        ENNReal.tsum_le_tsum fun tape => mul_le_mul_of_nonneg_left
          (perTape_le oracle table bits tape) zero_le
    _ = bound := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ ENNReal.ofReal (abortQueryCharge queries) * (abortUse oracle : ℝ≥0∞) :=
        bound_le_charge oracle bits queries small usedLe

/-- **The restated `AbortBound.perQuery`, proved**: `H → I^U` costs `abortQueryCharge q₁` per
stage-1 entry at an abort site. -/
theorem abortBound_perQuery' : AbortPerQuery' openedHybrid idealUniformHybrid :=
  abortBound_perQuery'_of keyAveragedFailBound

end Final

end

end Kriterion.ArgoMAC.Phase3.Lazy
