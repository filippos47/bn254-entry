/-
**Phase 3, P1d — planting in one sparse permutation: one query.**

`SparseRel sF sL D Dinv`: the sparse permutation `sF` is `sL` with the finite injection `D`
(inverse `Dinv`) planted on top, and `D`'s inputs and outputs are both still free in `sL`.

`sparse_forward_step`: one forward query, answered in `sF` (planted first) against `sL` (planted
later), with the later side charged `0` whenever the query **touches** `D` (its input is planted,
or its fresh answer is a planted output). Off a touch the later answer is uniform on
`Unknown sL`, the earlier one on the smaller set `Unknown sF = Unknown sL ∖ range D`, so every
later outcome has at least its mass on the earlier side, and the two new states are again related.
`sparse_inverse_step` is the same through `SparsePermutation.inverse_reverse_forward`.
-/

import Proof.Privacy.Phase3.PublicFirst.Sparse

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open Cryptography
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

variable {size : ℕ}

/-- A planted value, else the base lookup. -/
def overlay {α : Type} (planted base : Option α) : Option α :=
  match planted with
  | some value => some value
  | none => base

@[simp] theorem overlay_none {α : Type} (base : Option α) : overlay none base = base := rfl

@[simp] theorem overlay_some {α : Type} (value : α) (base : Option α) :
    overlay (some value) base = some value := rfl

/-- `sF` is `sL` with the finite injection `D` (inverse `Dinv`) planted on fresh points. -/
structure SparseRel (sF sL : SparsePermutation size) (D Dinv : Fin size → Option (Fin size)) :
    Prop where
  lookup : ∀ z, lk sF z = overlay (D z) (lk sL z)
  inverse : ∀ z y, D z = some y ↔ Dinv y = some z
  freshInput : ∀ z, D z ≠ none → lk sL z = none
  freshOutput : ∀ y, Dinv y ≠ none → ∀ w, lk sL w ≠ some y

/-- A forward query at `x` answered `a` touches the planted map. -/
def TouchForward (D Dinv : Fin size → Option (Fin size)) (x a : Fin size) : Prop :=
  D x ≠ none ∨ Dinv a ≠ none

instance (D Dinv : Fin size → Option (Fin size)) (x a : Fin size) :
    Decidable (TouchForward D Dinv x a) := by
  unfold TouchForward
  infer_instance

/-- `∑ (μ.map g) · f = ∑ μ · (f ∘ g)`. -/
theorem tsum_map_mul {α β : Type} (μ : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    ∑' o, (μ.map g) o * f o = ∑' a, μ a * f (g a) := by
  classical
  simp only [PMF.map_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (g a)]
  · rw [if_pos rfl]
  · intro o different
    rw [if_neg different, zero_mul]

theorem SparseRel.knownOutput_L {sF sL : SparsePermutation size} {D Dinv}
    (rel : SparseRel sF sL D Dinv) {y : Fin size} (known : sL.knownOutput y) : sF.knownOutput y := by
  obtain ⟨w, found⟩ := (knownOutput_iff sL y).mp known
  refine (knownOutput_iff sF y).mpr ⟨w, ?_⟩
  rw [rel.lookup]
  cases planted : D w with
  | none => simpa using found
  | some value =>
    have := rel.freshInput w (by simp [planted])
    rw [this] at found
    cases found

theorem SparseRel.knownOutput_F {sF sL : SparsePermutation size} {D Dinv}
    (rel : SparseRel sF sL D Dinv) {y : Fin size} (known : sF.knownOutput y) :
    sL.knownOutput y ∨ Dinv y ≠ none := by
  obtain ⟨w, found⟩ := (knownOutput_iff sF y).mp known
  rw [rel.lookup] at found
  cases planted : D w with
  | none =>
    rw [planted] at found
    exact Or.inl ((knownOutput_iff sL y).mpr ⟨w, found⟩)
  | some value =>
    rw [planted] at found
    cases found
    exact Or.inr (by rw [(rel.inverse w _).mp planted]; simp)

/-- A fresh step on both sides keeps the relation. -/
theorem SparseRel.extend {sF sL : SparsePermutation size} {D Dinv}
    (rel : SparseRel sF sL D Dinv) (x y : Fin size) (planted : D x = none)
    (freshL : ¬ sL.knownInput x) (freshF : ¬ sF.knownInput x)
    (outL : ¬ sL.knownOutput y) (outF : ¬ sF.knownOutput y) (notPlanted : Dinv y = none)
    (roomL : sL.used < size) (roomF : sF.used < size) :
    SparseRel (sF.extend roomF (sF.input.symm x) (sF.output.symm y))
      (sL.extend roomL (sL.input.symm x) (sL.output.symm y)) D Dinv where
  lookup z := by
    rw [lookup_extend sF x y freshF outF roomF, lookup_extend sL x y freshL outL roomL]
    by_cases same : z = x
    · subst same
      rw [if_pos rfl, if_pos rfl, planted, overlay_none]
    · rw [if_neg same, if_neg same, rel.lookup]
  inverse := rel.inverse
  freshInput z plantedZ := by
    rw [lookup_extend sL x y freshL outL roomL]
    have different : z ≠ x := fun same => plantedZ (same ▸ planted)
    rw [if_neg different, rel.freshInput z plantedZ]
  freshOutput value plantedValue w := by
    rw [lookup_extend sL x y freshL outL roomL]
    by_cases same : w = x
    · rw [if_pos same]
      intro equal
      cases equal
      exact plantedValue notPlanted
    · rw [if_neg same]
      exact rel.freshOutput value plantedValue w

/-- **One forward query.** -/
theorem sparse_forward_step {sF sL : SparsePermutation size} {D Dinv}
    (rel : SparseRel sF sL D Dinv) (x : Fin size)
    (hF hL : Fin size × SparsePermutation size → ℝ≥0∞)
    (mono : ∀ a sF' sL', SparseRel sF' sL' D Dinv → hL (a, sL') ≤ hF (a, sF')) :
    ∑' o, (sL.forward x).distribution o * (if TouchForward D Dinv x o.1 then 0 else hL o)
      ≤ ∑' o, (sF.forward x).distribution o * hF o := by
  classical
  by_cases planted : D x = none
  swap
  · refine le_trans (le_of_eq ?_) zero_le
    refine ENNReal.tsum_eq_zero.mpr fun o => ?_
    rw [if_pos (show TouchForward D Dinv x o.1 from Or.inl planted), mul_zero]
  by_cases knownL : sL.knownInput x
  · -- a stored answer on both sides
    have lookupL : lk sL x = some (sL.output (sL.input.symm x)) := by
      rw [lk_eq, if_pos knownL]
    have lookupF : lk sF x = some (sL.output (sL.input.symm x)) := by
      rw [rel.lookup, planted, overlay_none, lookupL]
    have knownF : sF.knownInput x := (knownInput_iff sF x).mpr (by rw [lookupF]; simp)
    have valueF : sF.output (sF.input.symm x) = sL.output (sL.input.symm x) := by
      have := lookupF
      rw [lk_eq, if_pos knownF] at this
      exact Option.some.inj this
    have forwardL : (sL.forward x).distribution = PMF.pure (sL.output (sL.input.symm x), sL) := by
      unfold SparsePermutation.forward
      dsimp only
      rw [dif_pos (show (sL.input.symm x).val < sL.used from knownL)]
      rfl
    have forwardF : (sF.forward x).distribution = PMF.pure (sF.output (sF.input.symm x), sF) := by
      unfold SparsePermutation.forward
      dsimp only
      rw [dif_pos (show (sF.input.symm x).val < sF.used from knownF)]
      rfl
    rw [forwardL, forwardF, tsum_eq_single (sL.output (sL.input.symm x), sL),
      tsum_eq_single (sF.output (sF.input.symm x), sF)]
    · rw [PMF.pure_apply, if_pos rfl, one_mul, PMF.pure_apply, if_pos rfl, one_mul]
      have untouched : ¬ TouchForward D Dinv x (sL.output (sL.input.symm x)) := by
        rintro (plantedX | plantedOut)
        · exact plantedX planted
        · exact rel.freshOutput _ plantedOut x lookupL
      rw [if_neg untouched, valueF]
      exact mono _ sF sL rel
    · intro o different
      rw [PMF.pure_apply, if_neg different, zero_mul]
    · intro o different
      rw [PMF.pure_apply, if_neg different, zero_mul]
  · -- a fresh input on both sides
    have lookupF : lk sF x = none := by
      rw [rel.lookup, planted, overlay_none, lk_eq, if_neg knownL]
    have knownF : ¬ sF.knownInput x := fun known =>
      ((knownInput_iff sF x).mp known) lookupF
    obtain ⟨roomL, nonemptyL, forwardL⟩ := forward_fresh_eq sL x knownL
    obtain ⟨roomF, nonemptyF, forwardF⟩ := forward_fresh_eq sF x knownF
    rw [forwardL, forwardF, tsum_map_mul, tsum_map_mul]
    -- sums over the unknown outputs, as indicator sums over all outputs
    have cardLe : Fintype.card (Unknown sF) ≤ Fintype.card (Unknown sL) :=
      Fintype.card_le_of_injective (fun y : Unknown sF => (⟨y.val, fun known =>
        y.property (rel.knownOutput_L known)⟩ : Unknown sL))
        (fun a b same => Subtype.ext (by simpa using congrArg Subtype.val same))
    have massLe : (Fintype.card (Unknown sL) : ℝ≥0∞)⁻¹ ≤ (Fintype.card (Unknown sF) : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_le_inv.mpr (by exact_mod_cast cardLe)
    let left : Fin size → ℝ≥0∞ := fun y =>
      if hy : ¬ sL.knownOutput y then
        (Fintype.card (Unknown sL) : ℝ≥0∞)⁻¹ *
          (if TouchForward D Dinv x y then 0 else
            hL (y, sL.extend roomL (sL.input.symm x) (sL.output.symm y)))
      else 0
    let right : Fin size → ℝ≥0∞ := fun y =>
      if hy : ¬ sF.knownOutput y then
        (Fintype.card (Unknown sF) : ℝ≥0∞)⁻¹ *
          hF (y, sF.extend roomF (sF.input.symm x) (sF.output.symm y))
      else 0
    have leftEq : ∑' y : Unknown sL, PMF.uniformOfFintype (Unknown sL) y *
        (if TouchForward D Dinv x y.val then 0 else
          hL (y.val, sL.extend roomL (sL.input.symm x) (sL.output.symm y.val)))
        = ∑' y, left y := by
      rw [← tsum_subtype_eq_of_support_subset (s := {y | ¬ sL.knownOutput y})]
      · refine tsum_congr fun y => ?_
        simp only [left, PMF.uniformOfFintype_apply, dif_pos y.property]
      · intro y inSupport
        by_contra outside
        simp only [Set.mem_ofPred_eq, not_not] at outside
        exact inSupport (by simp [left, outside])
    have rightEq : ∑' y : Unknown sF, PMF.uniformOfFintype (Unknown sF) y *
        hF (y.val, sF.extend roomF (sF.input.symm x) (sF.output.symm y.val))
        = ∑' y, right y := by
      rw [← tsum_subtype_eq_of_support_subset (s := {y | ¬ sF.knownOutput y})]
      · refine tsum_congr fun y => ?_
        simp only [right, PMF.uniformOfFintype_apply, dif_pos y.property]
      · intro y inSupport
        by_contra outside
        simp only [Set.mem_ofPred_eq, not_not] at outside
        exact inSupport (by simp [right, outside])
    change ∑' y : Unknown sL, PMF.uniformOfFintype (Unknown sL) y *
        (if TouchForward D Dinv x y.val then 0 else
          hL (y.val, sL.extend roomL (sL.input.symm x) (sL.output.symm y.val)))
      ≤ ∑' y : Unknown sF, PMF.uniformOfFintype (Unknown sF) y *
        hF (y.val, sF.extend roomF (sF.input.symm x) (sF.output.symm y.val))
    rw [leftEq, rightEq]
    refine ENNReal.tsum_le_tsum fun y => ?_
    simp only [left, right]
    by_cases outL : sL.knownOutput y
    · rw [dif_neg (not_not.mpr outL)]
      exact zero_le
    · rw [dif_pos outL]
      by_cases touched : TouchForward D Dinv x y
      · rw [if_pos touched, mul_zero]
        exact zero_le
      · rw [if_neg touched]
        have notPlanted : Dinv y = none := by
          by_contra plantedY
          exact touched (Or.inr plantedY)
        have outF : ¬ sF.knownOutput y := by
          intro known
          rcases rel.knownOutput_F known with inL | inD
          · exact outL inL
          · exact inD notPlanted
        rw [dif_pos outF]
        exact mul_le_mul' massLe (mono y _ _ (rel.extend x y planted knownL knownF outL outF
          notPlanted roomL roomF))

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open Cryptography
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

variable {size : ℕ}

/-- **Reversal exchanges the planted map and its inverse.** -/
theorem SparseRel.reverse {sF sL : SparsePermutation size} {D Dinv}
    (rel : SparseRel sF sL D Dinv) : SparseRel sF.reverse sL.reverse Dinv D where
  lookup w := by
    apply Option.ext
    intro z
    rw [lookup_reverse, rel.lookup]
    constructor
    · intro found
      cases planted : D z with
      | some v =>
        rw [planted, overlay_some] at found
        cases found
        rw [(rel.inverse z _).mp planted, overlay_some]
      | none =>
        rw [planted, overlay_none] at found
        have notPlanted : Dinv w = none := by
          by_contra plantedW
          exact rel.freshOutput w plantedW z found
        rw [notPlanted, overlay_none, lookup_reverse]
        exact found
    · intro found
      cases planted : Dinv w with
      | some v =>
        rw [planted, overlay_some] at found
        cases found
        rw [(rel.inverse z w).mpr planted, overlay_some]
      | none =>
        rw [planted, overlay_none, lookup_reverse] at found
        have notPlanted : D z = none := by
          by_contra plantedZ
          rw [rel.freshInput z plantedZ] at found
          cases found
        rw [notPlanted, overlay_none]
        exact found
  inverse z y := (rel.inverse y z).symm
  freshInput w plantedW := by
    cases found : lk sL.reverse w with
    | none => rfl
    | some z => exact absurd ((lookup_reverse sL z w).mp found) (rel.freshOutput w plantedW z)
  freshOutput z plantedZ w found := by
    have forward := (lookup_reverse sL z w).mp found
    rw [rel.freshInput z plantedZ] at forward
    cases forward

/-- **One inverse query**, through the reversed states. -/
theorem sparse_inverse_step {sF sL : SparsePermutation size} {D Dinv}
    (rel : SparseRel sF sL D Dinv) (y : Fin size)
    (hF hL : Fin size × SparsePermutation size → ℝ≥0∞)
    (mono : ∀ a sF' sL', SparseRel sF' sL' D Dinv → hL (a, sL') ≤ hF (a, sF')) :
    ∑' o, (sL.inverse y).distribution o * (if TouchForward Dinv D y o.1 then 0 else hL o)
      ≤ ∑' o, (sF.inverse y).distribution o * hF o := by
  rw [SparsePermutation.inverse_reverse_forward, SparsePermutation.inverse_reverse_forward,
    Draw.map_distribution, Draw.map_distribution, tsum_map_mul, tsum_map_mul]
  exact sparse_forward_step rel.reverse y (fun o => hF (o.1, o.2.reverse))
    (fun o => hL (o.1, o.2.reverse))
    (fun a sF' sL' related => mono a _ _ (by simpa using related.reverse))

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
