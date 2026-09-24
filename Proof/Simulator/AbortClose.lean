/-
**Abort-closeness**: the relation between a bounded (cut-off) sampler and its exact law.

`AbortClose ε bounded ideal` says that `bounded` is `ideal` with at most `ε` extra abort mass:
every value has at most its ideal mass, and the abort mass exceeds the ideal abort mass by at
most `ε`. The relation composes additively along abort-or-value binds (`bind_opt`), is preserved
by maps that keep `none` (`map_opt`), by binds out of a common law (`bind_common`) and by
independent products (`optionProduct`), and bounds the distance of two games' acceptance
probabilities (`advantage_le`).
-/

import Proof.Privacy.Phase3.Glue.AbstractSimulator

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-- A sum over `Option α` is its `none` term plus the sum over the values. -/
theorem tsum_option {α : Type} (f : Option α → ENNReal) :
    ∑' x, f x = f none + ∑' a, f (some a) := by
  rw [ENNReal.tsum_eq_add_tsum_ite none]
  congr 1
  rw [← Function.Injective.tsum_eq (Option.some_injective α)]
  · simp
  · intro x member
    cases x with
    | none => simp at member
    | some a => exact ⟨a, rfl⟩

/-- The value masses of a law sum to at most one. -/
theorem tsum_some_le_one {α : Type} (law : PMF (Option α)) : ∑' a, law (some a) ≤ 1 := by
  have total := law.tsum_coe
  rw [tsum_option] at total
  rw [← total]
  exact le_add_self

/-- The mass of `none` plus the value masses is one. -/
theorem none_add_tsum_some {α : Type} (law : PMF (Option α)) :
    law none + ∑' a, law (some a) = 1 := by
  rw [← tsum_option]
  exact law.tsum_coe

/-- `bounded` is `ideal` with at most `ε` extra abort mass. -/
def AbortClose {α : Type} (ε : ENNReal) (bounded ideal : PMF (Option α)) : Prop :=
  (∀ a, bounded (some a) ≤ ideal (some a)) ∧ bounded none ≤ ideal none + ε

namespace AbortClose

variable {α β : Type}

theorem refl (law : PMF (Option α)) : AbortClose 0 law law :=
  ⟨fun _ => le_rfl, by rw [add_zero]⟩

theorem mono {ε ε' : ENNReal} {bounded ideal : PMF (Option α)} (close : AbortClose ε bounded ideal)
    (le : ε ≤ ε') : AbortClose ε' bounded ideal :=
  ⟨close.1, close.2.trans (add_le_add le_rfl le)⟩

theorem trans {ε ε' : ENNReal} {bounded middle ideal : PMF (Option α)}
    (first : AbortClose ε bounded middle) (second : AbortClose ε' middle ideal) :
    AbortClose (ε + ε') bounded ideal :=
  ⟨fun a => (first.1 a).trans (second.1 a), by
    calc bounded none ≤ middle none + ε := first.2
      _ ≤ ideal none + ε' + ε := add_le_add second.2 le_rfl
      _ = ideal none + (ε + ε') := by ring⟩

/-- A law without aborts is abort-close to another if its value masses are pointwise below. -/
theorem of_le {ε : ENNReal} {bounded ideal : PMF (Option α)}
    (values : ∀ a, bounded (some a) ≤ ideal (some a)) (aborts : bounded none ≤ ideal none + ε) :
    AbortClose ε bounded ideal := ⟨values, aborts⟩

/-- **Maps that keep `none`.** -/
theorem map_opt {ε : ENNReal} {bounded ideal : PMF (Option α)} (close : AbortClose ε bounded ideal)
    (g : Option α → Option β) (keep : g none = none) :
    AbortClose ε (bounded.map g) (ideal.map g) := by
  refine ⟨fun b => ?_, ?_⟩
  · rw [PMF.map_apply, PMF.map_apply, tsum_option, tsum_option, keep]
    simp only [reduceCtorEq, if_false, zero_add]
    exact ENNReal.tsum_le_tsum fun a => by split <;> [exact close.1 a; exact le_rfl]
  · rw [PMF.map_apply, PMF.map_apply, tsum_option, tsum_option, keep]
    simp only [if_true]
    rw [add_right_comm]
    refine add_le_add close.2 (ENNReal.tsum_le_tsum fun a => ?_)
    split
    · exact close.1 a
    · exact le_rfl

/-- **Abort-or-value binds**: the extra abort masses add. -/
theorem bind_opt {ε ε' : ENNReal} {bounded ideal : PMF (Option α)}
    (close : AbortClose ε bounded ideal) (next next' : Option α → PMF (Option β))
    (stop : next none = PMF.pure none) (stop' : next' none = PMF.pure none)
    (step : ∀ a, AbortClose ε' (next (some a)) (next' (some a))) :
    AbortClose (ε + ε') (bounded.bind next) (ideal.bind next') := by
  refine ⟨fun b => ?_, ?_⟩
  · rw [PMF.bind_apply, PMF.bind_apply, tsum_option, tsum_option, stop, stop']
    simp only [PMF.pure_apply, reduceCtorEq, if_false, mul_zero, zero_add]
    exact ENNReal.tsum_le_tsum fun a => mul_le_mul' (close.1 a) ((step a).1 b)
  · rw [PMF.bind_apply, PMF.bind_apply, tsum_option, tsum_option, stop, stop']
    simp only [PMF.pure_apply, if_true, mul_one]
    calc bounded none + ∑' a, bounded (some a) * next (some a) none
        ≤ (ideal none + ε) + ∑' a, bounded (some a) * (next' (some a) none + ε') :=
          add_le_add close.2 (ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (step a).2)
      _ = (ideal none + ε) + (∑' a, bounded (some a) * next' (some a) none +
            (∑' a, bounded (some a)) * ε') := by
          rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
          simp only [mul_add]
      _ ≤ (ideal none + ε) + (∑' a, ideal (some a) * next' (some a) none + 1 * ε') :=
          add_le_add le_rfl (add_le_add
            (ENNReal.tsum_le_tsum fun a => mul_le_mul' (close.1 a) le_rfl)
            (mul_le_mul' (tsum_some_le_one bounded) le_rfl))
      _ = ideal none + ∑' a, ideal (some a) * next' (some a) none + (ε + ε') := by ring

/-- **Binds out of a common law.** -/
theorem bind_common {γ : Type} {ε : ENNReal} (common : PMF γ) (next next' : γ → PMF (Option β))
    (step : ∀ c, AbortClose ε (next c) (next' c)) :
    AbortClose ε (common.bind next) (common.bind next') := by
  refine ⟨fun b => ?_, ?_⟩
  · rw [PMF.bind_apply, PMF.bind_apply]
    exact ENNReal.tsum_le_tsum fun c => mul_le_mul' le_rfl ((step c).1 b)
  · rw [PMF.bind_apply, PMF.bind_apply]
    calc ∑' c, common c * next c none ≤ ∑' c, common c * (next' c none + ε) :=
          ENNReal.tsum_le_tsum fun c => mul_le_mul' le_rfl (step c).2
      _ = ∑' c, common c * next' c none + (∑' c, common c) * ε := by
          rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
          simp only [mul_add]
      _ = ∑' c, common c * next' c none + ε := by rw [common.tsum_coe, one_mul]

/-- **Independent products**: `count` draws, each at most `ε` from its ideal, are at most
`count · ε` from the ideal product. -/
theorem optionProduct {ε : ENNReal} :
    ∀ (count : Nat) (bounded ideal : Fin count → PMF (Option α)),
      (∀ index, AbortClose ε (bounded index) (ideal index)) →
        AbortClose (count * ε) (Phase3.Glue.optionProduct count bounded)
          (Phase3.Glue.optionProduct count ideal)
  | 0, _, _, _ => by
      simp only [Nat.cast_zero, zero_mul]
      exact refl _
  | count + 1, bounded, ideal, each => by
      have rest := optionProduct count (fun index => bounded index.succ)
        (fun index => ideal index.succ) (fun index => each index.succ)
      have shape : ((count + 1 : Nat) : ENNReal) * ε = ε + count * ε := by push_cast; ring
      rw [shape]
      exact bind_opt (each 0) _ _ rfl rfl fun head =>
        map_opt rest _ rfl

end AbortClose

/-! ### From abort-closeness to the advantage -/

/-- The acceptance probability of a game read off an abort-or-bit law. -/
theorem map_getD_true (law : PMF (Option Bool)) :
    (law.map fun result => result.getD false) true = law (some true) := by
  rw [PMF.map_apply, tsum_option]
  simp only [Option.getD_none, Bool.true_eq_false, if_false, zero_add]
  rw [tsum_eq_single true]
  · simp
  · intro value other
    cases value
    · simp
    · exact absurd rfl other

/-- **Abort-closeness bounds the advantage**: aborts count as `false` on both sides. -/
theorem advantage_le {ε : ENNReal} {bounded ideal : PMF (Option Bool)}
    (close : AbortClose ε bounded ideal) (finite : ε ≠ ⊤) :
    Assumptions.advantage (ideal.map fun result => result.getD false)
      (bounded.map fun result => result.getD false) ≤ ε.toReal := by
  rw [Assumptions.advantage, map_getD_true, map_getD_true]
  have upper : bounded (some true) ≤ ideal (some true) := close.1 true
  have lower : ideal (some true) ≤ bounded (some true) + ε := by
    have totalI := none_add_tsum_some ideal
    have totalB := none_add_tsum_some bounded
    rw [tsum_fintype, Fintype.sum_bool] at totalI totalB
    have falseLe : bounded (some false) ≤ ideal (some false) := close.1 false
    have finiteI : ideal none + ideal (some false) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩
    have key : ideal (some true) + (ideal none + ideal (some false)) ≤
        (bounded (some true) + ε) + (ideal none + ideal (some false)) := by
      calc ideal (some true) + (ideal none + ideal (some false))
          = ideal none + (ideal (some true) + ideal (some false)) := by ring
        _ = 1 := totalI
        _ = bounded none + (bounded (some true) + bounded (some false)) := totalB.symm
        _ ≤ (ideal none + ε) + (bounded (some true) + ideal (some false)) :=
            add_le_add close.2 (add_le_add le_rfl falseLe)
        _ = (bounded (some true) + ε) + (ideal none + ideal (some false)) := by ring
    exact (ENNReal.add_le_add_iff_right finiteI).mp key
  have finiteB : bounded (some true) ≠ ⊤ := PMF.apply_ne_top _ _
  have finiteIt : ideal (some true) ≠ ⊤ := PMF.apply_ne_top _ _
  rw [abs_le]
  constructor
  · have := ENNReal.toReal_mono finiteIt upper
    linarith [ENNReal.toReal_nonneg (a := ε)]
  · have step := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨finiteB, finite⟩) lower
    rw [ENNReal.toReal_add finiteB finite] at step
    linarith

end

end Kriterion.ArgoMAC.PlanB.SimMachine
