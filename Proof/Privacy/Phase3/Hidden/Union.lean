/-
**Phase 3, P1c — step 3, generic: the per-query union bound.**

`touch_mass_le`: if, for every value `v` of the view and every answered query `e`, the extra set
touched by `e` has mass at most `ε` jointly with `view = v` (`μ{view = v ∧ e touches} ≤
ε · μ{view = v}`), then a run that reads the view only and logs at most `n` queries touches the
extra set with mass at most `n · ε`. The run's randomness is independent of the extra set given
the view, which is what lets the bound be evaluated one query at a time.
-/

import Proof.Privacy.Phase3.Hidden.Bound

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open Kriterion.Cryptography
open scoped ENNReal

noncomputable section

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

open Classical in
/-- `1` on a touch, `0` otherwise. -/
def touchedWeight (H : Extra FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex) : ℝ≥0∞ :=
  if Touches H entry then 1 else 0

/-- The mass of a touch somewhere in the log is at most the number of touching entries. -/
theorem one_sub_clean_le (H : Extra FixedIndex EncIndex) (log : List (Asked FixedIndex EncIndex)) :
    1 - cleanWeight H log ≤ (log.map (touchedWeight H)).sum := by
  classical
  induction log with
  | nil => simp [cleanWeight_nil]
  | cons entry log ih =>
      rw [cleanWeight_cons, List.map_cons, List.sum_cons]
      unfold untouched touchedWeight
      by_cases touch : Touches H entry
      · simp only [if_pos touch, zero_mul, tsub_zero]
        exact le_self_add
      · simp only [if_neg touch, one_mul, zero_add]
        exact ih

theorem tsum_list_sum {α β : Type} (log : List β) (f : α → β → ℝ≥0∞) :
    ∑' a, (log.map (f a)).sum = (log.map fun b => ∑' a, f a b).sum := by
  induction log with
  | nil => simp
  | cons b log ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ENNReal.tsum_add, ih]

/-- **The union bound.** -/
theorem touch_mass_le {Ω View X : Type} (μ : PMF Ω) (view : Ω → View)
    (extra : Ω → Extra FixedIndex EncIndex) (run : View → PMF (X × List (Asked FixedIndex EncIndex)))
    (n : ℕ) (length : ∀ v o, o ∈ (run v).support → o.2.length ≤ n) (ε : ℝ≥0∞)
    (guess : ∀ v e, μ.toOuterMeasure {ω | view ω = v ∧ Touches (extra ω) e} ≤
      ε * μ.toOuterMeasure {ω | view ω = v}) :
    expect μ (fun ω => expect (run (view ω)) (fun o => 1 - cleanWeight (extra ω) o.2)) ≤
      n * ε := by
  classical
  let P : View → ℝ≥0∞ := fun v => μ.toOuterMeasure {ω | view ω = v}
  have fibre : ∀ ω, μ ω = ∑' v, if view ω = v then μ ω else 0 := fun ω => by
    rw [tsum_eq_single (view ω)]
    · rw [if_pos rfl]
    · intro v ne
      rw [if_neg (Ne.symm ne)]
  have touchMass : ∀ v e, ∑' ω, (if view ω = v then μ ω else 0) * touchedWeight (extra ω) e =
      μ.toOuterMeasure {ω | view ω = v ∧ Touches (extra ω) e} := by
    intro v e
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun ω => ?_
    unfold touchedWeight Set.indicator
    by_cases same : view ω = v <;> by_cases touch : Touches (extra ω) e <;> simp [same, touch]
  have total : ∑' v, P v = 1 := by
    have mapped : ∀ v, P v = (μ.map view) v := by
      intro v
      show μ.toOuterMeasure {ω | view ω = v} = _
      rw [PMF.map_apply, PMF.toOuterMeasure_apply]
      refine tsum_congr fun ω => ?_
      unfold Set.indicator
      by_cases same : view ω = v
      · simp [same]
      · simp [same, Ne.symm same]
    simp_rw [mapped]
    exact (μ.map view).tsum_coe
  calc expect μ (fun ω => expect (run (view ω)) (fun o => 1 - cleanWeight (extra ω) o.2))
      ≤ expect μ (fun ω => expect (run (view ω))
          (fun o => (o.2.map (touchedWeight (extra ω))).sum)) :=
        expect_mono _ fun ω => expect_mono _ fun o => one_sub_clean_le _ _
    _ = ∑' ω, ∑' v, (if view ω = v then μ ω else 0) *
          ∑' o, run v o * (o.2.map (touchedWeight (extra ω))).sum := by
        unfold expect
        refine tsum_congr fun ω => ?_
        conv_lhs => rw [fibre ω]
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun v => ?_
        by_cases same : view ω = v
        · subst same
          simp only [if_pos rfl]
        · rw [if_neg same, zero_mul, zero_mul]
    _ = ∑' v, ∑' o, run v o *
          (o.2.map fun e => ∑' ω, (if view ω = v then μ ω else 0) * touchedWeight (extra ω) e).sum := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun v => ?_
        have inner : ∀ ω, (if view ω = v then μ ω else 0) *
            ∑' o, run v o * (o.2.map (touchedWeight (extra ω))).sum =
            ∑' o, run v o * (o.2.map fun e =>
              (if view ω = v then μ ω else 0) * touchedWeight (extra ω) e).sum := by
          intro ω
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun o => ?_
          rw [List.sum_map_mul_left]
          ring
        simp_rw [inner]
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun o => ?_
        rw [ENNReal.tsum_mul_left, tsum_list_sum]
    _ ≤ ∑' v, ∑' o, run v o * (n * (ε * P v)) := by
        refine ENNReal.tsum_le_tsum fun v => ENNReal.tsum_le_tsum fun o => ?_
        by_cases zero : run v o = 0
        · rw [zero, zero_mul, zero_mul]
        · refine mul_le_mul' le_rfl ?_
          have short := length v o ((PMF.mem_support_iff _ _).mpr zero)
          calc (o.2.map fun e => ∑' ω, (if view ω = v then μ ω else 0) *
                touchedWeight (extra ω) e).sum
              ≤ (o.2.map fun _ => ε * P v).sum := by
                refine List.sum_le_sum fun e _ => ?_
                rw [touchMass]
                exact guess v e
            _ = o.2.length * (ε * P v) := by
                rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
            _ ≤ n * (ε * P v) := mul_le_mul' (Nat.cast_le.mpr short) le_rfl
    _ = ∑' v, n * ε * P v := by
        refine tsum_congr fun v => ?_
        rw [ENNReal.tsum_mul_right, (run v).tsum_coe, one_mul, mul_assoc]
    _ = n * ε := by rw [ENNReal.tsum_mul_left, total, mul_one]

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
