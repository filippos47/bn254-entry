/-
**Phase 3, P1b — the glue's identical-until-bad shapes are advantage bounds.**

`Glue.UntilBad first second ε` (flagged laws on `Bool × Bool` agreeing at every flag-down outcome,
bad mass `≤ ε`) holds **iff** `advantage first second ≤ ε` (for `ε ≥ 0`): the flags live on the
one-bit outcome, so the flag-down masses can always be taken to be `min(first b, second b)`
(`untilBad_of_advantage_le`), whose complement is exactly the advantage. Likewise
`Glue.CoreUntilBad` with the trivial core. Consequently `GameUntilBad` and `GameCoreUntilBad` are
exactly `HopBound`: the flagged shape documents how a hop is proved but does not constrain it, and a
hop is true iff its advantage bound is.
-/

import Proof.Privacy.Phase3.GameSwap

namespace Kriterion.ArgoMAC.Security.Phase3

open Cryptography
open Kriterion.ArgoMAC.Phase3.Glue (UntilBad CoreUntilBad badSet)
open scoped ENNReal

noncomputable section

/-- A law on `Bool × Bool` from its four masses. -/
def flaggedLaw (upTrue upFalse downTrue downFalse : ℝ≥0∞)
    (total : downTrue + upTrue + (downFalse + upFalse) = 1) : PMF (Bool × Bool) :=
  PMF.ofFintype (fun outcome => match outcome with
    | (true, false) => downTrue
    | (true, true) => upTrue
    | (false, false) => downFalse
    | (false, true) => upFalse) (by
      rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
      simpa [add_comm, add_left_comm, add_assoc] using total)

theorem flaggedLaw_fst (upTrue upFalse downTrue downFalse : ℝ≥0∞)
    (total : downTrue + upTrue + (downFalse + upFalse) = 1) (outcome : Bool) :
    (flaggedLaw upTrue upFalse downTrue downFalse total).map Prod.fst outcome
      = if outcome then downTrue + upTrue else downFalse + upFalse := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool,
    Fintype.sum_bool]
  cases outcome <;> simp [flaggedLaw, add_comm]

theorem flaggedLaw_bad (upTrue upFalse downTrue downFalse : ℝ≥0∞)
    (total : downTrue + upTrue + (downFalse + upFalse) = 1) :
    (flaggedLaw upTrue upFalse downTrue downFalse total).toOuterMeasure badSet = upTrue + upFalse := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.sum_bool, Fintype.sum_bool]
  simp [flaggedLaw, badSet, Set.indicator, add_comm]

/-- A `PMF Bool` is determined by its mass at `true`. -/
theorem pmf_bool_ext {first second : PMF Bool} (same : first true = second true) : first = second := by
  refine PMF.ext fun outcome => ?_
  cases outcome
  · rw [pmf_bool_false first, pmf_bool_false second, same]
  · exact same

/-- **Every advantage bound is an identical-until-bad pair.** -/
theorem untilBad_of_advantage_le {first second : PMF Bool} {error : ℝ}
    (bound : Assumptions.advantage first second ≤ error) : UntilBad first second error := by
  set a := first true
  set b := second true
  have aLe : a ≤ 1 := PMF.coe_le_one first true
  have bLe : b ≤ 1 := PMF.coe_le_one second true
  have aTop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top aLe
  have bTop : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top bLe
  have firstFalse : first false = 1 - a := pmf_bool_false first
  have secondFalse : second false = 1 - b := pmf_bool_false second
  have split (x y : ℝ≥0∞) (small : min x y ≤ x) : min x y + (x - min x y) = x :=
    add_tsub_cancel_of_le small
  have totalOf (x : ℝ≥0∞) (y z : ℝ≥0∞) (xLe : x ≤ 1) :
      min x y + (x - min x y) + (min (1 - x) z + ((1 - x) - min (1 - x) z)) = 1 := by
    rw [split _ _ (min_le_left _ _), split _ _ (min_le_left _ _)]
    exact add_tsub_cancel_of_le xLe
  refine ⟨flaggedLaw (a - min a b) ((1 - a) - min (1 - a) (1 - b)) (min a b) (min (1 - a) (1 - b))
      (totalOf a b (1 - b) aLe),
    flaggedLaw (b - min a b) ((1 - b) - min (1 - a) (1 - b)) (min a b) (min (1 - a) (1 - b))
      (by rw [min_comm a b, min_comm (1 - a) (1 - b)]; exact totalOf b a (1 - a) bLe),
    ?_, ?_, ?_, ?_⟩
  · refine pmf_bool_ext ?_
    rw [flaggedLaw_fst, if_pos rfl, split _ _ (min_le_left _ _)]
  · refine pmf_bool_ext ?_
    rw [flaggedLaw_fst, if_pos rfl, add_tsub_cancel_of_le (min_le_right _ _)]
  · intro outcome
    cases outcome <;> rfl
  · rw [flaggedLaw_bad]
    refine le_trans ?_ bound
    unfold Assumptions.advantage
    rcases le_total b a with ba | ab
    · have oneLe : 1 - a ≤ 1 - b := tsub_le_tsub_left ba 1
      rw [min_eq_right ba, min_eq_left oneLe, tsub_self, add_zero,
        ENNReal.toReal_sub_of_le ba aTop]
      exact le_abs_self _
    · have oneLe : 1 - b ≤ 1 - a := tsub_le_tsub_left ab 1
      rw [min_eq_left ab, min_eq_right oneLe, tsub_self, zero_add,
        ENNReal.toReal_sub_of_le oneLe (ENNReal.sub_ne_top ENNReal.one_ne_top),
        ENNReal.toReal_sub_of_le aLe ENNReal.one_ne_top,
        ENNReal.toReal_sub_of_le bLe ENNReal.one_ne_top]
      rw [abs_sub_comm]
      calc (1 : ℝ≥0∞).toReal - a.toReal - ((1 : ℝ≥0∞).toReal - b.toReal) = b.toReal - a.toReal := by
            ring
        _ ≤ |b.toReal - a.toReal| := le_abs_self _

/-- **`UntilBad` is exactly the advantage bound.** -/
theorem untilBad_iff {first second : PMF Bool} {error : ℝ} :
    UntilBad first second error ↔ Assumptions.advantage first second ≤ error :=
  ⟨fun bound => bound.advantage_le, untilBad_of_advantage_le⟩

/-- **`CoreUntilBad` is exactly the advantage bound** (with the trivial core). -/
theorem coreUntilBad_iff {first second : PMF Bool} {error : ℝ} :
    CoreUntilBad first second error ↔ Assumptions.advantage first second ≤ error := by
  refine ⟨fun bound => bound.untilBad.advantage_le, fun bound => ?_⟩
  obtain ⟨firstFlagged, secondFlagged, firstEq, secondEq, agree, bad⟩ :=
    untilBad_of_advantage_le bound
  exact ⟨Unit, PMF.pure (), PMF.pure (), fun _ => secondFlagged, firstFlagged, rfl, firstEq,
    by rw [PMF.pure_bind]; exact secondEq, by intro outcome; rw [PMF.pure_bind]; exact agree outcome,
    bad⟩

end

end Kriterion.ArgoMAC.Security.Phase3
