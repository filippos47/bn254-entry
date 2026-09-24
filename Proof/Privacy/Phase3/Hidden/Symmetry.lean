/-
**Phase 3, P1f — generic: a view-preserving symmetry bounds a guess.**

`card_mul_event_le`: let `μ` be a law on `Ω`, `view` an observation, `event` a predicate, and
`act : G → Ω → Ω` a finite family of `μ`-preserving maps that fix the view. If, from every `ω`, at
most `k` of the `g` move `ω` into the event, then

```
#G · μ{view = v ∧ event}  ≤  k · μ{view = v},
```

i.e. the event has conditional mass at most `k/#G` (`event_le_of_symmetry_count`; `k = 1` is
`event_le_of_symmetry`). Every guessing bound of hop (1) is this statement, at a symmetry of the
swapped tape that fixes the adversary's view and moves one hidden quantity (a garbler point, a
garbler output, a garbler label, the bridge key -- the last with `k = 2`, `bridgeInput` being at
most two-to-one).
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open scoped ENNReal

noncomputable section

open Classical in
theorem outer_eq_tsum_ite {Ω : Type} (μ : PMF Ω) (S : Set Ω) :
    μ.toOuterMeasure S = ∑' ω, if ω ∈ S then μ ω else 0 := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun ω => ?_
  by_cases h : ω ∈ S <;> simp [Set.indicator, h]

/-- A `μ`-preserving map moves the mass of a preimage. -/
theorem outer_preimage_of_map {Ω : Type} (μ : PMF Ω) (f : Ω → Ω) (preserve : μ.map f = μ)
    (S : Set Ω) : μ.toOuterMeasure (f ⁻¹' S) = μ.toOuterMeasure S := by
  conv_rhs => rw [← preserve]
  rw [PMF.toOuterMeasure_map_apply]

open Classical in
/-- **The symmetry bound for an event, counted**: at most `k` of the maps move a point into the
event. -/
theorem card_mul_event_le {Ω V G : Type} [Fintype G] (μ : PMF Ω) (view : Ω → V)
    (event : Ω → Prop) (act : G → Ω → Ω) (preserve : ∀ g, μ.map (act g) = μ)
    (sameView : ∀ g ω, view (act g ω) = view ω) (k : ℕ)
    (few : ∀ ω (s : Finset G), (∀ g ∈ s, event (act g ω)) → s.card ≤ k) (v : V) :
    (Fintype.card G : ℝ≥0∞) * μ.toOuterMeasure {ω | view ω = v ∧ event ω} ≤
      k * μ.toOuterMeasure {ω | view ω = v} := by
  classical
  have moved : ∀ g, μ.toOuterMeasure {ω | view ω = v ∧ event ω} =
      μ.toOuterMeasure {ω | view ω = v ∧ event (act g ω)} := by
    intro g
    rw [← outer_preimage_of_map μ (act g) (preserve g)]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, sameView]
  calc (Fintype.card G : ℝ≥0∞) * μ.toOuterMeasure {ω | view ω = v ∧ event ω}
      = ∑ g : G, μ.toOuterMeasure {ω | view ω = v ∧ event (act g ω)} := by
        rw [Finset.sum_congr rfl fun g _ => (moved g).symm, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
    _ = ∑' ω, ∑ g : G, if view ω = v ∧ event (act g ω) then μ ω else 0 := by
        simp only [outer_eq_tsum_ite, Set.mem_setOf_eq]
        rw [← tsum_fintype (L := .unconditional _)
            (fun g : G => ∑' ω, if view ω = v ∧ event (act g ω) then μ ω else 0),
          ENNReal.tsum_comm]
        exact tsum_congr fun ω =>
          tsum_fintype (L := .unconditional _) (fun g : G => if view ω = v ∧ event (act g ω) then μ ω else 0)
    _ ≤ ∑' ω, k * (if view ω = v then μ ω else 0) := by
        refine ENNReal.tsum_le_tsum fun ω => ?_
        by_cases hv : view ω = v
        · simp only [hv, true_and, if_true]
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul' (by exact_mod_cast few ω _ fun g member =>
            (Finset.mem_filter.mp member).2) le_rfl
        · simp [hv]
    _ = k * μ.toOuterMeasure {ω | view ω = v} := by
        rw [ENNReal.tsum_mul_left, outer_eq_tsum_ite]
        rfl

/-- **The symmetry bound for an event**: conditional mass at most `k/#G`. -/
theorem event_le_of_symmetry_count {Ω V G : Type} [Fintype G] [Nonempty G] (μ : PMF Ω)
    (view : Ω → V) (event : Ω → Prop) (act : G → Ω → Ω) (preserve : ∀ g, μ.map (act g) = μ)
    (sameView : ∀ g ω, view (act g ω) = view ω) (k : ℕ)
    (few : ∀ ω (s : Finset G), (∀ g ∈ s, event (act g ω)) → s.card ≤ k) (v : V) :
    μ.toOuterMeasure {ω | view ω = v ∧ event ω} ≤
      k * (Fintype.card G : ℝ≥0∞)⁻¹ * μ.toOuterMeasure {ω | view ω = v} := by
  have counted := card_mul_event_le μ view event act preserve sameView k few v
  have pos : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have fin : (Fintype.card G : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc μ.toOuterMeasure {ω | view ω = v ∧ event ω}
      = (Fintype.card G : ℝ≥0∞)⁻¹ * ((Fintype.card G : ℝ≥0∞) *
          μ.toOuterMeasure {ω | view ω = v ∧ event ω}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel pos fin, one_mul]
    _ ≤ (Fintype.card G : ℝ≥0∞)⁻¹ * (k * μ.toOuterMeasure {ω | view ω = v}) :=
        mul_le_mul' le_rfl counted
    _ = _ := by ring

/-- **The symmetry bound for an event**: at most one map moves a point into the event, so the
conditional mass is at most `1/#G`. -/
theorem event_le_of_symmetry {Ω V G : Type} [Fintype G] [Nonempty G] (μ : PMF Ω) (view : Ω → V)
    (event : Ω → Prop) (act : G → Ω → Ω) (preserve : ∀ g, μ.map (act g) = μ)
    (sameView : ∀ g ω, view (act g ω) = view ω)
    (few : ∀ ω g g', event (act g ω) → event (act g' ω) → g = g') (v : V) :
    μ.toOuterMeasure {ω | view ω = v ∧ event ω} ≤
      (Fintype.card G : ℝ≥0∞)⁻¹ * μ.toOuterMeasure {ω | view ω = v} := by
  have bound := event_le_of_symmetry_count μ view event act preserve sameView 1
    (fun ω s all => Finset.card_le_one.mpr fun g hg g' hg' => few ω g g' (all g hg) (all g' hg')) v
  rwa [Nat.cast_one, one_mul] at bound

/-- **Union of two guesses.** -/
theorem outer_and_or_le {Ω : Type} (μ : PMF Ω) (A B C : Set Ω) :
    μ.toOuterMeasure {ω | ω ∈ A ∧ (ω ∈ B ∨ ω ∈ C)} ≤
      μ.toOuterMeasure {ω | ω ∈ A ∧ ω ∈ B} + μ.toOuterMeasure {ω | ω ∈ A ∧ ω ∈ C} := by
  have split : {ω | ω ∈ A ∧ (ω ∈ B ∨ ω ∈ C)} = {ω | ω ∈ A ∧ ω ∈ B} ∪ {ω | ω ∈ A ∧ ω ∈ C} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [split]
  exact MeasureTheory.measure_union_le _ _

/-- A smaller event has smaller mass. -/
theorem outer_mono_event {Ω : Type} (μ : PMF Ω) {S T : Set Ω} (sub : S ⊆ T) :
    μ.toOuterMeasure S ≤ μ.toOuterMeasure T :=
  MeasureTheory.measure_mono sub

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
