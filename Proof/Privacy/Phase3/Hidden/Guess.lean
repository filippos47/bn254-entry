/-
**Phase 3, P1c — generic glue for the assembly.**

* `outer_eq_expect`: an outer measure is the expectation of an indicator;
* `guess_bind`: a per-shape conditional guessing bound survives an adaptive choice of the shape by
  a kernel of a coarser view (the stage-2 bound at the adversary's own input);
* `advantage_le_of_dominated`: two games that both dominate one sub-probability flagged law are
  within its missing mass.
-/

import Proof.Privacy.Phase3.Hidden.TwoStage
import Cryptography.Assumptions

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open Kriterion.Cryptography
open scoped ENNReal

noncomputable section

open Classical in
theorem outer_eq_expect {α : Type} (p : PMF α) (S : Set α) :
    p.toOuterMeasure S = expect p (fun a => if a ∈ S then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply]
  unfold expect
  refine tsum_congr fun a => ?_
  by_cases h : a ∈ S <;> simp [Set.indicator, h]

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **The per-shape guessing bound, at an adaptively chosen shape.** -/
theorem guess_bind {Ω V₁ V₂ Z : Type} (μ : PMF Ω) (v₁ : Ω → V₁) (K : V₁ → PMF Z)
    (W : Z → Ω → V₂) (π : V₂ → V₁) (hπ : ∀ z ω, π (W z ω) = v₁ ω)
    (extra : Z → Ω → Extra FixedIndex EncIndex) (ε : ℝ≥0∞)
    (guess : ∀ z w e, μ.toOuterMeasure {ω | W z ω = w ∧ Touches (extra z ω) e} ≤
      ε * μ.toOuterMeasure {ω | W z ω = w})
    (v : V₂ × Z) (e : Asked FixedIndex EncIndex) :
    (μ.bind fun ω => (K (v₁ ω)).map fun z => (ω, z)).toOuterMeasure
        {p | (W p.2 p.1, p.2) = v ∧ Touches (extra p.2 p.1) e} ≤
      ε * (μ.bind fun ω => (K (v₁ ω)).map fun z => (ω, z)).toOuterMeasure
        {p | (W p.2 p.1, p.2) = v} := by
  classical
  obtain ⟨w, z₀⟩ := v
  have side : ∀ (S : Z → Ω → Prop),
      (μ.bind fun ω => (K (v₁ ω)).map fun z => (ω, z)).toOuterMeasure
          {p | (W p.2 p.1, p.2) = (w, z₀) ∧ S p.2 p.1} =
        K (π w) z₀ * μ.toOuterMeasure {ω | W z₀ ω = w ∧ S z₀ ω} := by
    intro S
    rw [outer_eq_expect, expect_bind, outer_eq_expect, ← expect_const_mul]
    refine tsum_congr fun ω => ?_
    congr 1
    beta_reduce
    rw [expect_map]
    unfold expect
    rw [tsum_eq_single z₀]
    · by_cases hit : W z₀ ω = w ∧ S z₀ ω
      · have mem : ((ω, z₀) : Ω × Z) ∈ {p : Ω × Z | (W p.2 p.1, p.2) = (w, z₀) ∧ S p.2 p.1} :=
          ⟨by rw [hit.1], hit.2⟩
        have memω : ω ∈ {ω | W z₀ ω = w ∧ S z₀ ω} := hit
        beta_reduce
        rw [if_pos mem, if_pos memω, mul_one, mul_one, ← hπ z₀ ω, hit.1]
      · have notMem : ((ω, z₀) : Ω × Z) ∉ {p : Ω × Z | (W p.2 p.1, p.2) = (w, z₀) ∧ S p.2 p.1} :=
          fun ⟨h, hS⟩ => hit ⟨(Prod.mk.inj h).1, hS⟩
        have notMemω : ω ∉ {ω | W z₀ ω = w ∧ S z₀ ω} := hit
        beta_reduce
        rw [if_neg notMem, if_neg notMemω, mul_zero, mul_zero]
    · intro z ne
      have notMem : ((ω, z) : Ω × Z) ∉ {p : Ω × Z | (W p.2 p.1, p.2) = (w, z₀) ∧ S p.2 p.1} :=
        fun ⟨h, _⟩ => ne (Prod.mk.inj h).2
      beta_reduce
      rw [if_neg notMem, mul_zero]
  have touched := side fun z ω => Touches (extra z ω) e
  have all := side fun _ _ => True
  simp only [and_true] at all
  rw [touched, all, mul_left_comm]
  exact mul_le_mul' le_rfl (guess z₀ w e)

/-- **Two games dominating one flagged law are within its missing mass.** -/
theorem advantage_le_of_dominated (first second : PMF Bool) (A : Bool → ℝ≥0∞)
    (firstGe : ∀ b, A b ≤ first b) (secondGe : ∀ b, A b ≤ second b) (δ : ℝ≥0∞)
    (missing : 1 - (A true + A false) ≤ δ) (finite : δ ≠ ⊤) :
    Assumptions.advantage first second ≤ δ.toReal := by
  have total (p : PMF Bool) : p true + p false = 1 := by
    have := p.tsum_coe
    rwa [tsum_fintype, Fintype.sum_bool] at this
  have upper (p : PMF Bool) (ge : ∀ b, A b ≤ p b) : p true ≤ A true + δ := by
    have one : 1 ≤ δ + (A true + A false) := tsub_le_iff_right.mp missing
    calc p true = 1 - p false := by
          rw [← total p, ENNReal.add_sub_cancel_right (PMF.apply_ne_top p false)]
      _ ≤ 1 - A false := tsub_le_tsub_left (ge false) 1
      _ ≤ A true + δ := by
          rw [tsub_le_iff_right]
          calc (1 : ℝ≥0∞) ≤ δ + (A true + A false) := one
            _ = A true + δ + A false := by ring
  have aFinite : A true ≠ ⊤ := ne_top_of_le_ne_top (PMF.apply_ne_top first true) (firstGe true)
  have realBounds (p : PMF Bool) (ge : ∀ b, A b ≤ p b) :
      (A true).toReal ≤ (p true).toReal ∧ (p true).toReal ≤ (A true).toReal + δ.toReal := by
    constructor
    · exact ENNReal.toReal_mono (PMF.apply_ne_top p true) (ge true)
    · rw [← ENNReal.toReal_add aFinite finite]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨aFinite, finite⟩) (upper p ge)
  obtain ⟨f₁, f₂⟩ := realBounds first firstGe
  obtain ⟨s₁, s₂⟩ := realBounds second secondGe
  unfold Assumptions.advantage
  rw [abs_le]
  constructor <;> linarith

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
