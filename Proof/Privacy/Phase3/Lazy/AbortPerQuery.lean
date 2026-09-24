/-
**Phase 3, P4 — the restated `AbortBound.perQuery` from the per-prefix failure bound.**

`abortBound_perQuery'_of : KeyAveragedFailBound → AbortPerQuery' openedHybrid idealUniformHybrid`:
the two games are the opened game at skip and at abort; swapping stage 2 costs the prefix average
of the failure mass (`openedGame_etvDist_le`, `openedStage2_etvDist_le`); the key
averages out separately (`key_average`); the per-prefix bound charges `abortQueryCharge q₁` per
stage-1 entry at an abort site; the counts are the prefix averages of those entries, summing to at
most `q₁` (`stageOneMean_abortUse_le`).
-/

import Proof.Privacy.Phase3.Lazy.AbortReduction

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.Phase3 (openedSimulator openedHybrid simulatedRows skipInstallation
  abortInstallation idealUniformHybrid_eq_opened advantage_eq_etvDist)
open scoped ENNReal

noncomputable section

/-- **The restated `AbortBound.perQuery`, from the per-prefix analysis.** -/
theorem abortBound_perQuery'_of (bound : KeyAveragedFailBound) :
    AbortPerQuery' openedHybrid idealUniformHybrid := by
  intro field group adversary parameter scalar small
  let _ : DecidableEq FixedIndex := Classical.decEq _
  let _ : DecidableEq EncPRF.PermutationIndex := Classical.decEq _
  have small₁ : adversary.firstQueryBudget parameter < 2 ^ 100 := by omega
  let mean : AbortSite → ℝ≥0∞ := fun site =>
    stageOneMean adversary parameter (fun oracle => (siteEntries oracle site : ℝ≥0∞))
  have total : ∑ site, mean site =
      stageOneMean adversary parameter (fun oracle => (abortUse oracle : ℝ≥0∞)) := by
    rw [← stageOneMean_sum]
    refine congrArg (stageOneMean adversary parameter) (funext fun oracle => ?_)
    rw [abortUse, Nat.cast_sum]
  have totalLe : stageOneMean adversary parameter (fun oracle => (abortUse oracle : ℝ≥0∞)) ≤
      (adversary.firstQueryBudget parameter : ℝ≥0∞) :=
    stageOneMean_abortUse_le adversary parameter
  have totalFinite : stageOneMean adversary parameter (fun oracle => (abortUse oracle : ℝ≥0∞))
      ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) totalLe
  have meanFinite : ∀ site, mean site ≠ ⊤ := by
    intro site
    refine ne_top_of_le_ne_top totalFinite ?_
    rw [← total]
    exact Finset.single_le_sum (f := mean) (fun _ _ => zero_le) (Finset.mem_univ site)
  have countSum : ∑ site, (mean site).toReal =
      (stageOneMean adversary parameter (fun oracle => (abortUse oracle : ℝ≥0∞))).toReal := by
    rw [← total, ENNReal.toReal_sum fun site _ => meanFinite site]
  have chargeNonneg := abortQueryCharge_nonneg (adversary.firstQueryBudget parameter) small₁
  refine ⟨fun site => (mean site).toReal, fun _ => ENNReal.toReal_nonneg, ?_, ?_⟩
  · rw [countSum]
    have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) totalLe
    rwa [ENNReal.toReal_natCast] at this
  · -- the distance
    have gameI : atSolution idealUniformHybrid field group adversary parameter scalar =
        abstractIdealGame Scheme.scheme (openedSimulator simulatedRows abortInstallation)
          adversary parameter scalar () :=
      @idealUniformHybrid_eq_opened field group (Fintype.ofFinite _) (Fintype.ofFinite _)
        (Classical.decEq _) (Classical.decEq _) adversary parameter scalar
    let failBound : Stage1Source → AffineInput → Option Point → LState → ℝ≥0∞ :=
      fun source input output oracle => match output with
        | none => 0
        | some target => failMass source.publicValue input
            (Lamport.selectedLabels (source.key.encode (BitInput.ofAffine input))) target oracle
    have distance := openedGame_etvDist_le simulatedRows skipInstallation abortInstallation
      failBound (fun source input output oracle => openedStage2_etvDist_le source input output
        oracle) adversary parameter scalar
    -- the prefix average of the failure mass
    have averaged : (∑' first, (openedSimulator simulatedRows abortInstallation).stage1 parameter
          LazyOracle.empty (some first) *
        ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter first.1 ()) first.2.2)
          chosen * failBound first.2.1 chosen.1.1 (Scheme.scheme.function scalar chosen.1.1)
            chosen.2) ≤
        ENNReal.ofReal (abortQueryCharge (adversary.firstQueryBudget parameter)) *
          stageOneMean adversary parameter (fun oracle => (abortUse oracle : ℝ≥0∞)) := by
      refine le_trans (le_of_eq (stage1_collapse_opened simulatedRows abortInstallation parameter
        fun first => ∑' chosen,
          (LazyOracle.run (adversary.chooseInput parameter first.1 ()) first.2.2) chosen *
            failBound first.2.1 chosen.1.1 (Scheme.scheme.function scalar chosen.1.1) chosen.2)) ?_
      rw [key_average]
      unfold stageOneMean
      beta_reduce
      rw [stage1_collapse parameter fun first => ∑' chosen,
        (LazyOracle.run (adversary.chooseInput parameter first.1 ()) first.2.2) chosen *
          (abortUse chosen.2 : ℝ≥0∞), ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun source => ?_
      rw [← mul_assoc, mul_comm (ENNReal.ofReal _), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ zero_le
      calc (∑' key, PMF.uniformOfFintype InputMacKey key *
            ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter
              (withKey source key).publicValue ()) LazyOracle.empty) chosen *
                failBound (withKey source key) chosen.1.1
                  (Scheme.scheme.function scalar chosen.1.1) chosen.2)
          = ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
              LazyOracle.empty) chosen * ∑' key, PMF.uniformOfFintype InputMacKey key *
                failBound (withKey source key) chosen.1.1
                  (Scheme.scheme.function scalar chosen.1.1) chosen.2 := by
            simp only [publicValue_withKey]
            calc (∑' key, PMF.uniformOfFintype InputMacKey key *
                  ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter
                    source.publicValue ()) LazyOracle.empty) chosen *
                      failBound (withKey source key) chosen.1.1
                        (Scheme.scheme.function scalar chosen.1.1) chosen.2)
                = ∑' key, ∑' chosen, PMF.uniformOfFintype InputMacKey key *
                    ((LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
                      LazyOracle.empty) chosen * failBound (withKey source key) chosen.1.1
                        (Scheme.scheme.function scalar chosen.1.1) chosen.2) :=
                  tsum_congr fun key => ENNReal.tsum_mul_left.symm
              _ = ∑' chosen, ∑' key, PMF.uniformOfFintype InputMacKey key *
                    ((LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
                      LazyOracle.empty) chosen * failBound (withKey source key) chosen.1.1
                        (Scheme.scheme.function scalar chosen.1.1) chosen.2) := ENNReal.tsum_comm
              _ = _ := tsum_congr fun chosen => by
                  rw [← ENNReal.tsum_mul_left]
                  exact tsum_congr fun key => by ring
        _ ≤ ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
              LazyOracle.empty) chosen * (ENNReal.ofReal (abortQueryCharge
                (adversary.firstQueryBudget parameter)) * (abortUse chosen.2 : ℝ≥0∞)) := by
            refine ENNReal.tsum_le_tsum fun chosen => ?_
            by_cases zero : (LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
                LazyOracle.empty) chosen = 0
            · rw [zero, zero_mul, zero_mul]
            · refine mul_le_mul_of_nonneg_left ?_ zero_le
              cases output : Scheme.scheme.function scalar chosen.1.1 with
              | none => simp [failBound]
              | some target =>
                  exact bound source chosen.1.1 target chosen.2 _ small₁
                    (run_used_le adversary parameter _ chosen ((PMF.mem_support_iff _ _).mpr zero))
        _ = ENNReal.ofReal (abortQueryCharge (adversary.firstQueryBudget parameter)) *
              ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter
                (source.publicValue, source, (LazyOracle.empty : LState)).1 ())
                  (source.publicValue, source, (LazyOracle.empty : LState)).2.2) chosen *
                (abortUse chosen.2 : ℝ≥0∞) := by
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun chosen => by ring
    show Assumptions.advantage (abstractIdealGame Scheme.scheme
      (openedSimulator simulatedRows skipInstallation) adversary parameter scalar ()) _ ≤ _
    rw [gameI, advantage_eq_etvDist]
    have finiteRight : ENNReal.ofReal (abortQueryCharge (adversary.firstQueryBudget parameter)) *
        stageOneMean adversary parameter (fun oracle => (abortUse oracle : ℝ≥0∞)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top totalFinite
    refine le_trans (ENNReal.toReal_mono finiteRight (distance.trans averaged)) (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal chargeNonneg, ← countSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun site _ => mul_comm _ _

end

end Kriterion.ArgoMAC.Phase3.Lazy
