/-
**Phase 3, P4 — `MaskSwapBound.idealPerMask`: the lazy refill `I^U → I`, per derived vector.**

For every adversary:

* the sites are P1's switch-mask vector sites (`VectorSite`), `1,396 = laneVectorCount` of each
  lane (`sum_vectorSite_lane`), each costing its lane's sampler bias `laneDelta`;
* `advantage(I^U, I) ≤ Σ_{v : VectorSite} δ_{lane v}` (`idealUniform_etvDist_le`): the two
  stage-2 kernels are within that constant at every oracle state (`refillStage2_etvDist_le`), so
  the games are within its prefix average, which is at most the constant
  (`stageOneMean_const_le`).

There is no per-query charge: fresh lazy hash answers are exactly uniform, so the refill with fresh
uniform answers *is* `I` (`runRefill_uniform_eq`), and `Glue.idealRefillError = 0`.

`maskSwapBound_of` assembles P3's whole `H_swap` from P1's `G0 → G0U` and this lemma, given the two
data choices `maskSwapped := maskSwappedHybrid` (P1) and `idealUniform := idealUniformHybrid`.
-/

import Proof.Privacy.Phase3.Lazy.StageOne

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.Phase3 (VectorSite laneDelta laneDelta_ne_top sum_vectorSite_lane
  advantage_eq_etvDist maskSwappedHybrid maskSwapBound_real)
open scoped ENNReal

noncomputable section

/-- **`I^U` against `I`, as a distance**: the per-vector bias, nothing per query. -/
theorem idealUniform_etvDist_le [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    (abstractIdealGame Scheme.scheme (refillSimulator idealSamplers) adversary parameter scalar
        ()).etvDist (planBIdealGame idealSamplers adversary parameter scalar ()) ≤
      ∑ site : VectorSite, laneDelta site.lane :=
  le_trans (abstractIdealGame_stage2_etvDist_le Scheme.scheme
      (planBAbstractSimulator idealSamplers) (refillStage2 idealSamplers)
      (fun _ => ∑ site : VectorSite, laneDelta site.lane)
      (refillStage2_etvDist_le idealSamplers) adversary parameter scalar ())
    (stageOneMean_const_le adversary parameter _)

/-- Every lane has `laneVectorCount` vector sites. -/
theorem card_lane_vectorSite (vectorLane : Lane) :
    (Finset.univ.filter fun site : VectorSite => site.lane = vectorLane).card =
      laneVectorCount := by
  rw [Finset.card_filter, sum_vectorSite_lane (fun lane => if lane = vectorLane then 1 else 0)]
  simp only [smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ vectorLane, if_pos (Finset.mem_univ _),
    mul_one]
  rfl

set_option maxRecDepth 8000 in
/-- **`MaskSwapBound.idealPerMask`**, verbatim with `hybrids.idealUniform := idealUniformHybrid`:
the lazy refill `I^U → I`, charged per derived switch-mask vector (its lane's `laneDelta`), with
`laneVectorCount` vectors per lane and no per-query term. -/
theorem idealPerMask : ∀ (field : FieldCertificate) (group : @GroupCertificate field)
    (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      ∃ (Site : Type) (_ : Fintype Site) (lane : Site → Lane),
        (∀ vectorLane : Lane,
          (Finset.univ.filter fun site => lane site = vectorLane).card ≤ laneVectorCount) ∧
        Assumptions.advantage
            (atSolution idealUniformHybrid field group adversary parameter scalar)
            (atSolution idealHybrid field group adversary parameter scalar) ≤
          ∑ site, (laneDelta (lane site)).toReal := by
  intro field group adversary parameter scalar _
  let _ : DecidableEq FixedIndex := Classical.decEq _
  let _ : DecidableEq EncPRF.PermutationIndex := Classical.decEq _
  refine ⟨VectorSite, inferInstance, VectorSite.lane,
    fun vectorLane => (card_lane_vectorSite vectorLane).le, ?_⟩
  have distance := @idealUniform_etvDist_le field group (Classical.decEq _) (Classical.decEq _)
    adversary parameter scalar
  show Assumptions.advantage
      (abstractIdealGame Scheme.scheme (refillSimulator idealSamplers) adversary parameter
        scalar ()) (planBIdealGame idealSamplers adversary parameter scalar ()) ≤ _
  rw [advantage_eq_etvDist, ← ENNReal.toReal_sum fun site _ => laneDelta_ne_top site.lane]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun site _ => laneDelta_ne_top site.lane)
    distance

/-- **P3's `H_swap`, whole**: P1's `G0 → G0U` (`maskSwapBound_real`) and the lazy refill
(`idealPerMask`), for any `Hybrids` whose `maskSwapped` is P1's `maskSwappedHybrid` and whose
`idealUniform` is `idealUniformHybrid`. -/
theorem maskSwapBound_of (hybrids : Hybrids)
    (swapped : @Hybrids.maskSwapped hybrids = @maskSwappedHybrid)
    (uniform : @Hybrids.idealUniform hybrids = @idealUniformHybrid) : MaskSwapBound hybrids := by
  obtain ⟨maskSwapped, hiddenDeleted, publicFirst, opened, idealUniform⟩ := hybrids
  dsimp only at swapped uniform
  subst swapped uniform
  exact ⟨maskSwapBound_real, idealPerMask⟩

end

end Kriterion.ArgoMAC.Phase3.Lazy
