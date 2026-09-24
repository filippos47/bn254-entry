/-
**Phase 3, P1j — the lift, part 6: the coincidence bound from a per-input guessing bound.**

`CoincidenceBound` asks the coincidence mass under `G1U`'s stage 1, where the input is the
adversary's, chosen after the stage-1 view `(P, enc)` (the published value and the garbler's EncPRF
entries, which the stage-1 oracle holds). As in the hidden hop, it suffices to bound, **for every
fixed input**, the coincidence mass conditioned on the stage-1 view (`CoincidenceGuess`, a guessing
bound in the style of P1h's `StageOneGuess`): `coincidenceBound_of_guess`. The adaptive choice is
absorbed exactly: the stage-1 law of each outcome is a function of the view (`coincidenceMass_eq`).

Two facts the guessing bound needs, both immediate from the library: `Scheme.scheme.function scalar
u = none ↔ validate u = false` (`decodePoint`), so `M'`'s on/off-curve branch is the designed
rule's; and off the curve the reach's bridge value is `t_eval = t + mask·(x³ + 3 − y²) ≠ t`
(`CurveMembership.evaluateEncoded`, `mask ≠ 0`). The bridge input `bridgeInput` is at most
2-to-1, so the reach may still meet the hidden key `bridgeInput t`; `LawsGuess` charges that as
its own event (`BridgeHit`, `≤ 2/(p−1)`).

`planB_publicFirst_of_guess`: the Glue's `publicFirst` from `DesignedLaws`, `DesignedBounds` and
`CoincidenceGuess (ofReal coincidenceError)`.
-/

import Proof.Privacy.Phase3.PublicFirst.LiftOn

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary coincidenceError)
open Kriterion.ArgoMAC.Phase3.Lazy (LState)
open scoped ENNReal

noncomputable section

/-- An event's mass as a weighted sum. -/
theorem toOuterMeasure_eq_tsum {A : Type} (μ : PMF A) (event : Set A) [DecidablePred (· ∈ event)] :
    μ.toOuterMeasure event = ∑' x, μ x * (if x ∈ event then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases inside : x ∈ event
  · rw [Set.indicator_of_mem inside, if_pos inside, mul_one]
  · rw [Set.indicator_of_notMem inside, if_neg inside, mul_zero]

section Guess

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
  [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- `G1U`'s stage-1 view: the published value and the garbler's EncPRF entries. -/
def viewOf (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    Public × List (Entry FixedIndex EncPRF.PermutationIndex) :=
  ((Scheme.scheme.garble parameter scalar tape).1, (garblerTranscript scalar tape).filter Entry.IsEnc)

open Classical in
/-- The coincidence indicator at a fixed input. -/
def coincideWeight (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) : ℝ≥0∞ :=
  if Coincide parameter scalar tape input then 1 else 0

/-- The stage-1 law of an outcome, from the view. -/
def stageOneAt (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (view : Public × List (Entry FixedIndex EncPRF.PermutationIndex))
    (selected : (AffineInput × adversary.State) × LState) : ℝ≥0∞ :=
  LazyOracle.run (adversary.chooseInput parameter view.1 ()) (installAll view.2 LazyOracle.empty)
    selected

open Classical in
/-- **The coincidence mass, stage 1 first.** -/
theorem coincidenceMass_eq (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    coincidenceMass adversary parameter scalar =
      ∑' tape, swappedChallengeTape tape *
        ∑' selected, stageOneAt adversary parameter (viewOf parameter scalar tape) selected *
          coincideWeight parameter scalar tape selected.1.1 := by
  unfold coincidenceMass stageOneLaw
  rewrite [toOuterMeasure_eq_tsum, tsum_bind_mul]
  refine tsum_congr fun tape => ?_
  rewrite [tsum_map_mul]
  refine congrArg (fun value => swappedChallengeTape tape * value) (tsum_congr fun selected => ?_)
  refine congrArg₂ (· * ·) (by unfold stageOneAt viewOf; dsimp only) ?_
  unfold coincideWeight
  by_cases hit : Coincide parameter scalar tape selected.1.1
  · have inside : (tape, selected) ∈ {x : (Coins × Oracle) × ((AffineInput × adversary.State) × LState) |
        Coincide parameter scalar x.1 x.2.1.1} := hit
    rw [if_pos inside, if_pos hit]
  · have outside : (tape, selected) ∉ {x : (Coins × Oracle) × ((AffineInput × adversary.State) × LState) |
        Coincide parameter scalar x.1 x.2.1.1} := hit
    rw [if_neg outside, if_neg hit]

/-- **The per-input guessing bound**: at every fixed input, given the stage-1 view, the reach meets
a hidden garbler entry with mass at most `error`. -/
def CoincidenceGuess (error : ℝ≥0∞) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ)
    (scalar : NonZeroScalar) (input : AffineInput),
    (letI := field
     letI := group
     letI : Fintype FixedIndex := Fintype.ofFinite FixedIndex
     letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
     letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
     letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
     ∀ weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞,
       ∑' tape, swappedChallengeTape tape *
           (weight (viewOf parameter scalar tape) * coincideWeight parameter scalar tape input)
         ≤ error * ∑' tape, swappedChallengeTape tape * weight (viewOf parameter scalar tape))

/-- **The coincidence mass from the per-input guessing bound.** -/
theorem coincidenceMass_le (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) (error : ℝ≥0∞)
    (guess : ∀ (input : AffineInput) (weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) →
      ℝ≥0∞), ∑' tape, swappedChallengeTape tape *
          (weight (viewOf parameter scalar tape) * coincideWeight parameter scalar tape input)
        ≤ error * ∑' tape, swappedChallengeTape tape * weight (viewOf parameter scalar tape)) :
    coincidenceMass adversary parameter scalar ≤ error := by
  rw [coincidenceMass_eq]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  calc ∑' selected, ∑' tape, swappedChallengeTape tape *
        (stageOneAt adversary parameter (viewOf parameter scalar tape) selected *
          coincideWeight parameter scalar tape selected.1.1)
      ≤ ∑' selected, error * ∑' tape, swappedChallengeTape tape *
          stageOneAt adversary parameter (viewOf parameter scalar tape) selected :=
        ENNReal.tsum_le_tsum fun selected =>
          guess selected.1.1 fun view => stageOneAt adversary parameter view selected
    _ = error * ∑' tape, swappedChallengeTape tape *
          ∑' selected, stageOneAt adversary parameter (viewOf parameter scalar tape) selected := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
        simp_rw [ENNReal.tsum_mul_left]
    _ = error := by
        have total : ∀ tape, ∑' selected,
            stageOneAt adversary parameter (viewOf parameter scalar tape) selected = 1 :=
          fun tape => PMF.tsum_coe _
        simp only [total, mul_one, PMF.tsum_coe]

end Guess

/-- **`CoincidenceBound` from the per-input guessing bound.** -/
theorem coincidenceBound_of_guess (guess : CoincidenceGuess (ENNReal.ofReal coincidenceError)) :
    CoincidenceBound coincidenceError := by
  intro field group adversary parameter scalar _
  let _ := field
  let _ := group
  let _ : Fintype FixedIndex := Fintype.ofFinite FixedIndex
  let _ : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
  let _ : DecidableEq FixedIndex := Classical.decEq FixedIndex
  let _ : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
  have bound := coincidenceMass_le adversary parameter scalar _
    (fun input => guess field group parameter scalar input)
  have nonneg : 0 ≤ coincidenceError := by unfold coincidenceError; positivity
  calc (coincidenceMass adversary parameter scalar).toReal
      ≤ (ENNReal.ofReal coincidenceError).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top bound
    _ = coincidenceError := ENNReal.toReal_ofReal nonneg

/-- **The Glue's `publicFirst`, from the two laws, P1k's bounds and the per-input guessing
bound.** -/
theorem planB_publicFirst_of_guess (laws : DesignedLaws) (bounds : DesignedBounds)
    (guess : CoincidenceGuess (ENNReal.ofReal coincidenceError)) :
    Kriterion.ArgoMAC.Phase3.Glue.GameCoreUntilBad
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.hiddenDeleted
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.publicFirst fun first _ =>
        Kriterion.ArgoMAC.Phase3.Glue.stageOneHitError first +
          Kriterion.ArgoMAC.Phase3.Glue.exceptionalError +
            Kriterion.ArgoMAC.Phase3.Glue.maskSwapError + coincidenceError :=
  planB_publicFirst_of_laws laws bounds (coincidenceBound_of_guess guess)

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
