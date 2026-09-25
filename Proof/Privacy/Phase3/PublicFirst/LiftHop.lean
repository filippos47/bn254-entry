/-
**Phase 3, P1j — the lift, part 2: the designed hop `G1U → G1U°` (P1i's "V2", as a separate
hop), at the Glue's constant.**

Off the curve `G1U` installs *coincidence* entries — garbler entries its reach meets at points the
adversary cannot locate (system B and the gadget whitened with the tape's hash of the bridge input
`bridgeInput t_eval`) — and on the curve the gadget's label collisions (`pad₀ ⊕ pad₁ = Δ`). None
of them fits the flag budget of `M'`. **One identical-until-bad hop removes all of them**, and the
lift is against the coincidence-free game:

* `G1U° := hiddenDeletedWith designedInstall` — `G1U` with the **designed** entries of the hidden
  hop (`designedRule`, index-based: the fold gates of every paid step off the active parent, the
  hash limbs of the inactive vector sites, agreeing gadget positions, and system B and the bridge
  hash only on the curve) installed at the input choice, instead of the reach's;
* **`G1U → G1U°`** costs the mass of the coincidence event `visible ≠ designed` under `G1U`'s
  stage 1 (`hop_advantage_le`, `advantage_le_of_agree`). The obligation
  `CoincidenceBound coincidenceError` asks it below the Glue's budget term
  `coincidenceError = 2^16/2^128` (`LawsGuess`: `13813` label and bridge events of `≤ 2/2^128`
  each; grouping by label, not by reach query, is what keeps it small);
* **`G1U° → HW`** is the overlap with `M'` against `g1uLaterWith designedInstall`
  (`below_laterWith`), its flag mass from `PerPairBound`/`RevealBound`, and a **refined** mask-tape
  distance: off the curve the designed shadow's fill reads only the curve lanes' limbs, so the two
  readings of `M'` are within `curveSwapError = 1588·(δ_curveX + δ_curveY)` (proved for the
  designed shadow in `LiftTV.lean`), at most one copy of the mask swap (`curveSwapError_le`).

`planB_publicFirst_of_designed`: the Glue's `publicFirst` field at its constant
`stageOneHitError q₁ + exceptionalError + maskSwapError + coincidenceError`, from
`ShadowObligationDesigned` (the lift against `G1U°`, the two (B) bounds, the refined distance) and
`CoincidenceBound coincidenceError`.
-/

import Proof.Privacy.Phase3.PublicFirst.Lift
import Proof.Privacy.Phase3.Hidden.Designed
import Proof.Privacy.Phase3.Hidden.Containment

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary atSolution GameCoreUntilBad stageOneHitError
  exceptionalError maskSwapError coincidenceError laneVectorCount)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Tape uniformMaskTape)
open scoped ENNReal

noncomputable section

/-! ### 1. Two continuations that agree off an event -/

theorem bind_le_add_bad {A : Type} (μ : PMF A) (f g : A → PMF Bool) (bad : Set A)
    (agree : ∀ a, a ∉ bad → f a = g a) (b : Bool) :
    (μ.bind f) b ≤ (μ.bind g) b + μ.toOuterMeasure bad := by
  rw [PMF.bind_apply, PMF.bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases inside : a ∈ bad
  · rw [Set.indicator_of_mem inside]
    exact le_trans (mul_le_of_le_one_right' (PMF.coe_le_one _ _)) le_add_self
  · rw [Set.indicator_of_notMem inside, add_zero, agree a inside]

/-- **Identical until bad**: two continuations of one law that agree off an event are within its
mass. -/
theorem advantage_le_of_agree {A : Type} (μ : PMF A) (f g : A → PMF Bool) (bad : Set A)
    (agree : ∀ a, a ∉ bad → f a = g a) :
    Assumptions.advantage (μ.bind f) (μ.bind g) ≤ (μ.toOuterMeasure bad).toReal := by
  have finite : μ.toOuterMeasure bad ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [PMF.toOuterMeasure_apply]
    exact le_trans (ENNReal.tsum_le_tsum fun a => Set.indicator_le_self bad (⇑μ) a)
      (le_of_eq μ.tsum_coe)
  have one := bind_le_add_bad μ f g bad agree true
  have two := bind_le_add_bad μ g f bad (fun a outside => (agree a outside).symm) true
  have r1 : ((μ.bind f) true).toReal ≤ ((μ.bind g) true).toReal + (μ.toOuterMeasure bad).toReal := by
    rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) finite]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, finite⟩) one
  have r2 : ((μ.bind g) true).toReal ≤ ((μ.bind f) true).toReal + (μ.toOuterMeasure bad).toReal := by
    rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) finite]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, finite⟩) two
  unfold Assumptions.advantage
  rw [abs_le]
  constructor <;> linarith

/-! ### 2. `G1U°` and the hop `G1U → G1U°` -/

section Designed

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
  [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The designed rule as an installation rule**: the garbler's non-EncPRF entries that
`designedRule` keeps at the input (`designedEntries_eq`: exactly the hidden hop's designed
entries). -/
def designedInstall : InstallRule := fun scalar tape _ input _ =>
  (garblerTranscript scalar tape).filter fun entry =>
    !entry.IsEnc && designedRule scalar tape input entry

/-- The reach's rule (`G1U`'s own). -/
def visibleInstall : InstallRule := fun scalar tape table input labels =>
  visibleEntries scalar tape table input labels

/-- `G1U`'s stage 1: the tape and the adversary's stage-1 outcome on the EncPRF entries. -/
def stageOneLaw (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar) :
    PMF ((Coins × Oracle) × ((AffineInput × adversary.State) × LState)) :=
  swappedChallengeTape.bind fun tape =>
    (LazyOracle.run (adversary.chooseInput parameter (Scheme.scheme.garble parameter scalar tape).1 ())
        (installAll ((garblerTranscript scalar tape).filter Entry.IsEnc) LazyOracle.empty)).map
      fun selected => (tape, selected)

/-- `G1U`'s stage 2 read with a rule. -/
def stageTwoWith (installed : InstallRule) (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) (x : (Coins × Oracle) × ((AffineInput × adversary.State) × LState)) :
    PMF Bool :=
  (LazyOracle.run (adversary.decide parameter (Scheme.scheme.garble parameter scalar x.1).1
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar x.1).2 x.2.1.1) () x.2.1.2)
    (installAll (installed scalar x.1 (Scheme.scheme.garble parameter scalar x.1).1 x.2.1.1
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar x.1).2 x.2.1.1)) x.2.2)).map
    Prod.fst

theorem hiddenDeletedWith_eq (installed : InstallRule) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar) :
    hiddenDeletedWith installed adversary parameter scalar =
      (stageOneLaw adversary parameter scalar).bind (stageTwoWith installed adversary parameter scalar) := by
  unfold hiddenDeletedWith stageOneLaw
  rw [PMF.bind_bind]
  congr 1
  funext tape
  rw [PMF.bind_map]
  rfl

/-- **The coincidence event** at an input: the reach meets a garbler entry the designed rule hides
(the reach's entries are not the designed ones). -/
def Coincide (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput) :
    Prop :=
  visibleInstall scalar tape (Scheme.scheme.garble parameter scalar tape).1 input
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input) ≠
    designedInstall scalar tape (Scheme.scheme.garble parameter scalar tape).1 input
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)

/-- Its mass under `G1U`'s stage 1 (the input is the adversary's). -/
def coincidenceMass (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar) :
    ℝ≥0∞ :=
  (stageOneLaw adversary parameter scalar).toOuterMeasure
    {x | Coincide parameter scalar x.1 x.2.1.1}

/-- **The hop `G1U → G1U°`**: identical until a coincidence. -/
theorem hop_advantage_le (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar) :
    Assumptions.advantage (hiddenDeletedHybrid adversary parameter scalar)
        (hiddenDeletedWith designedInstall adversary parameter scalar)
      ≤ (coincidenceMass adversary parameter scalar).toReal := by
  rw [← hiddenDeletedWith_visible, show (fun scalar tape table input labels =>
      visibleEntries scalar tape table input labels) = (visibleInstall : InstallRule) from rfl,
    hiddenDeletedWith_eq, hiddenDeletedWith_eq]
  refine advantage_le_of_agree _ _ _ _ fun x outside => ?_
  have same : visibleInstall scalar x.1 (Scheme.scheme.garble parameter scalar x.1).1 x.2.1.1
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar x.1).2 x.2.1.1) =
    designedInstall scalar x.1 (Scheme.scheme.garble parameter scalar x.1).1 x.2.1.1
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar x.1).2 x.2.1.1) := by
    by_contra different
    exact outside different
  unfold stageTwoWith
  rw [same]

end Designed

/-! ### 3. The obligations and the constant -/

/-- **The curve lanes' share of the mask swap**: system A's `1588 + 1588` vectors, each at its
lane's bias. -/
def curveSwapError : ℝ≥0∞ := (laneVectorCount : ℝ≥0∞) * (laneDelta .curveX + laneDelta .curveY)

/-- The curve lanes' share fits in one copy of the mask swap. -/
theorem curveSwapError_le : curveSwapError.toReal ≤ maskSwapError := by
  unfold curveSwapError maskSwapError
  have finite : (laneVectorCount : ℝ≥0∞) * ∑ lane : Lane, laneDelta lane ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.sum_ne_top.mpr fun lane _ => laneDelta_ne_top lane)
  refine ENNReal.toReal_mono finite (mul_le_mul' le_rfl ?_)
  rw [← Finset.sum_pair (show (Lane.curveX : Lane) ≠ .curveY by decide)]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **The coincidence bound**: under `G1U`'s stage 1 (the adversary's input), the reach meets a
hidden garbler entry with mass at most `error`. -/
def CoincidenceBound (error : ℝ) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      (letI := field
       letI := group
       letI : Fintype FixedIndex := Fintype.ofFinite FixedIndex
       letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
       letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
       letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
       coincidenceMass adversary parameter scalar).toReal ≤ error

/-- **The lift's obligation against `G1U°`**: a shadow whose `M'` is below `g1uLater°` (the F4 lift
at the designed rule), with P1k's two (B) bounds, and whose two tape readings are within
`curveSwapError`. -/
def ShadowObligationDesigned : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      ∃ shadow : Shadow,
        (letI := field
         letI := group
         letI : Fintype FixedIndex := Fintype.ofFinite FixedIndex
         letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
         letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
         letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
         FlagMono (g1uLaterWith designedInstall adversary parameter scalar)
             (middleGameFill uniformMaskTape shadow adversary parameter scalar) ∧
           PerPairBound shadow scalar (4 / 2 ^ 128) ∧
           RevealBound shadow scalar (ENNReal.ofReal exceptionalError) ∧
           (middleGameFill uniformMaskTape shadow adversary parameter scalar).etvDist
               (middleGameFill (PMF.uniformOfFintype Tape) shadow adversary parameter scalar)
             ≤ curveSwapError)

/-! ### 4. The assembly -/

/-- **The Glue's `publicFirst` at its constant, through `G1U°`.** -/
theorem planB_publicFirst_of_designed (obligation : ShadowObligationDesigned)
    (coincidence : CoincidenceBound coincidenceError) :
    GameCoreUntilBad Kriterion.ArgoMAC.Security.Phase3.planBHybrids.hiddenDeleted
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.publicFirst fun first _ =>
        stageOneHitError first + exceptionalError + maskSwapError + coincidenceError := by
  intro field group adversary parameter scalar small
  obtain ⟨shadow, mono, perPair, reveal, tv⟩ := obligation field group adversary parameter scalar small
  have coincidenceLe := coincidence field group adversary parameter scalar small
  let _ := field
  let _ := group
  let _ : Fintype FixedIndex := Fintype.ofFinite FixedIndex
  let _ : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
  let _ : DecidableEq FixedIndex := Classical.decEq FixedIndex
  let _ : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
  have hop := hop_advantage_le adversary parameter scalar
  have belowDesigned : Below (hiddenDeletedWith designedInstall adversary parameter scalar)
      (middleGameFill uniformMaskTape shadow adversary parameter scalar) :=
    (below_laterWith designedInstall adversary parameter scalar).trans mono
  have belowHW : Below (atSolution publicFirstHybrid field group adversary parameter scalar)
      (middleGameFill (PMF.uniformOfFintype Tape) shadow adversary parameter scalar) := by
    rw [middleFill_uniform_eq]
    exact middle_below shadow adversary parameter scalar
  have overlap := advantage_le_of_overlap_tv belowDesigned belowHW
  have mass := middleFill_mass_le shadow adversary parameter scalar perPair reveal
  have finite : curveSwapError ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.add_ne_top.mpr ⟨laneDelta_ne_top _, laneDelta_ne_top _⟩)
  have tvReal := ENNReal.toReal_mono finite tv
  refine Kriterion.ArgoMAC.Security.Phase3.coreUntilBad_iff.mpr ?_
  have triangle : Assumptions.advantage
      (atSolution hiddenDeletedHybrid field group adversary parameter scalar)
      (atSolution publicFirstHybrid field group adversary parameter scalar) ≤
    Assumptions.advantage (hiddenDeletedHybrid adversary parameter scalar)
        (hiddenDeletedWith designedInstall adversary parameter scalar) +
      Assumptions.advantage (hiddenDeletedWith designedInstall adversary parameter scalar)
        (atSolution publicFirstHybrid field group adversary parameter scalar) := by
    unfold Assumptions.advantage
    exact abs_sub_le _ _ _
  refine le_trans triangle (le_trans (add_le_add (hop.trans coincidenceLe)
    (overlap.trans (add_le_add mass tvReal))) ?_)
  linarith [curveSwapError_le]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
