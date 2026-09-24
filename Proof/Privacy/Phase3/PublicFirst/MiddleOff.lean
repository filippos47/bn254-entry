/-
**Phase 3, P1g — the middle game `M'` of the corrected hop, and the extra `maskSwapError`.**

P1g.3 showed that off the curve `G1U` shows the adversary its system-A switch-mask vectors with
`G0U`'s **uniform** values, while `HW` leaves them to the lazy oracle (`sampleLane` of fresh hash
answers). The Glue charges `G1U → HW` with `+ maskSwapError`. The middle game carries that charge:

* `middleGameFill tapeLaw shadow` is P1e's `M` with its **off-curve private run through the fill
  runner** (`runFillFlag`): the first hash question at each untouched cell, at a fresh input, is
  programmed from a tape drawn from `tapeLaw`, every other question is lazy.
* **`M' := middleGameFill uniformMaskTape`** reads P4's mask tape (vectors uniform on `F_p^n`, limbs
  a uniform `sampleLane` preimage, exactly `G0U`'s swap kernel): it is the game
  `FlagMono (g1uLaterWith designedInstall)` must reach.
* **`middleGameFill (uniform Tape) = middleGame`** (`middleFill_uniform_eq`): with a uniform tape the
  fill is the flagged lazy run (`uniform_bind_runFillFlag`, `runFillFlag_uniform_eq`), so `Below HW`
  holds for it by P1e's `middle_below` — the "vectors drawn by `sampleLane` on fresh hash answers as
  `HW` sees them".
* the distance between the two readings is charged in `LiftHop`, for the designed shadow: its
  fill reads only the curve lanes' limbs, so the readings are within `curveSwapError`
  (`LiftTV.lean`, `LiftHop.curveSwapError_le`: at most one copy of `maskSwapError`).
* **`advantage_le_of_overlap_tv`**: a game above one flagged game and another above a second one are
  within the first's flag mass plus the two flagged games' total-variation distance.
-/

import Proof.Privacy.Phase3.PublicFirst.Middle
import Proof.Privacy.Phase3.PublicFirst.Fill
import Proof.Privacy.Phase3.Lazy.StepBound

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary Stage1Source openingQueriesM)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape uniformMaskTape)
open scoped ENNReal

noncomputable section

/-! ### 1. The overlap lemma with a total-variation step -/

theorem toOuterMeasure_true_none (law : PMF (Option Bool)) :
    law.toOuterMeasure {some true, none} = law (some true) + law none := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  simp [Set.indicator, Fintype.sum_option, add_comm]

/-- An event's mass moves by at most the total-variation distance. -/
theorem mass_le_add_etvDist {A : Type} (first second : PMF A) (event : Set A) :
    first.toOuterMeasure event ≤ second.toOuterMeasure event + first.etvDist second := by
  rw [PMF.etvDist_comm, Kriterion.ArgoMAC.Security.Phase3.etvDist_eq_tsum_tsub,
    PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun point => ?_
  by_cases inside : point ∈ event
  · rw [Set.indicator_of_mem inside, Set.indicator_of_mem inside]
    exact le_add_tsub
  · rw [Set.indicator_of_notMem inside]
    exact zero_le

/-- **Two games above two flagged games** are within the first's flag mass plus the flagged games'
total-variation distance. -/
theorem advantage_le_of_overlap_tv {first second : PMF Bool} {upper lower : PMF (Option Bool)}
    (firstBelow : Below first upper) (secondBelow : Below second lower) :
    Assumptions.advantage first second ≤ (upper none).toReal + (upper.etvDist lower).toReal := by
  have dFinite : upper.etvDist lower ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.etvDist_le_one _ _)
  have singleton := mass_le_add_etvDist upper lower {some true}
  have pair := mass_le_add_etvDist lower upper {some true, none}
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at singleton
  rw [toOuterMeasure_true_none, toOuterMeasure_true_none, PMF.etvDist_comm] at pair
  have upperTotal := flagged_total upper
  have lowerTotal := flagged_total lower
  have firstFalse := pmf_bool_false first
  have secondFalse := pmf_bool_false second
  have fin : ∀ x : Option Bool, upper x ≠ ⊤ := fun x => PMF.apply_ne_top _ _
  have finL : ∀ x : Option Bool, lower x ≠ ⊤ := fun x => PMF.apply_ne_top _ _
  have toR := fun {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (h : a ≤ b) => ENNReal.toReal_mono hb h
  have s1 : (upper (some true)).toReal ≤ (lower (some true)).toReal + (upper.etvDist lower).toReal := by
    rw [← ENNReal.toReal_add (finL _) dFinite]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨finL _, dFinite⟩) singleton
  have s2 : (lower (some true)).toReal + (lower none).toReal ≤
      (upper (some true)).toReal + (upper none).toReal + (upper.etvDist lower).toReal := by
    rw [← ENNReal.toReal_add (finL _) (finL _), ← ENNReal.toReal_add (fin _) (fin _),
      ← ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨fin _, fin _⟩) dFinite]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨fin _, fin _⟩, dFinite⟩) pair
  have u : (upper none).toReal + (upper (some true)).toReal + (upper (some false)).toReal = 1 := by
    rw [← ENNReal.toReal_add (fin _) (fin _),
      ← ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨fin _, fin _⟩) (fin _), upperTotal,
      ENNReal.toReal_one]
  have l : (lower none).toReal + (lower (some true)).toReal + (lower (some false)).toReal = 1 := by
    rw [← ENNReal.toReal_add (finL _) (finL _),
      ← ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨finL _, finL _⟩) (finL _), lowerTotal,
      ENNReal.toReal_one]
  have f : (first true).toReal + (first false).toReal = 1 := by
    rw [firstFalse, ENNReal.toReal_sub_of_le (PMF.coe_le_one _ _) ENNReal.one_ne_top,
      ENNReal.toReal_one]
    ring
  have s : (second true).toReal + (second false).toReal = 1 := by
    rw [secondFalse, ENNReal.toReal_sub_of_le (PMF.coe_le_one _ _) ENNReal.one_ne_top,
      ENNReal.toReal_one]
    ring
  have b1 : (upper (some true)).toReal ≤ (first true).toReal :=
    ENNReal.toReal_mono (PMF.apply_ne_top _ _) (firstBelow true)
  have b2 : (upper (some false)).toReal ≤ (first false).toReal :=
    ENNReal.toReal_mono (PMF.apply_ne_top _ _) (firstBelow false)
  have b3 : (lower (some true)).toReal ≤ (second true).toReal :=
    ENNReal.toReal_mono (PMF.apply_ne_top _ _) (secondBelow true)
  have b4 : (lower (some false)).toReal ≤ (second false).toReal :=
    ENNReal.toReal_mono (PMF.apply_ne_top _ _) (secondBelow false)
  unfold Assumptions.advantage
  rw [abs_le]
  constructor <;> linarith

/-! ### 2. `M'`: the off-curve private run through the fill runner -/

section Stage2

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

open Classical in
/-- **`M'`'s stage 2**: `M`'s, with the off-curve private run through the fill runner on a tape drawn
from `tapeLaw`. -/
def middleStage2Fill (tapeLaw : PMF Tape) (shadow : Shadow) (scalar : NonZeroScalar)
    (source : Stage1Source) (input : AffineInput) (output : Option Point) (planted : LState) :
    PMF (Option (Option (LamportSignature × LState))) :=
  let labels := sourceLabels source input
  let restored := Lamport.restore input labels
  match output with
  | none => shadow.law.bind fun coin =>
      (tapeLaw.bind fun tape => runFillFlag planted (fun cell => PMF.pure (tape cell))
        (shadow.offCurve source input coin) LazyOracle.empty ∅).bind fun shadowed =>
        match shadowed with
        | none => PMF.pure none
        | some result => if shadow.revealOff source input coin result.2 then PMF.pure none
            else PMF.pure (some (some (labels, mergeChoice planted result.2)))
  | some _ => refillStageM planted restored.input
      (openingQueriesM source.publicValue restored.input restored.inputMac)
      (privateCont shadow scalar planted source input)

/-- **The middle game with the fill runner off the curve.** -/
def middleGameFill (tapeLaw : PMF Tape) (shadow : Shadow) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar) : PMF (Option Bool) :=
  (PMF.uniformOfFintype Stage1Source).bind fun source =>
    (LazyOracle.run (adversary.chooseInput parameter source.publicValue ()) LazyOracle.empty).bind
      fun selected =>
        (middleStage2Fill tapeLaw shadow scalar source selected.1.1
            (Scheme.scheme.function scalar selected.1.1) selected.2).bind
          (finishM fun labels => adversary.decide parameter source.publicValue labels () selected.1.2)

/-- With a uniform tape, `M'`'s stage 2 is `M`'s. -/
theorem middleStage2Fill_uniform (shadow : Shadow) (scalar : NonZeroScalar)
    (source : Stage1Source) (input : AffineInput) (output : Option Point) (planted : LState) :
    middleStage2Fill (PMF.uniformOfFintype Tape) shadow scalar source input output planted =
      middleStage2 shadow scalar source input output planted := by
  cases output with
  | none =>
    simp only [middleStage2Fill, middleStage2]
    congr 1
    funext coin
    rw [uniform_bind_runFillFlag, runFillFlag_uniform_eq]
    rfl
  | some target => rfl

/-- **With a uniform tape, `M'` is P1e's `M`.** -/
theorem middleFill_uniform_eq (shadow : Shadow) (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    middleGameFill (PMF.uniformOfFintype Tape) shadow adversary parameter scalar =
      middleGame shadow adversary parameter scalar := by
  unfold middleGameFill middleGame
  simp only [middleStage2Fill_uniform]

end Stage2

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
