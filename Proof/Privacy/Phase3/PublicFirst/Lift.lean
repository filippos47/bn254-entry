/-
**Phase 3, P1j — the F4 lift, part 1: the adaptive plumbing (`FlagMono upper M'` from a per-input
core).**

The upper game of the corrected hop is `G1U` with the EncPRF entries planted at the input choice
(P1d). P1j lifts against a **family** of such games, one per installation rule: the entries
installed at the input choice are a parameter (`InstallRule`, the game `g1uLaterWith`);
`visibleEntries` gives P1d's game, the designed rule of the hidden hop gives the designed game of
`LiftHop.lean`. For every rule, `G1U` read with that rule is above its later form
(`below_laterWith`, P1d's argument).

**The per-input core.** `FlagMono (g1uLaterWith installed) M'` is reduced to one inequality per
(input, stage-1 state, adversary stage 2, published-value weight): `LiftCore`. The reduction
(`flagMono_of_core`) is the whole adaptive argument:

* **stage 1 flag.** `runFlag` (stopped at the first stage-1 touch of the planted EncPRF entries)
  keeps every unflagged path whose final state does not touch them (`runFlag_ge_untouched`: a touch
  stores the pair it touches with, `query_touch`, and states only grow, `run_grows`);
* **adaptivity.** Both games run the same stage 1 on the empty oracle from the published value
  alone; per stage-1 outcome `(u, st, σ₁)` its law is a function of the published value, which the
  core takes as the weight `weight`. The core must hold for every such weight, i.e. it is the
  statement *conditioned on the published value*;
* **stage 2.** `M'`'s flag-down stage-2 weight (`middleWeight`) against the upper game's
  (`upperWeight`: the stage-1 flag as an indicator on `σ₁`, then the adversary's stage 2 on the
  installed state).

Everything here is real; `LiftCore` is the remaining content of the lift.
-/

import Proof.Privacy.Phase3.PublicFirst.FlagBound
import Proof.Privacy.Phase3.PublicFirst.StageOne

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary Stage1Source)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Tape)
open scoped ENNReal

noncomputable section

/-! ### 1. The stage-1 flag keeps the untouched paths -/

section Generic

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- An EncPRF touch is a touch. -/
theorem encTouch_fullTouch (planted : LazyOracle.State FixedIndex EncIndex)
    (request : PublicQuery FixedIndex EncIndex) (answer : request.Answer)
    (touch : EncTouch planted request answer) : FullTouch planted request answer := by
  cases request with
  | fixedForward _ _ => exact touch.elim
  | fixedInverse _ _ => exact touch.elim
  | encForward _ _ => exact touch
  | encInverse _ _ => exact touch
  | hash _ => exact touch.elim

/-- **A lazy run only grows its state.** -/
theorem run_grows {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget) :
    ∀ (state : LazyOracle.State FixedIndex EncIndex) (outcome : Result × LazyOracle.State FixedIndex EncIndex),
      outcome ∈ (LazyOracle.run program state).support → Grows state outcome.2 := by
  induction program with
  | pure distribution =>
    intro state outcome member
    simp only [LazyOracle.run, runSampled] at member
    obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Grows.refl state
  | query request next ih =>
    intro state outcome member
    simp only [LazyOracle.run, runSampled] at member
    obtain ⟨answer, answerMember, outcomeMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    exact (query_grows request state answer answerMember).trans (ih answer.1 answer.2 outcome outcomeMember)
  | sample distribution next ih =>
    intro state outcome member
    simp only [LazyOracle.run, runSampled] at member
    obtain ⟨value, _, outcomeMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    exact ih value state outcome outcomeMember

open Classical in
/-- The indicator of an untouched final state. -/
def untouched (planted state : LazyOracle.State FixedIndex EncIndex) : ℝ≥0∞ :=
  if Touches planted (pointsOf state) then 0 else 1

theorem untouched_le_one (planted state : LazyOracle.State FixedIndex EncIndex) :
    untouched planted state ≤ 1 := by
  unfold untouched
  split_ifs <;> simp

theorem untouched_of_grows {planted s s' : LazyOracle.State FixedIndex EncIndex} (grow : Grows s s')
    (hit : Touches planted (pointsOf s)) : untouched planted s' = 0 := by
  unfold untouched
  rw [if_pos (touches_grows grow hit)]

/-- **The stage-1 flag keeps every path whose final state is untouched.** -/
theorem runFlag_ge_untouched (planted : LazyOracle.State FixedIndex EncIndex) {Result : Type}
    {budget : ℕ} (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget) :
    ∀ (state : LazyOracle.State FixedIndex EncIndex) (outcome : Result × LazyOracle.State FixedIndex EncIndex),
      LazyOracle.run program state outcome * untouched planted outcome.2
        ≤ runFlag planted program state (some outcome) := by
  classical
  induction program with
  | pure distribution =>
    intro state outcome
    refine le_trans (mul_le_of_le_one_right' (untouched_le_one planted outcome.2)) (le_of_eq ?_)
    simp only [runFlag, LazyOracle.run, runSampled]
    have factor : (fun result => some (result, state)) =
        (some : Result × LazyOracle.State FixedIndex EncIndex → _) ∘ fun result => (result, state) :=
      rfl
    rw [factor, ← PMF.map_comp, map_some_apply]
  | query request next ih =>
    intro state outcome
    simp only [LazyOracle.run, runSampled, runFlag]
    rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun answer => ?_
    rw [mul_assoc]
    by_cases member : answer ∈ (LazyOracle.query request state).support
    · refine mul_le_mul' le_rfl ?_
      by_cases touch : EncTouch planted request answer.1
      · rw [if_pos touch]
        have hit := query_touch planted request state answer member
          (encTouch_fullTouch planted request answer.1 touch)
        by_cases reached : outcome ∈ (runSampled LazyOracle.query (next answer.1) answer.2).support
        · have grow := run_grows (next answer.1) answer.2 outcome reached
          rw [untouched_of_grows grow hit, mul_zero]
          exact zero_le
        · rw [PMF.apply_eq_zero_iff _ _ |>.mpr reached, zero_mul]
          exact zero_le
      · rw [if_neg touch]
        exact ih answer.1 answer.2 outcome
    · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]
  | sample distribution next ih =>
    intro state outcome
    simp only [LazyOracle.run, runSampled, runFlag]
    rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun value => ?_
    rw [mul_assoc]
    exact mul_le_mul' le_rfl (ih value state outcome)

/-- **A flagged stage 1 followed by a continuation, flag-down, from below.** -/
theorem flagBind_ge_untouched (planted : LazyOracle.State FixedIndex EncIndex) {Result : Type}
    {budget : ℕ} (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : LazyOracle.State FixedIndex EncIndex)
    (continuation : Result → LazyOracle.State FixedIndex EncIndex → PMF Bool) (b : Bool) :
    ∑' outcome, LazyOracle.run program state outcome
        * (untouched planted outcome.2 * continuation outcome.1 outcome.2 b)
      ≤ flagBind (runFlag planted program state) continuation (some b) := by
  unfold flagBind
  rw [PMF.bind_apply, tsum_option _ ENNReal.summable]
  refine le_trans ?_ (le_add_left le_rfl)
  refine ENNReal.tsum_le_tsum fun outcome => ?_
  dsimp only
  rw [map_some_apply, ← mul_assoc]
  exact mul_le_mul' (runFlag_ge_untouched planted program state outcome) le_rfl

end Generic

/-! ### 2. The upper games of the family -/

section Upper

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
  [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **An installation rule**: the garbler's entries installed at the input choice, from the scalar,
the tape, the published value, the input and its labels. -/
abbrev InstallRule :=
  NonZeroScalar → (Coins × Oracle) → Public → AffineInput → LamportSignature →
    List (Entry FixedIndex EncPRF.PermutationIndex)

/-- **`G1U` read with an installation rule**: `G0U`'s garbling, stage 1 on the EncPRF entries, the
rule's entries installed at the input choice. -/
def hiddenDeletedWith (installed : InstallRule) (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) : PMF Bool :=
  swappedChallengeTape.bind fun tape =>
    let garbled := Scheme.scheme.garble parameter scalar tape
    (LazyOracle.run (adversary.chooseInput parameter garbled.1 ())
        (installAll ((garblerTranscript scalar tape).filter Entry.IsEnc) LazyOracle.empty)).bind
      fun selected =>
        let labels := Scheme.scheme.encode garbled.2 selected.1.1
        (LazyOracle.run (adversary.decide parameter garbled.1 labels () selected.1.2)
          (installAll (installed scalar tape garbled.1 selected.1.1 labels) selected.2)).map
          Prod.fst

/-- **Its later form**: the EncPRF entries planted at the input choice, a stage-1 touch flagged. -/
def g1uLaterWith (installed : InstallRule) (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) : PMF (Option Bool) :=
  swappedChallengeTape.bind fun tape =>
    let garbled := Scheme.scheme.garble parameter scalar tape
    flagBind (runFlag (plantAll (encEntries scalar tape) LazyOracle.empty)
        (adversary.chooseInput parameter garbled.1 ()) LazyOracle.empty)
      fun selected state =>
        let labels := Scheme.scheme.encode garbled.2 selected.1
        (LazyOracle.run (adversary.decide parameter garbled.1 labels () selected.2)
          (installAll (installed scalar tape garbled.1 selected.1 labels)
            (plantAll (encEntries scalar tape) state))).map Prod.fst

/-- The visible rule is `G1U` itself. -/
theorem hiddenDeletedWith_visible (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    hiddenDeletedWith (fun scalar tape table input labels => visibleEntries scalar tape table input labels)
        adversary parameter scalar = hiddenDeletedHybrid adversary parameter scalar := rfl

/-- **`G1U` read with any rule is above its later form**, for any install rule (P1d's argument). -/
theorem below_laterWith (installed : InstallRule) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar) :
    Below (hiddenDeletedWith installed adversary parameter scalar)
      (g1uLaterWith installed adversary parameter scalar) := by
  intro b
  unfold hiddenDeletedWith g1uLaterWith
  rw [PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
  let garbled := Scheme.scheme.garble parameter scalar tape
  let KF : AffineInput × adversary.State → LazyOracle.State FixedIndex EncPRF.PermutationIndex →
      PMF Bool := fun selected state =>
    (LazyOracle.run (adversary.decide parameter garbled.1
        (Scheme.scheme.encode garbled.2 selected.1) () selected.2)
      (installAll (installed scalar tape garbled.1 selected.1
        (Scheme.scheme.encode garbled.2 selected.1)) state)).map Prod.fst
  have agree : ∀ selected sF sL,
      EncRel (plantAll (encEntries scalar tape) LazyOracle.empty) sF sL →
        KF selected (plantAll (encEntries scalar tape) sL) = KF selected sF := by
    intro selected sF sL related
    have same := encRel_sameLookups (encEntries scalar tape) (encEntries_encOnly scalar tape) related
    exact run_map_fst_congr _ (plantAll_congr (installed scalar tape garbled.1 selected.1
      (Scheme.scheme.encode garbled.2 selected.1)) same.symm)
  have key := plant_ge (plantAll (encEntries scalar tape) LazyOracle.empty) KF
    (fun selected state => KF selected (plantAll (encEntries scalar tape) state)) agree
    (adversary.chooseInput parameter garbled.1 ()) _ _
    (encRel_base (encEntries scalar tape) (encEntries_encOnly scalar tape)) b
  exact key

end Upper

/-! ### 3. The per-input core, and the lift from it -/

section Core

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
  [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **`M'`'s flag-down stage-2 weight** at one input and stage-1 state, for an adversary stage 2
reading the published value and the labels. -/
def middleWeight (tapeLaw : PMF Tape) (shadow : Shadow) (scalar : NonZeroScalar)
    (source : Stage1Source) (input : AffineInput) (planted : LState) {budget : ℕ}
    (decide : Public → LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (b : Bool) : ℝ≥0∞ :=
  ∑' o, middleStage2Fill tapeLaw shadow scalar source input (Scheme.scheme.function scalar input)
    planted o * contM (decide source.publicValue) b o

/-- **The upper game's flag-down stage-2 weight** at one input and stage-1 state: the stage-1 flag
as an indicator on `σ₁`, then the adversary's stage 2 on the installed state. -/
def upperWeight (installed : InstallRule) (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) (input : AffineInput) (planted : LState) {budget : ℕ}
    (decide : Public → LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (b : Bool) : ℝ≥0∞ :=
  untouched (plantAll (encEntries scalar tape) LazyOracle.empty) planted *
    ((LazyOracle.run (decide (Scheme.scheme.garble parameter scalar tape).1
        (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input))
      (installAll (installed scalar tape (Scheme.scheme.garble parameter scalar tape).1 input
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input))
        (plantAll (encEntries scalar tape) planted))).map Prod.fst) b

/-- **The per-input core of the lift**: for every input, stage-1 state, adversary stage 2 and weight
on the published value (the stage-1 law of that outcome), `M'`'s flag-down stage-2 mass is below the
upper game's, both averaged over the published value's law. -/
def LiftCore (installed : InstallRule) (tapeLaw : PMF Tape) (shadow : Shadow) (parameter : ℕ)
    (scalar : NonZeroScalar) : Prop :=
  ∀ (input : AffineInput) (planted : LState) (budget : ℕ)
    (decide : Public → LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (weight : Public → ℝ≥0∞) (b : Bool),
    ∑' source, PMF.uniformOfFintype Stage1Source source *
        (weight source.publicValue * middleWeight tapeLaw shadow scalar source input planted decide b)
      ≤ ∑' tape, swappedChallengeTape tape *
        (weight (Scheme.scheme.garble parameter scalar tape).1 *
          upperWeight installed parameter scalar tape input planted decide b)

/-- `M'`, flag-down, as a sum over the stage-1 outcomes. -/
theorem middleFill_some_eq (tapeLaw : PMF Tape) (shadow : Shadow) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar) (b : Bool) :
    middleGameFill tapeLaw shadow adversary parameter scalar (some b) =
      ∑' source, PMF.uniformOfFintype Stage1Source source *
        ∑' selected, LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
            LazyOracle.empty selected *
          middleWeight tapeLaw shadow scalar source selected.1.1 selected.2
            (fun table labels => adversary.decide parameter table labels () selected.1.2) b := by
  unfold middleGameFill
  rw [PMF.bind_apply]
  refine tsum_congr fun source => ?_
  rw [PMF.bind_apply]
  congr 1
  refine tsum_congr fun selected => ?_
  rw [PMF.bind_apply]
  congr 1
  unfold middleWeight
  refine tsum_congr fun o => ?_
  rw [finishM_some]

/-- The upper game, flag-down, from below, as a sum over the stage-1 outcomes. -/
theorem laterWith_some_ge (installed : InstallRule) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar) (b : Bool) :
    ∑' tape, swappedChallengeTape tape *
        ∑' selected, LazyOracle.run (adversary.chooseInput parameter
            (Scheme.scheme.garble parameter scalar tape).1 ()) LazyOracle.empty selected *
          upperWeight installed parameter scalar tape selected.1.1 selected.2
            (fun table labels => adversary.decide parameter table labels () selected.1.2) b
      ≤ g1uLaterWith installed adversary parameter scalar (some b) := by
  unfold g1uLaterWith
  rw [PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
  exact flagBind_ge_untouched _ _ _ _ b

/-- **The lift from its per-input core**: `M'` is below the upper game of the rule. -/
theorem flagMono_of_core (installed : InstallRule) (tapeLaw : PMF Tape) (shadow : Shadow)
    (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar)
    (core : LiftCore installed tapeLaw shadow parameter scalar) :
    FlagMono (g1uLaterWith installed adversary parameter scalar)
      (middleGameFill tapeLaw shadow adversary parameter scalar) := by
  intro b
  rw [middleFill_some_eq]
  refine le_trans ?_ (laterWith_some_ge installed adversary parameter scalar b)
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun selected => ?_
  have step := core selected.1.1 selected.2 _
    (fun table labels => adversary.decide parameter table labels () selected.1.2)
    (fun table => LazyOracle.run (adversary.chooseInput parameter table ()) LazyOracle.empty
      selected) b
  refine le_trans (le_of_eq (tsum_congr fun source => ?_)) (le_trans step (le_of_eq
    (tsum_congr fun tape => ?_)))
  · ring
  · ring

end Core

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
