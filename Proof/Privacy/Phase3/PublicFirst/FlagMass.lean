/-
**Phase 3, P1i — (B), part 2: `M'`'s flag at stage 2 is a touch of the unflagged private points, or
the reveal flag.**

`privateStage2U` is `M'`'s private stage 2 (`middleStage2Fill`) with every flag removed: the refill
run is P4's `runRefill`, the designated installation `programAllSkip`, the shadow's questions
`runLazyQ`, the off-curve run the fill runner against the empty state. It returns the points it
stores — the final private state's pairs **and** the designated requests' hash inputs, whether or
not their programs succeed (`requestPoints`) — and the reveal bit (`none`: an abort).

**`middleStage2Fill_none_le`**: at every stage-1 state `σ₁`, the flag mass of `M'`'s stage 2 is at
most the mass with which the unflagged outcome aborts, meets `σ₁` (`Touches σ₁ points`), or
reveals (`outcomeWeight`). The runners are compared by `FlagTouch` (`runRefillFlag_le`,
`runLazyQFlag_le`, `runFillFlag_le`); the designated installation flags exactly when a request
touches `σ₁` (`programAllSkipFlag_none`), and otherwise is `programAllSkip`
(`programAllSkipFlag_some`).
-/

import Proof.Privacy.Phase3.PublicFirst.FlagTouch
import Proof.Privacy.Phase3.PublicFirst.MiddleOff

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary Stage1Source idealSamplers openingQueriesM
  designatedLimbs programRequests noRecord)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape runRefill uniformMaskTape)
open scoped ENNReal

noncomputable section

/-! ### Unions of points -/

section Points

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- The union of two point sets. -/
def Points.union (first second : Points FixedIndex EncIndex) : Points FixedIndex EncIndex where
  fixedIn i x := first.fixedIn i x ∨ second.fixedIn i x
  fixedOut i y := first.fixedOut i y ∨ second.fixedOut i y
  encIn i x := first.encIn i x ∨ second.encIn i x
  encOut i y := first.encOut i y ∨ second.encOut i y
  hashIn k := first.hashIn k ∨ second.hashIn k

theorem touches_union_left {planted : LazyOracle.State FixedIndex EncIndex}
    {first : Points FixedIndex EncIndex} (second : Points FixedIndex EncIndex)
    (hit : Touches planted first) : Touches planted (first.union second) := by
  rcases hit with ⟨i, x, y, found, hit⟩ | ⟨i, x, y, found, hit⟩ | ⟨k, v, found, hit⟩
  · exact Or.inl ⟨i, x, y, found, hit.imp Or.inl Or.inl⟩
  · exact Or.inr (Or.inl ⟨i, x, y, found, hit.imp Or.inl Or.inl⟩)
  · exact Or.inr (Or.inr ⟨k, v, found, Or.inl hit⟩)

theorem touches_union_right {planted : LazyOracle.State FixedIndex EncIndex}
    (first : Points FixedIndex EncIndex) {second : Points FixedIndex EncIndex}
    (hit : Touches planted second) : Touches planted (first.union second) := by
  rcases hit with ⟨i, x, y, found, hit⟩ | ⟨i, x, y, found, hit⟩ | ⟨k, v, found, hit⟩
  · exact Or.inl ⟨i, x, y, found, hit.imp Or.inr Or.inr⟩
  · exact Or.inr (Or.inl ⟨i, x, y, found, hit.imp Or.inr Or.inr⟩)
  · exact Or.inr (Or.inr ⟨k, v, found, Or.inr hit⟩)

end Points

/-! ### The designated installation -/

section Designated

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The designated requests' hash inputs, as points** (whether or not their programs
succeed). -/
def requestPoints (requests : List (Option BaseField × (Block × Block))) :
    Points FixedIndex EncPRF.PermutationIndex where
  fixedIn _ _ := False
  fixedOut _ _ := False
  encIn _ _ := False
  encOut _ _ := False
  hashIn k := ∃ answer, (some k, answer) ∈ requests

theorem requestPoints_mono {requests : List (Option BaseField × (Block × Block))}
    (request : Option BaseField × (Block × Block)) {planted : LState}
    (hit : Touches planted (requestPoints requests)) :
    Touches planted (requestPoints (request :: requests)) := by
  rcases hit with ⟨i, x, y, found, hit⟩ | ⟨i, x, y, found, hit⟩ | ⟨k, v, found, answer, member⟩
  · exact hit.elim (fun h => False.elim h) (fun h => False.elim h)
  · exact hit.elim (fun h => False.elim h) (fun h => False.elim h)
  · exact Or.inr (Or.inr ⟨k, v, found, answer, List.mem_cons_of_mem _ member⟩)

/-- **The designated installation flags exactly at a request touching `planted`.** -/
theorem programAllSkipFlag_none (planted : LState) :
    ∀ (requests : List (Option BaseField × (Block × Block))) (state : LState),
      programAllSkipFlag planted requests state = none →
        Touches planted (requestPoints requests) := by
  intro requests
  induction requests with
  | nil =>
    intro state flagged
    simp [programAllSkipFlag] at flagged
  | cons request rest ih =>
    intro state flagged
    obtain ⟨input, answer⟩ := request
    cases input with
    | none =>
      exact requestPoints_mono _ (ih state flagged)
    | some input =>
      simp only [programAllSkipFlag] at flagged
      split_ifs at flagged with touching
      · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp touching
        exact Or.inr (Or.inr ⟨input, v, hv, answer, List.mem_cons_self⟩)
      · exact requestPoints_mono _ (ih _ flagged)

/-- **Off a flag, the designated installation is `programAllSkip`.** -/
theorem programAllSkipFlag_some (planted : LState) :
    ∀ (requests : List (Option BaseField × (Block × Block))) (state installed : LState),
      programAllSkipFlag planted requests state = some installed →
        installed = programAllSkip requests state := by
  intro requests
  induction requests with
  | nil =>
    intro state installed done
    simp only [programAllSkipFlag, Option.some.injEq] at done
    exact done.symm
  | cons request rest ih =>
    intro state installed done
    obtain ⟨input, answer⟩ := request
    cases input with
    | none => exact ih state installed done
    | some input =>
      simp only [programAllSkipFlag] at done
      split_ifs at done with touching
      exact ih _ installed done

/-- **The designated installation only grows the state.** -/
theorem programAllSkip_grows :
    ∀ (requests : List (Option BaseField × (Block × Block))) (state : LState),
      Grows state (programAllSkip requests state) := by
  intro requests
  induction requests with
  | nil => exact fun state => Grows.refl state
  | cons request rest ih =>
    intro state
    obtain ⟨input, answer⟩ := request
    cases input with
    | none => exact ih state
    | some input =>
      show Grows state (programAllSkip rest
        ((LazyOracle.program (.hash input) answer state).getD state))
      cases success : LazyOracle.program (.hash input) answer state with
      | none => exact ih state
      | some updated =>
        exact (program_hash_grows input answer state updated success).trans (ih updated)

end Designated

/-! ### `M'`'s private stage 2, unflagged -/

section Stage2

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- The outcome of the unflagged private stage 2: the stored points and the reveal bit; `none` is
an abort. -/
abbrev PrivateOutcome := Option (Points FixedIndex EncPRF.PermutationIndex × Bool)

open Classical in
/-- **The flag weight of an unflagged outcome**: an abort, a touch of `planted`, or the reveal. -/
def outcomeWeight (planted : LState) : PrivateOutcome → ℝ≥0∞
  | none => 1
  | some (points, reveal) => if Touches planted points ∨ reveal = true then 1 else 0

open Classical in
/-- **`M'`'s private continuation after the refill run, unflagged.** -/
def privateContU (shadow : Shadow) (scalar : NonZeroScalar) (source : Stage1Source)
    (input : AffineInput)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) × LState ×
      Record) : PMF PrivateOutcome :=
  let labels := sourceLabels source input
  let restored := Lamport.restore input labels
  letI : Fintype Coins := Fintype.ofFinite Coins
  (PMF.uniformOfFintype Coins).bind fun coins =>
    (designatedLimbs idealSamplers source.publicValue restored.input ran.1.1 ran.1.2
        (fun digit => trueRows scalar coins input digit)).bind fun answers =>
      match answers with
      | none => PMF.pure none
      | some answers =>
        shadow.law.bind fun coin =>
          (runLazyQ (shadow.onCurve source input coins coin (ran.1, ran.2.2))
              (programAllSkip (programRequests restored.input ran.2.2 answers) ran.2.1)).map
            fun result => some ((pointsOf result.2).union
                (requestPoints (programRequests restored.input ran.2.2 answers)),
              decide (shadow.revealOn source input coins coin result.2))

open Classical in
/-- **`M'`'s private stage 2, unflagged.** -/
def privateStage2U (tapeLaw : PMF Tape) (shadow : Shadow) (scalar : NonZeroScalar)
    (source : Stage1Source) (input : AffineInput) (output : Option Point) : PMF PrivateOutcome :=
  let labels := sourceLabels source input
  let restored := Lamport.restore input labels
  match output with
  | none => shadow.law.bind fun coin =>
      (tapeLaw.bind fun tape => runFillFlag LazyOracle.empty (fun cell => PMF.pure (tape cell))
        (shadow.offCurve source input coin) LazyOracle.empty ∅).map fun shadowed =>
        match shadowed with
        | none => none
        | some result => some (pointsOf result.2, decide (shadow.revealOff source input coin result.2))
  | some _ => uniformMaskTape.bind fun tape =>
      (runRefill restored.input (fun cell => PMF.pure (tape cell))
          (openingQueriesM source.publicValue restored.input restored.inputMac) LazyOracle.empty
          noRecord ∅).bind (abortCont (privateContU shadow scalar source input))

/-- The mass at `none`. -/
def isNone {β : Type} : Option β → ℝ≥0∞
  | none => 1
  | some _ => 0

theorem apply_none_eq {β : Type} (p : PMF (Option β)) : p none = ∑' o, p o * isNone o := by
  rw [tsum_eq_single none]
  · simp [isNone]
  · intro o different
    cases o with
    | none => exact absurd rfl different
    | some _ => simp [isNone]

theorem outcomeWeight_one_of_touch (planted : LState) {points : Points FixedIndex EncPRF.PermutationIndex}
    (reveal : Bool) (hit : Touches planted points) : outcomeWeight planted (some (points, reveal)) = 1 := by
  classical
  simp only [outcomeWeight]
  rw [if_pos (Or.inl hit)]

open Classical in
/-- **After the refill run, the flagged continuation is below the unflagged one.** -/
theorem privateCont_none_le (shadow : Shadow) (scalar : NonZeroScalar) (planted : LState)
    (source : Stage1Source) (input : AffineInput)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) × LState ×
      Record) :
    privateCont shadow scalar planted source input ran none ≤
      ∑' o, privateContU shadow scalar source input ran o * outcomeWeight planted o := by
  rw [apply_none_eq]
  unfold privateCont privateContU
  dsimp only
  rw [tsum_bind_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun coins => mul_le_mul' le_rfl ?_
  rw [tsum_bind_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun answers => mul_le_mul' le_rfl ?_
  rcases answers with _ | answers
  · simp only [tsum_pure_mul, isNone, outcomeWeight]
    exact zero_le
  · dsimp only
    cases flagDown : programAllSkipFlag planted (programRequests
        (Lamport.restore input (sourceLabels source input)).input ran.2.2 answers) ran.2.1 with
    | none =>
      have hit := programAllSkipFlag_none planted _ _ flagDown
      simp only [tsum_pure_mul, isNone]
      refine one_le_expect _ _ fun o reached => ?_
      obtain ⟨coin, _, reached⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      obtain ⟨result, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      rw [outcomeWeight_one_of_touch planted _ (touches_union_right _ hit)]
    | some installed =>
      have same := programAllSkipFlag_some planted _ _ installed flagDown
      dsimp only
      rw [tsum_bind_mul, tsum_bind_mul]
      refine ENNReal.tsum_le_tsum fun coin => mul_le_mul' le_rfl ?_
      rw [tsum_bind_mul, tsum_map_mul, ← same]
      refine le_trans (le_of_eq (tsum_congr fun r => ?_))
        (runLazyQFlag_le planted
          (fun result => if shadow.revealOn source input coins coin result.2 then 1 else 0)
          (fun result => outcomeWeight planted (some ((pointsOf result.2).union
            (requestPoints (programRequests (Lamport.restore input (sourceLabels source input)).input
              ran.2.2 answers)), decide (shadow.revealOn source input coins coin result.2))))
          (fun result => ?_) (fun result hit => ?_) _ installed)
      · congr 1
        rcases r with _ | result
        · simp [isNone, flagWeight]
        · by_cases hit : shadow.revealOn source input coins coin result.2
          · simp [hit, isNone, flagWeight]
          · simp [hit, isNone, flagWeight]
      · by_cases hit : shadow.revealOn source input coins coin result.2
        · simp [hit, outcomeWeight]
        · simp [hit]
      · rw [outcomeWeight_one_of_touch planted _ (touches_union_left _ hit)]

open Classical in
/-- **The unflagged continuation is saturated on a refill state that meets `planted`.** -/
theorem privateContU_saturated (shadow : Shadow) (scalar : NonZeroScalar) (planted : LState)
    (source : Stage1Source) (input : AffineInput)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) × LState ×
      Record) (hit : Touches planted (pointsOf ran.2.1)) :
    1 ≤ ∑' o, privateContU shadow scalar source input ran o * outcomeWeight planted o := by
  refine one_le_expect _ _ fun o reached => ?_
  unfold privateContU at reached
  dsimp only at reached
  obtain ⟨coins, _, reached⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  obtain ⟨answers, _, reached⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  rcases answers with _ | answers
  · simp only [PMF.mem_support_pure_iff] at reached
    subst reached
    simp [outcomeWeight]
  · obtain ⟨coin, _, reached⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
    obtain ⟨result, resultMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
    have grow := (programAllSkip_grows _ ran.2.1).trans (runLazyQ_grows _ _ result resultMember)
    rw [outcomeWeight_one_of_touch planted _ (touches_union_left _ (touches_grows grow hit))]

/-- The flagged refill stage, generically in the computation, against the unflagged one. -/
theorem refillStageM_none_le (planted : LState) (bits : BitInput) {α β γ : Type}
    (computation : FreeQuery Programs.Spec α)
    (contF : α × LState × Record → PMF (Option (Option β)))
    (contU : α × LState × Record → PMF (Option γ)) (weight : Option γ → ℝ≥0∞)
    (abortOne : weight none = 1)
    (step : ∀ ran, contF ran none ≤ ∑' o, contU ran o * weight o)
    (saturated : ∀ ran, Touches planted (pointsOf ran.2.1) → 1 ≤ ∑' o, contU ran o * weight o) :
    refillStageM planted bits computation contF none ≤
      ∑' o, (uniformMaskTape.bind fun tape =>
        (runRefill bits (fun cell => PMF.pure (tape cell)) computation LazyOracle.empty
          noRecord ∅).bind (abortCont contU)) o * weight o := by
  rw [apply_none_eq]
  unfold refillStageM
  rw [tsum_bind_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
  rw [tsum_bind_mul, tsum_bind_mul]
  refine le_trans (le_of_eq (tsum_congr fun r => ?_)) (le_trans (runRefillFlag_le planted bits
    (fun cell => PMF.pure (tape cell)) (fun ran => contF ran none)
    (fun ran => ∑' o, contU ran o * weight o) step saturated computation LazyOracle.empty
    noRecord ∅) (le_of_eq (tsum_congr fun r => ?_)))
  · congr 1
    rcases r with _ | _ | ran
    · simp [flagCont, isNone, flagWeight2]
    · simp [flagCont, isNone, flagWeight2]
    · simp only [flagCont, flagWeight2]
      exact (apply_none_eq _).symm
  · congr 1
    rcases r with _ | ran
    · simp [abortCont, abortWeight, abortOne]
    · rfl

/-- **`M'`'s stage-2 flag is an abort, a touch of `σ₁` by the unflagged private points, or the
reveal.** -/
theorem middleStage2Fill_none_le (tapeLaw : PMF Tape) (shadow : Shadow) (scalar : NonZeroScalar)
    (source : Stage1Source) (input : AffineInput) (output : Option Point) (planted : LState) :
    middleStage2Fill tapeLaw shadow scalar source input output planted none ≤
      ∑' o, privateStage2U tapeLaw shadow scalar source input output o * outcomeWeight planted o := by
  classical
  cases output with
  | none =>
    rw [apply_none_eq]
    simp only [middleStage2Fill, privateStage2U]
    rw [tsum_bind_mul, tsum_bind_mul]
    refine ENNReal.tsum_le_tsum fun coin => mul_le_mul' le_rfl ?_
    rw [tsum_bind_mul, tsum_map_mul, tsum_bind_mul, tsum_bind_mul]
    refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
    refine le_trans (le_of_eq (tsum_congr fun r => ?_)) (le_trans (runFillFlag_le planted
      (fun cell => PMF.pure (tape cell))
      (fun result => if shadow.revealOff source input coin result.2 then 1 else 0)
      (fun result => outcomeWeight planted
        (some (pointsOf result.2, decide (shadow.revealOff source input coin result.2))))
      (fun result => ?_) (fun result hit => ?_) (shadow.offCurve source input coin)
      LazyOracle.empty ∅)
      (le_of_eq (tsum_congr fun r => ?_)))
    · congr 1
      rcases r with _ | result
      · simp [isNone, flagWeight]
      · by_cases hit : shadow.revealOff source input coin result.2
        · simp [hit, isNone, flagWeight]
        · simp [hit, isNone, flagWeight]
    · by_cases hit : shadow.revealOff source input coin result.2
      · simp [hit, outcomeWeight]
      · simp [hit]
    · exact le_of_eq (outcomeWeight_one_of_touch planted _ hit).symm
    · congr 1
      rcases r with _ | result
      · simp [flagWeight, outcomeWeight]
      · rfl
  | some target =>
    simp only [middleStage2Fill, privateStage2U]
    exact refillStageM_none_le planted _ _ (privateCont shadow scalar planted source input)
      (privateContU shadow scalar source input) (outcomeWeight planted) rfl
      (privateCont_none_le shadow scalar planted source input)
      (privateContU_saturated shadow scalar planted source input)

end Stage2

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
