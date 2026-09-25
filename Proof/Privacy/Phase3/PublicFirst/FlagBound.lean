/-
**Phase 3, P1i — (B), part 3: `M'`'s flag mass from two per-shadow bounds.**

`middleFill_none_le`: for any shadow, the flag mass of `M'` (`middleGameFill uniformMaskTape`) is at
most `q₁ · c + ρ` as soon as

* **`PerPairBound shadow scalar c`** — the points of the unflagged private stage 2
  (`privateStage2U`: the final private state's pairs and the designated requests), averaged over
  the Lamport key and the private randomness, have per-pair mass `≤ c` at every published part and
  every input (the stage-1 union bound, P1d's `run_touch_mass_le`); and
* **`RevealBound shadow scalar ρ`** — the unflagged reveal bit has mass `≤ ρ`.

The proof: the stage-2 flag is an abort, a touch or the reveal (`FlagMass.middleStage2Fill_none_le`);
the unflagged private stage 2 never aborts (`runRefill_ne_none`, `runFillFlag_empty_ne_none`,
`designatedLimbs_ne_none`: a consumed hash input is fresh, and the designated draws are exact); the source splits into its published part and its Lamport key
(`sourceEquiv`), stage 1 reads only the former, so the touch mass is P1d's union bound over the
`≤ q₁` stage-1 pairs against the key-averaged points.
-/

import Proof.Privacy.Phase3.PublicFirst.FlagMass

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary Stage1Source idealSamplers designatedLimbs)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell runRefill uniformMaskTape consumeCell
  consumeCell_spec program_hash_refill)
open scoped ENNReal

noncomputable section

/-! ### The unflagged private stage 2 never aborts -/

section NoAbort

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **P4's refill runner never aborts**: a consumed input is fresh, so its hash program
succeeds. -/
theorem runRefill_ne_none (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell),
      none ∉ (runRefill bits draw computation oracle record touched).support := by
  induction computation with
  | pure value =>
    intro oracle record touched member
    simp [runRefill] at member
  | query request next ih =>
    intro oracle record touched member
    simp only [runRefill] at member
    cases intercept : Kriterion.ArgoMAC.Phase3.Glue.interceptAnswer bits request with
    | some answer =>
      rw [intercept] at member
      exact ih answer oracle _ touched member
    | none =>
      rw [intercept] at member
      simp only at member
      cases consumed : consumeCell touched oracle request with
      | some cell =>
        rw [consumed] at member
        obtain ⟨input, rfl, _, fresh, _⟩ := consumeCell_spec consumed
        simp only [PMF.mem_support_bind_iff] at member
        obtain ⟨value, _, rest⟩ := member
        rw [program_hash_refill, if_pos fresh] at rest
        exact ih _ _ _ _ rest
      | none =>
        rw [consumed] at member
        simp only [PMF.mem_support_bind_iff] at member
        obtain ⟨answer, _, rest⟩ := member
        exact ih _ _ _ _ rest

/-- **The fill runner against the empty state never stops**: nothing touches the empty state, and
a consumed input is fresh. -/
theorem runFillFlag_empty_ne_none (draw : Cell → PMF (Block × Block)) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (touched : Set Cell),
      none ∉ (runFillFlag LazyOracle.empty draw computation oracle touched).support := by
  induction computation with
  | pure value =>
    intro oracle touched member
    simp [runFillFlag] at member
  | query request next ih =>
    intro oracle touched member
    simp only [runFillFlag] at member
    cases consumed : consumeCell touched oracle request with
    | some cell =>
      rw [consumed] at member
      obtain ⟨input, rfl, _, fresh, _⟩ := consumeCell_spec consumed
      simp only [PMF.mem_support_bind_iff] at member
      obtain ⟨value, _, rest⟩ := member
      rw [if_neg (not_fullTouch_empty _ _), program_hash_refill, if_pos fresh] at rest
      exact ih _ _ _ rest
    | none =>
      rw [consumed] at member
      simp only [PMF.mem_support_bind_iff] at member
      obtain ⟨answer, _, rest⟩ := member
      rw [if_neg (not_fullTouch_empty _ _)] at rest
      exact ih _ _ _ rest

/-- **The exact designated draws never abort**: the free coordinates are uniform, the `362` hash
answers a fibre draw. -/
theorem designatedLimbs_ne_none (table : Public) (bits : BitInput)
    (pointX : Fin pointElementCountX → BaseField) (pointY : Fin pointElementCountY → BaseField)
    (targets : Fin digitCount → FieldMacToECMac.HomogeneousValue) :
    none ∉ (designatedLimbs idealSamplers table bits pointX pointY targets).support := by
  intro member
  unfold designatedLimbs at member
  obtain ⟨free, freeMember, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp freeMember
  obtain ⟨limbs, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp rest
  cases same

end NoAbort

/-! ### The source: its published part and its Lamport key -/

section Source

/-- A default Lamport key. -/
def defaultKey : InputMacKey := ⟨Vector.replicate _ ⟨0, 0⟩, Vector.replicate _ ⟨0, 0⟩⟩

/-- The published part of a source: the source with the default key. -/
abbrev PubPart := {source : Stage1Source // source.key = defaultKey}

noncomputable instance pubPartFintype : Fintype PubPart := Fintype.ofFinite _

noncomputable instance keyFintype' : Fintype InputMacKey := Fintype.ofFinite _

instance pubPartNonempty : Nonempty PubPart :=
  ⟨⟨{ (Classical.arbitrary Stage1Source) with key := defaultKey }, rfl⟩⟩

instance inputMacKeyNonempty : Nonempty InputMacKey := ⟨defaultKey⟩

/-- A published part with a key. -/
def joinSource (pub : PubPart) (key : InputMacKey) : Stage1Source := { pub.1 with key := key }

/-- **A source is its published part and its key.** -/
def sourceEquiv : PubPart × InputMacKey ≃ Stage1Source where
  toFun pair := joinSource pair.1 pair.2
  invFun source := (⟨{ source with key := defaultKey }, rfl⟩, source.key)
  left_inv pair := by
    obtain ⟨⟨source, same⟩, key⟩ := pair
    simp only [joinSource]
    refine Prod.ext (Subtype.ext ?_) rfl
    cases source
    simp only at same
    subst same
    rfl
  right_inv source := rfl

/-- The published value does not read the key. -/
theorem publicValue_joinSource (pub : PubPart) (key : InputMacKey) :
    (joinSource pub key).publicValue = pub.1.publicValue := rfl

/-- **The uniform source is a uniform published part and an independent uniform key.** -/
theorem uniform_source_eq {β : Type} (next : Stage1Source → PMF β) :
    (PMF.uniformOfFintype Stage1Source).bind next =
      (PMF.uniformOfFintype PubPart).bind fun pub =>
        (PMF.uniformOfFintype InputMacKey).bind fun key => next (joinSource pub key) := by
  rw [← Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv sourceEquiv, PMF.bind_map,
    Kriterion.ArgoMAC.Phase3.Lazy.uniform_pair_bind]
  rfl

/-- The same for an average. -/
theorem tsum_source_split (F : Stage1Source → ℝ≥0∞) :
    ∑' source, PMF.uniformOfFintype Stage1Source source * F source =
      ∑' pub, PMF.uniformOfFintype PubPart pub *
        ∑' key, PMF.uniformOfFintype InputMacKey key * F (joinSource pub key) := by
  have law := uniform_source_eq (fun source => PMF.pure source)
  rw [PMF.bind_pure] at law
  rw [law, tsum_bind_mul]
  refine tsum_congr fun pub => congrArg _ ?_
  rw [tsum_bind_mul]
  refine tsum_congr fun key => congrArg _ ?_
  exact tsum_pure_mul _ _

end Source

/-! ### The flag mass -/

section Bound

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
  [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- No points. -/
def noPoints : Points FixedIndex EncPRF.PermutationIndex where
  fixedIn _ _ := False
  fixedOut _ _ := False
  encIn _ _ := False
  encOut _ _ := False
  hashIn _ := False

/-- The points of an unflagged outcome (an abort stores none). -/
def outcomePoints : PrivateOutcome → Points FixedIndex EncPRF.PermutationIndex
  | none => noPoints
  | some (points, _) => points

/-- The reveal bit of an unflagged outcome, as a weight. -/
def revealWeight : PrivateOutcome → ℝ≥0∞
  | none => 0
  | some (_, reveal) => if reveal then 1 else 0

/-- **The key-averaged points** of `M'`'s unflagged stage 2, at a published part and an input. -/
def keyedPoints (shadow : Shadow) (scalar : NonZeroScalar) (pub : PubPart) (input : AffineInput) :
    PMF (Points FixedIndex EncPRF.PermutationIndex) :=
  (PMF.uniformOfFintype InputMacKey).bind fun key =>
    (privateStage2U uniformMaskTape shadow scalar (joinSource pub key) input
      (Scheme.scheme.function scalar input)).map outcomePoints

/-- **(B)'s per-pair hypothesis**: the key-averaged private points have per-pair mass `≤ c`. -/
def PerPairBound (shadow : Shadow) (scalar : NonZeroScalar) (c : ℝ≥0∞) : Prop :=
  ∀ (pub : PubPart) (input : AffineInput),
    (∀ i x y, (keyedPoints shadow scalar pub input).toOuterMeasure {p | p.fixedIn i x} +
      (keyedPoints shadow scalar pub input).toOuterMeasure {p | p.fixedOut i y} ≤ c) ∧
    (∀ i x y, (keyedPoints shadow scalar pub input).toOuterMeasure {p | p.encIn i x} +
      (keyedPoints shadow scalar pub input).toOuterMeasure {p | p.encOut i y} ≤ c) ∧
    (∀ k, (keyedPoints shadow scalar pub input).toOuterMeasure {p | p.hashIn k} ≤ c)

/-- **(B)'s reveal hypothesis**: the unflagged reveal bit has mass `≤ ρ`. -/
def RevealBound (shadow : Shadow) (scalar : NonZeroScalar) (ρ : ℝ≥0∞) : Prop :=
  ∀ (source : Stage1Source) (input : AffineInput),
    ∑' o, privateStage2U uniformMaskTape shadow scalar source input
      (Scheme.scheme.function scalar input) o * revealWeight o ≤ ρ

/-- The unflagged private stage 2 never aborts. -/
theorem privateStage2U_ne_none (shadow : Shadow) (scalar : NonZeroScalar) (source : Stage1Source)
    (input : AffineInput) (output : Option Point) :
    none ∉ (privateStage2U uniformMaskTape shadow scalar source input output).support := by
  intro member
  cases output with
  | none =>
    simp only [privateStage2U, PMF.mem_support_bind_iff] at member
    obtain ⟨coin, _, member⟩ := member
    obtain ⟨r, rMember, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rcases r with _ | r
    · obtain ⟨tape, _, inner⟩ := (PMF.mem_support_bind_iff _ _ _).mp rMember
      exact runFillFlag_empty_ne_none _ _ _ _ inner
    · cases same
  | some target =>
    simp only [privateStage2U, PMF.mem_support_bind_iff] at member
    obtain ⟨tape, _, ran, ranMember, rest⟩ := member
    rcases ran with _ | ran
    · exact runRefill_ne_none _ _ _ _ _ _ ranMember
    · simp only [abortCont] at rest
      unfold privateContU at rest
      dsimp only at rest
      obtain ⟨coins, _, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp rest
      obtain ⟨answers, answersMember, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp rest
      rcases answers with _ | answers
      · exact designatedLimbs_ne_none _ _ _ _ _ answersMember
      · obtain ⟨coin, _, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp rest
        obtain ⟨result, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp rest
        cases same

open Classical in
/-- An outcome's flag weight is at most its touch weight plus its reveal weight, off an abort. -/
theorem outcomeWeight_le (planted : LState) (o : PrivateOutcome) (notAbort : o ≠ none) :
    outcomeWeight planted o ≤
      (if Touches planted (outcomePoints o) then 1 else 0) + revealWeight o := by
  rcases o with _ | ⟨points, reveal⟩
  · exact absurd rfl notAbort
  · simp only [outcomeWeight, outcomePoints, revealWeight]
    by_cases hit : Touches planted points
    · simp [hit]
    · by_cases up : reveal = true
      · simp [hit, up]
      · simp [hit, up]

/-- The flag mass of `M'`, as an average of stage-2 flag masses. -/
theorem middleFill_none_eq (shadow : Shadow) (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    middleGameFill uniformMaskTape shadow adversary parameter scalar none =
      ∑' source, PMF.uniformOfFintype Stage1Source source *
        ∑' selected, LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
          LazyOracle.empty selected *
            middleStage2Fill uniformMaskTape shadow scalar source selected.1.1
              (Scheme.scheme.function scalar selected.1.1) selected.2 none := by
  unfold middleGameFill
  rw [PMF.bind_apply]
  refine tsum_congr fun source => congrArg _ ?_
  rw [PMF.bind_apply]
  refine tsum_congr fun selected => congrArg _ ?_
  rw [PMF.bind_apply, tsum_eq_single none]
  · simp [finishM]
  · intro o different
    rcases o with _ | _ | ⟨labels, updated⟩
    · exact absurd rfl different
    · simp [finishM]
    · simp [finishM]

open Classical in
/-- **`M'`'s flag mass from the per-pair and reveal bounds.** -/
theorem middleFill_none_le (shadow : Shadow) (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) (c ρ : ℝ≥0∞) (perPair : PerPairBound shadow scalar c)
    (reveal : RevealBound shadow scalar ρ) :
    middleGameFill uniformMaskTape shadow adversary parameter scalar none ≤
      adversary.firstQueryBudget parameter * c + ρ := by
  rw [middleFill_none_eq]
  -- each stage-2 flag mass is a touch mass plus a reveal mass
  have perStage : ∀ (source : Stage1Source) (selected : (AffineInput × adversary.State) × LState),
      middleStage2Fill uniformMaskTape shadow scalar source selected.1.1
        (Scheme.scheme.function scalar selected.1.1) selected.2 none ≤
      ∑' o, privateStage2U uniformMaskTape shadow scalar source selected.1.1
          (Scheme.scheme.function scalar selected.1.1) o *
        (if Touches selected.2 (outcomePoints o) then 1 else 0) + ρ := by
    intro source selected
    refine le_trans (middleStage2Fill_none_le _ _ _ _ _ _ _) ?_
    refine le_trans (ENNReal.tsum_le_tsum fun o => ?_)
      (le_trans (le_of_eq ENNReal.tsum_add) (add_le_add le_rfl (reveal source selected.1.1)))
    by_cases member : o ∈ (privateStage2U uniformMaskTape shadow scalar source selected.1.1
        (Scheme.scheme.function scalar selected.1.1)).support
    · rw [← mul_add]
      refine mul_le_mul' le_rfl (outcomeWeight_le _ o fun same => ?_)
      subst same
      exact privateStage2U_ne_none _ _ _ _ _ member
    · rw [(PMF.apply_eq_zero_iff _ _).mpr member]
      simp
  -- the touch part, averaged over the key, is the union bound
  have touchPart : ∀ pub : PubPart,
      ∑' selected, LazyOracle.run (adversary.chooseInput parameter pub.1.publicValue ())
          LazyOracle.empty selected *
        (keyedPoints shadow scalar pub selected.1.1).toOuterMeasure
          {p | Touches selected.2 p} ≤ adversary.firstQueryBudget parameter * c := by
    intro pub
    exact run_touch_mass_le (adversary.chooseInput parameter pub.1.publicValue ())
      (fun selected => keyedPoints shadow scalar pub selected.1.1) c
      (fun selected => (perPair pub selected.1.1).1) (fun selected => (perPair pub selected.1.1).2.1)
      (fun selected => (perPair pub selected.1.1).2.2)
  calc ∑' source, PMF.uniformOfFintype Stage1Source source *
        ∑' selected, LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
          LazyOracle.empty selected *
            middleStage2Fill uniformMaskTape shadow scalar source selected.1.1
              (Scheme.scheme.function scalar selected.1.1) selected.2 none
      ≤ ∑' source, PMF.uniformOfFintype Stage1Source source *
        ∑' selected, LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
          LazyOracle.empty selected *
            (∑' o, privateStage2U uniformMaskTape shadow scalar source selected.1.1
              (Scheme.scheme.function scalar selected.1.1) o *
                (if Touches selected.2 (outcomePoints o) then 1 else 0) + ρ) :=
        ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl
          (ENNReal.tsum_le_tsum fun selected => mul_le_mul' le_rfl (perStage source selected))
    _ = (∑' source, PMF.uniformOfFintype Stage1Source source *
          ∑' selected, LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
            LazyOracle.empty selected *
              ∑' o, privateStage2U uniformMaskTape shadow scalar source selected.1.1
                (Scheme.scheme.function scalar selected.1.1) o *
                  (if Touches selected.2 (outcomePoints o) then 1 else 0)) + ρ := by
        have inner : ∀ source : Stage1Source,
            ∑' selected, LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
              LazyOracle.empty selected *
                (∑' o, privateStage2U uniformMaskTape shadow scalar source selected.1.1
                  (Scheme.scheme.function scalar selected.1.1) o *
                    (if Touches selected.2 (outcomePoints o) then 1 else 0) + ρ)
            = (∑' selected, LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
                LazyOracle.empty selected *
                  ∑' o, privateStage2U uniformMaskTape shadow scalar source selected.1.1
                    (Scheme.scheme.function scalar selected.1.1) o *
                      (if Touches selected.2 (outcomePoints o) then 1 else 0)) + ρ := by
          intro source
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        simp_rw [inner, mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ adversary.firstQueryBudget parameter * c + ρ := by
        refine add_le_add ?_ le_rfl
        -- split the source into its published part and its key
        rw [show (∑' source, PMF.uniformOfFintype Stage1Source source *
            ∑' selected, LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
              LazyOracle.empty selected *
                ∑' o, privateStage2U uniformMaskTape shadow scalar source selected.1.1
                  (Scheme.scheme.function scalar selected.1.1) o *
                    (if Touches selected.2 (outcomePoints o) then 1 else 0))
          = ∑' pub, PMF.uniformOfFintype PubPart pub *
              ∑' selected, LazyOracle.run (adversary.chooseInput parameter pub.1.publicValue ())
                LazyOracle.empty selected *
                  (keyedPoints shadow scalar pub selected.1.1).toOuterMeasure
                    {p | Touches selected.2 p} from ?_]
        · calc ∑' pub, PMF.uniformOfFintype PubPart pub *
                ∑' selected, LazyOracle.run (adversary.chooseInput parameter pub.1.publicValue ())
                  LazyOracle.empty selected *
                    (keyedPoints shadow scalar pub selected.1.1).toOuterMeasure
                      {p | Touches selected.2 p}
              ≤ ∑' pub, PMF.uniformOfFintype PubPart pub *
                  (adversary.firstQueryBudget parameter * c) :=
                ENNReal.tsum_le_tsum fun pub => mul_le_mul' le_rfl (touchPart pub)
            _ = adversary.firstQueryBudget parameter * c := by
                rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        · rw [tsum_source_split]
          refine tsum_congr fun pub => congrArg _ ?_
          simp only [publicValue_joinSource]
          simp_rw [← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun selected => ?_
          rw [keyedPoints, PMF.toOuterMeasure_apply]
          rw [show (∑' p, Set.indicator {p | Touches selected.2 p} ((PMF.uniformOfFintype
              InputMacKey).bind fun key => (privateStage2U uniformMaskTape shadow scalar
                (joinSource pub key) selected.1.1 (Scheme.scheme.function scalar selected.1.1)).map
                  outcomePoints) p)
            = ∑' p, ((PMF.uniformOfFintype InputMacKey).bind
              fun key => (privateStage2U uniformMaskTape shadow scalar (joinSource pub key)
                selected.1.1 (Scheme.scheme.function scalar selected.1.1)).map outcomePoints) p *
                  (if Touches selected.2 p then 1 else 0) from
            tsum_congr fun p => by
              simp only [Set.indicator, Set.mem_ofPred_eq]
              split_ifs <;> simp]
          rw [tsum_bind_mul, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun key => ?_
          rw [tsum_map_mul, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun o => ?_
          ring

/-- **(B) at the honest constant, from the two per-shadow bounds**: per-pair mass `4/2^128` and
reveal mass `364/(r−1)` give `M'`'s flag mass `4q₁/2^128 + 364/(r−1)`. -/
theorem middleFill_mass_le (shadow : Shadow) (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) (perPair : PerPairBound shadow scalar (4 / 2 ^ 128))
    (reveal : RevealBound shadow scalar
      (ENNReal.ofReal Kriterion.ArgoMAC.Phase3.Glue.exceptionalError)) :
    (middleGameFill uniformMaskTape shadow adversary parameter scalar none).toReal ≤
      Kriterion.ArgoMAC.Phase3.Glue.stageOneHitError (adversary.firstQueryBudget parameter) +
        Kriterion.ArgoMAC.Phase3.Glue.exceptionalError := by
  have bound := middleFill_none_le shadow adversary parameter scalar _ _ perPair reveal
  have finite : (adversary.firstQueryBudget parameter : ℝ≥0∞) * (4 / 2 ^ 128) +
      ENNReal.ofReal Kriterion.ArgoMAC.Phase3.Glue.exceptionalError ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_,
      ENNReal.ofReal_ne_top⟩
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  refine le_trans (ENNReal.toReal_mono finite bound) (le_of_eq ?_)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.div_ne_top (by norm_num) (by norm_num))) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal Kriterion.ArgoMAC.Phase3.Glue.exceptionalError_nonneg,
    ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast]
  unfold Kriterion.ArgoMAC.Phase3.Glue.stageOneHitError
  norm_num
  ring

end Bound

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
