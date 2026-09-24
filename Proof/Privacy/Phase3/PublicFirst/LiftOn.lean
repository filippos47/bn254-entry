/-
**Phase 3, P1j — the lift, part 5: the per-input core on the curve, from the on-curve law.**

On the curve `M'`'s stage 2 is `HW`'s opening run privately (the refill runner, flagged), the rows'
coins, the designated draws (free coordinates, collector solve, the `452` hash answers), the
designated installation (flagged), the designed shadow (the prefix again, the bit-`true` pads, the
whole evaluator; flagged) and the reveal flag, then the merge. Here:

* **each flagged stage is its unflagged stage on the untouched outcomes** (`runRefillFlag_some_le`,
  `runRefillFlag_abort_le`, `programAllSkipFlag_untouched`, `runLazyQFlag_some_le`; the lazy steps
  of every kind add exactly their own pair, `touches_after_query_any`), and the unflagged opening
  and designated draws never abort (`runRefill_ne_none`, `designatedLimbs_ne_none`); the reveal
  flag only lowers `M'` (`middleWeight_on_le`);
* **on the upper side the shadow's extra questions are discardable** (`extras_le`): running the
  shadow lazily after the garbler's entries and merging, flagged, is below `G1U°`'s own stage 2
  (P1e's `runLazyQ_ge` and `discard_run`, on the lockstep merge `plantAll_rel`);
* **`liftCore_on`**: the core at an on-curve input from `LawOn`: jointly with the published value and
  the labels, the unflagged private final state off the reveal event (`onPrivate`, a revealing
  outcome is `none`) is dominated in law by the garbler's EncPRF and designed entries planted on the
  empty oracle **followed by the same shadow run lazily** (its gadget questions at non-agreeing
  positions are the only fresh ones);
* **`designedLift_of_laws`**, **`planB_publicFirst_of_laws`**: the F4 lift, and the Glue's
  `publicFirst`, from `DesignedLaws` (`LawOff` off the curve, `LawOn` on it, at every input).
-/

import Proof.Privacy.Phase3.PublicFirst.LiftOff

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source idealSamplers openingQueriesM designatedLimbs
  programRequests interceptAnswer noRecord coincidenceError)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Record uniformMaskTape consumeCell consumeCell_spec
  refillAnswer runRefill)
open scoped ENNReal

noncomputable section

/-! ### 1. Every lazy step adds exactly its own pair -/

section Generic

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

theorem addsPair_inverse {size : ℕ} (state : SparsePermutation size) (y : Fin size)
    (answer : Fin size × SparsePermutation size)
    (member : answer ∈ (state.inverse y).distribution.support) :
    AddsPair state answer.2 answer.1 y := by
  intro z w found
  unfold SparsePermutation.inverse at member
  dsimp only at member
  split at member
  · simp only [Draw.distribution, PMF.mem_support_pure_iff] at member
    subst member
    exact Or.inl found
  · rename_i fresh
    obtain ⟨rank, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rw [← same] at found ⊢
    dsimp only at found ⊢
    have freshY : ¬ state.knownOutput y := fresh
    have freshX : ¬ state.knownInput (state.input (state.suffix rank)) := by
      show ¬ (state.input.symm (state.input (state.suffix rank))).val < state.used
      rw [Equiv.symm_apply_apply]
      simp [SparsePermutation.suffix]
    have room : state.used < size := by
      have := (state.output.symm y).isLt
      unfold SparsePermutation.knownOutput at freshY
      omega
    have shape := lookup_extend state (state.input (state.suffix rank)) y freshX freshY room z
    rw [Equiv.symm_apply_apply] at shape
    rw [shape] at found
    split at found
    · rename_i hz
      exact Or.inr ⟨hz, (Option.some.inj found).symm⟩
    · exact Or.inl found

theorem touchForward_swap {size : ℕ} (D Dinv : Fin size → Option (Fin size)) (x y : Fin size)
    (touch : TouchForward D Dinv x y) : TouchForward Dinv D y x := by
  rcases touch with hit | hit
  · exact Or.inr hit
  · exact Or.inl hit

/-- **After any lazy question, a meeting is an old meeting or the question's own touch.** -/
theorem touches_after_query_any (planted : LazyOracle.State FixedIndex EncIndex)
    (request : PublicQuery FixedIndex EncIndex) (state : LazyOracle.State FixedIndex EncIndex)
    (outcome : request.Answer × LazyOracle.State FixedIndex EncIndex)
    (member : outcome ∈ (LazyOracle.query request state).support)
    (hit : Touches planted (pointsOf outcome.2)) :
    Touches planted (pointsOf state) ∨ FullTouch planted request outcome.1 := by
  cases request with
  | fixedInverse index output =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rcases touches_update_fixed planted state index answer.2 answer.1 output.toFin
        (addsPair_inverse _ _ answer answerMember) hit with old | new
    · exact Or.inl old
    · right
      have swapped := touchForward_swap _ _ _ _ new
      simpa [FullTouch, BitVec.toFin_ofFin] using swapped
  | encInverse index output =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rcases touches_update_enc planted state index answer.2 answer.1 output.toFin
        (addsPair_inverse _ _ answer answerMember) hit with old | new
    · exact Or.inl old
    · right
      have swapped := touchForward_swap _ _ _ _ new
      simpa [FullTouch, BitVec.toFin_ofFin] using swapped
  | fixedForward index input =>
    exact touches_after_query planted (.fixedForward index input) trivial state outcome member hit
  | encForward index input =>
    exact touches_after_query planted (.encForward index input) trivial state outcome member hit
  | hash input =>
    exact touches_after_query planted (.hash input) trivial state outcome member hit

end Generic

/-! ### 2. Each flagged stage of `M'` is its unflagged stage on the untouched outcomes -/

section Stages

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The flagged refill run, completed.** -/
theorem runRefillFlag_some_le (planted : LState) (bits : BitInput)
    (draw : Cell → PMF (Block × Block)) {α : Type} (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell),
      ¬ Touches planted (pointsOf oracle) → ∀ ran,
        runRefillFlag planted bits draw computation oracle record touched (some (some ran))
          ≤ runRefill bits draw computation oracle record touched (some ran)
            * untouched planted ran.2.1 := by
  induction computation with
  | pure value =>
    intro oracle record touched fresh ran
    simp only [runRefillFlag, runRefill]
    by_cases same : ran = (value, oracle, record)
    · subst same
      rw [untouched_eq_one fresh, mul_one]
      simp [PMF.pure_apply]
    · rw [PMF.pure_apply, if_neg (fun h => same (Option.some.inj (Option.some.inj h)))]
      exact zero_le
  | query request next ih =>
    intro oracle record touched fresh ran
    simp only [runRefillFlag, runRefill]
    cases intercept : interceptAnswer bits request with
    | some answer =>
      dsimp only
      exact ih _ _ _ _ fresh ran
    | none =>
      dsimp only
      cases consumed : consumeCell touched oracle request with
      | some cell =>
        dsimp only
        have forward : NoInverse request := by
          obtain ⟨input, rfl, _⟩ := consumeCell_spec consumed
          trivial
        rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_right]
        refine ENNReal.tsum_le_tsum fun limb => ?_
        rw [mul_assoc]
        refine mul_le_mul' le_rfl ?_
        by_cases hit : FullTouch planted request (refillAnswer request limb)
        · rw [if_pos hit, PMF.pure_apply, if_neg (by simp)]
          exact zero_le
        · rw [if_neg hit]
          cases programmed : LazyOracle.program request (refillAnswer request limb) oracle with
          | none => simp [PMF.pure_apply]
          | some updated =>
            dsimp only
            have fresh' : ¬ Touches planted (pointsOf updated) := fun hitU =>
              (touches_after_program planted request forward _ oracle updated programmed hitU).elim
                fresh hit
            exact ih _ updated _ _ fresh' ran
      | none =>
        dsimp only
        rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_right]
        refine ENNReal.tsum_le_tsum fun answer => ?_
        rw [mul_assoc]
        by_cases member : answer ∈ (LazyOracle.query request oracle).support
        · refine mul_le_mul' le_rfl ?_
          by_cases hit : FullTouch planted request answer.1
          · rw [if_pos hit, PMF.pure_apply, if_neg (by simp)]
            exact zero_le
          · rw [if_neg hit]
            have fresh' : ¬ Touches planted (pointsOf answer.2) := fun hitU =>
              (touches_after_query_any planted request oracle answer member hitU).elim fresh hit
            exact ih _ answer.2 _ _ fresh' ran
        · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

/-- **The flagged refill run's own abort is the unflagged one's.** -/
theorem runRefillFlag_abort_le (planted : LState) (bits : BitInput)
    (draw : Cell → PMF (Block × Block)) {α : Type} (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell),
      runRefillFlag planted bits draw computation oracle record touched (some none)
        ≤ runRefill bits draw computation oracle record touched none := by
  induction computation with
  | pure value =>
    intro oracle record touched
    simp only [runRefillFlag, runRefill, PMF.pure_apply]
    rw [if_neg (by simp)]
    exact zero_le
  | query request next ih =>
    intro oracle record touched
    simp only [runRefillFlag, runRefill]
    cases intercept : interceptAnswer bits request with
    | some answer =>
      dsimp only
      exact ih _ _ _ _
    | none =>
      dsimp only
      cases consumed : consumeCell touched oracle request with
      | some cell =>
        dsimp only
        rw [PMF.bind_apply, PMF.bind_apply]
        refine ENNReal.tsum_le_tsum fun limb => mul_le_mul' le_rfl ?_
        by_cases hit : FullTouch planted request (refillAnswer request limb)
        · rw [if_pos hit, PMF.pure_apply, if_neg (by simp)]
          exact zero_le
        · rw [if_neg hit]
          cases LazyOracle.program request (refillAnswer request limb) oracle with
          | none => simp
          | some updated => exact ih _ _ _ _
      | none =>
        dsimp only
        rw [PMF.bind_apply, PMF.bind_apply]
        refine ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl ?_
        by_cases hit : FullTouch planted request answer.1
        · rw [if_pos hit, PMF.pure_apply, if_neg (by simp)]
          exact zero_le
        · rw [if_neg hit]
          exact ih _ _ _ _

/-- **The flagged designated installation, off a flag, keeps the private state untouched.** -/
theorem programAllSkipFlag_untouched (planted : LState) :
    ∀ (requests : List (Option BaseField × (Block × Block))) (state installed : LState),
      programAllSkipFlag planted requests state = some installed →
        ¬ Touches planted (pointsOf state) → ¬ Touches planted (pointsOf installed) := by
  intro requests
  induction requests with
  | nil =>
    intro state installed done fresh
    simp only [programAllSkipFlag, Option.some.injEq] at done
    subst done
    exact fresh
  | cons request rest ih =>
    intro state installed done fresh
    obtain ⟨input, answer⟩ := request
    cases input with
    | none => exact ih state installed done fresh
    | some input =>
      simp only [programAllSkipFlag] at done
      split_ifs at done with touching
      refine ih _ installed done ?_
      cases programmed : LazyOracle.program (.hash input) answer state with
      | none =>
        rw [Option.getD_none]
        exact fresh
      | some updated =>
        rw [Option.getD_some]
        exact fun hitU => (touches_after_program planted (.hash input) trivial _ state
          updated programmed hitU).elim fresh touching

/-- **The flagged extra queries, completed.** -/
theorem runLazyQFlag_some_le (planted : LState) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (state : LState), ¬ Touches planted (pointsOf state) → ∀ outcome,
      runLazyQFlag planted computation state (some outcome)
        ≤ runLazyQ computation state outcome * untouched planted outcome.2 := by
  induction computation with
  | pure value =>
    intro state fresh outcome
    simp only [runLazyQFlag, runLazyQ]
    by_cases same : outcome = (value, state)
    · subst same
      rw [untouched_eq_one fresh, mul_one, PMF.pure_apply, PMF.pure_apply, if_pos rfl, if_pos rfl]
    · rw [PMF.pure_apply, if_neg (fun h => same (Option.some.inj h))]
      exact zero_le
  | query request next ih =>
    intro state fresh outcome
    simp only [runLazyQFlag, runLazyQ]
    rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun answer => ?_
    rw [mul_assoc]
    by_cases member : answer ∈ (LazyOracle.query request state).support
    · refine mul_le_mul' le_rfl ?_
      by_cases hit : FullTouch planted request answer.1
      · rw [if_pos hit, PMF.pure_apply, if_neg (by simp)]
        exact zero_le
      · rw [if_neg hit]
        have fresh' : ¬ Touches planted (pointsOf answer.2) := fun hitU =>
          (touches_after_query_any planted request state answer member hitU).elim fresh hit
        exact ih _ answer.2 fresh' outcome
    · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

/-- **An unflagged run on the untouched outcomes is below the flagged run** (the converse). -/
theorem runLazyQFlag_ge_untouched (planted : LState) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (state : LState) (outcome : α × LState),
      runLazyQ computation state outcome * untouched planted outcome.2
        ≤ runLazyQFlag planted computation state (some outcome) := by
  induction computation with
  | pure value =>
    intro state outcome
    simp only [runLazyQFlag, runLazyQ]
    refine le_trans (mul_le_of_le_one_right' (untouched_le_one planted outcome.2)) (le_of_eq ?_)
    by_cases same : outcome = (value, state)
    · subst same
      simp [PMF.pure_apply]
    · rw [PMF.pure_apply, PMF.pure_apply, if_neg same, if_neg (fun h => same (Option.some.inj h))]
  | query request next ih =>
    intro state outcome
    simp only [runLazyQFlag, runLazyQ]
    rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun answer => ?_
    rw [mul_assoc]
    by_cases member : answer ∈ (LazyOracle.query request state).support
    · refine mul_le_mul' le_rfl ?_
      by_cases hit : FullTouch planted request answer.1
      · rw [if_pos hit]
        have touched := query_touch planted request state answer member hit
        by_cases reached : outcome ∈ (runLazyQ (next answer.1) answer.2).support
        · rw [untouched_of_grows (runLazyQ_grows (next answer.1) answer.2 outcome reached) touched,
            mul_zero]
          exact zero_le
        · rw [(PMF.apply_eq_zero_iff _ _).mpr reached, zero_mul]
          exact zero_le
      · rw [if_neg hit]
        exact ih answer.1 answer.2 outcome
    · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

end Stages

/-! ### 3. The upper side: the shadow's extra questions are discardable -/

section Extras

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
  [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]

/-- **Extra lazy questions after the private state, merged and weighed on the untouched
outcomes, are below the related shared state.** -/
theorem extras_le (planted sF s₀ : LState) (rel : FullRel planted sF s₀) {α : Type}
    (extra : FreeQuery Programs.Spec α) {budget : ℕ}
    (decide : OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (b : Bool) :
    ∑' s, runLazyQ extra s₀ s * (untouched planted s.2 *
        ((LazyOracle.run decide (mergeChoice planted s.2)).map Prod.fst) b)
      ≤ ((LazyOracle.run decide sF).map Prod.fst) b := by
  have converse : ∀ s, runLazyQ extra s₀ s * (untouched planted s.2 *
      ((LazyOracle.run decide (mergeChoice planted s.2)).map Prod.fst) b) ≤
      runLazyQFlag planted extra s₀ (some s) *
        flagged (fun o => ((LazyOracle.run decide (mergeChoice planted o.2)).map Prod.fst) b)
          (some s) := by
    intro s
    rw [← mul_assoc]
    exact mul_le_mul' (runLazyQFlag_ge_untouched planted extra s₀ s) le_rfl
  refine le_trans (ENNReal.tsum_le_tsum converse) ?_
  have split : ∑' o, runLazyQFlag planted extra s₀ o *
      flagged (fun o => ((LazyOracle.run decide (mergeChoice planted o.2)).map Prod.fst) b) o =
      ∑' a, runLazyQFlag planted extra s₀ (some a) *
        flagged (fun o => ((LazyOracle.run decide (mergeChoice planted o.2)).map Prod.fst) b)
          (some a) := by
    rw [tsum_option _ ENNReal.summable]
    simp [flagged]
  rw [← split]
  refine le_trans (runLazyQ_ge planted (fun o => ((LazyOracle.run decide o.2).map Prod.fst) b)
    (fun o => ((LazyOracle.run decide (mergeChoice planted o.2)).map Prod.fst) b)
    (fun a sF' sL' related => le_of_eq (run_map_fst_congr _ (mergeChoice_sameLookups related) ▸ rfl))
    extra sF s₀ rel) (le_of_eq ?_)
  have law := congrArg (fun distribution : PMF Bool => distribution b) (discard_run decide extra sF)
  simp only [PMF.bind_apply] at law
  exact law

end Extras

/-! ### 4. The per-input core on the curve, from the on-curve law -/

section Core

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
  [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

open Classical in
/-- The unflagged private continuation on the curve: the rows' coins, the designated draws (free
coordinates, collector solve, the `452` hash answers), the designated installation, the shadow,
and **the reveal flag kept** (a revealing outcome is `none`: on the exact exceptional input the
garbler's gadget entries do correlate with the published entry, so no law can hold there). -/
def onCont (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) × LState ×
      Record) : PMF (Option LState) :=
  letI : Fintype Coins := Fintype.ofFinite Coins
  (PMF.uniformOfFintype Coins).bind fun coins =>
    (designatedLimbs idealSamplers source.publicValue
        (Lamport.restore input (sourceLabels source input)).input ran.1.1 ran.1.2
        (fun digit => trueRows scalar coins input digit)).bind fun limbs =>
      match limbs with
      | none => PMF.pure none
      | some limbs =>
        (designedShadow scalar).law.bind fun coin =>
          (runLazyQ ((designedShadow scalar).onCurve source input coins coin (ran.1, ran.2.2))
            (programAllSkip (programRequests (Lamport.restore input (sourceLabels source input)).input
              ran.2.2 limbs) ran.2.1)).map fun x =>
            if (designedShadow scalar).revealOn source input coins coin x.2 then none else some x.2

/-- **The designed shadow's private final state on the curve, unflagged.** -/
def onPrivate (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput) :
    PMF (Option LState) :=
  uniformMaskTape.bind fun tape =>
    (runRefill (Lamport.restore input (sourceLabels source input)).input
        (fun cell => PMF.pure (tape cell))
        (openingQueriesM source.publicValue (Lamport.restore input (sourceLabels source input)).input
          (Lamport.restore input (sourceLabels source input)).inputMac)
        LazyOracle.empty noRecord ∅).bind fun ran =>
      match ran with
      | none => PMF.pure none
      | some ran => onCont scalar source input ran

/-- **The on-curve law** — the content of the lift on the curve: jointly with the published value
and the labels, the private final state **off the reveal event** is dominated, for every
lookup-invariant weight, by the lookups of the garbler's EncPRF and designed entries planted on the
empty oracle followed by the same shadow run lazily. (Off the reveal event the two laws should be
equal; on it — `u` the exact exceptional input of a nonzero digit — the garbler's gadget answers
determine the published entry's slot, which no private run reproduces.) -/
def LawOn (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) : Prop :=
  ∀ Ψ : Public → LamportSignature → LState → ℝ≥0∞,
    (∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second) →
    ∑' source, PMF.uniformOfFintype Stage1Source source *
        ∑' r, onPrivate scalar source input r *
          (match r with
            | none => 0
            | some state => Ψ source.publicValue (sourceLabels source input) state)
      ≤ ∑' tape, swappedChallengeTape tape *
          ∑' s, runLazyQ (shadowOnM (Scheme.scheme.garble parameter scalar tape).1
              (Lamport.restore input
                (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)).input
              (Lamport.restore input
                (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)).inputMac)
            (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) s *
            Ψ (Scheme.scheme.garble parameter scalar tape).1
              (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input) s.2

/-- The flag-down weight of an unflagged on-curve outcome. -/
def onWeight (planted : LState) {budget : ℕ}
    (decide : OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (b : Bool) : Option LState → ℝ≥0∞
  | none => 0
  | some state => untouched planted state *
      ((LazyOracle.run decide (mergeChoice planted state)).map Prod.fst) b

/-- The upper side's weight equals its planted form when the private entries are untouched. -/
theorem upperWeight_eq_of_fresh (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (planted : LState) {budget : ℕ}
    (decide : Public → LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (b : Bool)
    (fresh : ¬ Touches planted (pointsOf (plantAll (upperEntries parameter scalar tape input)
      LazyOracle.empty))) :
    upperWeight designedInstall parameter scalar tape input planted decide b =
      ((LazyOracle.run (decide (Scheme.scheme.garble parameter scalar tape).1
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input))
        (plantAll (upperEntries parameter scalar tape input) planted)).map Prod.fst) b := by
  have split : ∀ state, plantAll (upperEntries parameter scalar tape input) state =
      installAll (designedInstall scalar tape (Scheme.scheme.garble parameter scalar tape).1 input
        (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input))
        (plantAll (encEntries scalar tape) state) := by
    intro state
    unfold upperEntries plantAll
    rw [List.foldl_append]
    rfl
  have encFresh : untouched (plantAll (encEntries scalar tape) LazyOracle.empty) planted = 1 := by
    refine untouched_eq_one fun encHit => fresh ?_
    have grow : Grows (plantAll (encEntries scalar tape) LazyOracle.empty)
        (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) := by
      rw [split]
      exact plantAll_grows _ (fun e member => upperEntries_noInverse parameter scalar tape input e
        (List.mem_append_right _ member)) _
    exact touches_grows grow (touches_symm _ _ encHit)
  unfold upperWeight
  rw [encFresh, one_mul, split]

/-- **The upper side on the curve**: the shadow run lazily after the planted entries, merged and
weighed on the untouched outcomes, is below `G1U°`'s stage 2. -/
theorem upper_ge_shadowed (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (planted : LState) {budget : ℕ}
    (decide : Public → LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (b : Bool) {α : Type} (extra : FreeQuery Programs.Spec α) :
    ∑' s, runLazyQ extra (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) s *
        (untouched planted s.2 *
          ((LazyOracle.run (decide (Scheme.scheme.garble parameter scalar tape).1
              (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input))
            (mergeChoice planted s.2)).map Prod.fst) b)
      ≤ upperWeight designedInstall parameter scalar tape input planted decide b := by
  set s₀ := plantAll (upperEntries parameter scalar tape input) LazyOracle.empty with s₀Eq
  by_cases hit : Touches planted (pointsOf s₀)
  · refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun s => ?_)) zero_le
    by_cases reached : s ∈ (runLazyQ extra s₀).support
    · rw [untouched_of_grows (runLazyQ_grows extra s₀ s reached) hit, zero_mul, mul_zero]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr reached, zero_mul]
  · rw [upperWeight_eq_of_fresh parameter scalar tape input planted decide b hit]
    exact extras_le planted _ s₀ (plantAll_rel planted _
      (upperEntries_noInverse parameter scalar tape input) planted LazyOracle.empty
      (fullRel_base planted) hit) extra _ b

/-- The shadow step with the reveal flag on both sides (generic, so that no tactic ever sees the
concrete reveal predicate). -/
theorem cont_step {condition : Prop} (decidable : Decidable condition) (labels : LamportSignature)
    (state : LState) {budget : ℕ}
    (decide : LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (b : Bool) (planted : LState) (flaggedMass mass : ℝ≥0∞)
    (step : flaggedMass ≤ mass * untouched planted state) :
    flaggedMass * ∑' o, (@ite _ condition decidable (PMF.pure none)
        (PMF.pure (some (some (labels, mergeChoice planted state))))) o * contM decide b o
      ≤ mass * onWeight planted (decide labels) b
          (@ite _ condition decidable none (some state)) := by
  by_cases revealed : condition
  · rw [if_pos revealed, if_pos revealed, tsum_pure_mul]
    show flaggedMass * 0 ≤ mass * 0
    rw [mul_zero, mul_zero]
  · rw [if_neg revealed, if_neg revealed, tsum_pure_mul]
    show flaggedMass * contHW decide b (some (labels, mergeChoice planted state)) ≤
      mass * (untouched planted state *
        ((LazyOracle.run (decide labels) (mergeChoice planted state)).map Prod.fst) b)
    rw [← mul_assoc]
    exact mul_le_mul' step le_rfl

theorem tsum_option_option_eq {A : Type} (f : Option (Option A) → ℝ≥0∞) (zero : f none = 0)
    (abort : f (some none) = 0) : ∑' r, f r = ∑' a, f (some (some a)) := by
  rw [tsum_option _ ENNReal.summable, zero, zero_add,
    tsum_option (fun x => f (some x)) ENNReal.summable, abort, zero_add]

theorem tsum_some_le {A : Type} (g : Option A → ℝ≥0∞) : ∑' a, g (some a) ≤ ∑' r, g r := by
  rw [tsum_option _ ENNReal.summable]
  exact le_add_self

/-- **After the refill run, `M'`'s private continuation is below the unflagged one** (untouched
start; the designated draws never abort; the reveal flag only lowers). -/
theorem privateCont_le_onCont (scalar : NonZeroScalar) (source : Stage1Source)
    (input : AffineInput) (planted : LState) {budget : ℕ}
    (decide : Public → LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (b : Bool)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) × LState ×
      Record) (fresh : ¬ Touches planted (pointsOf ran.2.1)) :
    ∑' o, privateCont (designedShadow scalar) scalar planted source input ran o *
        contM (decide source.publicValue) b o
      ≤ ∑' r, onCont scalar source input ran r *
        onWeight planted (decide source.publicValue (sourceLabels source input)) b r := by
  unfold privateCont onCont
  dsimp only
  rw [tsum_bind_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun coins => mul_le_mul' le_rfl ?_
  rw [tsum_bind_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun limbs => ?_
  rcases limbs with _ | limbs
  · rw [(PMF.apply_eq_zero_iff _ _).mpr (designatedLimbs_ne_none _ _ _ _ _), zero_mul, zero_mul]
  · refine mul_le_mul' le_rfl ?_
    dsimp only
    cases flag : programAllSkipFlag planted (programRequests
        (Lamport.restore input (sourceLabels source input)).input ran.2.2 limbs) ran.2.1 with
    | none =>
      simp only [tsum_pure_mul, contM]
      exact zero_le
    | some installed =>
      dsimp only
      have same := programAllSkipFlag_some planted _ _ installed flag
      have freshInstalled := programAllSkipFlag_untouched planted _ _ installed flag fresh
      rw [← same, tsum_bind_mul, tsum_bind_mul]
      refine ENNReal.tsum_le_tsum fun coin => mul_le_mul' le_rfl ?_
      rw [tsum_bind_mul, tsum_map_mul, tsum_option _ ENNReal.summable]
      simp only [tsum_pure_mul, contM, mul_zero, zero_add]
      refine ENNReal.tsum_le_tsum fun x => ?_
      have step := runLazyQFlag_some_le planted
        ((designedShadow scalar).onCurve source input coins coin (ran.1, ran.2.2)) installed
        freshInstalled x
      exact cont_step _ _ _ _ _ planted _ _ step

/-- **`M'` on the curve, flag-down, is at most the unflagged private run's untouched
outcomes.** -/
theorem middleWeight_on_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (target : Point) (on : Scheme.scheme.function scalar input = some target) (planted : LState)
    {budget : ℕ}
    (decide : Public → LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (b : Bool) :
    middleWeight uniformMaskTape (designedShadow scalar) scalar source input planted decide b ≤
      ∑' r, onPrivate scalar source input r *
        onWeight planted (decide source.publicValue (sourceLabels source input)) b r := by
  unfold middleWeight onPrivate
  rw [on]
  simp only [middleStage2Fill, refillStageM]
  rw [tsum_bind_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
  rw [tsum_bind_mul, tsum_bind_mul]
  have abortZero : runRefill (Lamport.restore input (sourceLabels source input)).input
      (fun cell => PMF.pure (tape cell))
      (openingQueriesM source.publicValue (Lamport.restore input (sourceLabels source input)).input
        (Lamport.restore input (sourceLabels source input)).inputMac)
      LazyOracle.empty noRecord ∅ none = 0 :=
    (PMF.apply_eq_zero_iff _ _).mpr (runRefill_ne_none _ _ _ _ _ _)
  have flagAbortZero := le_antisymm ((runRefillFlag_abort_le planted
    (Lamport.restore input (sourceLabels source input)).input (fun cell => PMF.pure (tape cell))
    (openingQueriesM source.publicValue (Lamport.restore input (sourceLabels source input)).input
      (Lamport.restore input (sourceLabels source input)).inputMac)
    LazyOracle.empty noRecord ∅).trans (le_of_eq abortZero)) zero_le
  refine le_trans (le_of_eq (tsum_option_option_eq _ ?_ ?_))
    (le_trans (ENNReal.tsum_le_tsum fun ran => ?_) (tsum_some_le _))
  · simp only [flagCont, tsum_pure_mul, contM, mul_zero]
  · rw [flagAbortZero, zero_mul]
  dsimp only [flagCont]
  have step := runRefillFlag_some_le planted (Lamport.restore input (sourceLabels source input)).input
    (fun cell => PMF.pure (tape cell))
    (openingQueriesM source.publicValue (Lamport.restore input (sourceLabels source input)).input
      (Lamport.restore input (sourceLabels source input)).inputMac)
    LazyOracle.empty noRecord ∅ (not_touches_empty planted) ran
  by_cases hit : Touches planted (pointsOf ran.2.1)
  · have zero : runRefillFlag planted (Lamport.restore input (sourceLabels source input)).input
        (fun cell => PMF.pure (tape cell))
        (openingQueriesM source.publicValue (Lamport.restore input (sourceLabels source input)).input
          (Lamport.restore input (sourceLabels source input)).inputMac)
        LazyOracle.empty noRecord ∅ (some (some ran)) = 0 := by
      refine le_antisymm (step.trans ?_) zero_le
      unfold untouched
      rw [if_pos hit, mul_zero]
    rw [zero, zero_mul]
    exact zero_le
  · rw [untouched_eq_one hit, mul_one] at step
    exact mul_le_mul' step (privateCont_le_onCont scalar source input planted decide b ran hit)

/-- **The per-input core on the curve, from the on-curve law.** -/
theorem liftCore_on (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (target : Point)
    (on : Scheme.scheme.function scalar input = some target) (law : LawOn parameter scalar input)
    (planted : LState) (budget : ℕ)
    (decide : Public → LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (weight : Public → ℝ≥0∞) (b : Bool) :
    ∑' source, PMF.uniformOfFintype Stage1Source source *
        (weight source.publicValue *
          middleWeight uniformMaskTape (designedShadow scalar) scalar source input planted decide b)
      ≤ ∑' tape, swappedChallengeTape tape *
        (weight (Scheme.scheme.garble parameter scalar tape).1 *
          upperWeight designedInstall parameter scalar tape input planted decide b) := by
  let Ψ : Public → LamportSignature → LState → ℝ≥0∞ := fun table labels state =>
    weight table * (untouched planted state *
      ((LazyOracle.run (decide table labels) (mergeChoice planted state)).map Prod.fst) b)
  have invariant : ∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second := by
    intro table labels first second same
    simp only [Ψ, untouched_congr planted same, mergeChoice_congr planted same]
  calc ∑' source, PMF.uniformOfFintype Stage1Source source *
        (weight source.publicValue *
          middleWeight uniformMaskTape (designedShadow scalar) scalar source input planted decide b)
      ≤ ∑' source, PMF.uniformOfFintype Stage1Source source *
          ∑' r, onPrivate scalar source input r *
            (match r with
              | none => 0
              | some state => Ψ source.publicValue (sourceLabels source input) state) := by
        refine ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl ?_
        refine le_trans (mul_le_mul' le_rfl
          (middleWeight_on_le scalar source input target on planted decide b)) (le_of_eq ?_)
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun r => ?_
        rcases r with _ | state
        · simp [onWeight]
        · simp only [onWeight, Ψ]
          ring
    _ ≤ _ := law Ψ invariant
    _ ≤ _ := by
        refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
        simp only [Ψ]
        simp_rw [← mul_assoc, mul_comm _ (weight _), mul_assoc]
        rw [ENNReal.tsum_mul_left]
        exact mul_le_mul' le_rfl (upper_ge_shadowed parameter scalar tape input planted decide b _)

/-- **The per-input core from the two laws.** -/
theorem liftCore_of_laws (parameter : ℕ) (scalar : NonZeroScalar)
    (lawOff : ∀ input, Scheme.scheme.function scalar input = none → LawOff parameter scalar input)
    (lawOn : ∀ input target, Scheme.scheme.function scalar input = some target →
      LawOn parameter scalar input) :
    LiftCore designedInstall uniformMaskTape (designedShadow scalar) parameter scalar := by
  intro input planted budget decide weight b
  cases output : Scheme.scheme.function scalar input with
  | none =>
    exact liftCore_off parameter scalar input output (lawOff input output) planted budget decide
      weight b
  | some target =>
    exact liftCore_on parameter scalar input target output (lawOn input target output) planted
      budget decide weight b

end Core

/-! ### 5. The lift from the two laws, and the Glue's field -/

/-- **The content of the lift**: the off-curve and on-curve laws, at every input. -/
def DesignedLaws : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (parameter : ℕ)
    (scalar : NonZeroScalar),
    (letI := field
     letI := group
     letI : Fintype FixedIndex := Fintype.ofFinite FixedIndex
     letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
     letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
     letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
     (∀ input, Scheme.scheme.function scalar input = none → LawOff parameter scalar input) ∧
       (∀ input target, Scheme.scheme.function scalar input = some target →
         LawOn parameter scalar input))

/-- **The F4 lift for the designed shadow, from the two laws.** -/
theorem designedLift_of_laws (laws : DesignedLaws) : DesignedLift := by
  intro field group adversary parameter scalar _
  obtain ⟨lawOff, lawOn⟩ := laws field group parameter scalar
  let _ := field
  let _ := group
  let _ : Fintype FixedIndex := Fintype.ofFinite FixedIndex
  let _ : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
  let _ : DecidableEq FixedIndex := Classical.decEq FixedIndex
  let _ : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
  exact flagMono_of_core designedInstall uniformMaskTape (designedShadow scalar) adversary parameter
    scalar (liftCore_of_laws parameter scalar lawOff lawOn)

/-- **The Glue's `publicFirst`, from the two laws, P1k's bounds and the coincidence bound.** -/
theorem planB_publicFirst_of_laws (laws : DesignedLaws) (bounds : DesignedBounds)
    (coincidence : CoincidenceBound coincidenceError) :
    Kriterion.ArgoMAC.Phase3.Glue.GameCoreUntilBad
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.hiddenDeleted
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.publicFirst fun first _ =>
        Kriterion.ArgoMAC.Phase3.Glue.stageOneHitError first +
          Kriterion.ArgoMAC.Phase3.Glue.exceptionalError +
            Kriterion.ArgoMAC.Phase3.Glue.maskSwapError + coincidenceError :=
  planB_publicFirst_of_lift (designedLift_of_laws laws) bounds coincidence

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
