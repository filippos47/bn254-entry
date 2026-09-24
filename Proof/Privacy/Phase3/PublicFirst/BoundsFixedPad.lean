/-
**Phase 3, P1m — (B1) the fixed-key part on the curve: inputs that pass through an EncPRF pad.**

System B's level-1 fold inputs are whitened labels `pad₀ ⊕ L` and the gadget's inputs transformed
labels `pad_u ⊕ L`; each pad is `π_j(u ⊕ k₁) ⊕ k₂` for the prefix's keys `k`.

* `programAllSkip_potential`, `post_le`, **`onCurve_split_le`** — on the curve, an event bounded at
  the final state by a potential chosen after a first part of the opening (its value) has mass at
  most a bound on that potential after the first part: the potential must not be raised by a
  forward question and must be kept by every hash program (the refill run's consumed questions and
  the designated installation are hash programs).
* `pad_final`, `enc_final_small` — both pads of every position are stored at the final state at the
  opening's keys, and every EncPRF index holds at most two pairs;
* **`pad_le`** — an event forcing the final answer of `π_j` at `u ⊕ k₁` to a target read from `k`
  has mass `≤ 1/(2^128 − 1)` (the potential `padF`, chosen after the prefix, where the EncPRF part
  is still empty).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsHash

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM whitePadsM noRecord
  programRequests DesignatedLimbs)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request AllQ runRefill runRefillT
  runRefill_eq_runRefillT runRefillT_bind continueT dropTouched uniformMaskTape queriesAlong
  queriesAlong_bind)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Potentials after a first part of the opening -/

section Split

/-- **A potential kept by every hash program is kept by the designated installation.** -/
theorem programAllSkip_potential (Φ : LState → ℝ≥0∞)
    (hashSame : ∀ (state updated : LState) (input : BaseField) (value : Block × Block),
      LazyOracle.program (.hash input) value state = some updated → Φ updated = Φ state) :
    ∀ (requests : List (Option BaseField × (Block × Block))) (state : LState),
      Φ (programAllSkip requests state) = Φ state := by
  intro requests
  induction requests with
  | nil => exact fun _ => rfl
  | cons request rest ih =>
    intro state
    obtain ⟨input, answer⟩ := request
    cases input with
    | none => exact ih state
    | some input =>
      show Φ (programAllSkip rest ((LazyOracle.program (.hash input) answer state).getD state)) = _
      rw [ih]
      cases success : LazyOracle.program (.hash input) answer state with
      | none => rfl
      | some updated => exact hashSame state updated input answer success

variable [FieldCertificate] [GroupCertificate]

/-- **After the opening**: the continuation's event mass, from a per-installation bound. -/
theorem post_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (event : Points FixedIndex EncPRF.PermutationIndex → Prop)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record) (bound : ℝ≥0∞)
    (perRun : ∀ answers : DesignatedLimbs,
        ∑' result, runLazyQ (shadowOnM source.publicValue (restoredBits source input)
              (restoredMac source input))
            (programAllSkip (programRequests (restoredBits source input) ran.2.2 answers) ran.2.1)
            result *
          ind (event ((pointsOf result.2).union
            (requestPoints (programRequests (restoredBits source input) ran.2.2 answers)))) ≤
        bound) :
    ∑' o, privateContU (planBShadow scalar off) scalar source input ran o *
      ind (event (outcomePoints o)) ≤ bound := by
  unfold privateContU
  dsimp only
  rw [tsum_bind_mul]
  refine tsum_le_of_support _ _ _ fun coins _ => ?_
  rw [tsum_bind_mul]
  refine tsum_le_of_support _ _ _ fun answers answersMember => ?_
  rcases answers with _ | answers
  · exact absurd answersMember (designatedLimbs_ne_none _ _ _ _ _)
  · dsimp only
    rw [tsum_bind_mul]
    refine tsum_le_of_support _ _ _ fun coin _ => ?_
    obtain ⟨delta, offCoin⟩ := coin
    rw [tsum_map_mul]
    simp only [planBShadow_onCurve, outcomePoints]
    rw [show (Lamport.restore input (sourceLabels source input)).input = restoredBits source input
      from rfl]
    exact perRun answers

/-- **On the curve, with the potential chosen after a first part of the opening.** -/
theorem onCurve_split_le {β : Type} (scalar : NonZeroScalar) (off : OffShadow)
    (source : Stage1Source) (input : AffineInput) (target : Point)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (first : Programs.M β)
    (rest : β → Programs.M ((Fin pointElementCountX → BaseField) ×
      (Fin pointElementCountY → BaseField)))
    (split : openingQueriesM source.publicValue (restoredBits source input)
      (restoredMac source input) = first >>= rest)
    (restForward : ∀ value, AllQ ForwardOnly (rest value)) (potential : β → LState → ℝ≥0∞)
    (hashSame : ∀ (value : β) (state updated : LState) (input' : BaseField)
      (answer : Block × Block),
      LazyOracle.program (.hash input') answer state = some updated →
        potential value updated = potential value state)
    (step : ∀ (value : β) (request : Request) (state : LState), ForwardOnly request →
      ∑' answer, LazyOracle.query request state answer * potential value answer.2 ≤
        potential value state)
    (c : ℝ≥0∞)
    (initial : ∀ (tape : Tape) (mid : β × LState × Record × Set Cell),
      some mid ∈ (runRefillT (restoredBits source input) (fun cell => PMF.pure (tape cell)) first
        LazyOracle.empty noRecord ∅).support → potential mid.1 mid.2.1 ≤ c)
    (final : ∀ (tape : Tape) (mid : β × LState × Record × Set Cell),
      some mid ∈ (runRefillT (restoredBits source input) (fun cell => PMF.pure (tape cell)) first
        LazyOracle.empty noRecord ∅).support →
      ∀ ranT : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
          LState × Record × Set Cell,
        some ranT ∈ (runRefillT (restoredBits source input) (fun cell => PMF.pure (tape cell))
          (rest mid.1) mid.2.1 mid.2.2.1 mid.2.2.2).support →
        some (dropTouched ranT) ∈ (openingRun source input tape).support →
      ∀ (answers : DesignatedLimbs) (result : Unit × LState),
        result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
            (dropTouched ranT).2.2 answers) (dropTouched ranT).2.1)).support →
        ind (event ((pointsOf result.2).union (requestPoints (programRequests
          (restoredBits source input) (dropTouched ranT).2.2 answers)))) ≤
          potential mid.1 result.2) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind (event (outcomePoints o)) ≤ c := by
  rw [privateStage2U_some_eq, tsum_bind_mul]
  refine le_trans (ENNReal.tsum_le_tsum (g := fun tape => uniformMaskTape tape * c)
    fun tape => mul_le_mul' le_rfl ?_) (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe,
      one_mul]))
  have whole : openingRun source input tape =
      ((runRefillT (restoredBits source input) (fun cell => PMF.pure (tape cell)) first
        LazyOracle.empty noRecord ∅).bind (continueT (restoredBits source input)
          (fun cell => PMF.pure (tape cell)) rest)).map (Option.map dropTouched) := by
    unfold openingRun
    rw [split, runRefill_eq_runRefillT, runRefillT_bind]
  rw [tsum_bind_mul, whole, tsum_map_mul, tsum_bind_mul]
  refine le_trans (tsum_mul_le_of_support _ _ (fun _ => c) fun midT midMember => ?_)
    (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
  rcases midT with _ | mid
  · exfalso
    apply openingRun_ne_none source input tape
    rw [whole]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨none, (PMF.mem_support_bind_iff _ _ _).mpr
      ⟨none, midMember, by simp [continueT]⟩, rfl⟩
  · show ∑' ranT, runRefillT _ _ (rest mid.1) mid.2.1 mid.2.2.1 mid.2.2.2 ranT * _ ≤ c
    refine le_trans (tsum_mul_le_of_support _ _ (optWeightT (potential mid.1))
      fun ranT ranMember => ?_) (le_trans (runRefillT_potential_prog _ _ (potential mid.1)
        (hashSame mid.1) (step mid.1) _ (restForward mid.1) _ _ _) (initial tape mid midMember))
    rcases ranT with _ | ranT
    · exfalso
      apply openingRun_ne_none source input tape
      rw [whole]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨none, (PMF.mem_support_bind_iff _ _ _).mpr
        ⟨some mid, midMember, ranMember⟩, rfl⟩
    · have openMember : some (dropTouched ranT) ∈ (openingRun source input tape).support := by
        rw [whole]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some ranT,
          (PMF.mem_support_bind_iff _ _ _).mpr ⟨some mid, midMember, ranMember⟩, rfl⟩
      simp only [Option.map_some, abortCont, optWeightT]
      refine post_le scalar off source input event (dropTouched ranT) _ fun answers => ?_
      refine le_trans (tsum_mul_le_of_support _ _ (fun result => potential mid.1 result.2)
        fun result resultMember => final tape mid midMember ranT ranMember openMember answers
          result resultMember) ?_
      refine le_trans (runLazyQ_potential ForwardOnly (potential mid.1) (step mid.1) _
        (shadowOnM_forwardOnly _ _ _) _) (le_of_eq ?_)
      exact programAllSkip_potential _ (hashSame mid.1) _ _

end Split

/-! ### The prefix -/

section Prefix

variable [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac)

/-- The opening after its prefix. -/
abbrev prefixRest (hashed : Block × Block) :
    Programs.M ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) :=
  whitePadsM ⟨hashed.1, hashed.2⟩ >>= fun pads =>
    pointXM table bits (Programs.whitenMacOf pads mac) >>= fun pointX =>
      pointYM table bits (Programs.whitenMacOf pads mac) >>= fun pointY => pure (pointX, pointY)

theorem openingQueriesM_prefixSplit :
    openingQueriesM table bits mac = curvePrefixM table bits mac >>= prefixRest table bits mac :=
  openingQueriesM_eq_prefix table bits mac

theorem prefixRest_forward (hashed : Block × Block) :
    AllQ ForwardOnly (prefixRest table bits mac hashed) :=
  (whitePadsM_forwardOnly _).bind fun _ => (evalLaneM_forwardOnly _ _ _ _ _).bind fun _ =>
    (evalLaneM_forwardOnly _ _ _ _ _).bind fun _ => .pure _

theorem curvePrefixM_fresh : Fresh bits ∅ (curvePrefixM table bits mac) := by
  unfold curvePrefixM
  refine Fresh.bind (S := laneCells .curveX) (evalLaneM_fresh bits _ _ _ _ _)
    (evalLaneM_inCells bits _ _ _ _ _) fun _ => ?_
  refine Fresh.bind (S := laneCells .curveY)
    (lane_fresh_avoid bits _ _ _ _ _ _ fun cell inside outside => ?_)
    (evalLaneM_inCells bits _ _ _ _ _) fun _ => ?_
  · rcases outside with outside | outside
    · exact outside
    · exact laneCells_ne (by decide) inside outside
  · exact Fresh.of_none (.query _ _ (consumedCell_bridge bits _) fun _ => .pure _) _

end Prefix

theorem mem_queriesAlong_of_transcript {α : Type} (ans : (request : Request) → request.Answer)
    (c : FreeQuery Programs.Spec α) (entry : Entry FixedIndex EncPRF.PermutationIndex)
    (inside : entry ∈ transcript ans c) : entry.1 ∈ queriesAlong ans c := by
  induction c with
  | pure value => cases inside
  | query request next ih =>
    rcases List.mem_cons.mp inside with rfl | inside
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih _ inside)

/-- A stored forward EncPRF pair, as a lookup. -/
theorem stored_enc_lk {state : LState} {j : EncPRF.PermutationIndex} {x a : Block}
    (stored : StoredAs state ⟨.encForward j x, a⟩) :
    lk (state.enc j) x.toFin = some a.toFin := by
  change (lk (state.enc j) x.toFin).map BitVec.ofFin = some a at stored
  cases found : lk (state.enc j) x.toFin with
  | none => rw [found] at stored; cases stored
  | some y =>
    rw [found] at stored
    simp only [Option.map_some, Option.some.injEq] at stored
    rw [← stored]

/-! ### Pads at the final state -/

section Final

variable [FieldCertificate] [GroupCertificate] (source : Stage1Source) (input : AffineInput)
  (tape : Tape)
  (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
    LState × Record)
  (member : some ran ∈ (openingRun source input tape).support)
  (answers : DesignatedLimbs) (result : Unit × LState)
  (resultMember : result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
    (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
      ran.2.2 answers) ran.2.1)).support)

include member resultMember

/-- The final state reads the opening's keys. -/
theorem kOf_final :
    kOf source.publicValue (restoredBits source input) (restoredMac source input)
        (answerOf result.2) =
      kOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1) := by
  have grow := final_grows source input tape ran member answers result resultMember
  show answerOf result.2 (.hash (bridgeInput (tOf _ _ _ (answerOf result.2)))) = _
  rw [tOf_agree source input tape ran member result.2 grow]
  refine opening_agree source input tape ran member result.2 grow _ ?_
    (Kriterion.ArgoMAC.Phase3.Lazy.interceptAnswer_plain _ fun designated =>
      Kriterion.ArgoMAC.Phase3.Lazy.bridgeInput_not_cellAt _ _ _
        (Kriterion.ArgoMAC.Phase3.Lazy.designated_cellAt designated))
  rw [queriesAlong_opening]
  exact List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ List.mem_cons_self))

/-- **Both pads of every position are stored at the final state, at the opening's keys.** -/
theorem pad_final (j : EncPRF.PermutationIndex) (bit : Bool) :
    StoredAs result.2 ⟨.encForward j (encodeBit bit ^^^
      (kOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1)).1),
      answerOf result.2 (.encForward j (encodeBit bit ^^^
        (kOf source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1)).1))⟩ := by
  have grow := final_grows source input tape ran member answers result resultMember
  cases bit with
  | false =>
    have onPath : .encForward j (encodeBit false ^^^ (kOf source.publicValue
        (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1)).1) ∈
        queriesAlong (refillAns (restoredBits source input) ran.2.1)
          (openingQueriesM source.publicValue (restoredBits source input)
            (restoredMac source input)) := by
      rw [queriesAlong_opening]
      refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ ?_)))
      exact mem_queriesAlong_of_transcript _ _ _ (whitePad_mem_transcript _ _ j)
    have stored := storedAs_grows grow
      ((opening_described source input tape ran (openingRun_mem member)).stored _ onPath rfl)
    rw [answerOf_of_stored stored]
    exact stored
  | true =>
    obtain ⟨_, storedPath, _⟩ := runLazyQ_stores _ _ result resultMember
    have entry : (⟨.encForward j (encodeBit true ^^^ (FreeQuery.eval (answerOf result.2)
        (curvePrefixM source.publicValue (restoredBits source input)
          (restoredMac source input))).1),
        answerOf result.2 (.encForward j (encodeBit true ^^^ (FreeQuery.eval (answerOf result.2)
          (curvePrefixM source.publicValue (restoredBits source input)
            (restoredMac source input))).1))⟩ : Entry FixedIndex EncPRF.PermutationIndex) ∈
        transcript (answerOf result.2) (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) := by
      unfold shadowOnM
      refine mem_transcript_right (answerOf result.2) ?_
      generalize FreeQuery.eval (answerOf result.2) (curvePrefixM source.publicValue
        (restoredBits source input) (restoredMac source input)) = E
      exact mem_transcript_left (answerOf result.2)
        (truePad_mem_transcript (answerOf result.2) ⟨E.1, E.2⟩ j)
    have inShadow := storedPath _ entry
    rw [eval_curvePrefixM, kOf_final source input tape ran member answers result resultMember]
      at inShadow
    exact inShadow

/-- **At most two pairs at every EncPRF index of the final state.** -/
theorem enc_final_small (j : EncPRF.PermutationIndex) : (result.2.enc j).used ≤ 2 := by
  obtain ⟨stored, keysSame, exact⟩ := installed_facts source input tape ran member
    (programRequests (restoredBits source input) ran.2.2 answers)
  rw [← keysSame] at exact
  exact used_le_two _ _ _ (shadow_enc_final _ _ _ _ stored exact result resultMember j)

end Final

/-! ### The pad potential -/

section PadBound

variable [FieldCertificate] [GroupCertificate]

/-- **An event forcing a pad's final answer to a target read from the keys has mass
`≤ 1/(2^128 − 1)`.** -/
theorem pad_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (j : EncPRF.PermutationIndex)
    (bit : Bool) (goal : Block × Block → Block)
    (reduce : ∀ (tape : Tape)
      (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
        LState × Record), some ran ∈ (openingRun source input tape).support →
      ∀ (answers : DesignatedLimbs) (result : Unit × LState),
        result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
            ran.2.2 answers) ran.2.1)).support →
        event ((pointsOf result.2).union (requestPoints (programRequests
          (restoredBits source input) ran.2.2 answers))) →
        (answerOf result.2 (.encForward j (encodeBit bit ^^^
          (kOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1)).1)) : Block) =
          goal (kOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1))) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind (event (outcomePoints o)) ≤ epsOne := by
  refine onCurve_split_le scalar off source input target event
    (curvePrefixM source.publicValue (restoredBits source input) (restoredMac source input))
    (prefixRest source.publicValue (restoredBits source input) (restoredMac source input))
    (openingQueriesM_prefixSplit _ _ _) (prefixRest_forward _ _ _)
    (fun k s => padF (encodeBit bit ^^^ k.1).toFin (goal k).toFin (s.enc j))
    (fun k state updated input' answer success => by
      rw [program_hash_enc input' answer state updated success])
    (fun k request state forward => enc_lift_step j _ (padF_step _ _) request forward state) epsOne
    (fun tape mid midMember => ?_) (fun tape mid midMember ranT ranMember openMember answers
      result resultMember => ?_)
  · -- after the prefix the EncPRF part is empty
    have encEmpty := runRefill_enc_same (restoredBits source input)
      (fun cell => PMF.pure (tape cell)) _ (curvePrefixM_encFree _ _ _) _ _ _ _
      (runRefillT_mem_runRefill _ _ _ _ _ _ _ midMember)
    have zero : (mid.2.1.enc j).used = 0 := by
      have := congrArg (fun e => (e j).used) encEmpty
      exact this
    have unknown : ¬ (mid.2.1.enc j).knownInput (encodeBit bit ^^^ mid.1.1).toFin := by
      unfold SparsePermutation.knownInput
      omega
    show padF _ _ _ ≤ epsOne
    unfold padF
    rw [if_neg unknown, if_pos (by omega)]
  · -- the keys at the final state are the prefix's value
    have d1 := runRefill_describe (restoredBits source input) tape _
      (curvePrefixM_forwardOnly _ _ _) ∅ (curvePrefixM_fresh _ _ _) LazyOracle.empty noRecord ∅
      (fun _ _ => ⟨fun h => h, fun _ => rfl⟩) _ (runRefillT_mem_runRefill _ _ _ _ _ _ _ midMember)
    have grow : Grows mid.2.1 (dropTouched ranT).2.1 :=
      runRefill_grows _ _ _ _ _ _ _ (runRefillT_mem_runRefill _ _ _ _ _ _ _ ranMember)
    have keyEq : kOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) (dropTouched ranT).2.1) = mid.1 := by
      have value : mid.1 = FreeQuery.eval (refillAns (restoredBits source input) mid.2.1)
          (curvePrefixM source.publicValue (restoredBits source input)
            (restoredMac source input)) :=
        d1.value
      rw [value, ← eval_curvePrefixM]
      refine (queriesAlong_congr _ _ _ fun q onPath => ?_).2
      have plain := mem_queriesAlong_allQ _ (curvePrefixM_notIntercepted _ _ _) q onPath
      rw [refillAns_plain plain, refillAns_plain plain]
      exact answerOf_of_stored (storedAs_grows grow (d1.stored q onPath plain))
    have stored := pad_final source input tape (dropTouched ranT) openMember answers result
      resultMember j bit
    rw [keyEq] at stored
    have found := stored_enc_lk stored
    have small := enc_final_small source input tape (dropTouched ranT) openMember answers result
      resultMember j
    refine le_trans (ind_mono fun hit => ?_) (padF_bound _ _ _ _ found small)
    have same := reduce tape (dropTouched ranT) openMember answers result resultMember hit
    rw [keyEq] at same
    rw [same]

end PadBound

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
