/-
**Phase 3, P1m — (B1): the EncPRF conjunct of `PerPairBound`, on the curve.**

* `keyedPoints_le_of_source` — a per-source bound on the mass of an event of `M'`'s unflagged
  private points is a bound on the key-averaged points (`keyedPoints`).
* `onCurve_event_le` — on the curve, the mass of an event factors through the opening's final state
  (`G`), once the shadow's run after it is bounded by `G` (aborts have no mass).
* `encIn_onCurve_le` — `Pr[x ∈ encIn_j] ≤ 2/2^128`: the stored inputs are `0 ⊕ k₁`, `1 ⊕ k₁`
  (`shadow_enc_final`), and `k₁`'s law is the key potential's (`keyPotential_opening`,
  `runRefill_potential`, `keyPotential_step`).
* `encOut_onCurve_le` — `Pr[y ∈ encOut_j] ≤ 2/2^128`, the **exact** marginal (`outPotential`: at most
  two pairs per EncPRF index, the first answer uniform on `2^128` outputs, the second on the
  `2^128 − 1` others).

Every statement holds for `planBShadow scalar off` at any off-curve part `off`; the off-curve half
and the conjunct for the designed shadow are in `BoundsEncOff.lean`.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsEnc

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM idealSamplers
  designatedLimbs programRequests noRecord DesignatedLimbs)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape runRefill uniformMaskTape AllQ
  consumeCell refillAnswer consumeCell_spec touch)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A pointwise bound on the support bounds the expectation. -/
theorem tsum_mul_le_of_support {X : Type} (μ : PMF X) (f g : X → ℝ≥0∞)
    (bound : ∀ x ∈ μ.support, f x ≤ g x) : ∑' x, μ x * f x ≤ ∑' x, μ x * g x :=
  ENNReal.tsum_le_tsum fun x => by
    by_cases member : x ∈ μ.support
    · exact mul_le_mul' le_rfl (bound x member)
    · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

/-! ### From a per-source bound to the key-averaged points -/

section Keyed

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
  [Fintype EncPRF.PermutationIndex]

theorem toOuterMeasure_eq_tsum_ind {X : Type} (μ : PMF X) (P : X → Prop) :
    μ.toOuterMeasure {x | P x} = ∑' x, μ x * ind (P x) := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases h : P x
  · rw [Set.indicator_of_mem (show x ∈ {x | P x} from h), ind_pos h, mul_one]
  · rw [Set.indicator_of_notMem (show x ∉ {x | P x} from h), ind_neg h, mul_zero]

/-- **The key-averaged mass of an event**, as an average over the key of the per-source mass. -/
theorem keyedPoints_measure_eq (shadow : Shadow) (scalar : NonZeroScalar) (pub : PubPart)
    (input : AffineInput) (P : Points FixedIndex EncPRF.PermutationIndex → Prop) :
    (keyedPoints shadow scalar pub input).toOuterMeasure {p | P p} =
      ∑' key, PMF.uniformOfFintype InputMacKey key *
        ∑' o, privateStage2U uniformMaskTape shadow scalar (joinSource pub key) input
          (Scheme.scheme.function scalar input) o * ind (P (outcomePoints o)) := by
  rw [toOuterMeasure_eq_tsum_ind]
  unfold keyedPoints
  rw [tsum_bind_mul]
  refine tsum_congr fun key => congrArg _ ?_
  rw [tsum_map_mul]

/-- **A per-source bound is a bound on the key-averaged points.** -/
theorem keyedPoints_le_of_source (shadow : Shadow) (scalar : NonZeroScalar) (pub : PubPart)
    (input : AffineInput) (P : Points FixedIndex EncPRF.PermutationIndex → Prop) (c : ℝ≥0∞)
    (bound : ∀ source : Stage1Source,
      ∑' o, privateStage2U uniformMaskTape shadow scalar source input
        (Scheme.scheme.function scalar input) o * ind (P (outcomePoints o)) ≤ c) :
    (keyedPoints shadow scalar pub input).toOuterMeasure {p | P p} ≤ c := by
  rw [keyedPoints_measure_eq]
  exact tsum_le_of_support _ _ _ fun key _ => bound _

end Keyed

/-! ### On the curve: factoring through the opening -/

section OnCurve

variable [FieldCertificate] [GroupCertificate]

/-- The opening run of a source and an input, on a tape. (A `def`: the unifier must never compare
it with the unfolded runner, whose program it would unfold.) -/
def openingRun (source : Stage1Source) (input : AffineInput) (tape : Tape) :
    PMF (Option (((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)) :=
  runRefill (restoredBits source input) (fun cell => PMF.pure (tape cell))
    (openingQueriesM source.publicValue (restoredBits source input) (restoredMac source input))
    LazyOracle.empty noRecord ∅

theorem openingRun_mem {source : Stage1Source} {input : AffineInput} {tape : Tape}
    {ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record} (member : some ran ∈ (openingRun source input tape).support) :
    some ran ∈ (runRefill (restoredBits source input) (fun cell => PMF.pure (tape cell))
      (openingQueriesM source.publicValue (restoredBits source input) (restoredMac source input))
      LazyOracle.empty noRecord ∅).support := by
  unfold openingRun at member
  exact member

theorem openingRun_ne_none (source : Stage1Source) (input : AffineInput) (tape : Tape) :
    none ∉ (openingRun source input tape).support := by
  unfold openingRun
  exact runRefill_ne_none _ _ _ _ _ _

/-- `M'`'s private stage 2 on the curve, with the opening run named. -/
theorem privateStage2U_some_eq (shadow : Shadow) (scalar : NonZeroScalar) (source : Stage1Source)
    (input : AffineInput) (target : Point) :
    privateStage2U uniformMaskTape shadow scalar source input (some target) =
      uniformMaskTape.bind fun tape =>
        (openingRun source input tape).bind (abortCont (privateContU shadow scalar source input)) := by
  unfold openingRun
  rfl

/-- **The opening run as a supermartingale** for a potential reading only the EncPRF part and the
off-scale hash lookups, not raised by any forward question. -/
theorem openingRun_potential (source : Stage1Source) (input : AffineInput) (tape : Tape)
    (potential : LState → ℝ≥0∞)
    (congr : ∀ s s' : LState, s.enc = s'.enc →
      (∀ k, OffScale k → s.hash.lookup k = s'.hash.lookup k) → potential s = potential s')
    (step : ∀ (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState),
      ForwardOnly request →
        ∑' answer, LazyOracle.query request state answer * potential answer.2 ≤ potential state) :
    ∑' ran, openingRun source input tape ran * optWeight potential ran ≤
      potential LazyOracle.empty := by
  have key := runRefill_potential (restoredBits source input) (fun cell => PMF.pure (tape cell))
    ForwardOnly potential congr step
    (openingQueriesM source.publicValue (restoredBits source input) (restoredMac source input))
    (openingQueriesM_forwardOnly source.publicValue (restoredBits source input)
      (restoredMac source input)) LazyOracle.empty noRecord ∅
  unfold openingRun
  exact key

/-- **On the curve, an event's mass factors through the opening's final state.** -/
theorem onCurve_event_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (G : LState → ℝ≥0∞)
    (perRun : ∀ (tape : Tape)
      (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
        LState × Record), some ran ∈ (openingRun source input tape).support →
      ∀ answers : DesignatedLimbs,
        ∑' result, runLazyQ (shadowOnM source.publicValue (restoredBits source input)
              (restoredMac source input))
            (programAllSkip (programRequests (restoredBits source input) ran.2.2 answers) ran.2.1)
            result *
          ind (event ((pointsOf result.2).union
            (requestPoints (programRequests (restoredBits source input) ran.2.2 answers)))) ≤
        G ran.2.1) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind (event (outcomePoints o)) ≤
      ∑' tape, uniformMaskTape tape * ∑' ran, openingRun source input tape ran * optWeight G ran := by
  rw [privateStage2U_some_eq, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
  rw [tsum_bind_mul]
  refine tsum_mul_le_of_support _ _ _ fun ran member => ?_
  rcases ran with _ | ran
  · exact absurd member (openingRun_ne_none source input tape)
  · simp only [abortCont, optWeight]
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
      have bound := perRun tape ran member answers
      rw [show (Lamport.restore input (sourceLabels source input)).input = restoredBits source input
        from rfl]
      exact bound

/-- After the opening and the designated installation: the prefix is stored, its keys are the
opening's, and the EncPRF part is exact. -/
theorem installed_facts (source : Stage1Source) (input : AffineInput) (tape : Tape)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record) (member : some ran ∈ (openingRun source input tape).support)
    (requests : List (Option BaseField × (Block × Block))) :
    StoredPath (programAllSkip requests ran.2.1) (curvePrefixM source.publicValue
        (restoredBits source input) (restoredMac source input)) ∧
      prefixKeysOn (programAllSkip requests ran.2.1) source.publicValue (restoredBits source input)
          (restoredMac source input) =
        prefixKeysOn ran.2.1 source.publicValue (restoredBits source input)
          (restoredMac source input) ∧
      EncExact (programAllSkip requests ran.2.1) (prefixKeysOn ran.2.1 source.publicValue
        (restoredBits source input) (restoredMac source input)).1 := by
  have run := openingRun_mem member
  have prefixStored := opening_stores_prefix source.publicValue (restoredBits source input)
    (restoredMac source input) _ _ _ _ ran run
  have grow := programAllSkip_grows requests ran.2.1
  refine ⟨(storedPath_grows _ grow prefixStored).1, (storedPath_grows _ grow prefixStored).2, ?_⟩
  exact encExact_of_enc (programAllSkip_enc _ _) (opening_encExact source.publicValue
    (restoredBits source input) (restoredMac source input) _ ran run)

/-- The two keys whose pads would expose `x`. -/
def keysOf (x : Block) : Finset Block := {x ^^^ encodeBit false, x ^^^ encodeBit true}

theorem keysOf_card (x : Block) : (keysOf x).card ≤ 2 := Finset.card_le_two

theorem mem_keysOf_of_pad {x w : Block} (bit : Bool) (same : x = encodeBit bit ^^^ w) :
    w ∈ keysOf x := by
  have back : w = x ^^^ encodeBit bit := by
    rw [same, BitVec.xor_comm (encodeBit bit) w, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]
  cases bit
  · exact Finset.mem_insert.mpr (Or.inl back)
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr back))

/-- **The EncPRF input mass on the curve.** -/
theorem encIn_onCurve_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (j : EncPRF.PermutationIndex) (x : Block) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).encIn j x) ≤ 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  refine le_trans (onCurve_event_le scalar off source input target (fun p => p.encIn j x)
    (fun state => ind ((prefixKeysOn state source.publicValue (restoredBits source input)
      (restoredMac source input)).1 ∈ keysOf x)) fun tape ran member answers => ?_) ?_
  · obtain ⟨stored, keysSame, exact⟩ := installed_facts source input tape ran member
      (programRequests (restoredBits source input) ran.2.2 answers)
    rw [← keysSame] at exact ⊢
    refine tsum_le_of_support _ _ _ fun result resultMember => ind_mono fun hit => ?_
    rcases hit with inside | inside
    · generalize hk : prefixKeysOn (programAllSkip (programRequests (restoredBits source input)
        ran.2.2 answers) ran.2.1) source.publicValue (restoredBits source input)
        (restoredMac source input) = k at exact ⊢
      have final := shadow_enc_final _ _ _ _ stored (hk ▸ exact) result resultMember j x.toFin inside
      rw [hk] at final
      rcases final with same | same
      · exact mem_keysOf_of_pad false (BitVec.toFin_inj.mp same)
      · exact mem_keysOf_of_pad true (BitVec.toFin_inj.mp same)
    · exact inside.elim
  · calc ∑' tape, uniformMaskTape tape * ∑' ran, openingRun source input tape ran *
          optWeight (fun state => ind ((prefixKeysOn state source.publicValue
            (restoredBits source input) (restoredMac source input)).1 ∈ keysOf x)) ran
        ≤ ∑' tape, uniformMaskTape tape * keyPotential (keysOf x) LazyOracle.empty := by
          refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
          refine le_trans (tsum_mul_le_of_support _ _ (optWeight (keyPotential (keysOf x)))
            fun ran member => ?_) (openingRun_potential source input tape (keyPotential (keysOf x))
              (fun s s' _ same => keyPotential_congr _ s s' same)
              (fun request state _ => keyPotential_step _ request state))
          rcases ran with _ | ran
          · exact zero_le
          · simp only [optWeight]
            exact keyPotential_opening source.publicValue (restoredBits source input)
              (restoredMac source input) (fun cell => PMF.pure (tape cell)) (keysOf x) ran
              (openingRun_mem member)
      _ = keyPotential (keysOf x) LazyOracle.empty := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      _ ≤ 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
          have empty : ∀ k, OffScale k → (LazyOracle.empty : LState).hash.lookup k = none :=
            fun _ _ => rfl
          unfold keyPotential
          rw [if_pos empty]
          exact mul_le_mul' (by exact_mod_cast keysOf_card x) le_rfl

end OnCurve

/-! ### At most two stored pairs: the output indicator is below the output potential -/

section OutBound

/-- A permutation state whose stored inputs lie in a two-point set has at most two pairs. -/
theorem used_le_two {size : ℕ} (state : SparsePermutation size) (a b : Fin size)
    (inputs : ∀ z, lk state z ≠ none → z = a ∨ z = b) : state.used ≤ 2 := by
  classical
  rw [← card_known]
  refine le_trans (Fintype.card_le_of_injective
    (fun z : {z // state.knownInput z} => (if z.1 = a then (0 : Fin 2) else 1)) ?_) (by simp)
  intro first second same
  apply Subtype.ext
  have hf := inputs first.1 ((knownInput_iff _ _).mp first.2)
  have hs := inputs second.1 ((knownInput_iff _ _).mp second.2)
  dsimp only at same
  by_cases fa : first.1 = a
  · by_cases sa : second.1 = a
    · rw [fa, sa]
    · rw [if_pos fa, if_neg sa] at same
      exact absurd same (by decide)
  · by_cases sa : second.1 = a
    · rw [if_neg fa, if_pos sa] at same
      exact absurd same (by decide)
    · rw [hf.resolve_left fa, hs.resolve_left sa]

open Classical in
/-- **With at most two pairs at `j`, the output indicator is below the output potential.** -/
theorem encOut_ind_le (j : EncPRF.PermutationIndex) (y : Block) (state : LState)
    (small : (state.enc j).used ≤ 2) :
    ind ((pointsOf state).encOut j y) ≤ outPotential j y.toFin state := by
  by_cases hit : (pointsOf state).encOut j y
  · rw [ind_pos hit]
    have known : (state.enc j).knownOutput y.toFin := (knownOutput_iff _ _).mpr hit
    have positive : (state.enc j).used ≠ 0 := by
      intro zero
      have := known
      unfold SparsePermutation.knownOutput at this
      omega
    unfold outPotential
    rw [if_neg positive]
    by_cases one : (state.enc j).used = 1
    · rw [if_pos one, if_pos known]
    · have two : (state.enc j).used = 2 := by omega
      rw [if_neg one, if_pos two, if_pos known]
  · rw [ind_neg hit]
    exact zero_le

theorem outPotential_empty (j : EncPRF.PermutationIndex) (y : Fin (2 ^ 128)) :
    outPotential j y (LazyOracle.empty : LState) = 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  have zero : ((LazyOracle.empty : LState).enc j).used = 0 := rfl
  unfold outPotential
  rw [if_pos zero]

end OutBound

section OnCurveOut

variable [FieldCertificate] [GroupCertificate]

/-- **The EncPRF output mass on the curve** (the exact marginal). -/
theorem encOut_onCurve_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (j : EncPRF.PermutationIndex) (y : Block) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).encOut j y) ≤ 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  refine le_trans (onCurve_event_le scalar off source input target (fun p => p.encOut j y)
    (outPotential j y.toFin) fun tape ran member answers => ?_) ?_
  · obtain ⟨stored, keysSame, exact⟩ := installed_facts source input tape ran member
      (programRequests (restoredBits source input) ran.2.2 answers)
    rw [← keysSame] at exact
    refine le_trans (tsum_mul_le_of_support _ _ (fun result => outPotential j y.toFin result.2)
      fun result resultMember => ?_) ?_
    · generalize hk : prefixKeysOn (programAllSkip (programRequests (restoredBits source input)
        ran.2.2 answers) ran.2.1) source.publicValue (restoredBits source input)
        (restoredMac source input) = k at exact
      have inputs := shadow_enc_final _ _ _ _ stored (hk ▸ exact) result resultMember j
      rw [hk] at inputs
      have small := used_le_two (result.2.enc j) _ _ inputs
      refine le_trans (le_of_eq ?_) (encOut_ind_le j y result.2 small)
      show ind ((pointsOf result.2).encOut j y ∨ False) = _
      rw [or_false]
    · refine le_trans (runLazyQ_potential ForwardOnly (outPotential j y.toFin)
        (fun request state forward => outPotential_step j y.toFin request forward state)
        (shadowOnM source.publicValue (restoredBits source input) (restoredMac source input))
        (shadowOnM_forwardOnly source.publicValue (restoredBits source input)
          (restoredMac source input)) _) (le_of_eq ?_)
      exact outPotential_congr j y.toFin _ _ (programAllSkip_enc _ _)
  · calc ∑' tape, uniformMaskTape tape * ∑' ran, openingRun source input tape ran *
          optWeight (outPotential j y.toFin) ran
        ≤ ∑' tape, uniformMaskTape tape * outPotential j y.toFin LazyOracle.empty :=
          ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl
            (openingRun_potential source input tape (outPotential j y.toFin)
              (fun s s' same _ => outPotential_congr j y.toFin s s' same)
              (fun request state forward => outPotential_step j y.toFin request forward state))
      _ = 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, outPotential_empty]

end OnCurveOut

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
