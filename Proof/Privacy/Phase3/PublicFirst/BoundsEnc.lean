/-
**Phase 3, P1k — (B1), the EncPRF and structural part: the shape of the EncPRF and hash parts of
`M'`'s private stage 2 on the curve.**

* `opening_offScale_oneKey` — `HW`'s opening stores exactly one off-scale hash key, the prefix's
  bridge input (the lanes ask only scale inputs, `onScale_of_laneAt`), so the key potential of its
  final state is the indicator of the prefix's key (`keyPotential_opening`).
* `shadow_enc_final` — after the shadow, the EncPRF part stores at every position only the inputs
  `0 ⊕ k₁`, `1 ⊕ k₁` (the opening's whitening pads, the shadow's bit-`true` pads; the shadow's
  re-run of the evaluator reads them back: `onCurveM_eq_prefix`, `storedPath_of_allQ`).
* `onCurveRest`, `onCurveM_eq_prefix` — the evaluator after its prefix and its pads.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsEncRun

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (openingQueriesM whitePadsM noRecord)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell runRefill consumeCell_spec AllQ LaneAt
  evalLaneM_allQ fq_bind_assoc)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Generic run facts -/

section Generic

/-- A question that asks no off-scale hash key (every hash question in the scale range). -/
def OnScale : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward _ _ => True
  | .fixedInverse _ _ => True
  | .encForward _ _ => True
  | .encInverse _ _ => True
  | .hash input => input.val < scaleRange

/-- A lane's question is on the scale range: a fold question, or a hash question at a cell
input. -/
theorem onScale_of_laneAt {lane : Lane}
    {request : PublicQuery FixedIndex EncPRF.PermutationIndex} (inside : ∃ c, LaneAt lane c request) :
    OnScale request := by
  obtain ⟨_, inside⟩ := inside
  cases request with
  | hash input =>
    rcases inside with fixed | ⟨cell, label, _, _, rfl⟩
    · exact fixed.elim
    · exact scaleInput_val_lt_scaleRange _ _ _ _ _
  | _ => trivial

theorem onScale_of_encInputIs {value : Block}
    {request : PublicQuery FixedIndex EncPRF.PermutationIndex} (inside : EncInputIs value request) :
    OnScale request := by
  cases request with
  | hash _ => exact inside.elim
  | _ => trivial

/-- **A refill run of a program on the scale range keeps the off-scale hash lookups.** -/
theorem runRefill_offScale_same (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (computation : FreeQuery Programs.Spec α) (free : AllQ OnScale computation) (oracle : LState)
    (record : Record) (touched : Set Cell) (outcome : α × LState × Record)
    (member : some outcome ∈ (runRefill bits draw computation oracle record touched).support) :
    ∀ k, OffScale k → outcome.2.1.hash.lookup k = oracle.hash.lookup k :=
  runRefill_invariant bits draw OnScale
    (fun state => ∀ k, OffScale k → state.hash.lookup k = oracle.hash.lookup k)
    (fun request state holds same answer answerMember k off => by
      refine (query_hash_frame request state answer answerMember k ?_).trans (same k off)
      rintro rfl
      exact off holds)
    (fun request state _ _ _ updated _ same consumed success k off => by
      obtain ⟨input, rfl, _, _, found⟩ := consumeCell_spec consumed
      exact (program_hash_offScale (cellOf_scale found) success k off).trans (same k off))
    computation free oracle record touched outcome (fun _ _ => rfl) member

/-- **An invariant of the lazy runner**, for a program all of whose questions satisfy `Q`. -/
theorem runLazyQ_invariant (Q : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop)
    (Inv : LState → Prop)
    (step : ∀ (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState),
      Q request → Inv state → ∀ answer ∈ (LazyOracle.query request state).support, Inv answer.2)
    {α : Type} (computation : FreeQuery Programs.Spec α) (holds : AllQ Q computation) :
    ∀ (state : LState) (outcome : α × LState), Inv state →
      outcome ∈ (runLazyQ computation state).support → Inv outcome.2 := by
  induction computation with
  | pure value =>
    intro state outcome invariant member
    simp only [runLazyQ, PMF.mem_support_pure_iff] at member
    subst member
    exact invariant
  | query request next ih =>
    intro state outcome invariant member
    simp only [runLazyQ, PMF.mem_support_bind_iff] at member
    obtain ⟨answer, answerMember, rest⟩ := member
    exact ih answer.1 (AllQ.tail holds _) answer.2 outcome
      (step request state (AllQ.head holds) invariant answer answerMember) rest

/-- **A program all of whose questions are stored is a stored path.** -/
theorem storedPath_of_allQ (P : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop)
    (state : LState) (stored : ∀ request, P request → ∃ answer, StoredAs state ⟨request, answer⟩)
    {α : Type} (computation : FreeQuery Programs.Spec α) (holds : AllQ P computation) :
    StoredPath state computation := by
  induction computation with
  | pure value => exact fun _ member => by cases member
  | query request next ih =>
    obtain ⟨answer, here⟩ := stored request (AllQ.head holds)
    have same : answerOf state request = answer := answerOf_of_stored here
    refine storedPath_query.mpr ⟨by rw [same]; exact here, ih _ (AllQ.tail holds _)⟩

end Generic

/-! ### The opening's off-scale hash part -/

section OpeningHash

variable [FieldCertificate]

theorem lanes_onScale (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    AllQ OnScale (Programs.evalLaneM lane joins scale word labels) :=
  (evalLaneM_allQ lane joins scale word labels).mono fun _ inside => onScale_of_laneAt inside

/-- **`HW`'s opening stores at most one off-scale hash key** (the bridge input). -/
theorem opening_offScale_oneKey (table : Public) (bits : BitInput) (mac : InputMac)
    (draw : Cell → PMF (Block × Block))
    (outcome : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)
    (member : some outcome ∈ (runRefill bits draw (openingQueriesM table bits mac) LazyOracle.empty
      noRecord ∅).support) :
    ∀ k k', OffScale k → OffScale k' → outcome.2.1.hash.lookup k ≠ none →
      outcome.2.1.hash.lookup k' ≠ none → k = k' := by
  rw [openingQueriesM_eq_prefix] at member
  obtain ⟨mid, _, midMember, restMember⟩ := runRefill_bind_mem bits draw _ _ _ _ _ _ member
  -- the part after the prefix asks no off-scale key
  have restFree : AllQ OnScale (whitePadsM ⟨mid.1.1, mid.1.2⟩ >>= fun pads =>
      Programs.evalLaneM .pointX table.pointXHot
          (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
          (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)
        >>= fun pointX =>
      Programs.evalLaneM .pointY table.pointYHot
          (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
          (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
        >>= fun pointY => pure (pointX, pointY)) :=
    ((whitePadsM_encInput _).mono fun _ inside => onScale_of_encInputIs inside).bind fun _ =>
      (lanes_onScale _ _ _ _ _).bind fun _ => (lanes_onScale _ _ _ _ _).bind fun _ => .pure _
  have restSame := runRefill_offScale_same bits draw _ restFree _ _ _ _ restMember
  -- the prefix: two lanes on the scale range, then the bridge question
  unfold curvePrefixM at midMember
  obtain ⟨lane1, _, lane1Member, rest1⟩ := runRefill_bind_mem bits draw _ _ _ _ _ _ midMember
  obtain ⟨lane2, _, lane2Member, rest2⟩ := runRefill_bind_mem bits draw _ _ _ _ _ _ rest1
  have empty1 := runRefill_offScale_same bits draw _ (lanes_onScale _ _ _ _ _) _ _ _ _ lane1Member
  have empty2 := runRefill_offScale_same bits draw _ (lanes_onScale _ _ _ _ _) _ _ _ _ lane2Member
  set key := bridgeInput (CurveMembership.evaluate table.curve bits.toAffine
    (Pipeline.curveValues lane1.1 lane2.1)) with keyDef
  have only := runRefill_invariant bits draw (fun request => request = .hash key)
    (fun state => ∀ k, OffScale k → state.hash.lookup k ≠ none → k = key)
    (fun request state holds invariant answer answerMember k off found => by
      subst holds
      by_cases same : k = key
      · exact same
      · refine invariant k off ?_
        rw [← query_hash_frame _ state answer answerMember k fun equal =>
          same (PublicQuery.hash.inj equal).symm]
        exact found)
    (fun request state _ _ _ _ holds _ consumed _ => by
      obtain ⟨input, rfl, _, _, found⟩ := consumeCell_spec consumed
      cases PublicQuery.hash.inj holds
      exact absurd (cellOf_scale found) (bridgeInput_val_ge _).not_gt)
    (Programs.askHash key) (.query _ _ rfl fun _ => .pure _) _ _ _ _
    (fun k off found => by
      rw [empty2 k off, empty1 k off] at found
      exact absurd rfl found) rest2
  intro k k' off off' hk hk'
  rw [restSame k off] at hk
  rw [restSame k' off'] at hk'
  exact (only k off hk).trans (only k' off' hk').symm

/-- The prefix's key is its bridge hash answer. -/
theorem prefixKeysOn_eq (state : LState) (table : Public) (bits : BitInput) (mac : InputMac) :
    ∃ input, OffScale input ∧ prefixKeysOn state table bits mac = answerOf state (.hash input) ∧
      (⟨.hash input, answerOf state (.hash input)⟩ : Entry FixedIndex EncPRF.PermutationIndex) ∈
        transcript (answerOf state) (curvePrefixM table bits mac) := by
  refine ⟨bridgeInput (CurveMembership.evaluate table.curve bits.toAffine (Pipeline.curveValues
    (FreeQuery.eval (answerOf state) (Programs.evalLaneM .curveX table.curveXHot
      (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x)))
    (FreeQuery.eval (answerOf state) (Programs.evalLaneM .curveY table.curveYHot
      (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y))))),
    (bridgeInput_val_ge _).not_gt, ?_, ?_⟩
  · unfold prefixKeysOn curvePrefixM
    simp only [FreeQuery.eval_bind]
    rfl
  · unfold curvePrefixM
    exact mem_transcript_right _ (mem_transcript_right _ List.mem_cons_self)

/-- **At the opening's final state, the key potential is at least the indicator of its key.** -/
theorem keyPotential_opening (table : Public) (bits : BitInput) (mac : InputMac)
    (draw : Cell → PMF (Block × Block)) (S : Finset Block)
    (outcome : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)
    (member : some outcome ∈ (runRefill bits draw (openingQueriesM table bits mac) LazyOracle.empty
      noRecord ∅).support) :
    ind ((prefixKeysOn outcome.2.1 table bits mac).1 ∈ S) ≤ keyPotential S outcome.2.1 := by
  classical
  have stored := opening_stores_prefix table bits mac draw _ _ _ outcome member
  obtain ⟨input, off, keyEq, onPath⟩ := prefixKeysOn_eq outcome.2.1 table bits mac
  have here := stored _ onPath
  have oneKey := opening_offScale_oneKey table bits mac draw outcome member
  have present : outcome.2.1.hash.lookup input ≠ none := by
    intro missing
    change (outcome.2.1.hash.lookup input).map _ = some _ at here
    rw [missing] at here
    cases here
  by_cases hit : (prefixKeysOn outcome.2.1 table bits mac).1 ∈ S
  · rw [ind_pos hit]
    unfold keyPotential
    rw [if_neg fun empty => present (empty input off), if_pos oneKey, if_pos]
    refine ⟨input, answerOf outcome.2.1 (.hash input), off, here, ?_⟩
    rw [← keyEq]
    exact hit
  · rw [ind_neg hit]
    exact zero_le

end OpeningHash

/-! ### The shadow's EncPRF part -/

section ShadowEnc

variable [FieldCertificate] [GroupCertificate]

/-- The evaluator after its prefix and its pads. -/
def onCurveRest (table : Public) (bits : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    Programs.M (Option (Option Point)) :=
  Programs.evalLaneM .pointX table.pointXHot
      (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)
    >>= fun pointX =>
  Programs.evalLaneM .pointY table.pointYHot
      (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
    >>= fun pointY =>
  Programs.unlockM (Pipeline.pointTable table) bits.toAffine (Programs.transformMacOf pads mac)
    >>= fun digits =>
  pure (some (Garbling.decodeResult
    { point := bits.toAffine
      pointMacs := FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable table)
        (Pipeline.digitValues pointX pointY) bits.toAffine
      exceptionDigits := digits }))

/-- **The evaluator starts with the prefix and its pads.** -/
theorem onCurveM_eq_prefix (table : Public) (bits : BitInput) (mac : InputMac) :
    Programs.onCurveM table bits mac = curvePrefixM table bits mac >>= fun hashed =>
      Programs.evalPadsM ⟨hashed.1, hashed.2⟩ bits >>= fun pads =>
        onCurveRest table bits mac pads := by
  unfold Programs.onCurveM curvePrefixM onCurveRest
  simp only [fq_bind_assoc]

theorem hashM_encFree (index : FixedIndex) (label : Block) :
    AllQ EncFree (Programs.hashM index label) := by
  refine AllQ.bind ?_ fun _ => .pure _
  exact .query _ _ trivial fun _ => .pure _

theorem onCurveRest_encFree (table : Public) (bits : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    AllQ EncFree (onCurveRest table bits mac pads) :=
  ((evalLaneM_allQ _ _ _ _ _).mono fun _ inside => encFree_of_laneAt inside).bind fun _ =>
    ((evalLaneM_allQ _ _ _ _ _).mono fun _ inside => encFree_of_laneAt inside).bind fun _ =>
      (AllQ.vector fun _ =>
        (((AllQ.vector fun _ => hashM_encFree _ _).bind fun _ => .pure _).bind fun _ =>
          ((AllQ.vector fun _ => hashM_encFree _ _).bind fun _ => .pure _).bind fun _ =>
            .pure _).bind fun _ => .pure _).bind fun _ => .pure _

/-- An EncPRF forward question at one of the two pad inputs of key `w`. -/
def EncPad (w : Block) : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward _ _ => False
  | .fixedInverse _ _ => False
  | .encForward _ input => input = encodeBit false ^^^ w ∨ input = encodeBit true ^^^ w
  | .encInverse _ _ => False
  | .hash _ => False

theorem padM_encPad (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    AllQ (EncPad keys.first) (Programs.padM keys coordinate index bit) :=
  (padM_encInput keys coordinate index bit).mono fun request inside => by
    cases request with
    | encForward _ input =>
      change input = encodeBit bit ^^^ keys.first at inside
      cases bit
      · exact Or.inl inside
      · exact Or.inr inside
    | fixedForward _ _ => exact inside.elim
    | fixedInverse _ _ => exact inside.elim
    | encInverse _ _ => exact inside.elim
    | hash _ => exact inside.elim

theorem evalPadsM_encPad (keys : WhiteningKeys) (bits : BitInput) :
    AllQ (EncPad keys.first) (Programs.evalPadsM keys bits) := by
  unfold Programs.evalPadsM
  dsimp only
  exact (AllQ.vector fun _ => (padM_encPad _ _ _ _).bind fun _ =>
      AllQ.ite ((padM_encPad _ _ _ _).bind fun _ => .pure _) (.pure _)).bind fun _ =>
    (AllQ.vector fun _ => (padM_encPad _ _ _ _).bind fun _ =>
      AllQ.ite ((padM_encPad _ _ _ _).bind fun _ => .pure _) (.pure _)).bind fun _ => .pure _

/-- A known EncPRF input is a stored question. -/
theorem storedAs_of_enc {state : LState} {j : EncPRF.PermutationIndex} {input : Block}
    (known : lk (state.enc j) input.toFin ≠ none) :
    ∃ answer, StoredAs state ⟨.encForward j input, answer⟩ := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp known
  refine ⟨BitVec.ofFin a, ?_⟩
  change (lk (state.enc j) input.toFin).map BitVec.ofFin = some (BitVec.ofFin a)
  rw [ha]
  rfl

/-- **After the shadow, every stored EncPRF input is one of the two pad inputs.** -/
theorem shadow_enc_final (table : Public) (bits : BitInput) (mac : InputMac) (state : LState)
    (stored : StoredPath state (curvePrefixM table bits mac))
    (exact : EncExact state (prefixKeysOn state table bits mac).1)
    (final : Unit × LState) (member : final ∈ (runLazyQ (shadowOnM table bits mac) state).support) :
    ∀ j z, lk (final.2.enc j) z ≠ none →
      z = padInput false (prefixKeysOn state table bits mac).1 ∨
        z = padInput true (prefixKeysOn state table bits mac).1 := by
  rw [shadowOnM_run _ _ _ state stored, runLazyQ_bind] at member
  generalize hk : prefixKeysOn state table bits mac = k at member exact ⊢
  obtain ⟨pads, padsMember, restMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  obtain ⟨padsGrow, padsStored, _⟩ := runLazyQ_stores _ state pads padsMember
  -- after the bit-`true` pads: only the two inputs
  have padsOnly := runLazyQ_invariant
    (EncInputIs (encodeBit true ^^^ k.1))
    (fun s => ∀ j z, lk (s.enc j) z ≠ none → z = padInput false k.1 ∨ z = padInput true k.1)
    (fun request s holds invariant answer answerMember => by
      cases request with
      | encForward index input =>
        change input = _ at holds
        subst holds
        obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        intro j z found
        by_cases same : j = index
        · subst same
          simp only [Function.update_self] at found
          rcases forward_new _ _ drawn drawnMember z found with old | new
          · exact invariant j z old
          · exact Or.inr new
        · simp only [Function.update_of_ne same] at found
          exact invariant j z found
      | fixedForward _ _ => exact holds.elim
      | fixedInverse _ _ => exact holds.elim
      | encInverse _ _ => exact holds.elim
      | hash _ => exact holds.elim)
    _ (truePadsM_encInput ⟨k.1, k.2⟩) state pads
    (fun j z found => Or.inl ((exact j z).mp found)) padsMember
  -- the evaluator re-run keeps the EncPRF part
  have prefixStored := (storedPath_grows _ padsGrow stored).1
  have keysSame := (storedPath_grows _ padsGrow stored).2
  rw [onCurveM_eq_prefix, fq_bind_assoc, runLazyQ_bind, runLazyQ_storedPath _ _ prefixStored,
    PMF.pure_bind] at restMember
  dsimp only at restMember
  have padsPath : StoredPath pads.2 (Programs.evalPadsM
      ⟨(FreeQuery.eval (answerOf pads.2) (curvePrefixM table bits mac)).1,
        (FreeQuery.eval (answerOf pads.2) (curvePrefixM table bits mac)).2⟩ bits) := by
    refine storedPath_of_allQ _ pads.2 (fun request inside => ?_) _ (evalPadsM_encPad _ _)
    cases request with
    | encForward j input =>
      have keyEq : (FreeQuery.eval (answerOf pads.2) (curvePrefixM table bits mac)).1 = k.1 := by
        rw [← hk]
        unfold prefixKeysOn
        exact congrArg Prod.fst keysSame
      change input = _ ∨ input = _ at inside
      rw [keyEq] at inside
      rcases inside with rfl | rfl
      · exact storedAs_of_enc (ne_none_of_grows (padsGrow.enc j) ((exact j _).mpr rfl))
      · exact storedAs_of_enc (enc_ne_none_of_stored
          (padsStored _ (truePad_mem_transcript _ _ j)))
    | fixedForward _ _ => exact inside.elim
    | fixedInverse _ _ => exact inside.elim
    | encInverse _ _ => exact inside.elim
    | hash _ => exact inside.elim
  rw [fq_bind_assoc, runLazyQ_bind, runLazyQ_storedPath _ _ padsPath, PMF.pure_bind] at restMember
  dsimp only at restMember
  have encSame := runLazyQ_invariant EncFree (fun s => s.enc = pads.2.enc)
    (fun request s holds same answer answerMember => by
      cases request with
      | encForward _ _ => exact holds.elim
      | encInverse _ _ => exact holds.elim
      | fixedForward _ _ =>
        obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        exact same
      | fixedInverse _ _ =>
        obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        exact same
      | hash _ =>
        obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        exact same)
    _ ((onCurveRest_encFree _ _ _ _).bind fun _ => .pure _) pads.2 final rfl restMember
  intro j z found
  rw [encSame] at found
  exact padsOnly j z found

end ShadowEnc

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
