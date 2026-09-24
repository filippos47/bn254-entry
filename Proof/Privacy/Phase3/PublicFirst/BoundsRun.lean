/-
**Phase 3, P1k — run tools for the per-shadow bounds, and the EncPRF part after `HW`'s opening.**

Generic tools for P4's refill runner and the lazy runner:

* `runRefill_bind_mem` — a refill run of a sequence passes through a run of its first part;
* `runRefill_invariant` — a state invariant kept by every question of a program (`AllQ`) is kept by
  the refill run; `runRefill_enc_same`: a program asking no EncPRF question keeps the EncPRF part
  (a consumed question is a hash program, `program_hash_enc`);
* `runLazyQ_stores` — a lazy run stores its path and returns its value;
* `runLazyQ_potential` — a potential that no question of a program raises in expectation is a
  supermartingale along the lazy run.

The EncPRF part after `HW`'s opening (`opening_encExact`): the opening's only EncPRF questions are
the 508 bit-`false` whitening pads at the prefix's key `k₁`, so its final state stores exactly the
inputs `0 ⊕ k₁` at every position (`EncExact`), with `k₁` the key the evaluator's prefix reads
there. The designated installation keeps it (`programAllSkip_enc`).
-/

import Proof.Privacy.Phase3.PublicFirst.Stored

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM interceptAnswer whitePadsM)
open Kriterion.ArgoMAC.Phase3.Glue (noRecord)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell consumeCell refillAnswer touch runRefill
  consumeCell_spec AllQ LaneAt runRefillT runRefill_eq_runRefillT runRefillT_bind continueT
  dropTouched evalLaneM_allQ)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Runs of sequences, invariants, stored paths, potentials -/

section Runs

/-- **A refill run of a sequence passes through a run of its first part.** -/
theorem runRefill_bind_mem (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α β : Type}
    (first : FreeQuery Programs.Spec α) (rest : α → FreeQuery Programs.Spec β) (oracle : LState)
    (record : Record) (touched : Set Cell) (outcome : β × LState × Record)
    (member : some outcome ∈ (runRefill bits draw (first >>= rest) oracle record touched).support) :
    ∃ (mid : α × LState × Record) (touchedMid : Set Cell),
      some mid ∈ (runRefill bits draw first oracle record touched).support ∧
        some outcome ∈ (runRefill bits draw (rest mid.1) mid.2.1 mid.2.2 touchedMid).support := by
  rw [runRefill_eq_runRefillT, runRefillT_bind] at member
  obtain ⟨final, finalMember, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  obtain ⟨mid, midMember, restMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp finalMember
  rcases mid with _ | mid
  · simp only [continueT, PMF.mem_support_pure_iff] at restMember
    subst restMember
    simp at same
  · rcases final with _ | final
    · simp at same
    · simp only [Option.map_some, Option.some.injEq] at same
      subst same
      refine ⟨dropTouched mid, mid.2.2.2, ?_, ?_⟩
      · rw [runRefill_eq_runRefillT]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some mid, midMember, rfl⟩
      · rw [runRefill_eq_runRefillT]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some final, restMember, rfl⟩

/-- **An invariant of the refill runner**, for a program all of whose questions satisfy `Q`: it is
kept by the lazy answers and by the programmed (consumed) ones. -/
theorem runRefill_invariant (bits : BitInput) (draw : Cell → PMF (Block × Block))
    (Q : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop) (Inv : LState → Prop)
    (lazyStep : ∀ (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState),
      Q request → Inv state → ∀ answer ∈ (LazyOracle.query request state).support, Inv answer.2)
    (programStep : ∀ (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState)
      (touched : Set Cell) (cell : Cell) (value : Block × Block) (updated : LState),
      Q request → Inv state → consumeCell touched state request = some cell →
        LazyOracle.program request (refillAnswer request value) state = some updated → Inv updated)
    {α : Type} (computation : FreeQuery Programs.Spec α) (holds : AllQ Q computation) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell)
      (outcome : α × LState × Record), Inv oracle →
      some outcome ∈ (runRefill bits draw computation oracle record touched).support →
        Inv outcome.2.1 := by
  induction computation with
  | pure value =>
    intro oracle record touched outcome invariant member
    simp only [runRefill, PMF.mem_support_pure_iff, Option.some.injEq] at member
    subst member
    exact invariant
  | query request next ih =>
    intro oracle record touched outcome invariant member
    simp only [runRefill] at member
    cases intercept : interceptAnswer bits request with
    | some answer =>
      rw [intercept] at member
      exact ih answer (AllQ.tail holds _) _ _ _ _ invariant member
    | none =>
      rw [intercept] at member
      simp only at member
      cases consumed : consumeCell touched oracle request with
      | some cell =>
        rw [consumed] at member
        simp only [PMF.mem_support_bind_iff] at member
        obtain ⟨value, _, rest⟩ := member
        split at rest
        · simp at rest
        · rename_i updated success
          exact ih _ (AllQ.tail holds _) _ _ _ _
            (programStep request oracle touched cell value updated (AllQ.head holds) invariant
              consumed success) rest
      | none =>
        rw [consumed] at member
        simp only [PMF.mem_support_bind_iff] at member
        obtain ⟨answer, answerMember, rest⟩ := member
        exact ih _ (AllQ.tail holds _) _ _ _ _
          (lazyStep request oracle (AllQ.head holds) invariant answer answerMember) rest

/-- **A lazy run stores its path**, grows the state, and returns the path's value. -/
theorem runLazyQ_stores {α : Type} (computation : FreeQuery Programs.Spec α) :
    ∀ (state : LState) (outcome : α × LState), outcome ∈ (runLazyQ computation state).support →
      Grows state outcome.2 ∧ StoredPath outcome.2 computation ∧
        outcome.1 = FreeQuery.eval (answerOf outcome.2) computation := by
  induction computation with
  | pure value =>
    intro state outcome member
    simp only [runLazyQ, PMF.mem_support_pure_iff] at member
    subst member
    exact ⟨Grows.refl _, (fun _ member => by cases member), rfl⟩
  | query request next ih =>
    intro state outcome member
    simp only [runLazyQ, PMF.mem_support_bind_iff] at member
    obtain ⟨answer, answerMember, rest⟩ := member
    obtain ⟨grow, stored, value⟩ := ih answer.1 answer.2 outcome rest
    have head := storedAs_grows grow (query_stores request state answer answerMember)
    have same : answerOf outcome.2 request = answer.1 := answerOf_of_stored head
    refine ⟨(query_grows request state answer answerMember).trans grow,
      storedPath_query.mpr ⟨by rw [same]; exact head, by rw [same]; exact stored⟩, ?_⟩
    show outcome.1 = FreeQuery.eval (answerOf outcome.2) (next (answerOf outcome.2 request))
    rw [same]
    exact value

/-- **A potential no question raises in expectation is a supermartingale along the lazy run.** -/
theorem runLazyQ_potential (Q : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop)
    (potential : LState → ℝ≥0∞)
    (step : ∀ (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState),
      Q request →
        ∑' answer, LazyOracle.query request state answer * potential answer.2 ≤ potential state)
    {α : Type} (computation : FreeQuery Programs.Spec α) (holds : AllQ Q computation) :
    ∀ state : LState,
      ∑' outcome, runLazyQ computation state outcome * potential outcome.2 ≤ potential state := by
  induction computation with
  | pure value =>
    intro state
    simp only [runLazyQ]
    rw [tsum_pure_mul]
  | query request next ih =>
    intro state
    simp only [runLazyQ]
    rw [tsum_bind_mul]
    exact le_trans (ENNReal.tsum_le_tsum fun answer =>
      mul_le_mul' le_rfl (ih answer.1 (AllQ.tail holds _) answer.2))
      (step request state (AllQ.head holds))

end Runs

/-! ### Questions that do not touch the EncPRF part -/

section EncPart

/-- A question that is not an EncPRF question. -/
def EncFree : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward _ _ => True
  | .fixedInverse _ _ => True
  | .encForward _ _ => False
  | .encInverse _ _ => False
  | .hash _ => True

/-- An EncPRF forward question at a given input. -/
def EncInputIs (value : Block) : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward _ _ => False
  | .fixedInverse _ _ => False
  | .encForward _ input => input = value
  | .encInverse _ _ => False
  | .hash _ => False

/-- A lane's question (a fold question or a hash question at a cell input) is not an EncPRF
question. -/
theorem encFree_of_laneAt {lane : Lane}
    {request : PublicQuery FixedIndex EncPRF.PermutationIndex} (inside : ∃ c, LaneAt lane c request) :
    EncFree request := by
  obtain ⟨_, inside⟩ := inside
  cases request with
  | fixedForward _ _ => trivial
  | fixedInverse _ _ => exact inside.elim (fun h => h.elim) (fun h => h.elim)
  | encForward _ _ => exact inside.elim (fun h => h.elim) (fun h => h.elim)
  | encInverse _ _ => exact inside.elim (fun h => h.elim) (fun h => h.elim)
  | hash _ => trivial

/-- A non-EncPRF lazy question keeps the EncPRF part. -/
theorem query_enc_of_encFree (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (free : EncFree request) (state : LState) (answer : request.Answer × LState)
    (member : answer ∈ (LazyOracle.query request state).support) : answer.2.enc = state.enc := by
  cases request with
  | fixedForward index input =>
    obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rfl
  | fixedInverse index output =>
    obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rfl
  | encForward _ _ => exact free.elim
  | encInverse _ _ => exact free.elim
  | hash input =>
    obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rfl

/-- A hash program keeps the EncPRF part. -/
theorem program_hash_enc (input : BaseField) (value : Block × Block) (state updated : LState)
    (success : LazyOracle.program (.hash input) value state = some updated) :
    updated.enc = state.enc := by
  simp only [LazyOracle.program] at success
  split_ifs at success
  cases success
  rfl

/-- **A refill run of a program asking no EncPRF question keeps the EncPRF part.** -/
theorem runRefill_enc_same (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (computation : FreeQuery Programs.Spec α) (free : AllQ EncFree computation) (oracle : LState)
    (record : Record) (touched : Set Cell) (outcome : α × LState × Record)
    (member : some outcome ∈ (runRefill bits draw computation oracle record touched).support) :
    outcome.2.1.enc = oracle.enc :=
  runRefill_invariant bits draw EncFree (fun state => state.enc = oracle.enc)
    (fun request state holds same answer answerMember =>
      (query_enc_of_encFree request holds state answer answerMember).trans same)
    (fun request state _ _ _ updated _ same consumed success => by
      obtain ⟨input, rfl, _⟩ := consumeCell_spec consumed
      exact (program_hash_enc input _ state updated success).trans same)
    computation free oracle record touched outcome rfl member

/-- **The designated installation keeps the EncPRF part.** -/
theorem programAllSkip_enc :
    ∀ (requests : List (Option BaseField × (Block × Block))) (state : LState),
      (programAllSkip requests state).enc = state.enc := by
  intro requests
  induction requests with
  | nil => exact fun state => rfl
  | cons request rest ih =>
    intro state
    obtain ⟨input, answer⟩ := request
    cases input with
    | none => exact ih state
    | some input =>
      show (programAllSkip rest
        ((LazyOracle.program (.hash input) answer state).getD state)).enc = state.enc
      rw [ih]
      cases success : LazyOracle.program (.hash input) answer state with
      | none => rfl
      | some updated => exact program_hash_enc input answer state updated success

/-- A forward sparse query adds at most its own input. -/
theorem forward_new {size : ℕ} (state : SparsePermutation size) (x : Fin size)
    (answer : Fin size × SparsePermutation size)
    (member : answer ∈ (state.forward x).distribution.support) (z : Fin size)
    (found : lk answer.2 z ≠ none) : lk state z ≠ none ∨ z = x := by
  unfold SparsePermutation.forward at member
  dsimp only at member
  split at member
  · simp only [Draw.distribution, PMF.mem_support_pure_iff] at member
    subst member
    exact Or.inl found
  · rename_i fresh
    obtain ⟨rank, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rw [← same] at found
    dsimp only at found
    have freshX : ¬ state.knownInput x := fresh
    have freshY : ¬ state.knownOutput (state.output (state.suffix rank)) := by
      show ¬ (state.output.symm (state.output (state.suffix rank))).val < state.used
      rw [Equiv.symm_apply_apply]
      simp [SparsePermutation.suffix]
    have room : state.used < size := by
      have := (state.input.symm x).isLt
      unfold SparsePermutation.knownInput at freshX
      omega
    have shape := lookup_extend state x (state.output (state.suffix rank)) freshX freshY room z
    rw [Equiv.symm_apply_apply] at shape
    rw [shape] at found
    by_cases same : z = x
    · exact Or.inr same
    · rw [if_neg same] at found
      exact Or.inl found

end EncPart

/-! ### The EncPRF part after the opening -/

section Opening

/-- The EncPRF input of the bit-`bit` pad at the whitening key `first`. -/
abbrev padInput (bit : Bool) (first : Block) : Fin (2 ^ 128) := (encodeBit bit ^^^ first).toFin

theorem padInput_true_ne (first : Block) : padInput true first ≠ padInput false first := by
  intro same
  have blocks : encodeBit true ^^^ first = encodeBit false ^^^ first := BitVec.toFin_inj.mp same
  have cancel := congrArg (· ^^^ first) blocks
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at cancel
  simp [encodeBit] at cancel

/-- **The EncPRF part of a state is exactly the bit-`false` pads at key `w`**: at every position the
stored inputs are exactly `0 ⊕ w`. -/
def EncExact (state : LState) (w : Block) : Prop :=
  ∀ (j : EncPRF.PermutationIndex) (z : Fin (2 ^ 128)), lk (state.enc j) z ≠ none ↔ z = padInput false w

theorem encExact_of_enc {state other : LState} (same : other.enc = state.enc) {w : Block}
    (exact : EncExact state w) : EncExact other w := by
  intro j z
  rw [same]
  exact exact j z

/-- The opening's prefix asks no EncPRF question. -/
theorem curvePrefixM_encFree [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac) :
    AllQ EncFree (curvePrefixM table bits mac) :=
  ((evalLaneM_allQ _ _ _ _ _).mono fun _ inside => encFree_of_laneAt inside).bind fun _ =>
    ((evalLaneM_allQ _ _ _ _ _).mono fun _ inside => encFree_of_laneAt inside).bind fun _ =>
      .query (.hash _) _ trivial fun _ => .pure _

/-- The bit-`bit` pads' questions are at their input. -/
theorem padM_encInput (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    AllQ (EncInputIs (encodeBit bit ^^^ keys.first)) (Programs.padM keys coordinate index bit) := by
  refine AllQ.bind ?_ fun _ => .pure _
  exact .query _ _ rfl fun _ => .pure _

theorem whitePadsM_encInput (keys : WhiteningKeys) :
    AllQ (EncInputIs (encodeBit false ^^^ keys.first)) (whitePadsM keys) :=
  (AllQ.vector fun _ => padM_encInput _ _ _ _).bind fun _ =>
    (AllQ.vector fun _ => padM_encInput _ _ _ _).bind fun _ => .pure _

theorem whitePadsM_notIntercepted (bits : BitInput) (keys : WhiteningKeys) :
    AllQ (NotIntercepted bits) (whitePadsM keys) :=
  (whitePadsM_encInput keys).mono fun request inside => by
    cases request with
    | fixedForward _ _ => exact inside.elim
    | fixedInverse _ _ => exact inside.elim
    | encForward _ _ => rfl
    | encInverse _ _ => exact inside.elim
    | hash _ => exact inside.elim

/-- A pad's question is on the transcript of the whitening pads. -/
theorem whitePad_mem_transcript (answer : ∀ query : PublicQuery FixedIndex EncPRF.PermutationIndex,
    query.Answer) (keys : WhiteningKeys) (j : EncPRF.PermutationIndex) :
    ⟨.encForward j (encodeBit false ^^^ keys.first),
        answer (.encForward j (encodeBit false ^^^ keys.first))⟩ ∈
      transcript answer (whitePadsM keys) := by
  obtain ⟨coordinate, index⟩ := j
  have single : ∀ c : EncPRF.Coordinate,
      (⟨.encForward (c, index) (encodeBit false ^^^ keys.first),
        answer (.encForward (c, index) (encodeBit false ^^^ keys.first))⟩ :
          Entry FixedIndex EncPRF.PermutationIndex) ∈
        transcript answer (Programs.padM keys c index false) := by
    intro c
    exact List.mem_cons_self
  cases coordinate with
  | x =>
    exact mem_transcript_left answer
      (mem_transcript_vector answer coordinateBitCount _ index (single .x))
  | y =>
    exact mem_transcript_right answer (mem_transcript_left answer
      (mem_transcript_vector answer coordinateBitCount _ index (single .y)))

/-- A stored EncPRF question is a known input. -/
theorem enc_ne_none_of_stored {state : LState} {j : EncPRF.PermutationIndex} {input answer : Block}
    (stored : StoredAs state ⟨.encForward j input, answer⟩) : lk (state.enc j) input.toFin ≠ none := by
  change (lk (state.enc j) input.toFin).map BitVec.ofFin = some answer at stored
  intro missing
  rw [missing] at stored
  cases stored

/-- **The whitening pads, run from an empty EncPRF part, leave it exact.** -/
theorem whitePads_encExact (bits : BitInput) (draw : Cell → PMF (Block × Block))
    (keys : WhiteningKeys) (oracle : LState) (empty : ∀ j z, lk (oracle.enc j) z = none)
    (record : Record) (touched : Set Cell)
    (outcome : (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) × LState × Record)
    (member : some outcome ∈ (runRefill bits draw (whitePadsM keys) oracle record touched).support) :
    EncExact outcome.2.1 keys.first := by
  have only := runRefill_invariant bits draw (EncInputIs (encodeBit false ^^^ keys.first))
    (fun state => ∀ j z, lk (state.enc j) z ≠ none → z = padInput false keys.first)
    (fun request state holds invariant answer answerMember => by
      cases request with
      | fixedForward _ _ => exact holds.elim
      | fixedInverse _ _ => exact holds.elim
      | encInverse _ _ => exact holds.elim
      | hash _ => exact holds.elim
      | encForward index input =>
        change input = encodeBit false ^^^ keys.first at holds
        subst holds
        obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        intro j z found
        by_cases same : j = index
        · subst same
          simp only [Function.update_self] at found
          rcases forward_new _ _ drawn drawnMember z found with old | new
          · exact invariant j z old
          · exact new
        · simp only [Function.update_of_ne same] at found
          exact invariant j z found)
    (fun request state touched cell value updated holds _ consumed _ => by
      obtain ⟨input, rfl, _⟩ := consumeCell_spec consumed
      exact holds.elim)
    (whitePadsM keys) (whitePadsM_encInput keys) oracle record touched outcome
    (fun j z found => absurd (empty j z) found) member
  have stored := (runRefill_storedPath bits draw (whitePadsM keys)
    (whitePadsM_notIntercepted bits keys) oracle record touched outcome member).1
  intro j z
  constructor
  · exact only j z
  · rintro rfl
    exact enc_ne_none_of_stored (stored _ (whitePad_mem_transcript _ keys j))

/-- **After `HW`'s opening, the EncPRF part is exactly the bit-`false` pads at the prefix's key.** -/
theorem opening_encExact [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac)
    (draw : Cell → PMF (Block × Block))
    (outcome : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)
    (member : some outcome ∈ (runRefill bits draw (openingQueriesM table bits mac) LazyOracle.empty
      noRecord ∅).support) :
    EncExact outcome.2.1 (prefixKeysOn outcome.2.1 table bits mac).1 := by
  rw [openingQueriesM_eq_prefix] at member
  obtain ⟨mid, touchedMid, midMember, restMember⟩ :=
    runRefill_bind_mem bits draw _ _ _ _ _ _ member
  obtain ⟨mid2, touchedMid2, mid2Member, lastMember⟩ :=
    runRefill_bind_mem bits draw _ _ _ _ _ _ restMember
  -- the prefix keeps the EncPRF part empty and stores its keys
  have prefixEnc : mid.2.1.enc = (LazyOracle.empty : LState).enc :=
    runRefill_enc_same bits draw _ (curvePrefixM_encFree table bits mac) _ _ _ _ midMember
  obtain ⟨prefixStored, prefixValue⟩ := runRefill_storedPath bits draw _
    (curvePrefixM_notIntercepted table bits mac) _ _ _ _ midMember
  -- the pads
  have padsExact : EncExact mid2.2.1 mid.1.1 :=
    whitePads_encExact bits draw ⟨mid.1.1, mid.1.2⟩ mid.2.1
      (fun j z => by rw [prefixEnc]; rfl) mid.2.2 touchedMid mid2 mid2Member
  -- the point lanes keep the EncPRF part
  have lanesFree : AllQ EncFree
      (Programs.evalLaneM .pointX table.pointXHot
          (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
          (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf mid2.1 mac) .x)
        >>= fun pointX =>
      Programs.evalLaneM .pointY table.pointYHot
          (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
          (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf mid2.1 mac) .y)
        >>= fun pointY => pure (pointX, pointY)) :=
    ((evalLaneM_allQ _ _ _ _ _).mono fun _ inside => encFree_of_laneAt inside).bind fun _ =>
      ((evalLaneM_allQ _ _ _ _ _).mono fun _ inside => encFree_of_laneAt inside).bind fun _ =>
        .pure _
  have lastEnc : outcome.2.1.enc = mid2.2.1.enc :=
    runRefill_enc_same bits draw _ lanesFree _ _ _ _ lastMember
  -- the keys the final state reads are the prefix's
  have grow : Grows mid.2.1 outcome.2.1 := runRefill_grows _ _ _ _ _ _ _ restMember
  have keysSame : prefixKeysOn outcome.2.1 table bits mac = prefixKeysOn mid.2.1 table bits mac :=
    (storedPath_grows _ grow prefixStored).2
  have valueKeys : mid.1 = prefixKeysOn mid.2.1 table bits mac := prefixValue
  rw [keysSame, ← valueKeys]
  exact encExact_of_enc lastEnc padsExact

end Opening

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
