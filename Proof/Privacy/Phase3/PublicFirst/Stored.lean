/-
**Phase 3, P1i — stored paths: a run stores the path it takes, and a re-run of a stored path is
deterministic.**

`StoredPath state P`: every question on `P`'s path, read from `state` (`answerOf`), is stored in
`state` with that answer. It survives growth, with the same value (`storedPath_grows`), and on it a
lazy re-run of `P` returns `P`'s value without sampling or changing the state
(`runLazyQ_storedPath`).

`runRefill_storedPath`: P4's refill run of a program none of whose questions is intercepted ends
in a state that stores its path, and returns the path's value. With `openingQueriesM_eq_prefix`,
after `HW`'s opening the evaluator's prefix (system A and the bridge hash) is stored
(`opening_stores_prefix`), so the on-curve shadow's re-run of the prefix reads the opening's keys.
-/

import Proof.Privacy.Phase3.PublicFirst.Shadow
import Proof.Privacy.Phase3.PublicFirst.Probe
import Proof.Privacy.Phase3.Lazy.RunBind
import Proof.Privacy.Phase3.Lazy.Decompose

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM interceptAnswer)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell consumeCell refillAnswer touch runRefill
  consumeCell_spec AllQ program_hash_refill)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Stored questions -/

/-- A question stored in a state with this answer. -/
def StoredAs (state : LState) (entry : Entry FixedIndex EncPRF.PermutationIndex) : Prop :=
  LazyOracle.lookup entry.1 state = some entry.2

/-- A stored question is read back by `answerOf`. -/
theorem answerOf_of_stored {state : LState} {request : PublicQuery FixedIndex EncPRF.PermutationIndex}
    {answer : request.Answer} (stored : StoredAs state ⟨request, answer⟩) :
    answerOf state request = answer := by
  cases request <;> simp only [StoredAs] at stored <;> simp only [answerOf, stored] <;> rfl

/-- **Stored questions survive growth.** -/
theorem storedAs_grows {state later : LState} (grow : Grows state later)
    {entry : Entry FixedIndex EncPRF.PermutationIndex} (stored : StoredAs state entry) :
    StoredAs later entry := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index input =>
    change (lk (state.fixed index) input.toFin).map BitVec.ofFin = some answer at stored
    change (lk (later.fixed index) input.toFin).map BitVec.ofFin = some answer
    cases found : lk (state.fixed index) input.toFin with
    | none => rw [found] at stored; cases stored
    | some y => rw [grow.fixed index _ y found]; rw [found] at stored; exact stored
  | fixedInverse index output =>
    change (lk (state.fixed index).reverse output.toFin).map BitVec.ofFin = some answer at stored
    change (lk (later.fixed index).reverse output.toFin).map BitVec.ofFin = some answer
    cases found : lk (state.fixed index).reverse output.toFin with
    | none => rw [found] at stored; cases stored
    | some x =>
      rw [(lookup_reverse _ x _).mpr (grow.fixed index x _ ((lookup_reverse _ x _).mp found))]
      rw [found] at stored
      exact stored
  | encForward index input =>
    change (lk (state.enc index) input.toFin).map BitVec.ofFin = some answer at stored
    change (lk (later.enc index) input.toFin).map BitVec.ofFin = some answer
    cases found : lk (state.enc index) input.toFin with
    | none => rw [found] at stored; cases stored
    | some y => rw [grow.enc index _ y found]; rw [found] at stored; exact stored
  | encInverse index output =>
    change (lk (state.enc index).reverse output.toFin).map BitVec.ofFin = some answer at stored
    change (lk (later.enc index).reverse output.toFin).map BitVec.ofFin = some answer
    cases found : lk (state.enc index).reverse output.toFin with
    | none => rw [found] at stored; cases stored
    | some x =>
      rw [(lookup_reverse _ x _).mpr (grow.enc index x _ ((lookup_reverse _ x _).mp found))]
      rw [found] at stored
      exact stored
  | hash input =>
    simp only [StoredAs, LazyOracle.lookup] at stored ⊢
    cases found : state.hash.lookup input with
    | none => rw [found] at stored; cases stored
    | some v => rw [grow.hash input v found]; rw [found] at stored; exact stored

/-- An inverse question at a stored output returns its input without sampling. -/
theorem inverse_of_reverse_lookup {n : ℕ} (s : SparsePermutation n) (y x : Fin n)
    (found : lk s.reverse y = some x) : s.inverse y = Draw.pure (x, s) := by
  rw [lk_eq] at found
  split at found
  · rename_i known
    cases found
    unfold SparsePermutation.inverse
    dsimp only
    split
    · rfl
    · rename_i unknown
      exact absurd known unknown
  · cases found

/-- **A stored question is answered without sampling.** -/
theorem query_of_stored {state : LState} {request : PublicQuery FixedIndex EncPRF.PermutationIndex}
    {answer : request.Answer} (stored : StoredAs state ⟨request, answer⟩) :
    LazyOracle.query request state = PMF.pure (answer, state) := by
  cases request with
  | fixedForward index input =>
    change (lk (state.fixed index) input.toFin).map BitVec.ofFin = some answer at stored
    cases found : lk (state.fixed index) input.toFin with
    | none => rw [found] at stored; cases stored
    | some y =>
      rw [found] at stored
      have same : BitVec.ofFin y = answer := Option.some.inj stored
      subst same
      exact query_fixedForward_stored state index input (BitVec.ofFin y)
        (by rw [BitVec.toFin_ofFin]; exact found)
  | fixedInverse index output =>
    change (lk (state.fixed index).reverse output.toFin).map BitVec.ofFin = some answer at stored
    cases found : lk (state.fixed index).reverse output.toFin with
    | none => rw [found] at stored; cases stored
    | some x =>
      rw [found] at stored
      have same : BitVec.ofFin x = answer := Option.some.inj stored
      subst same
      show ((state.fixed index).inverse output.toFin).distribution.map (fun answer =>
        (BitVec.ofFin answer.1, { state with fixed := Function.update state.fixed index answer.2 }))
          = _
      rw [inverse_of_reverse_lookup _ _ _ found]
      simp only [Draw.distribution, PMF.pure_map, Function.update_eq_self]
      rfl
  | encForward index input =>
    change (lk (state.enc index) input.toFin).map BitVec.ofFin = some answer at stored
    cases found : lk (state.enc index) input.toFin with
    | none => rw [found] at stored; cases stored
    | some y =>
      rw [found] at stored
      have same : BitVec.ofFin y = answer := Option.some.inj stored
      subst same
      show ((state.enc index).forward input.toFin).distribution.map (fun answer =>
        (BitVec.ofFin answer.1, { state with enc := Function.update state.enc index answer.2 })) = _
      rw [LazyOracle.lookup_forward (state.enc index) input.toFin y found]
      simp only [Draw.distribution, PMF.pure_map, Function.update_eq_self]
      rfl
  | encInverse index output =>
    change (lk (state.enc index).reverse output.toFin).map BitVec.ofFin = some answer at stored
    cases found : lk (state.enc index).reverse output.toFin with
    | none => rw [found] at stored; cases stored
    | some x =>
      rw [found] at stored
      have same : BitVec.ofFin x = answer := Option.some.inj stored
      subst same
      show ((state.enc index).inverse output.toFin).distribution.map (fun answer =>
        (BitVec.ofFin answer.1, { state with enc := Function.update state.enc index answer.2 })) = _
      rw [inverse_of_reverse_lookup _ _ _ found]
      simp only [Draw.distribution, PMF.pure_map, Function.update_eq_self]
      rfl
  | hash input =>
    simp only [StoredAs, LazyOracle.lookup] at stored
    cases found : state.hash.lookup input with
    | none => rw [found] at stored; cases stored
    | some v =>
      rw [found] at stored
      have same := Option.some.inj stored
      subst same
      simp only [LazyOracle.query, HashTable.query, found, Draw.distribution, PMF.pure_map]

/-- A hash query stores the value it returns. -/
theorem hash_query_records {n : ℕ} (positive : 0 < n) (table : HashTable BN254.BaseField n)
    (key : BN254.BaseField) (answer : Fin n × HashTable BN254.BaseField n)
    (member : answer ∈ (table.query positive key).distribution.support) :
    answer.2.lookup key = some answer.1 := by
  unfold HashTable.query at member
  split at member
  · rename_i value found
    simp only [Draw.distribution, PMF.mem_support_pure_iff] at member
    subst member
    exact found
  · obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rw [← same]
    simp [List.lookup]

/-- **A lazy question stores the pair it returns.** -/
theorem query_stores (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState)
    (outcome : request.Answer × LState)
    (member : outcome ∈ (LazyOracle.query request state).support) :
    StoredAs outcome.2 ⟨request, outcome.1⟩ := by
  cases request with
  | fixedForward index input =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    change Option.map (fun y => (BitVec.ofFin y : Block))
      (LazyOracle.permutationLookup ((Function.update state.fixed index answer.2) index)
        input.toFin) =
        some (BitVec.ofFin answer.1)
    rw [Function.update_self, LazyOracle.forward_lookup _ _ answer answerMember]
    rfl
  | fixedInverse index output =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    change Option.map (fun y => (BitVec.ofFin y : Block))
      (lk ((Function.update state.fixed index answer.2) index).reverse output.toFin) =
        some (BitVec.ofFin answer.1)
    rw [Function.update_self,
      (lookup_reverse _ answer.1 output.toFin).mpr (inverse_records _ _ answer answerMember)]
    rfl
  | encForward index input =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    change Option.map (fun y => (BitVec.ofFin y : Block))
      (LazyOracle.permutationLookup ((Function.update state.enc index answer.2) index)
        input.toFin) =
        some (BitVec.ofFin answer.1)
    rw [Function.update_self, LazyOracle.forward_lookup _ _ answer answerMember]
    rfl
  | encInverse index output =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    change Option.map (fun y => (BitVec.ofFin y : Block))
      (lk ((Function.update state.enc index answer.2) index).reverse output.toFin) =
        some (BitVec.ofFin answer.1)
    rw [Function.update_self,
      (lookup_reverse _ answer.1 output.toFin).mpr (inverse_records _ _ answer answerMember)]
    rfl
  | hash input =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    simp only [StoredAs, LazyOracle.lookup]
    rw [hash_query_records _ state.hash input answer answerMember]
    rfl

/-! ### Stored paths -/

/-- **Every question on `P`'s path, read from `state`, is stored there.** -/
def StoredPath {α : Type} (state : LState) (computation : FreeQuery Programs.Spec α) : Prop :=
  ∀ entry ∈ transcript (answerOf state) computation, StoredAs state entry

theorem storedPath_query {α : Type} {state : LState}
    {request : PublicQuery FixedIndex EncPRF.PermutationIndex}
    {next : request.Answer → FreeQuery Programs.Spec α} :
    StoredPath state (.query request next) ↔
      StoredAs state ⟨request, answerOf state request⟩ ∧
        StoredPath state (next (answerOf state request)) := by
  constructor
  · intro stored
    exact ⟨stored _ List.mem_cons_self, fun entry member => stored entry (List.mem_cons_of_mem _ member)⟩
  · rintro ⟨head, rest⟩ entry member
    rcases List.mem_cons.mp member with same | member
    · subst same
      exact head
    · exact rest entry member

/-- **A stored path survives growth, with the same value.** -/
theorem storedPath_grows {α : Type} (computation : FreeQuery Programs.Spec α) :
    ∀ {state later : LState}, Grows state later → StoredPath state computation →
      StoredPath later computation ∧
        FreeQuery.eval (answerOf later) computation = FreeQuery.eval (answerOf state) computation := by
  induction computation with
  | pure value => exact fun _ _ => ⟨(fun _ member => by cases member), rfl⟩
  | query request next ih =>
    intro state later grow stored
    obtain ⟨head, rest⟩ := storedPath_query.mp stored
    have headLater := storedAs_grows grow head
    have same : answerOf later request = answerOf state request := answerOf_of_stored headLater
    obtain ⟨restLater, value⟩ := ih (answerOf state request) grow rest
    refine ⟨storedPath_query.mpr ⟨by rw [same]; exact headLater, by rw [same]; exact restLater⟩, ?_⟩
    show FreeQuery.eval (answerOf later) (next (answerOf later request)) =
      FreeQuery.eval (answerOf state) (next (answerOf state request))
    rw [same, value]

/-- **A lazy re-run of a stored path returns its value and changes nothing.** -/
theorem runLazyQ_storedPath {α : Type} (computation : FreeQuery Programs.Spec α) (state : LState)
    (stored : StoredPath state computation) :
    runLazyQ computation state = PMF.pure (FreeQuery.eval (answerOf state) computation, state) :=
  runLazyQ_of_stored (answerOf state) computation state fun entry member =>
    query_of_stored (stored entry member)

/-! ### A refill run stores its path -/

/-- A question the refill run does not intercept. -/
def NotIntercepted (bits : BitInput) (request : PublicQuery FixedIndex EncPRF.PermutationIndex) :
    Prop :=
  interceptAnswer bits request = none

/-- **P4's refill run of an intercept-free program stores its path**, and returns its value. -/
theorem runRefill_storedPath (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (computation : FreeQuery Programs.Spec α) (free : AllQ (NotIntercepted bits) computation) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell) (outcome : α × LState × Record),
      some outcome ∈ (runRefill bits draw computation oracle record touched).support →
        StoredPath outcome.2.1 computation ∧
          outcome.1 = FreeQuery.eval (answerOf outcome.2.1) computation := by
  induction computation with
  | pure value =>
    intro oracle record touched outcome member
    simp only [runRefill, PMF.mem_support_pure_iff, Option.some.injEq] at member
    subst member
    exact ⟨(fun _ member => by cases member), rfl⟩
  | query request next ih =>
    intro oracle record touched outcome member
    have notIntercepted : interceptAnswer bits request = none := AllQ.head free
    simp only [runRefill] at member
    rw [notIntercepted] at member
    simp only at member
    -- the answer the run got at this question, and the state it stored it in
    have step : ∃ (answer : request.Answer) (updated : LState),
        StoredAs updated ⟨request, answer⟩ ∧ Grows updated outcome.2.1 ∧
          (StoredPath outcome.2.1 (next answer) ∧
            outcome.1 = FreeQuery.eval (answerOf outcome.2.1) (next answer)) := by
      cases consumed : consumeCell touched oracle request with
      | some cell =>
        rw [consumed] at member
        obtain ⟨input, rfl, _, fresh, _⟩ := consumeCell_spec consumed
        simp only [PMF.mem_support_bind_iff] at member
        obtain ⟨value, _, rest⟩ := member
        split at rest
        · simp at rest
        · rename_i updated success
          refine ⟨refillAnswer (.hash input) value, updated, ?_,
            runRefill_grows _ _ _ _ _ _ _ rest, ih _ (AllQ.tail free _) _ _ _ _ rest⟩
          rw [program_hash_refill, if_pos fresh] at success
          cases success
          show ((oracle.hash.program input (Fintype.equivFin (Block × Block) value)).lookup
            input).map (Fintype.equivFin (Block × Block)).symm = some value
          rw [HashTable.program_lookup, Function.update_self, Option.map_some,
            Equiv.symm_apply_apply]
      | none =>
        rw [consumed] at member
        simp only [PMF.mem_support_bind_iff] at member
        obtain ⟨answer, answerMember, rest⟩ := member
        refine ⟨answer.1, answer.2, ?_, runRefill_grows _ _ _ _ _ _ _ rest,
          ih _ (AllQ.tail free _) _ _ _ _ rest⟩
        exact query_stores request oracle answer answerMember
    obtain ⟨answer, updated, head, grow, restStored, value⟩ := step
    have headFinal := storedAs_grows grow head
    have same : answerOf outcome.2.1 request = answer := answerOf_of_stored headFinal
    refine ⟨storedPath_query.mpr ⟨by rw [same]; exact headFinal, by rw [same]; exact restStored⟩, ?_⟩
    show outcome.1 = FreeQuery.eval (answerOf outcome.2.1) (next (answerOf outcome.2.1 request))
    rw [same]
    exact value

/-! ### The opening stores the evaluator's prefix -/

section Prefix

variable [FieldCertificate]

open Kriterion.ArgoMAC.Phase3.Lazy (LaneAt evalLaneM_allQ cellAt_unique designated_cellAt
  bridgeInput_not_cellAt interceptAnswer_plain runRefillT runRefill_eq_runRefillT runRefillT_bind
  continueT dropTouched)

/-- A system-A question is never intercepted: its fold questions are fixed-key, and its hash
questions are at `curveX`/`curveY` cell inputs, never at a designated (`pointX`) input. -/
theorem curve_notIntercepted (bits : BitInput) (lane : Lane) (curve : lane = .curveX ∨ lane = .curveY)
    (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (inside : ∃ c, LaneAt lane c request) : NotIntercepted bits request := by
  obtain ⟨c, inside⟩ := inside
  cases request with
  | fixedForward _ _ => rfl
  | fixedInverse _ _ => exact inside.elim (fun h => h.elim) (fun h => h.elim)
  | encForward _ _ => exact inside.elim (fun h => h.elim) (fun h => h.elim)
  | encInverse _ _ => exact inside.elim (fun h => h.elim) (fun h => h.elim)
  | hash input =>
    rcases inside with fixed | cellAt
    · exact fixed.elim
    · refine interceptAnswer_plain bits fun designated => ?_
      have same := (cellAt_unique (designated_cellAt designated) cellAt).1
      rcases curve with rfl | rfl <;> cases same

/-- **The evaluator's prefix is never intercepted** (the bridge input is no cell input). -/
theorem curvePrefixM_notIntercepted (table : Public) (bits : BitInput) (mac : InputMac) :
    AllQ (NotIntercepted bits) (curvePrefixM table bits mac) :=
  ((evalLaneM_allQ _ _ _ _ _).mono (curve_notIntercepted bits .curveX (Or.inl rfl))).bind
    fun _ => ((evalLaneM_allQ _ _ _ _ _).mono (curve_notIntercepted bits .curveY
      (Or.inr rfl))).bind fun _ => .query (.hash _) _
        (interceptAnswer_plain bits fun designated =>
          bridgeInput_not_cellAt _ _ _ (designated_cellAt designated)) fun _ => .pure _

/-- **After a refill run of a program that starts with an intercept-free part, the final state
stores that part's path.** -/
theorem runRefill_bind_stores (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α β : Type}
    (first : FreeQuery Programs.Spec α) (free : AllQ (NotIntercepted bits) first)
    (rest : α → FreeQuery Programs.Spec β) (oracle : LState) (record : Record)
    (touched : Set Cell) (outcome : β × LState × Record)
    (member : some outcome ∈ (runRefill bits draw (first >>= rest) oracle record touched).support) :
    StoredPath outcome.2.1 first := by
  rw [runRefill_eq_runRefillT, runRefillT_bind] at member
  obtain ⟨final, finalMember, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  obtain ⟨mid, midMember, restMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp finalMember
  rcases mid with _ | mid
  · simp [continueT] at restMember
    rcases final with _ | final
    · cases same
    · simp at restMember
  · rcases final with _ | final
    · cases same
    · simp only [Option.map_some, Option.some.injEq] at same
      subst same
      have midRun : some (dropTouched mid) ∈
          (runRefill bits draw first oracle record touched).support := by
        rw [runRefill_eq_runRefillT]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some mid, midMember, rfl⟩
      have stored := (runRefill_storedPath bits draw first free oracle record touched _ midRun).1
      have restRun : some (dropTouched final) ∈ (runRefill bits draw (rest mid.1) mid.2.1
          mid.2.2.1 mid.2.2.2).support := by
        rw [runRefill_eq_runRefillT]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some final, restMember, rfl⟩
      exact (storedPath_grows first (runRefill_grows _ _ _ _ _ _ _ restRun) stored).1

/-- **After `HW`'s opening, the evaluator's prefix is stored.** -/
theorem opening_stores_prefix (table : Public) (bits : BitInput) (mac : InputMac)
    (draw : Cell → PMF (Block × Block)) (oracle : LState) (record : Record) (touched : Set Cell)
    (outcome : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)
    (member : some outcome ∈
      (runRefill bits draw (openingQueriesM table bits mac) oracle record touched).support) :
    StoredPath outcome.2.1 (curvePrefixM table bits mac) := by
  rw [openingQueriesM_eq_prefix] at member
  exact runRefill_bind_stores bits draw _ (curvePrefixM_notIntercepted table bits mac) _ oracle
    record touched outcome member

/-- **On a state storing the prefix, the on-curve shadow reads the stored keys**: its re-run of the
prefix samples nothing, and it continues with the bit-`true` pads at `prefixKeysOn`. -/
theorem shadowOnM_run [GroupCertificate] (table : Public) (bits : BitInput) (mac : InputMac)
    (state : LState) (stored : StoredPath state (curvePrefixM table bits mac)) :
    runLazyQ (shadowOnM table bits mac) state =
      runLazyQ (truePadsM ⟨(prefixKeysOn state table bits mac).1,
          (prefixKeysOn state table bits mac).2⟩ >>= fun _ =>
        Programs.onCurveM table bits mac >>= fun _ => pure ()) state := by
  unfold shadowOnM
  rw [runLazyQ_bind, runLazyQ_storedPath _ state stored, PMF.pure_bind]
  rfl

end Prefix

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
