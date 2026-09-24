/-
**Phase 3, P1m — (B1) tools: where the pairs of a run come from.**

* `refillAns bits state` — the answers along a refill run's path: an intercepted (designated)
  question gets its interception, every other one its stored answer.
* `Fresh bits used c` — along every path of `c`, the consumed cells (`consumedCell`: a
  non-designated hash question at a cell input) are pairwise distinct and avoid `used`. Closed
  under `bind` (with cell sets), `FreeQuery.vector` (pairwise disjoint cell sets), `ite`.
* **`runRefill_describe`** — P4's refill run of a forward-only `Fresh` program on a tape, from a
  state whose cells off `used` are untouched with no stored input (`CellsFree`): the value is the
  program along `refillAns`, every non-intercepted question on the path is stored, every fixed-key
  pair of the final state is old or the pair of a question on the path, every hash key is old or
  asked on the path, **a consumed cell's question reads the tape** (`Described.tape`), and every
  new record is a designated question's label on the path.
* **`runLazyQ_provenance`** — the lazy runner of a forward-only program: every new fixed-key pair
  and hash key of the final state is asked on its path (read from the final state).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsEnc

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (interceptAnswer recordAfter IsDesignated designatedInput)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request runRefill AllQ consumeCell
  consumeHash refillAnswer consumeCell_spec touch cellOf cellOf_spec cellOf_cellInput cellInput
  cellInput_injective queriesAlong consumedCell interceptAnswer_designated interceptAnswer_plain
  program_hash_eq program_hash_refill)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Paths along an answer function -/

section Paths

theorem mem_queriesAlong_allQ {P : Request → Prop} {α : Type}
    (answer : (request : Request) → request.Answer) {c : FreeQuery Programs.Spec α}
    (holds : AllQ P c) : ∀ r ∈ queriesAlong answer c, P r := by
  induction holds with
  | pure value => exact fun _ member => by cases member
  | query request next here _ ih =>
    intro r member
    rcases List.mem_cons.mp member with rfl | member
    · exact here
    · exact ih _ r member

/-- **Two answer functions agreeing along one's path give the same path and value.** -/
theorem queriesAlong_congr {α : Type} (answer other : (request : Request) → request.Answer)
    (c : FreeQuery Programs.Spec α)
    (agree : ∀ r ∈ queriesAlong answer c, other r = answer r) :
    queriesAlong other c = queriesAlong answer c ∧
      FreeQuery.eval other c = FreeQuery.eval answer c := by
  induction c with
  | pure value => exact ⟨rfl, rfl⟩
  | query request next ih =>
    have head : other request = answer request := agree request List.mem_cons_self
    have rest := ih (answer request) fun r member => agree r (List.mem_cons_of_mem _ member)
    refine ⟨?_, ?_⟩
    · show request :: queriesAlong other (next (other request)) =
        request :: queriesAlong answer (next (answer request))
      rw [head, rest.1]
    · show FreeQuery.eval other (next (other request)) = FreeQuery.eval answer (next (answer request))
      rw [head, rest.2]

end Paths

/-! ### The refill run's answers -/

section Answers

/-- **The answers along a refill run's path**: the interception where there is one, else the
stored answer. -/
def refillAns (bits : BitInput) (state : LState) (request : Request) : request.Answer :=
  match interceptAnswer bits request with
  | some answer => answer
  | none => answerOf state request

theorem refillAns_intercept {bits : BitInput} {state : LState} {request : Request}
    {answer : request.Answer} (intercept : interceptAnswer bits request = some answer) :
    refillAns bits state request = answer := by
  unfold refillAns
  rw [intercept]

theorem refillAns_plain {bits : BitInput} {state : LState} {request : Request}
    (intercept : interceptAnswer bits request = none) :
    refillAns bits state request = answerOf state request := by
  unfold refillAns
  rw [intercept]

end Answers

/-! ### Fresh programs -/

section Fresh

/-- The consumed cell of a request lies in `S`. -/
def InCells (bits : BitInput) (S : Set Cell) (request : Request) : Prop :=
  ∀ cell, consumedCell bits request = some cell → cell ∈ S

/-- **Along every path, the consumed cells are distinct and avoid `used`.** -/
inductive Fresh (bits : BitInput) {α : Type} : Set Cell → FreeQuery Programs.Spec α → Prop
  | pure (used : Set Cell) (value : α) : Fresh bits used (.pure value)
  | query (used : Set Cell) (request : Request)
      (next : request.Answer → FreeQuery Programs.Spec α) :
      (∀ cell, consumedCell bits request = some cell → cell ∉ used) →
      (∀ answer, Fresh bits (used ∪ {cell | consumedCell bits request = some cell}) (next answer)) →
      Fresh bits used (.query request next)

namespace Fresh

variable {bits : BitInput} {α β : Type}

theorem mono {used : Set Cell} {c : FreeQuery Programs.Spec α} (fresh : Fresh bits used c) :
    ∀ {smaller : Set Cell}, smaller ⊆ used → Fresh bits smaller c := by
  induction fresh with
  | pure used value => exact fun _ => .pure _ value
  | query used request next avoid _ ih =>
    intro smaller sub
    refine .query smaller request next (fun i hi inside => avoid i hi (sub inside)) fun answer => ?_
    exact ih answer (Set.union_subset_union_left _ sub)

theorem tail {used : Set Cell} {request : Request}
    {next : request.Answer → FreeQuery Programs.Spec α} (fresh : Fresh bits used (.query request next))
    (answer : request.Answer) :
    Fresh bits (used ∪ {cell | consumedCell bits request = some cell}) (next answer) := by
  cases fresh with
  | query _ _ _ _ rest => exact rest answer

theorem head {used : Set Cell} {request : Request}
    {next : request.Answer → FreeQuery Programs.Spec α} (fresh : Fresh bits used (.query request next)) :
    ∀ cell, consumedCell bits request = some cell → cell ∉ used := by
  cases fresh with
  | query _ _ _ avoid _ => exact avoid

/-- **A sequence of fresh programs with disjoint cell sets is fresh.** -/
theorem bind {S : Set Cell} {c : FreeQuery Programs.Spec α} {used : Set Cell}
    (first : Fresh bits used c) (inside : AllQ (InCells bits S) c)
    {f : α → FreeQuery Programs.Spec β} (rest : ∀ value, Fresh bits (used ∪ S) (f value)) :
    Fresh bits used (c >>= f) := by
  induction first with
  | pure used value => exact (rest value).mono Set.subset_union_left
  | query used request next avoid _ ih =>
    refine .query used request _ avoid fun answer => ?_
    refine ih answer (AllQ.tail inside answer) fun value => (rest value).mono ?_
    intro i member
    rcases member with (member | member) | member
    · exact Or.inl member
    · exact Or.inr (AllQ.head inside i member)
    · exact Or.inr member

/-- A fresh program stays fresh against cells outside its cell set. -/
theorem union_disjoint {S : Set Cell} {c : FreeQuery Programs.Spec α} {used : Set Cell}
    (fresh : Fresh bits used c) (inside : AllQ (InCells bits S) c) {U : Set Cell}
    (disjoint : ∀ i ∈ S, i ∉ U) : Fresh bits (used ∪ U) c := by
  induction fresh with
  | pure used value => exact .pure _ value
  | query used request next avoid _ ih =>
    refine .query _ request next (fun i hi member => ?_) fun answer => ?_
    · rcases member with member | member
      · exact avoid i hi member
      · exact disjoint i (AllQ.head inside i hi) member
    · refine (ih answer (AllQ.tail inside answer)).mono ?_
      intro i member
      rcases member with (member | member) | member
      · exact Or.inl (Or.inl member)
      · exact Or.inr member
      · exact Or.inl (Or.inr member)

/-- A program consuming nothing is fresh. -/
theorem of_none {c : FreeQuery Programs.Spec α}
    (holds : AllQ (fun request => consumedCell bits request = none) c) :
    ∀ used, Fresh bits used c := by
  induction holds with
  | pure value => exact fun used => .pure used value
  | query request next here _ ih =>
    intro used
    refine .query used request next (fun i hi => by rw [here] at hi; cases hi) fun answer => ?_
    exact ih answer _

theorem ite {condition : Prop} [Decidable condition] {first second : FreeQuery Programs.Spec α}
    {used : Set Cell} (yes : Fresh bits used first) (no : Fresh bits used second) :
    Fresh bits used (if condition then first else second) := by
  split
  · exact yes
  · exact no

/-- **A loop of fresh programs with pairwise disjoint cell sets is fresh.** -/
theorem vector {count : ℕ} {program : Fin count → FreeQuery Programs.Spec α}
    (S : Fin count → Set Cell) (each : ∀ index, Fresh bits ∅ (program index))
    (inside : ∀ index, AllQ (InCells bits (S index)) (program index))
    (disjoint : ∀ index index', index ≠ index' → ∀ i ∈ S index, i ∉ S index') :
    ∀ (used : Set Cell), (∀ index, ∀ i ∈ S index, i ∉ used) →
      Fresh bits used (FreeQuery.vector count program) := by
  induction count with
  | zero => exact fun used _ => .pure _ _
  | succ count ih =>
    intro used avoid
    show Fresh bits used (FreeQuery.vector count (fun index => program index.castSucc) >>=
      fun values => program (Fin.last count) >>= fun value => Pure.pure (values.push value))
    refine bind (S := {i | ∃ index : Fin count, i ∈ S index.castSucc})
      (ih (fun index => S index.castSucc) (fun index => each _) (fun index => inside _)
        (fun a b ne => disjoint _ _ (fun same => ne (Fin.castSucc_injective _ same)))
        used (fun index => avoid _))
      (AllQ.vector fun index => (inside index.castSucc).mono fun r holds i hi =>
        ⟨index, holds i hi⟩) fun values => ?_
    refine bind (S := S (Fin.last count)) ?_ (inside _) fun value => .pure _ _
    have base := union_disjoint (each (Fin.last count)) (inside _)
      (U := used ∪ {i | ∃ index : Fin count, i ∈ S index.castSucc}) fun i member outside => by
        rcases outside with outside | ⟨index, inS⟩
        · exact avoid _ i member outside
        · exact disjoint _ _ (Fin.castSucc_lt_last index).ne i inS member
    exact base.mono fun i member => Or.inr member

end Fresh

end Fresh

/-! ### One step: the pairs a lazy question or a program adds -/

section Steps

/-- **A forward lazy question adds at most its own pair.** -/
theorem query_fixed_pairs (request : Request) (forward : ForwardOnly request) (state : LState)
    (answer : request.Answer × LState) (member : answer ∈ (LazyOracle.query request state).support)
    (i : FixedIndex) (x y : Fin (2 ^ 128)) (found : lk (answer.2.fixed i) x = some y) :
    lk (state.fixed i) x = some y ∨ request = .fixedForward i (BitVec.ofFin x) := by
  cases request with
  | fixedForward index input =>
    obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    by_cases same : i = index
    · subst same
      simp only [Function.update_self] at found
      rcases forward_new _ _ drawn drawnMember x (by rw [found]; exact Option.some_ne_none _)
        with old | new
      · obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.mp old
        have later := forward_grows _ _ drawn drawnMember x y' hy'
        rw [found] at later
        cases later
        exact Or.inl hy'
      · subst new
        have stored := LazyOracle.forward_lookup _ _ drawn drawnMember
        change lk drawn.2 input.toFin = some drawn.1 at stored
        exact Or.inr (by rw [BitVec.ofFin_toFin])
    · simp only [Function.update_of_ne same] at found
      exact Or.inl found
  | fixedInverse _ _ => exact forward.elim
  | encForward index input =>
    obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Or.inl found
  | encInverse _ _ => exact forward.elim
  | hash input =>
    obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Or.inl found

/-- **A lazy question adds at most its own hash key.** -/
theorem query_hash_pairs (request : Request) (state : LState)
    (answer : request.Answer × LState) (member : answer ∈ (LazyOracle.query request state).support)
    (k : BaseField) (v : Fin (Fintype.card (Block × Block)))
    (found : answer.2.hash.lookup k = some v) :
    state.hash.lookup k = some v ∨ request = .hash k := by
  cases request with
  | fixedForward index input =>
    obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Or.inl found
  | fixedInverse index output =>
    obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Or.inl found
  | encForward index input =>
    obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Or.inl found
  | encInverse index output =>
    obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Or.inl found
  | hash input =>
    obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    by_cases same : k = input
    · exact Or.inr (by rw [same])
    · left
      unfold HashTable.query at drawnMember
      split at drawnMember
      · simp only [Draw.distribution, PMF.mem_support_pure_iff] at drawnMember
        subst drawnMember
        exact found
      · simp only [Draw.distribution] at drawnMember
        obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp drawnMember
        have different : (k == input) = false := by simpa [beq_iff_eq] using same
        simpa [List.lookup, different] using found

/-- **A hash program adds exactly its own key**, with the programmed answer, and keeps the
fixed-key part. -/
theorem program_hash_pairs (input : BaseField) (value : Block × Block) (state updated : LState)
    (success : LazyOracle.program (.hash input) value state = some updated) :
    updated.fixed = state.fixed ∧
      ∀ k v, updated.hash.lookup k = some v →
        state.hash.lookup k = some v ∨ (k = input ∧ v = Fintype.equivFin (Block × Block) value) := by
  simp only [LazyOracle.program] at success
  split_ifs at success
  cases success
  refine ⟨rfl, fun k v found => ?_⟩
  change (state.hash.program input _).lookup k = some v at found
  rw [HashTable.program_lookup] at found
  by_cases same : k = input
  · subst same
    rw [Function.update_self] at found
    exact Or.inr ⟨rfl, (Option.some.inj found).symm⟩
  · rw [Function.update_of_ne same] at found
    exact Or.inl found

end Steps

/-! ### The refill run, described -/

section Refill

/-- **What a refill run leaves.** -/
structure Described (bits : BitInput) (tape : Tape) {α : Type} (computation : FreeQuery Programs.Spec α)
    (oracle : LState) (record : Record) (outcome : α × LState × Record) : Prop where
  grows : Grows oracle outcome.2.1
  value : outcome.1 = FreeQuery.eval (refillAns bits outcome.2.1) computation
  stored : ∀ r ∈ queriesAlong (refillAns bits outcome.2.1) computation,
    interceptAnswer bits r = none → StoredAs outcome.2.1 ⟨r, answerOf outcome.2.1 r⟩
  fixed : ∀ i x y, lk (outcome.2.1.fixed i) x = some y → lk (oracle.fixed i) x = some y ∨
    .fixedForward i (BitVec.ofFin x) ∈ queriesAlong (refillAns bits outcome.2.1) computation
  hash : ∀ k v, outcome.2.1.hash.lookup k = some v → oracle.hash.lookup k = some v ∨
    .hash k ∈ queriesAlong (refillAns bits outcome.2.1) computation
  tape : ∀ k cell, .hash k ∈ queriesAlong (refillAns bits outcome.2.1) computation →
    consumedCell bits (.hash k) = some cell → answerOf outcome.2.1 (.hash k) = tape cell
  records : ∀ limb, outcome.2.2 limb = record limb ∨ ∃ label, outcome.2.2 limb = some label ∧
    .hash (designatedInput bits limb label) ∈ queriesAlong (refillAns bits outcome.2.1) computation

theorem notDesignated_of_intercept {bits : BitInput} {input : BaseField}
    (intercept : interceptAnswer bits (.hash input) = none) : ¬ IsDesignated bits input := by
  intro designated
  rw [interceptAnswer_designated bits designated] at intercept
  cases intercept

theorem consumedCell_plain {bits : BitInput} {input : BaseField}
    (notDesignated : ¬ IsDesignated bits input) :
    consumedCell bits (.hash input) = cellOf input := by
  classical
  simp only [consumedCell, if_neg notDesignated]

theorem recordAfter_cases (bits : BitInput) (request : Request) (record : Record)
    (limb : Fin (limbCount .pointX)) :
    recordAfter bits request record limb = record limb ∨
      ∃ label, recordAfter bits request record limb = some label ∧
        request = .hash (designatedInput bits limb label) := by
  cases request with
  | hash input =>
    simp only [recordAfter]
    split_ifs with same
    · exact Or.inr ⟨_, rfl, by rw [same]⟩
    · exact Or.inl rfl
  | _ => exact Or.inl rfl

/-- The cells off `used` are untouched and none of their inputs is stored. -/
def CellsFree (used touched : Set Cell) (oracle : LState) : Prop :=
  ∀ cell, cell ∉ used → cell ∉ touched ∧ ∀ label, oracle.hash.lookup (cellInput cell label) = none

/-- **P4's refill run of a fresh forward-only program, described.** -/
theorem runRefill_describe (bits : BitInput) (tape : Tape) {α : Type}
    (computation : FreeQuery Programs.Spec α) (forward : AllQ ForwardOnly computation) :
    ∀ (used : Set Cell), Fresh bits used computation →
      ∀ (oracle : LState) (record : Record) (touched : Set Cell), CellsFree used touched oracle →
        ∀ outcome, some outcome ∈ (runRefill bits (fun cell => PMF.pure (tape cell)) computation
          oracle record touched).support →
          Described bits tape computation oracle record outcome := by
  induction computation with
  | pure value =>
    intro used _ oracle record touched _ outcome member
    simp only [runRefill, PMF.mem_support_pure_iff, Option.some.injEq] at member
    subst member
    exact ⟨Grows.refl _, rfl, (fun _ h => by cases h), (fun _ _ _ found => Or.inl found),
      (fun _ _ found => Or.inl found), (fun _ _ h => by cases h), (fun _ => Or.inl rfl)⟩
  | query request next ih =>
    intro used fresh oracle record touched free outcome member
    have isForward : ForwardOnly request := AllQ.head forward
    simp only [runRefill] at member
    cases intercept : interceptAnswer bits request with
    | some answer =>
      rw [intercept] at member
      have d := ih answer (AllQ.tail forward answer) _ (fresh.tail answer) oracle _ touched
        (fun cell outside => free cell fun inside => outside (Or.inl inside)) outcome member
      have same : refillAns bits outcome.2.1 request = answer := refillAns_intercept intercept
      have path : queriesAlong (refillAns bits outcome.2.1) (.query request next) =
          request :: queriesAlong (refillAns bits outcome.2.1) (next answer) := by
        show request :: queriesAlong _ (next (refillAns bits outcome.2.1 request)) = _
        rw [same]
      -- an intercepted question is a designated hash question: it consumes nothing
      have noCell : ∀ cell, consumedCell bits request ≠ some cell := by
        intro cell consumed
        cases request with
        | hash input =>
          by_cases designated : IsDesignated bits input
          · classical
            simp [consumedCell, designated] at consumed
          · rw [interceptAnswer_plain bits designated] at intercept
            cases intercept
        | _ => cases consumed
      refine ⟨d.grows, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show outcome.1 = FreeQuery.eval _ (next (refillAns bits outcome.2.1 request))
        rw [same]
        exact d.value
      · intro r member' notIntercepted
        rw [path] at member'
        rcases List.mem_cons.mp member' with rfl | member'
        · rw [intercept] at notIntercepted
          cases notIntercepted
        · exact d.stored r member' notIntercepted
      · intro i x y found
        rw [path]
        rcases d.fixed i x y found with old | onPath
        · exact Or.inl old
        · exact Or.inr (List.mem_cons_of_mem _ onPath)
      · intro k v found
        rw [path]
        rcases d.hash k v found with old | onPath
        · exact Or.inl old
        · exact Or.inr (List.mem_cons_of_mem _ onPath)
      · intro k cell member' consumed
        rw [path] at member'
        rcases List.mem_cons.mp member' with same' | member'
        · rw [same'] at consumed
          exact absurd consumed (noCell cell)
        · exact d.tape k cell member' consumed
      · intro limb
        rw [path]
        rcases d.records limb with same' | ⟨label, recorded, onPath⟩
        · rcases recordAfter_cases bits request record limb with kept | ⟨label, recorded, rfl⟩
          · exact Or.inl (same'.trans kept)
          · exact Or.inr ⟨label, same'.trans recorded, List.mem_cons_self⟩
        · exact Or.inr ⟨label, recorded, List.mem_cons_of_mem _ onPath⟩
    | none =>
      rw [intercept] at member
      simp only at member
      cases consumed : consumeCell touched oracle request with
      | some cell =>
        rw [consumed] at member
        obtain ⟨input, rfl, notTouched, fresh', found⟩ := consumeCell_spec consumed
        simp only [PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at member
        obtain ⟨value, rfl, rest⟩ := member
        have notDesignated := notDesignated_of_intercept intercept
        have consumedEq : consumedCell bits (.hash input) = some cell := by
          rw [consumedCell_plain notDesignated, found]
        rw [program_hash_refill, if_pos fresh'] at rest
        set updated : LState := { oracle with
          hash := oracle.hash.program input (Fintype.equivFin (Block × Block) (tape cell)) }
          with updatedDef
        have success : LazyOracle.program (.hash input) (tape cell) oracle = some updated := by
          rw [program_hash_eq, if_pos fresh']
        obtain ⟨sameFixed, newKeys⟩ := program_hash_pairs input _ oracle updated success
        obtain ⟨label0, inputEq⟩ := cellOf_spec found
        have tailFree : CellsFree (used ∪ {c | consumedCell bits (.hash input) = some c})
            (touch (.hash input) touched) updated := by
          intro other outside
          have notUsed : other ∉ used := fun inside => outside (Or.inl inside)
          have different : other ≠ cell := fun same => outside (Or.inr (by rw [same]; exact consumedEq))
          refine ⟨?_, fun label => ?_⟩
          · rintro (inside | inside)
            · exact (free other notUsed).1 inside
            · exact different (Option.some.inj (inside.symm.trans found))
          · cases lookupNew : updated.hash.lookup (cellInput other label) with
            | none => rfl
            | some v =>
              rcases newKeys _ v lookupNew with old | ⟨atInput, _⟩
              · rw [(free other notUsed).2 label] at old
                cases old
              · rw [← inputEq] at atInput
                exact absurd (congrArg Prod.fst (cellInput_injective (a₁ := (other, label))
                  (a₂ := (cell, label0)) atInput)) different
        have d := ih _ (AllQ.tail forward _) _ (fresh.tail _) _ record _ tailFree outcome rest
        have storedHere : StoredAs outcome.2.1 ⟨.hash input, tape cell⟩ := by
          refine storedAs_grows d.grows ?_
          show (updated.hash.lookup input).map (Fintype.equivFin (Block × Block)).symm = _
          rw [updatedDef]
          show ((oracle.hash.program input _).lookup input).map _ = _
          rw [HashTable.program_lookup, Function.update_self, Option.map_some,
            Equiv.symm_apply_apply]
          rfl
        have same : refillAns bits outcome.2.1 (.hash input) = tape cell := by
          rw [refillAns_plain intercept]
          exact answerOf_of_stored storedHere
        have path : queriesAlong (refillAns bits outcome.2.1) (.query (.hash input) next) =
            .hash input :: queriesAlong (refillAns bits outcome.2.1) (next (tape cell)) := by
          show _ :: queriesAlong _ (next (refillAns bits outcome.2.1 (.hash input))) = _
          rw [same]
        refine ⟨(program_hash_grows input _ oracle updated success).trans d.grows, ?_, ?_, ?_, ?_,
          ?_, ?_⟩
        · show outcome.1 = FreeQuery.eval _ (next (refillAns bits outcome.2.1 (.hash input)))
          rw [same]
          exact d.value
        · intro r member' notIntercepted
          rw [path] at member'
          rcases List.mem_cons.mp member' with rfl | member'
          · rw [answerOf_of_stored storedHere]
            exact storedHere
          · exact d.stored r member' notIntercepted
        · intro i x y found'
          rw [path]
          rcases d.fixed i x y found' with old | onPath
          · left
            rw [← sameFixed]
            exact old
          · exact Or.inr (List.mem_cons_of_mem _ onPath)
        · intro k v found'
          rw [path]
          rcases d.hash k v found' with old | onPath
          · rcases newKeys k v old with older | ⟨rfl, _⟩
            · exact Or.inl older
            · exact Or.inr List.mem_cons_self
          · exact Or.inr (List.mem_cons_of_mem _ onPath)
        · intro k cell' member' consumed'
          rw [path] at member'
          rcases List.mem_cons.mp member' with same' | member'
          · cases PublicQuery.hash.inj same'
            rw [consumedEq] at consumed'
            cases consumed'
            exact answerOf_of_stored storedHere
          · exact d.tape k cell' member' consumed'
        · intro limb
          rw [path]
          rcases d.records limb with same' | ⟨label, recorded, onPath⟩
          · exact Or.inl same'
          · exact Or.inr ⟨label, recorded, List.mem_cons_of_mem _ onPath⟩
      | none =>
        rw [consumed] at member
        simp only [PMF.mem_support_bind_iff] at member
        obtain ⟨answer, answerMember, rest⟩ := member
        -- a lazily answered question consumes no cell: a fresh cell at an unstored input would
        -- have been consumed
        have noCell : ∀ cell, consumedCell bits request ≠ some cell := by
          intro cell hit
          cases request with
          | hash input =>
            have notDesignated := notDesignated_of_intercept intercept
            rw [consumedCell_plain notDesignated] at hit
            obtain ⟨label, inputEq⟩ := cellOf_spec hit
            have notUsed : cell ∉ used := fresh.head cell (by rw [consumedCell_plain notDesignated,
              hit])
            have untouched := (free cell notUsed).1
            have unstored := (free cell notUsed).2 label
            rw [inputEq] at unstored
            change consumeHash touched oracle input = none at consumed
            unfold consumeHash at consumed
            rw [hit] at consumed
            dsimp only at consumed
            rw [if_neg (by
              rintro (inside | stored)
              · exact untouched inside
              · exact stored unstored)] at consumed
            cases consumed
          | _ => cases hit
        have tailFree : CellsFree (used ∪ {c | consumedCell bits request = some c})
            (touch request touched) answer.2 := by
          intro other outside
          have notUsed : other ∉ used := fun inside => outside (Or.inl inside)
          refine ⟨?_, fun label => ?_⟩
          · rintro (inside | inside)
            · exact (free other notUsed).1 inside
            · cases request with
              | hash input =>
                have notDesignated := notDesignated_of_intercept intercept
                exact noCell other (by rw [consumedCell_plain notDesignated]; exact inside)
              | _ => cases inside
          · cases lookupNew : answer.2.hash.lookup (cellInput other label) with
            | none => rfl
            | some v =>
              rcases query_hash_pairs request oracle answer answerMember _ v lookupNew with
                old | rfl
              · rw [(free other notUsed).2 label] at old
                cases old
              · have notDesignated := notDesignated_of_intercept intercept
                exact absurd (by rw [consumedCell_plain notDesignated, cellOf_cellInput])
                  (noCell other)
        have d := ih answer.1 (AllQ.tail forward _) _ (fresh.tail _) answer.2 record _ tailFree
          outcome rest
        have storedHere : StoredAs outcome.2.1 ⟨request, answer.1⟩ :=
          storedAs_grows d.grows (query_stores request oracle answer answerMember)
        have same : refillAns bits outcome.2.1 request = answer.1 := by
          rw [refillAns_plain intercept]
          exact answerOf_of_stored storedHere
        have path : queriesAlong (refillAns bits outcome.2.1) (.query request next) =
            request :: queriesAlong (refillAns bits outcome.2.1) (next answer.1) := by
          show request :: queriesAlong _ (next (refillAns bits outcome.2.1 request)) = _
          rw [same]
        refine ⟨(query_grows request oracle answer answerMember).trans d.grows, ?_, ?_, ?_, ?_, ?_,
          ?_⟩
        · show outcome.1 = FreeQuery.eval _ (next (refillAns bits outcome.2.1 request))
          rw [same]
          exact d.value
        · intro r member' notIntercepted
          rw [path] at member'
          rcases List.mem_cons.mp member' with rfl | member'
          · rw [answerOf_of_stored storedHere]
            exact storedHere
          · exact d.stored r member' notIntercepted
        · intro i x y found
          rw [path]
          rcases d.fixed i x y found with old | onPath
          · rcases query_fixed_pairs request isForward oracle answer answerMember i x y old
              with older | rfl
            · exact Or.inl older
            · exact Or.inr List.mem_cons_self
          · exact Or.inr (List.mem_cons_of_mem _ onPath)
        · intro k v found
          rw [path]
          rcases d.hash k v found with old | onPath
          · rcases query_hash_pairs request oracle answer answerMember k v old with older | rfl
            · exact Or.inl older
            · exact Or.inr List.mem_cons_self
          · exact Or.inr (List.mem_cons_of_mem _ onPath)
        · intro k cell member' consumed'
          rw [path] at member'
          rcases List.mem_cons.mp member' with same' | member'
          · rw [same'] at consumed'
            exact absurd consumed' (noCell cell)
          · exact d.tape k cell member' consumed'
        · intro limb
          rw [path]
          rcases d.records limb with same' | ⟨label, recorded, onPath⟩
          · exact Or.inl same'
          · exact Or.inr ⟨label, recorded, List.mem_cons_of_mem _ onPath⟩

end Refill

/-! ### The lazy run: provenance -/

section Lazy

/-- **Every new pair of a lazy run of a forward-only program is asked on its path.** -/
theorem runLazyQ_provenance {α : Type} (computation : FreeQuery Programs.Spec α)
    (forward : AllQ ForwardOnly computation) :
    ∀ (state : LState) (outcome : α × LState), outcome ∈ (runLazyQ computation state).support →
      (∀ i x y, lk (outcome.2.fixed i) x = some y → lk (state.fixed i) x = some y ∨
        .fixedForward i (BitVec.ofFin x) ∈ queriesAlong (answerOf outcome.2) computation) ∧
      (∀ k v, outcome.2.hash.lookup k = some v → state.hash.lookup k = some v ∨
        .hash k ∈ queriesAlong (answerOf outcome.2) computation) := by
  induction computation with
  | pure value =>
    intro state outcome member
    simp only [runLazyQ, PMF.mem_support_pure_iff] at member
    subst member
    exact ⟨fun _ _ _ found => Or.inl found, fun _ _ found => Or.inl found⟩
  | query request next ih =>
    intro state outcome member
    simp only [runLazyQ, PMF.mem_support_bind_iff] at member
    obtain ⟨answer, answerMember, rest⟩ := member
    obtain ⟨fixedRest, hashRest⟩ := ih answer.1 (AllQ.tail forward _) answer.2 outcome rest
    have grow := runLazyQ_grows _ answer.2 outcome rest
    have storedHere : StoredAs outcome.2 ⟨request, answer.1⟩ :=
      storedAs_grows grow (query_stores request state answer answerMember)
    have same : answerOf outcome.2 request = answer.1 := answerOf_of_stored storedHere
    have path : queriesAlong (answerOf outcome.2) (.query request next) =
        request :: queriesAlong (answerOf outcome.2) (next answer.1) := by
      show request :: queriesAlong _ (next (answerOf outcome.2 request)) = _
      rw [same]
    rw [path]
    refine ⟨fun i x y found => ?_, fun k v found => ?_⟩
    · rcases fixedRest i x y found with old | onPath
      · rcases query_fixed_pairs request (AllQ.head forward) state answer answerMember i x y old
          with older | rfl
        · exact Or.inl older
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ onPath)
    · rcases hashRest k v found with old | onPath
      · rcases query_hash_pairs request state answer answerMember k v old with older | rfl
        · exact Or.inl older
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ onPath)

end Lazy

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
