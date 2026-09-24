/-
**Phase 3, P4b — the refill runner where it needs no randomness.**

On a fixed tape, a query that is intercepted (a designated hash input) or consumed (a first touch of
a cell at an unknown input) is answered deterministically. `detRun` runs a program that way; `none`
means it met a query needing the lazy oracle.

* `detRun_spec` — where `detRun` succeeds, the refill run is the point mass at its result.
* `detRun_value` — the value is the program evaluated against the tape answers `tapeAnswer`
  (a designated hash query gets `(0, 0)`, a cell's hash query the tape's answer at the cell), so
  the hashes it computes are the tape's, **whatever the labels**.
* `detRun_ne_none` — it succeeds when every query along the tape path is intercepted or is a first
  touch of its cell at an unknown input, at pairwise distinct cells (`queriesAlong`).
* `detRun_frame`, `detRun_record_plain` — what a successful run changes.
-/

import Proof.Privacy.Phase3.Lazy.RunFrame

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

section Det

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
  (bits : BitInput) (tape : Tape)

/-- **The refill runner on a tape, without randomness.** The outer `none`: a query needing the
lazy oracle was met. The inner `none`: a failed program (an abort of the run). -/
def detRun {α : Type} : FreeQuery Programs.Spec α → LState → Record → Set Cell →
    Option (Option (α × LState × Record × Set Cell))
  | .pure value, oracle, record, touched => some (some (value, oracle, record, touched))
  | .query request next, oracle, record, touched =>
      match interceptAnswer bits request with
      | some answer => detRun (next answer) oracle (recordAfter bits request record) touched
      | none => match consumeCell touched oracle request with
        | some cell =>
            match LazyOracle.program request (refillAnswer request (tape cell)) oracle with
            | none => some none
            | some updated => detRun (next (refillAnswer request (tape cell))) updated record
                (touch request touched)
        | none => none

theorem detRun_intercepted {α : Type} (request : Request)
    (next : request.Answer → FreeQuery Programs.Spec α) (oracle : LState) (record : Record)
    (touched : Set Cell) (answer : request.Answer)
    (intercepted : interceptAnswer bits request = some answer) :
    detRun bits tape (.query request next) oracle record touched =
      detRun bits tape (next answer) oracle (recordAfter bits request record) touched := by
  conv_lhs => unfold detRun
  rw [intercepted]

theorem detRun_consumed {α : Type} (request : Request)
    (next : request.Answer → FreeQuery Programs.Spec α) (oracle : LState) (record : Record)
    (touched : Set Cell) (cell : Cell) (intercept : interceptAnswer bits request = none)
    (consume : consumeCell touched oracle request = some cell) :
    detRun bits tape (.query request next) oracle record touched =
      match LazyOracle.program request (refillAnswer request (tape cell)) oracle with
      | none => some none
      | some updated => detRun bits tape (next (refillAnswer request (tape cell))) updated record
          (touch request touched) := by
  conv_lhs => unfold detRun
  rw [intercept]
  dsimp only
  rw [consume]

/-- **Where `detRun` succeeds, the refill run on the tape is its point mass.** -/
theorem detRun_spec {α : Type} (c : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell)
      (result : Option (α × LState × Record × Set Cell)),
      detRun bits tape c oracle record touched = some result →
        runRefillT bits (fun cell => PMF.pure (tape cell)) c oracle record touched =
          PMF.pure result := by
  induction c with
  | pure value =>
      intro oracle record touched result success
      simp only [detRun, Option.some.injEq] at success
      subst success
      rfl
  | query request next ih =>
      intro oracle record touched result success
      cases intercept : interceptAnswer bits request with
      | some answer =>
          simp only [detRun, intercept] at success
          rw [runRefillT_intercepted bits _ request next oracle record touched answer intercept]
          exact ih _ _ _ _ _ success
      | none =>
          cases consume : consumeCell touched oracle request with
          | some cell =>
              simp only [detRun, intercept, consume] at success
              rw [runRefillT_consumed bits _ request next oracle record touched cell intercept
                consume, PMF.pure_bind]
              cases programmed : LazyOracle.program request (refillAnswer request (tape cell))
                  oracle with
              | none =>
                  simp only [programmed, Option.some.injEq] at success
                  subst success
                  rfl
              | some updated =>
                  simp only [programmed] at success
                  exact ih _ _ _ _ _ success
          | none => simp [detRun, intercept, consume] at success

/-- The bind law of `detRun`'s spec: a successful first part hands over to the rest. -/
theorem detRun_bind_spec {α β : Type} (c : FreeQuery Programs.Spec α)
    (k : α → FreeQuery Programs.Spec β) (oracle : LState) (record : Record)
    (touched : Set Cell) (result : Option (α × LState × Record × Set Cell))
    (success : detRun bits tape c oracle record touched = some result) :
    runRefillT bits (fun cell => PMF.pure (tape cell)) (c >>= k) oracle record touched =
      continueT bits (fun cell => PMF.pure (tape cell)) k result := by
  rw [runRefillT_bind, detRun_spec bits tape c oracle record touched result success,
    PMF.pure_bind]

/-! ### The value -/

open Classical in
/-- The tape answer of a hash query: `(0, 0)` at a designated input, the tape's answer at a cell's
input. -/
def tapeHash (input : BaseField) : Block × Block :=
  if IsDesignated bits input then (0, 0) else
    match cellOf input with
    | some cell => tape cell
    | none => (0, 0)

/-- **The tape answers**: a designated hash query gets `(0, 0)`, a cell's hash query the tape's
answer at the cell. -/
def tapeAnswer : (request : Request) → request.Answer
  | .fixedForward _ _ => (0 : Block)
  | .fixedInverse _ _ => (0 : Block)
  | .encForward _ _ => (0 : Block)
  | .encInverse _ _ => (0 : Block)
  | .hash input => tapeHash bits tape input

theorem tapeHash_cell (cell : Cell) (label : Block)
    (notDesignated : ¬ IsDesignated bits (cellInput cell label)) :
    tapeHash bits tape (cellInput cell label) = tape cell := by
  unfold tapeHash
  rw [if_neg notDesignated, cellOf_cellInput]

/-- A hash query of a program evaluated against any answers reads the answer at its input. -/
theorem eval_askHash_answer (answer : (request : Request) → request.Answer) (input : BaseField) :
    FreeQuery.eval answer (Programs.askHash input) = answer (.hash input) := rfl

theorem tapeAnswer_hash (input : BaseField) :
    tapeAnswer bits tape (.hash input) = tapeHash bits tape input := rfl

/-- The tape answer at a switch's cell input is the tape's answer at the cell. -/
theorem tapeHash_scale (lane : Lane) (chunk : Fin chunkCount)
    (switch : Fin (2 ^ chunkWidth chunk)) (limb : Fin (limbCount lane)) (label : Block)
    (notDesignated : ¬ IsDesignated bits (scaleInput lane chunk switch.val limb.val label)) :
    tapeHash bits tape (scaleInput lane chunk switch.val limb.val label) =
      tape ⟨⟨lane, chunk, switch⟩, limb⟩ :=
  tapeHash_cell bits tape ⟨⟨lane, chunk, switch⟩, limb⟩ label notDesignated

theorem interceptAnswer_tapeAnswer {request : Request} {answer : request.Answer}
    (intercepted : interceptAnswer bits request = some answer) :
    answer = tapeAnswer bits tape request := by
  cases request with
  | hash input =>
      by_cases designated : IsDesignated bits input
      · rw [interceptAnswer_designated bits designated] at intercepted
        cases intercepted
        show _ = tapeHash bits tape input
        unfold tapeHash
        rw [if_pos designated]
      · rw [interceptAnswer_plain bits designated] at intercepted
        cases intercepted
  | fixedForward _ _ => cases intercepted
  | fixedInverse _ _ => cases intercepted
  | encForward _ _ => cases intercepted
  | encInverse _ _ => cases intercepted

theorem consumeCell_tapeAnswer {request : Request} {touched : Set Cell} {oracle : LState}
    {cell : Cell} (intercept : interceptAnswer bits request = none)
    (consumed : consumeCell touched oracle request = some cell) :
    refillAnswer request (tape cell) = tapeAnswer bits tape request := by
  obtain ⟨input, rfl, _, _, found⟩ := consumeCell_spec consumed
  have notDesignated : ¬ IsDesignated bits input := by
    intro designated
    rw [interceptAnswer_designated bits designated] at intercept
    cases intercept
  show tape cell = tapeHash bits tape input
  unfold tapeHash
  rw [if_neg notDesignated, found]

/-- **The value of a successful `detRun` is the program against the tape answers.** -/
theorem detRun_value {α : Type} (c : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell)
      (result : α × LState × Record × Set Cell),
      detRun bits tape c oracle record touched = some (some result) →
        result.1 = FreeQuery.eval (tapeAnswer bits tape) c := by
  induction c with
  | pure value =>
      intro oracle record touched result success
      simp only [detRun, Option.some.injEq] at success
      subst success
      rfl
  | query request next ih =>
      intro oracle record touched result success
      cases intercept : interceptAnswer bits request with
      | some answer =>
          simp only [detRun, intercept] at success
          rw [ih _ _ _ _ _ success, interceptAnswer_tapeAnswer bits tape intercept]
          rfl
      | none =>
          cases consume : consumeCell touched oracle request with
          | some cell =>
              simp only [detRun, intercept, consume] at success
              cases programmed : LazyOracle.program request (refillAnswer request (tape cell))
                  oracle with
              | none => simp [programmed] at success
              | some updated =>
                  simp only [programmed] at success
                  rw [ih _ _ _ _ _ success, consumeCell_tapeAnswer bits tape intercept consume]
                  rfl
          | none => simp [detRun, intercept, consume] at success

/-! ### When `detRun` succeeds -/

/-- The queries along the path an answer function selects. -/
def queriesAlong {α : Type} (answer : (request : Request) → request.Answer) :
    FreeQuery Programs.Spec α → List Request
  | .pure _ => []
  | .query request next => request :: queriesAlong answer (next (answer request))

theorem queriesAlong_bind {α β : Type} (answer : (request : Request) → request.Answer)
    (c : FreeQuery Programs.Spec α) (f : α → FreeQuery Programs.Spec β) :
    queriesAlong answer (c >>= f) =
      queriesAlong answer c ++ queriesAlong answer (f (FreeQuery.eval answer c)) := by
  induction c with
  | pure value => rfl
  | query request next ih =>
      show request :: queriesAlong answer (next (answer request) >>= f) = _
      rw [ih]
      rfl

theorem queriesAlong_pure {α : Type} (answer : (request : Request) → request.Answer) (value : α) :
    queriesAlong answer (Pure.pure value : FreeQuery Programs.Spec α) = [] := rfl

theorem queriesAlong_vector {α : Type} (answer : (request : Request) → request.Answer) :
    ∀ (count : Nat) (program : Fin count → FreeQuery Programs.Spec α),
      queriesAlong answer (FreeQuery.vector count program) =
        (List.finRange count).flatMap fun index => queriesAlong answer (program index)
  | 0, _ => rfl
  | count + 1, program => by
      show queriesAlong answer (FreeQuery.vector count (fun index => program index.castSucc) >>=
        fun values => program (Fin.last count) >>= fun value => Pure.pure (values.push value)) = _
      rw [queriesAlong_bind, queriesAlong_bind, queriesAlong_pure, List.append_nil,
        queriesAlong_vector answer count, List.finRange_succ_last, List.flatMap_append,
        List.flatMap_map, List.flatMap_singleton]

open Classical in
/-- The cell a request consumes, if it is a non-designated hash query at a cell input. -/
def consumedCell : Request → Option Cell
  | .fixedForward _ _ => none
  | .fixedInverse _ _ => none
  | .encForward _ _ => none
  | .encInverse _ _ => none
  | .hash input => if IsDesignated bits input then none else cellOf input

/-- A request the tape runner answers from `(oracle, touched)`: a designated hash query, or a first
touch of a cell at an unknown input. -/
def TapeReady (oracle : LState) (touched : Set Cell) : Request → Prop
  | .fixedForward _ _ => False
  | .fixedInverse _ _ => False
  | .encForward _ _ => False
  | .encInverse _ _ => False
  | .hash input => IsDesignated bits input ∨
      ∃ cell, cellOf input = some cell ∧ cell ∉ touched ∧ oracle.hash.lookup input = none

/-- **`detRun` succeeds** when every query along the tape path is ready and the consumed cells are
pairwise distinct. -/
theorem detRun_ne_none {α : Type} (c : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell),
      (∀ request ∈ queriesAlong (tapeAnswer bits tape) c, TapeReady bits oracle touched request) →
      ((queriesAlong (tapeAnswer bits tape) c).filterMap (consumedCell bits)).Nodup →
        detRun bits tape c oracle record touched ≠ none := by
  induction c with
  | pure value => intro oracle record touched _ _; simp [detRun]
  | query request next ih =>
      intro oracle record touched ready distinct
      have here := ready request List.mem_cons_self
      have later : ∀ r ∈ queriesAlong (tapeAnswer bits tape) (next (tapeAnswer bits tape request)),
          TapeReady bits oracle touched r := fun r member =>
        ready r (List.mem_cons_of_mem _ member)
      cases request with
      | hash input =>
          by_cases designated : IsDesignated bits input
          · have intercept := interceptAnswer_designated bits designated
            rw [detRun_intercepted bits tape (.hash input) next oracle record touched (0, 0)
              intercept]
            have answerEq : tapeAnswer bits tape (.hash input) = ((0, 0) : Block × Block) := by
              show tapeHash bits tape input = _
              unfold tapeHash
              rw [if_pos designated]
            rw [answerEq] at later
            refine ih (0, 0) _ _ _ later ?_
            have tailDistinct := distinct
            simp only [queriesAlong, List.filterMap_cons] at tailDistinct
            have noCell : consumedCell bits (.hash input) = none := by
              simp only [consumedCell]
              rw [if_pos designated]
            rw [noCell, answerEq] at tailDistinct
            exact tailDistinct
          · obtain ⟨cell, cellEq, untouched, fresh⟩ := here.resolve_left designated
            have intercept := interceptAnswer_plain bits designated
            have consume : consumeCell touched oracle (.hash input) = some cell := by
              change consumeHash touched oracle input = some cell
              unfold consumeHash
              rw [cellEq]
              dsimp only
              rw [if_neg (by rintro (hit | hit); exacts [untouched hit, hit fresh])]
            have answerEq : refillAnswer (.hash input) (tape cell) =
                tapeAnswer bits tape (.hash input) :=
              consumeCell_tapeAnswer bits tape intercept consume
            rw [detRun_consumed bits tape (.hash input) next oracle record touched cell intercept
              consume]
            cases programmed : LazyOracle.program (.hash input)
                (refillAnswer (.hash input) (tape cell)) oracle with
            | none => simp
            | some updated =>
                simp only
                rw [answerEq]
                have consumedEq : consumedCell bits (.hash input) = some cell := by
                  simp only [consumedCell]
                  rw [if_neg designated, cellEq]
                have distinct' := distinct
                simp only [queriesAlong, List.filterMap_cons] at distinct'
                rw [consumedEq] at distinct'
                simp only [List.nodup_cons] at distinct'
                refine ih _ _ _ _ (fun r member => ?_) distinct'.2
                have old := later r member
                cases r with
                | hash input' =>
                    by_cases designated' : IsDesignated bits input'
                    · exact Or.inl designated'
                    · obtain ⟨cell', cellEq', untouched', fresh'⟩ := old.resolve_left designated'
                      have different : cell' ≠ cell := by
                        intro same
                        apply distinct'.1
                        refine List.mem_filterMap.mpr ⟨.hash input', member, ?_⟩
                        simp only [consumedCell]
                        rw [if_neg designated', cellEq', same]
                      have inputNe : input' ≠ input := by
                        rintro rfl
                        rw [cellEq] at cellEq'
                        exact different (Option.some.inj cellEq').symm
                      refine Or.inr ⟨cell', cellEq', ?_, ?_⟩
                      · simp only [touch, Set.mem_ofPred_eq, touchedCell]
                        rintro (hit | hit)
                        · exact untouched' hit
                        · rw [cellEq] at hit
                          exact different (Option.some.inj hit).symm
                      · rw [(program_lookup_frame input _ oracle updated programmed).2.2 input'
                          inputNe]
                        exact fresh'
                | fixedForward _ _ => exact old.elim
                | fixedInverse _ _ => exact old.elim
                | encForward _ _ => exact old.elim
                | encInverse _ _ => exact old.elim
      | fixedForward _ _ => exact here.elim
      | fixedInverse _ _ => exact here.elim
      | encForward _ _ => exact here.elim
      | encInverse _ _ => exact here.elim

/-- **What a successful `detRun` changes**: only the hash lookups at the inputs its queries ask
(and the touched marks of their cells); never the fixed-key or EncPRF parts. -/
theorem detRun_frame (S : BaseField → Prop) {α : Type} {c : FreeQuery Programs.Spec α}
    (inside : AllQ (HashIn S) c) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell)
      (result : α × LState × Record × Set Cell),
      detRun bits tape c oracle record touched = some (some result) →
        result.2.1.fixed = oracle.fixed ∧ result.2.1.enc = oracle.enc ∧
        (∀ input, ¬ S input → result.2.1.hash.lookup input = oracle.hash.lookup input) ∧
        (∀ cell, (∀ label, ¬ S (cellInput cell label)) →
          (cell ∈ result.2.2.2 ↔ cell ∈ touched)) := by
  induction inside with
  | pure value =>
      intro oracle record touched result success
      simp only [detRun, Option.some.injEq] at success
      subst success
      exact ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => Iff.rfl⟩
  | query request next here _ ih =>
      intro oracle record touched result success
      cases request with
      | hash input =>
          cases intercept : interceptAnswer bits (.hash input) with
          | some answer =>
              simp only [detRun, intercept] at success
              exact ih _ _ _ _ _ success
          | none =>
              cases consume : consumeCell touched oracle (.hash input) with
              | some cell =>
                  simp only [detRun, intercept, consume] at success
                  cases programmed : LazyOracle.program (.hash input)
                      (refillAnswer (.hash input) (tape cell)) oracle with
                  | none => simp [programmed] at success
                  | some updated =>
                      simp only [programmed] at success
                      obtain ⟨fixedSame, encSame, hashSame, touchedSame⟩ := ih _ _ _ _ _ success
                      obtain ⟨fixedStep, encStep, hashStep⟩ :=
                        program_lookup_frame input _ oracle updated programmed
                      refine ⟨fixedSame.trans fixedStep, encSame.trans encStep,
                        fun other outside => ?_, fun other outside => ?_⟩
                      · rw [hashSame other outside]
                        exact hashStep other fun same => outside (same ▸ here)
                      · rw [touchedSame other outside]
                        simp only [touch, Set.mem_ofPred_eq, touchedCell]
                        refine ⟨fun hit => hit.elim id fun found => ?_, Or.inl⟩
                        obtain ⟨label, same⟩ := cellOf_spec found
                        exact (outside label (same ▸ here)).elim
              | none => simp [detRun, intercept, consume] at success
      | fixedForward _ _ => exact here.elim
      | fixedInverse _ _ => exact here.elim
      | encForward _ _ => exact here.elim
      | encInverse _ _ => exact here.elim

/-- **A successful `detRun` of a program that asks no designated input keeps the record.** -/
theorem detRun_record_plain {α : Type} {c : FreeQuery Programs.Spec α}
    (plain : AllQ (fun request => ∀ input, request = .hash input → ¬ IsDesignated bits input) c) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell)
      (result : α × LState × Record × Set Cell),
      detRun bits tape c oracle record touched = some (some result) → result.2.2.1 = record := by
  induction plain with
  | pure value =>
      intro oracle record touched result success
      simp only [detRun, Option.some.injEq] at success
      subst success
      rfl
  | query request next here _ ih =>
      intro oracle record touched result success
      cases intercept : interceptAnswer bits request with
      | some answer =>
          exfalso
          cases request with
          | hash input =>
              by_cases designated : IsDesignated bits input
              · exact here input rfl designated
              · rw [interceptAnswer_plain bits designated] at intercept
                cases intercept
          | fixedForward _ _ => cases intercept
          | fixedInverse _ _ => cases intercept
          | encForward _ _ => cases intercept
          | encInverse _ _ => cases intercept
      | none =>
          cases consume : consumeCell touched oracle request with
          | some cell =>
              simp only [detRun, intercept, consume] at success
              cases programmed : LazyOracle.program request (refillAnswer request (tape cell))
                  oracle with
              | none => simp [programmed] at success
              | some updated =>
                  simp only [programmed] at success
                  exact ih _ _ _ _ _ success
          | none => simp [detRun, intercept, consume] at success

end Det

end

end Kriterion.ArgoMAC.Phase3.Lazy
