/-
**Phase 3, P1g — tools for stored paths: sequencing lazy runs, transcripts, stored answers.**

* `runLazyQ_bind`: the lazy run of a sequence is the lazy run of its first stage, then of the rest;
* `transcript_bind`, `mem_transcript_left`, `mem_transcript_right`, `mem_transcript_vector`: where
  an entry of a transcript comes from;
* `runLazyQ_of_stored`: a program whose every question (along a complete oracle) is stored in the
  lazy state is answered deterministically, and leaves the state alone;
* `query_fixedForward_stored`: a stored forward pair is answered without sampling.
-/

import Proof.Privacy.Phase3.PublicFirst.Private

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (LState)

noncomputable section

/-! ### 1. Sequencing lazy runs -/

section Run

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- The lazy run of a sequence. -/
theorem runLazyQ_bind {α β : Type} (c : FreeQuery (publicOracleSpec FixedIndex EncIndex) α)
    (f : α → FreeQuery (publicOracleSpec FixedIndex EncIndex) β) :
    ∀ state, runLazyQ (c >>= f) state = (runLazyQ c state).bind fun r => runLazyQ (f r.1) r.2 := by
  induction c with
  | pure value =>
    intro state
    show runLazyQ (f value) state = (PMF.pure (value, state)).bind _
    rw [PMF.pure_bind]
  | query request next ih =>
    intro state
    show (LazyOracle.query request state).bind (fun answer =>
        runLazyQ (next answer.1 >>= f) answer.2) = _
    simp only [runLazyQ, PMF.bind_bind]
    congr 1
    funext answer
    exact ih answer.1 answer.2

end Run

/-! ### 2. Transcripts -/

section Transcript

variable (answer : ∀ query : PublicQuery FixedIndex EncPRF.PermutationIndex, query.Answer)

theorem transcript_bind {α β : Type} (c : FreeQuery Programs.Spec α)
    (f : α → FreeQuery Programs.Spec β) :
    transcript answer (c >>= f) =
      transcript answer c ++ transcript answer (f (FreeQuery.eval answer c)) := by
  induction c with
  | pure value => rfl
  | query request next ih =>
    show ⟨request, answer request⟩ :: transcript answer (next (answer request) >>= f) = _
    rw [ih]
    rfl

theorem mem_transcript_left {α β : Type} {c : FreeQuery Programs.Spec α}
    {f : α → FreeQuery Programs.Spec β} {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript answer c) : entry ∈ transcript answer (c >>= f) := by
  rw [transcript_bind]
  exact List.mem_append_left _ member

theorem mem_transcript_right {α β : Type} {c : FreeQuery Programs.Spec α}
    {f : α → FreeQuery Programs.Spec β} {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript answer (f (FreeQuery.eval answer c))) :
    entry ∈ transcript answer (c >>= f) := by
  rw [transcript_bind]
  exact List.mem_append_right _ member

theorem mem_transcript_vector {α : Type} {entry : Entry FixedIndex EncPRF.PermutationIndex} :
    ∀ (count : ℕ) (program : Fin count → FreeQuery Programs.Spec α) (index : Fin count),
      entry ∈ transcript answer (program index) →
        entry ∈ transcript answer (FreeQuery.vector count program)
  | 0, _, index, _ => index.elim0
  | count + 1, program, index, member => by
      show entry ∈ transcript answer (FreeQuery.vector count (fun index => program index.castSucc)
        >>= fun values => program (Fin.last count) >>= fun value =>
          (Pure.pure (values.push value) : FreeQuery Programs.Spec (Vector α (count + 1))))
      induction index using Fin.lastCases with
      | last => exact mem_transcript_right answer (mem_transcript_left answer member)
      | cast index =>
        exact mem_transcript_left answer
          (mem_transcript_vector count (fun index => program index.castSucc) index member)

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **A program whose questions are stored runs deterministically**, leaving the state alone. -/
theorem runLazyQ_of_stored {α : Type} (c : FreeQuery Programs.Spec α) (state : LState)
    (stored : ∀ entry ∈ transcript answer c,
      LazyOracle.query entry.1 state = PMF.pure (entry.2, state)) :
    runLazyQ c state = PMF.pure (FreeQuery.eval answer c, state) := by
  induction c with
  | pure value => rfl
  | query request next ih =>
    have head := stored ⟨request, answer request⟩ List.mem_cons_self
    show (LazyOracle.query request state).bind _ = _
    rw [head, PMF.pure_bind]
    exact ih (answer request) fun entry member => stored entry (List.mem_cons_of_mem _ member)

/-- A stored forward pair is answered without sampling. -/
theorem query_fixedForward_stored (state : LState) (index : FixedIndex) (input output : Block)
    (found : lk (state.fixed index) input.toFin = some output.toFin) :
    LazyOracle.query (.fixedForward index input) state = PMF.pure (output, state) := by
  have forward := LazyOracle.lookup_forward (state.fixed index) input.toFin output.toFin found
  show ((state.fixed index).forward input.toFin).distribution.map (fun answer =>
    (BitVec.ofFin answer.1, { state with fixed := Function.update state.fixed index answer.2 })) = _
  rw [forward]
  simp only [Draw.distribution, PMF.pure_map, Function.update_eq_self, BitVec.ofFin_toFin]

end Transcript

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
