/-
**Phase 3, P4 — the installation failure, event by event.**

`programAll_fail`: when every request carries an input and the request inputs are pairwise
distinct, a failed installation has a request whose input is already stored **in the oracle the
installation started from**: a hash program fails only at a stored input, and earlier programs
store other inputs only. With `runRefill_records` (every input present) and `runRefill_frame` (the
run leaves designated inputs as stage 1 left them), the failure mass of `I^U` is the mass of the
input event (d) against the stage-1 hash entries at the designated inputs
(`FailCurve.run_fail_collides`). There is no output event: hash answers may collide.
-/

import Proof.Privacy.Phase3.Lazy.Frame

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A request collides with the oracle: its input is stored. -/
def Collides (oracle : LState) (request : Option BaseField × (Block × Block)) : Prop :=
  ∃ input, request.1 = some input ∧ oracle.hash.lookup input ≠ none

/-- A rejected hash program is at a stored input. -/
theorem program_none (input : BaseField) (answer : Block × Block) (oracle : LState)
    (rejected : LazyOracle.program (.hash input) answer oracle = none) :
    oracle.hash.lookup input ≠ none := by
  rw [program_hash_eq] at rejected
  split_ifs at rejected with fresh
  exact fresh

/-- **A failed installation is a collision against the starting oracle.** -/
theorem programAll_fail :
    ∀ (requests : List (Option BaseField × (Block × Block))) (oracle : LState),
      (∀ request ∈ requests, request.1 ≠ none) → (requests.filterMap Prod.fst).Nodup →
        programAll requests oracle = none → ∃ request ∈ requests, Collides oracle request
  | [], _, _, _, failed => by simp [programAll] at failed
  | (input, answer) :: rest, oracle, present, distinct, failed => by
      cases input with
      | none => exact absurd rfl (present _ List.mem_cons_self)
      | some input =>
          change (LazyOracle.program (.hash input) answer oracle).bind (programAll rest) = none
            at failed
          cases programmed : LazyOracle.program (.hash input) answer oracle with
          | none =>
              exact ⟨_, List.mem_cons_self, input, rfl, program_none input answer oracle programmed⟩
          | some updated =>
              rw [programmed, Option.bind_some] at failed
              change (input :: rest.filterMap Prod.fst).Nodup at distinct
              rw [List.nodup_cons] at distinct
              obtain ⟨request, member, collides⟩ := programAll_fail rest updated
                (fun request member => present request (List.mem_cons_of_mem _ member))
                distinct.2 failed
              refine ⟨request, List.mem_cons_of_mem _ member, ?_⟩
              obtain ⟨input', same, hit⟩ := collides
              have away : input' ≠ input := fun equal =>
                distinct.1 (List.mem_filterMap.mpr ⟨request, member, equal ▸ same⟩)
              refine ⟨input', same, ?_⟩
              rw [(program_lookup_frame input answer oracle updated programmed).2.2 input' away]
                at hit
              exact hit

end

end Kriterion.ArgoMAC.Phase3.Lazy
