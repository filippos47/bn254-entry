/-
**Phase 3, P4 — evaluator unfolding (1): the refill run of a sequence.**

`runRefill` does not return its touched set, so it has no bind law. `runRefillT` is the same runner
returning the touched set as well:

* `runRefill_eq_runRefillT` — `runRefill` is `runRefillT` with the touched set dropped;
* `runRefillT_bind` — the run of `c >>= f` is the run of `c`, then the run of `f` on its value,
  from the oracle, record and touched set it leaves; an abort aborts.

These isolate the sub-runs of `openingQueriesM`: the curve lanes, the bridge hash, the pads, the
`pointX` lane (chunk 0 first) and the `pointY` lane.
-/

import Proof.Privacy.Phase3.Lazy.FailEvents

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **`runRefill`, returning the touched set too.** -/
def runRefillT (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type} :
    FreeQuery Programs.Spec α → LState → Record → Set Cell →
      PMF (Option (α × LState × Record × Set Cell))
  | .pure value, oracle, record, touched => PMF.pure (some (value, oracle, record, touched))
  | .query request next, oracle, record, touched =>
      match interceptAnswer bits request with
      | some answer => runRefillT bits draw (next answer) oracle (recordAfter bits request record)
          touched
      | none => match consumeCell touched oracle request with
        | some cell => (draw cell).bind fun value =>
            match LazyOracle.program request (refillAnswer request value) oracle with
            | none => PMF.pure none
            | some updated => runRefillT bits draw (next (refillAnswer request value)) updated
                record (touch request touched)
        | none => (LazyOracle.query request oracle).bind fun answer =>
            runRefillT bits draw (next answer.1) answer.2 record (touch request touched)

/-- Drop the touched set. -/
def dropTouched {α : Type} (result : α × LState × Record × Set Cell) : α × LState × Record :=
  (result.1, result.2.1, result.2.2.1)

/-- **`runRefill` is `runRefillT` with the touched set dropped.** -/
theorem runRefill_eq_runRefillT (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell),
      runRefill bits draw computation oracle record touched =
        (runRefillT bits draw computation oracle record touched).map (Option.map dropTouched) := by
  induction computation with
  | pure value =>
      intro oracle record touched
      simp only [runRefill, runRefillT, PMF.pure_map, Option.map_some]
      rfl
  | query request next ih =>
      intro oracle record touched
      simp only [runRefill, runRefillT]
      split
      · rename_i answer intercepted
        simp only [intercepted]
        exact ih _ _ _ _
      · rename_i intercepted
        simp only [intercepted]
        split
        · rename_i cell consumed
          simp only [consumed]
          rw [PMF.map_bind]
          refine congrArg _ (funext fun value => ?_)
          split
          · rename_i programmed
            simp only [programmed, PMF.pure_map, Option.map_none]
          · rename_i updated programmed
            simp only [programmed]
            exact ih _ _ _ _
        · rename_i consumed
          simp only [consumed]
          rw [PMF.map_bind]
          exact congrArg _ (funext fun answer => ih _ _ _ _)

/-- The continuation of a run: an abort stays an abort. -/
def continueT {α β : Type} (bits : BitInput) (draw : Cell → PMF (Block × Block))
    (f : α → FreeQuery Programs.Spec β) :
    Option (α × LState × Record × Set Cell) →
      PMF (Option (β × LState × Record × Set Cell))
  | none => PMF.pure none
  | some result => runRefillT bits draw (f result.1) result.2.1 result.2.2.1 result.2.2.2

/-- **The run of a sequence is the run of its first part, then of the rest.** -/
theorem runRefillT_bind (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α β : Type}
    (computation : FreeQuery Programs.Spec α) (f : α → FreeQuery Programs.Spec β) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell),
      runRefillT bits draw (computation >>= f) oracle record touched =
        (runRefillT bits draw computation oracle record touched).bind
          (continueT bits draw f) := by
  induction computation with
  | pure value =>
      intro oracle record touched
      simp only [runRefillT, PMF.pure_bind, continueT]
      rfl
  | query request next ih =>
      intro oracle record touched
      show runRefillT bits draw (.query request fun answer => next answer >>= f) oracle record
        touched = _
      simp only [runRefillT]
      split
      · rename_i answer intercepted
        exact ih _ _ _ _
      · rename_i intercepted
        split
        · rename_i cell consumed
          rw [PMF.bind_bind]
          refine congrArg _ (funext fun value => ?_)
          split
          · simp only [PMF.pure_bind, continueT]
          · exact ih _ _ _ _
        · rename_i consumed
          rw [PMF.bind_bind]
          exact congrArg _ (funext fun answer => ih _ _ _ _)

end

end Kriterion.ArgoMAC.Phase3.Lazy
