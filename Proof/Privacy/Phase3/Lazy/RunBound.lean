/-
**Phase 3, P4 — the `I^U` opening against `I`'s: `Σ_v δ_{lane v}`.**

* `refillRun_etvDist_le` — the `I^U` run (mask tape) against `runIntercept`: the tape bias
  `Σ_{v : VectorSite} laneDelta (lane v)` (`uniformMaskTape_etvDist_le`), then eager = lazy
  (`uniform_bind_runRefill`), then fresh uniform answers are `I`'s run, exactly
  (`runRefill_uniform_eq`). No per-query term.
* `refillStage2_etvDist_le` — the same bound for the two stage-2 kernels: the rest of the opening
  (tail, lifts, the designated vector's free coordinates and collector solve, its `362` hash
  answers, the `362` programs) is a common continuation.
-/

import Proof.Privacy.Phase3.Lazy.StepBound

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.Phase3 (VectorSite laneDelta)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The `I^U` run against `I`'s**: the tape bias `Σ_v δ_{lane v}`, nothing per query. -/
theorem refillRun_etvDist_le (bits : BitInput) {α : Type}
    (computation : FreeQuery Programs.Spec α) (oracle : LState) :
    (refillRun bits computation oracle).etvDist
        ((runIntercept bits computation oracle noRecord).map some) ≤
      ∑ site : VectorSite, laneDelta site.lane := by
  unfold refillRun
  rw [← runRefill_uniform_eq bits computation oracle noRecord ∅, ← uniform_bind_runRefill]
  exact le_trans (PMF.etvDist_bind_right_le _ _ _) uniformMaskTape_etvDist_le

/-- **The `I^U` opening against `I`'s.** -/
theorem refillOpening_etvDist_le [FieldCertificate] [GroupCertificate] (samplers : Samplers)
    (table : Public) (input : AffineInput) (labels : LamportSignature) (target : Point)
    (oracle : LState) :
    (refillOpening samplers table input labels target oracle).etvDist
        (opening samplers table input labels target oracle) ≤
      ∑ site : VectorSite, laneDelta site.lane := by
  let K := fun ran : Option (((Fin pointElementCountX → BaseField) ×
      (Fin pointElementCountY → BaseField)) × LState × Record) => match ran with
    | none => PMF.pure none
    | some ran => openingCont samplers table input labels target ran
  have openingForm : opening samplers table input labels target oracle =
      ((runIntercept (Lamport.restore input labels).input
          (openingQueriesM table (Lamport.restore input labels).input
            (Lamport.restore input labels).inputMac) oracle noRecord).map some).bind K := by
    rw [opening_eq, PMF.bind_map]
    rfl
  rw [openingForm]
  exact le_trans (PMF.etvDist_bind_right_le K _ _) (refillRun_etvDist_le _ _ oracle)

/-- **The two stage-2 kernels.** -/
theorem refillStage2_etvDist_le [FieldCertificate] [GroupCertificate] (samplers : Samplers)
    (source : Stage1Source) (input : AffineInput) (output : Option Point) (oracle : LState) :
    (refillStage2 samplers source input output oracle).etvDist
        ((planBAbstractSimulator samplers).stage2 source input output oracle) ≤
      ∑ site : VectorSite, laneDelta site.lane := by
  cases output with
  | none =>
      simp only [refillStage2, planBAbstractSimulator, PMF.etvDist_self]
      exact zero_le
  | some target =>
      exact le_trans (PMF.etvDist_map_le _ _ _) (refillOpening_etvDist_le _ _ _ _ _ _)

end

end Kriterion.ArgoMAC.Phase3.Lazy
