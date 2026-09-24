/-
**Phase 3, P1m — (B1) the fixed-key part on the curve: outputs.**

The designated installation programs hash inputs only (`programRequests`: the `452` limbs of the
designated vector, at `designatedInput`), so it adds no fixed-key pair: every fixed-key pair of
`M'`'s private state is a lazy forward answer, at its index's canonical input (`final_fixed`), so at
most one per index (`final_used_le`). The designated entries' answers are hash answers, which the
fixed-key conjunct of `PerPairBound` never reads.

* `onCurve_whole_le` — on the curve, an event bounded at the final state by a potential of the whole
  process (not raised by any forward question, kept by every hash program) has mass at most the
  potential of the empty state;
* **`fixedOut_onCurve_le`** — `Pr[y ∈ fixedOut_i] ≤ 1/2^128` at every fixed-key index (`singleF`).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedPad

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source programRequests DesignatedLimbs)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Tape Request uniformMaskTape)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
variable [FieldCertificate] [GroupCertificate]

/-- **On the curve, an event bounded by a potential of the whole process has mass at most the
potential of the empty state.** -/
theorem onCurve_whole_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (Φ : LState → ℝ≥0∞)
    (hashSame : ∀ (state updated : LState) (input' : BaseField) (answer : Block × Block),
      LazyOracle.program (.hash input') answer state = some updated → Φ updated = Φ state)
    (step : ∀ (request : Request) (state : LState), ForwardOnly request →
      ∑' answer, LazyOracle.query request state answer * Φ answer.2 ≤ Φ state)
    (final : ∀ (tape : Tape)
      (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
        LState × Record), some ran ∈ (openingRun source input tape).support →
      ∀ (answers : DesignatedLimbs) (result : Unit × LState),
        result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
            ran.2.2 answers) ran.2.1)).support →
        ind (event ((pointsOf result.2).union (requestPoints (programRequests
          (restoredBits source input) ran.2.2 answers)))) ≤ Φ result.2) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind (event (outcomePoints o)) ≤ Φ LazyOracle.empty := by
  refine le_trans (onCurve_event_le scalar off source input target event Φ
    fun tape ran member answers => ?_) ?_
  · refine le_trans (tsum_mul_le_of_support _ _ (fun result => Φ result.2)
      fun result resultMember => final tape ran member answers result resultMember) ?_
    refine le_trans (runLazyQ_potential ForwardOnly Φ step _ (shadowOnM_forwardOnly _ _ _) _)
      (le_of_eq ?_)
    exact programAllSkip_potential Φ hashSame _ _
  · refine tsum_le_of_support _ _ _ fun tape _ => ?_
    unfold openingRun
    exact runRefill_potential_prog _ _ Φ hashSame step _ (openingQueriesM_forwardOnly _ _ _) _ _ _

/-- **On the curve, every fixed-key output has mass `≤ 1/2^128`.** -/
theorem fixedOut_onCurve_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (i : FixedIndex) (y : Block) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedOut i y) ≤ delta := by
  refine le_trans (onCurve_whole_le scalar off source input target (fun p => p.fixedOut i y)
    (fun state => singleF y.toFin (state.fixed i))
    (fun state updated input' answer success => by
      rw [(program_hash_pairs input' answer state updated success).1])
    (fun request state forward => fixed_lift_step i _ (singleF_step _) request forward state)
    fun tape ran member answers result resultMember => ?_) (le_of_eq ?_)
  · refine le_trans (ind_mono fun hit => ?_) (singleF_bound _ _
      (final_used_le source input tape ran member answers result resultMember i))
    rcases hit with ⟨x, found⟩ | never
    · exact ⟨x, found⟩
    · exact never.elim
  · show singleF y.toFin (SparsePermutation.empty _) = delta
    unfold singleF
    rw [if_pos (show (SparsePermutation.empty (2 ^ 128)).used = 0 from rfl)]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
