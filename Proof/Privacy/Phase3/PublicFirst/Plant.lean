/-
**Phase 3, P1d (P1b's step 2) — planting EncPRF pairs before a run versus after it.**

`EncRel planted sF sL`: the lazy state `sF` is `sL` with the EncPRF pairs of `planted` planted on
top (fixed-key and hash components equal, every EncPRF component `SparseRel`). A query **touches**
the planted pairs (`EncTouch`) when it is an EncPRF query whose input is planted or whose fresh
answer is a planted output (forward), or symmetrically (inverse).

`runFlag planted A s` runs `A` lazily from `s` and returns `none` at the first touching query.

**`plant_ge`** (the planting lemma, flag-down form): for continuations that agree on related states,
the run planted first dominates, outcome by outcome, the run planted later restricted to the runs
that never touch the planted pairs:

  `flagBind (runFlag planted A sL) KL (some x) ≤ ((run A sF).bind KF) x`.

Nothing is lost off a touch: at a fresh EncPRF input the earlier answer is uniform on the smaller set
`Unknown sL ∖ range planted`, so each untouched later answer has at least its mass on the earlier
side (`sparse_forward_step`). The touch mass itself is paid by the caller, in the later game, where
the planted pairs are independent of the run.
-/

import Proof.Privacy.Phase3.PublicFirst.SparseStep

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open Cryptography GarbledCircuit
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- `sF` is `sL` with the EncPRF pairs of `planted` planted on top. -/
structure EncRel (planted sF sL : LazyOracle.State FixedIndex EncIndex) : Prop where
  fixed : sF.fixed = sL.fixed
  hash : sF.hash = sL.hash
  enc : ∀ index, SparseRel (sF.enc index) (sL.enc index) (lk (planted.enc index))
    (lk (planted.enc index).reverse)

/-- A query touches the planted EncPRF pairs. -/
def EncTouch (planted : LazyOracle.State FixedIndex EncIndex) :
    (request : PublicQuery FixedIndex EncIndex) → request.Answer → Prop
  | .encForward index input, answer =>
      TouchForward (lk (planted.enc index)) (lk (planted.enc index).reverse) input.toFin answer.toFin
  | .encInverse index output, answer =>
      TouchForward (lk (planted.enc index).reverse) (lk (planted.enc index)) output.toFin answer.toFin
  | .fixedForward _ _, _ => False
  | .fixedInverse _ _, _ => False
  | .hash _, _ => False

instance (planted : LazyOracle.State FixedIndex EncIndex) (request : PublicQuery FixedIndex EncIndex)
    (answer : request.Answer) : Decidable (EncTouch planted request answer) := by
  cases request <;> unfold EncTouch <;> infer_instance

/-- **One query of the lazy oracle**, planted first against planted later. -/
theorem query_step {planted sF sL : LazyOracle.State FixedIndex EncIndex}
    (rel : EncRel planted sF sL) (request : PublicQuery FixedIndex EncIndex)
    (hF hL : request.Answer × LazyOracle.State FixedIndex EncIndex → ℝ≥0∞)
    (mono : ∀ a sF' sL', EncRel planted sF' sL' → hL (a, sL') ≤ hF (a, sF')) :
    ∑' o, LazyOracle.query request sL o * (if EncTouch planted request o.1 then 0 else hL o)
      ≤ ∑' o, LazyOracle.query request sF o * hF o := by
  classical
  cases request with
  | fixedForward index input =>
    simp only [LazyOracle.query]
    rw [tsum_map_mul, tsum_map_mul, show sF.fixed index = sL.fixed index from congrFun rel.fixed index]
    refine ENNReal.tsum_le_tsum fun o => ?_
    rw [if_neg (by simp [EncTouch])]
    exact mul_le_mul' le_rfl (mono _ _ _ ⟨by simp [rel.fixed], rel.hash, rel.enc⟩)
  | fixedInverse index output =>
    simp only [LazyOracle.query]
    rw [tsum_map_mul, tsum_map_mul, show sF.fixed index = sL.fixed index from congrFun rel.fixed index]
    refine ENNReal.tsum_le_tsum fun o => ?_
    rw [if_neg (by simp [EncTouch])]
    exact mul_le_mul' le_rfl (mono _ _ _ ⟨by simp [rel.fixed], rel.hash, rel.enc⟩)
  | hash input =>
    simp only [LazyOracle.query]
    rw [tsum_map_mul, tsum_map_mul, rel.hash]
    refine ENNReal.tsum_le_tsum fun o => ?_
    rw [if_neg (by simp [EncTouch])]
    exact mul_le_mul' le_rfl (mono _ _ _ ⟨rel.fixed, rfl, rel.enc⟩)
  | encForward index input =>
    simp only [LazyOracle.query]
    rw [tsum_map_mul, tsum_map_mul]
    refine sparse_forward_step (rel.enc index) input.toFin
      (fun o => hF (BitVec.ofFin o.1, { sF with enc := Function.update sF.enc index o.2 }))
      (fun o => hL (BitVec.ofFin o.1, { sL with enc := Function.update sL.enc index o.2 }))
      (fun a sF' sL' related => mono _ _ _ ⟨rel.fixed, rel.hash, fun other => ?_⟩)
    by_cases same : other = index
    · subst same
      simpa using related
    · simpa [Function.update_of_ne same] using rel.enc other
  | encInverse index output =>
    simp only [LazyOracle.query]
    rw [tsum_map_mul, tsum_map_mul]
    refine sparse_inverse_step (rel.enc index) output.toFin
      (fun o => hF (BitVec.ofFin o.1, { sF with enc := Function.update sF.enc index o.2 }))
      (fun o => hL (BitVec.ofFin o.1, { sL with enc := Function.update sL.enc index o.2 }))
      (fun a sF' sL' related => mono _ _ _ ⟨rel.fixed, rel.hash, fun other => ?_⟩)
    by_cases same : other = index
    · subst same
      simpa using related
    · simpa [Function.update_of_ne same] using rel.enc other

/-- The lazy run that stops (`none`) at the first query touching the planted EncPRF pairs. -/
def runFlag (planted : LazyOracle.State FixedIndex EncIndex) {Result : Type} :
    {budget : ℕ} → OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget →
      LazyOracle.State FixedIndex EncIndex →
        PMF (Option (Result × LazyOracle.State FixedIndex EncIndex))
  | _, .pure distribution, state => distribution.map fun result => some (result, state)
  | _, .query request next, state => (LazyOracle.query request state).bind fun o =>
      if EncTouch planted request o.1 then PMF.pure none else runFlag planted (next o.1) o.2
  | _, .sample distribution next, state => distribution.bind fun value =>
      runFlag planted (next value) state

/-- A flagged run followed by a continuation; the flag stays up. -/
def flagBind {α S β : Type} (flagged : PMF (Option (α × S))) (continuation : α → S → PMF β) :
    PMF (Option β) :=
  flagged.bind fun o => match o with
    | none => PMF.pure none
    | some r => (continuation r.1 r.2).map some

theorem map_some_apply {β : Type} (law : PMF β) (x : β) : (law.map some) (some x) = law x := by
  rw [PMF.map_apply, tsum_eq_single x]
  · rw [if_pos rfl]
  · intro other different
    rw [if_neg (fun same => different (Option.some.inj same).symm)]

/-- **The planting lemma.** -/
theorem plant_ge (planted : LazyOracle.State FixedIndex EncIndex) {Result β : Type}
    (KF KL : Result → LazyOracle.State FixedIndex EncIndex → PMF β)
    (agree : ∀ r sF' sL', EncRel planted sF' sL' → KL r sL' = KF r sF') {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget) :
    ∀ (sF sL : LazyOracle.State FixedIndex EncIndex), EncRel planted sF sL → ∀ x,
      flagBind (runFlag planted program sL) KL (some x)
        ≤ ((LazyOracle.run program sF).bind fun r => KF r.1 r.2) x := by
  classical
  induction program with
  | pure distribution =>
    intro sF sL rel x
    simp only [flagBind, runFlag, LazyOracle.run, runSampled, PMF.bind_map, Function.comp_def]
    rw [PMF.bind_apply, PMF.bind_apply]
    refine ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl ?_
    rw [map_some_apply, agree r sF sL rel]
  | query request next ih =>
    intro sF sL rel x
    simp only [flagBind, runFlag, LazyOracle.run, runSampled, PMF.bind_bind]
    rw [PMF.bind_apply, PMF.bind_apply]
    have step := query_step rel request
      (fun o => ((LazyOracle.run (next o.1) o.2).bind fun r => KF r.1 r.2) x)
      (fun o => flagBind (runFlag planted (next o.1) o.2) KL (some x))
      (fun a sF' sL' related => ih a sF' sL' related x)
    refine le_trans (le_of_eq (tsum_congr fun o => ?_)) step
    congr 1
    split_ifs
    · simp
    · rfl
  | sample distribution next ih =>
    intro sF sL rel x
    simp only [flagBind, runFlag, LazyOracle.run, runSampled, PMF.bind_bind]
    rw [PMF.bind_apply, PMF.bind_apply]
    exact ENNReal.tsum_le_tsum fun v => mul_le_mul' le_rfl (ih v sF sL rel x)

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
