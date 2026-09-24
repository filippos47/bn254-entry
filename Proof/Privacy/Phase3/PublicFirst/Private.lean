/-
**Phase 3, P1e — the private run: its base, its merge, the designated installation, extra queries.**

The middle game runs the simulator's stage 2 on a private empty oracle `τ` and continues on the
stage-1 state `σ₁` *overlaid* with `τ`. This module supplies the pieces around `runRefill_ge`:

* `fullRel_base` — every state is related to the empty one by planting itself:
  `FullRel σ₁ σ₁ empty`;
* `sameLookups_of_fullRel` — two states related to the same `(σ₁, τ)` have the same lookups, so
  **`mergeChoice σ₁ τ`** (any state related to `(σ₁, τ)`, by choice) is the merge, up to lookups
  (`mergeChoice_sameLookups`); no installation order is needed;
* `programAllSkipFlag` / `programAllSkip_rel` — the designated installation (skip semantics),
  flagged at a touch, keeps the relation;
* `runLazyQ` / `runLazyQFlag` / `runLazyQ_ge` — extra lazy queries (the shadow of `G1U`'s
  `G1U`-only entries) run privately and flagged are dominated by the same queries on the shared
  state, and **`discard_run`**: on the shared state extra lazy queries whose answers are discarded
  do not change the law of any later adversary run (eager/lazy: P3's `public_step`,
  `public_run_result`).
-/

import Proof.Privacy.Phase3.PublicFirst.FullRel
import Proof.Privacy.Phase3.PublicFirst.Install

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open Cryptography GarbledCircuit
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion public_step public_run_result)
open scoped ENNReal

noncomputable section

section Generic

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-! ### The base and the merge -/

omit [DecidableEq FixedIndex] [DecidableEq EncIndex] in
theorem sparseRel_base {size : ℕ} (planted : SparsePermutation size) :
    SparseRel planted (SparsePermutation.empty size) (lk planted) (lk planted.reverse) where
  lookup z := by
    have none : lk (SparsePermutation.empty size) z = none := by
      rw [lk_eq, if_neg]
      show ¬ _ < 0
      omega
    rw [none]
    cases lk planted z <;> rfl
  inverse z y := (lookup_reverse planted z y).symm
  freshInput z _ := by
    rw [lk_eq, if_neg]
    show ¬ _ < 0
    omega
  freshOutput y _ w := by
    rw [lk_eq, if_neg]
    · simp
    · show ¬ _ < 0
      omega

/-- **Every state is the empty one with itself planted.** -/
theorem fullRel_base (planted : LazyOracle.State FixedIndex EncIndex) :
    FullRel planted planted LazyOracle.empty where
  fixed index := sparseRel_base (planted.fixed index)
  enc index := sparseRel_base (planted.enc index)
  hash := ⟨fun k => by cases planted.hash.lookup k <;> rfl, fun _ _ => rfl⟩

/-- **Two states related to the same `(planted, sL)` answer every lookup alike.** -/
theorem sameLookups_of_fullRel {planted first second sL : LazyOracle.State FixedIndex EncIndex}
    (one : FullRel planted first sL) (two : FullRel planted second sL) :
    SameLookups first second :=
  sameLookups_of_forward (fun i z => by rw [(one.fixed i).lookup, (two.fixed i).lookup])
    (fun i z => by rw [(one.enc i).lookup, (two.enc i).lookup])
    (fun k => by rw [one.hash.lookup, two.hash.lookup])

instance lazyStateNonempty : Nonempty (LazyOracle.State FixedIndex EncIndex) :=
  ⟨LazyOracle.empty⟩

/-- **The merge**: a state with `planted` overlaid on `sL`, by choice. -/
def mergeChoice (planted sL : LazyOracle.State FixedIndex EncIndex) :
    LazyOracle.State FixedIndex EncIndex :=
  Classical.epsilon fun merged => FullRel planted merged sL

theorem mergeChoice_sameLookups {planted sF sL : LazyOracle.State FixedIndex EncIndex}
    (rel : FullRel planted sF sL) : SameLookups (mergeChoice planted sL) sF :=
  sameLookups_of_fullRel (Classical.epsilon_spec (p := fun merged => FullRel planted merged sL)
    ⟨sF, rel⟩) rel

/-! ### Extra lazy queries -/

/-- A query computation run on the lazy oracle. -/
def runLazyQ {α : Type} : FreeQuery (publicOracleSpec FixedIndex EncIndex) α →
    LazyOracle.State FixedIndex EncIndex → PMF (α × LazyOracle.State FixedIndex EncIndex)
  | .pure value, state => PMF.pure (value, state)
  | .query request next, state => (LazyOracle.query request state).bind fun answer =>
      runLazyQ (next answer.1) answer.2

/-- The same, stopped (`none`) at the first query touching `planted`. -/
def runLazyQFlag (planted : LazyOracle.State FixedIndex EncIndex) {α : Type} :
    FreeQuery (publicOracleSpec FixedIndex EncIndex) α →
      LazyOracle.State FixedIndex EncIndex → PMF (Option (α × LazyOracle.State FixedIndex EncIndex))
  | .pure value, state => PMF.pure (some (value, state))
  | .query request next, state => (LazyOracle.query request state).bind fun answer =>
      if FullTouch planted request answer.1 then PMF.pure none
      else runLazyQFlag planted (next answer.1) answer.2

/-- **Extra queries, private and flagged against shared.** -/
theorem runLazyQ_ge (planted : LazyOracle.State FixedIndex EncIndex) {α : Type}
    (hF hL : α × LazyOracle.State FixedIndex EncIndex → ℝ≥0∞)
    (mono : ∀ a sF sL, FullRel planted sF sL → hL (a, sL) ≤ hF (a, sF))
    (computation : FreeQuery (publicOracleSpec FixedIndex EncIndex) α) :
    ∀ sF sL, FullRel planted sF sL →
      ∑' o, runLazyQFlag planted computation sL o * flagged hL o
        ≤ ∑' o, runLazyQ computation sF o * hF o := by
  induction computation with
  | pure value =>
    intro sF sL rel
    simp only [runLazyQFlag, runLazyQ, tsum_pure_mul, flagged]
    exact mono value sF sL rel
  | query request next ih =>
    intro sF sL rel
    simp only [runLazyQFlag, runLazyQ]
    rw [tsum_bind_mul, tsum_bind_mul]
    refine le_trans (le_of_eq (tsum_congr fun o => ?_)) (full_query_step rel request
      (fun o => ∑' r, runLazyQ (next o.1) o.2 r * hF r)
      (fun o => ∑' r, runLazyQFlag planted (next o.1) o.2 r * flagged hL r)
      (fun a sF' sL' related => ih a sF' sL' related))
    congr 1
    split_ifs
    · simp [tsum_pure_mul, flagged]
    · rfl

variable [Fintype FixedIndex] [Fintype EncIndex]

/-- The completion law survives one lazy query whose answer is discarded. -/
theorem query_bind_completion (request : PublicQuery FixedIndex EncIndex)
    (state : LazyOracle.State FixedIndex EncIndex) :
    (LazyOracle.query request state).bind (fun answer => publicCompletion answer.2)
      = publicCompletion state := by
  have step := congrArg (PMF.map Prod.snd) (public_step request state)
  rw [PMF.map_comp, PMF.map_bind] at step
  have handler : (Prod.snd ∘ publicHandler id request) = id := by
    funext complete
    rfl
  rw [handler, PMF.map_id] at step
  rw [step]
  congr 1
  funext answer
  rw [PMF.map_comp]
  exact (PMF.map_id _).symm

/-- **Discarded extra queries leave every later run's law unchanged.** -/
theorem discard_run {α Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (computation : FreeQuery (publicOracleSpec FixedIndex EncIndex) α) :
    ∀ state, (runLazyQ computation state).bind (fun r => (LazyOracle.run program r.2).map Prod.fst)
      = (LazyOracle.run program state).map Prod.fst := by
  induction computation with
  | pure value =>
    intro state
    simp only [runLazyQ, PMF.pure_bind]
  | query request next ih =>
    intro state
    simp only [runLazyQ, PMF.bind_bind]
    simp_rw [ih]
    simp_rw [← public_run_result]
    rw [← PMF.bind_bind, query_bind_completion]

end Generic

/-! ### The designated installation -/

section Designated

open BN254 Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Phase3.Lazy (LState)

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- `programAllSkip`, stopped (`none`) at the first program touching `planted` (at a planted hash
key). -/
def programAllSkipFlag (planted : LState) :
    List (Option BaseField × (Block × Block)) → LState → Option LState
  | [], oracle => some oracle
  | (input, answer) :: rest, oracle => match input with
    | none => programAllSkipFlag planted rest oracle
    | some input =>
      if planted.hash.lookup input ≠ none then none
      else programAllSkipFlag planted rest
        ((LazyOracle.program (.hash input) answer oracle).getD oracle)

/-- **The designated installation keeps the relation** when no program touches `planted`. -/
theorem programAllSkip_rel (planted : LState)
    (requests : List (Option BaseField × (Block × Block))) :
    ∀ sF sL, FullRel planted sF sL → ∀ τ, programAllSkipFlag planted requests sL = some τ →
      FullRel planted (programAllSkip requests sF) τ := by
  induction requests with
  | nil =>
    intro sF sL rel τ done
    simp only [programAllSkipFlag, Option.some.injEq] at done
    subst done
    exact rel
  | cons request rest ih =>
    intro sF sL rel τ done
    obtain ⟨input, answer⟩ := request
    cases input with
    | none => exact ih sF sL rel τ done
    | some input =>
      simp only [programAllSkipFlag] at done
      split_ifs at done with touching
      rcases program_hash_rel rel input answer (not_not.mp touching) with
        ⟨tF, tL, successF, successL, related⟩ | ⟨failF, failL⟩
      · rw [successL, Option.getD_some] at done
        show FullRel planted (programAllSkip rest ((LazyOracle.program _ _ sF).getD sF)) τ
        rw [successF, Option.getD_some]
        exact ih tF tL related τ done
      · rw [failL, Option.getD_none] at done
        show FullRel planted (programAllSkip rest ((LazyOracle.program _ _ sF).getD sF)) τ
        rw [failF, Option.getD_none]
        exact ih sF sL rel τ done

end Designated

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
