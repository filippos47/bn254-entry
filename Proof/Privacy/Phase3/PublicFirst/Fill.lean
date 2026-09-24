/-
**Phase 3, P1g — the flagged refill without intercepts, and its uniform reading.**

`runFillFlag planted draw` is P4's refill runner without the designated intercepts, stopped
(`none`) at the first touch of `planted` (and at a failed program): the first hash question at an
untouched cell, at an input the lazy table does not hold (P4's `consumeCell`), programs
`input ↦ value` with `value` drawn from `draw`; every other question is lazy. It is the off-curve
private run of the middle game `M'` (`PublicFirst/MiddleOff.lean`), where the answers come from
P4's `uniformMaskTape` (uniform switch-mask vectors, as `G1U`'s swapped system-A entries).

* `uniform_bind_runFillFlag` — a uniform tape is a fresh uniform answer at each consumed cell (P4's
  `uniform_bind_runRefill`, for this runner);
* `runFillFlag_uniform_eq` — **with fresh uniform answers the runner is the flagged lazy run**
  `runLazyQFlag`: a consumed input is fresh, so its program never fails, and a lazy hash query at a
  fresh input is a uniform answer, stored (P4's `query_hash_fresh`).
-/

import Proof.Privacy.Phase3.PublicFirst.Private
import Proof.Privacy.Phase3.Lazy.StepBound

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape Request consumeCell refillAnswer touch
  subset_touch consumeCell_spec mem_touch_of_consumeCell uniform_update_eq uniform_pair_bind
  program_hash_refill query_hash_fresh)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The flagged refill runner without intercepts.** -/
def runFillFlag (planted : LState) (draw : Cell → PMF (Block × Block)) {α : Type} :
    FreeQuery Programs.Spec α → LState → Set Cell → PMF (Option (α × LState))
  | .pure value, oracle, _ => PMF.pure (some (value, oracle))
  | .query request next, oracle, touched =>
      match consumeCell touched oracle request with
      | some cell => (draw cell).bind fun value =>
          if FullTouch planted request (refillAnswer request value) then PMF.pure none else
          match LazyOracle.program request (refillAnswer request value) oracle with
          | none => PMF.pure none
          | some updated =>
              runFillFlag planted draw (next (refillAnswer request value)) updated
                (touch request touched)
      | none => (LazyOracle.query request oracle).bind fun answer =>
          if FullTouch planted request answer.1 then PMF.pure none else
          runFillFlag planted draw (next answer.1) answer.2 (touch request touched)

/-- The run reads the tape only at untouched cells. -/
theorem runFillFlag_tape_congr (planted : LState) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (touched : Set Cell) (first second : Tape),
      (∀ cell, cell ∉ touched → first cell = second cell) →
      runFillFlag planted (fun cell => PMF.pure (first cell)) computation oracle touched =
        runFillFlag planted (fun cell => PMF.pure (second cell)) computation oracle touched := by
  induction computation with
  | pure value => intros; rfl
  | query request next ih =>
      intro oracle touched first second agree
      have later : ∀ cell, cell ∉ touch request touched → first cell = second cell :=
        fun cell notTouched => agree cell fun member => notTouched (subset_touch _ _ member)
      simp only [runFillFlag]
      split
      · rename_i cell consumed
        obtain ⟨input, rfl, fresh, _, _⟩ := consumeCell_spec consumed
        rw [agree cell fresh]
        refine congrArg _ (funext fun value => ?_)
        split
        · rfl
        · split
          · rfl
          · exact ih _ _ _ _ _ later
      · refine congrArg _ (funext fun answer => ?_)
        split
        · rfl
        · exact ih _ _ _ _ _ later

/-- **Eager = lazy for the fill runner**: a uniform tape is a fresh uniform answer per consumed
cell. -/
theorem uniform_bind_runFillFlag (planted : LState) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (touched : Set Cell),
      (PMF.uniformOfFintype Tape).bind (fun tape =>
          runFillFlag planted (fun cell => PMF.pure (tape cell)) computation oracle touched) =
        runFillFlag planted (fun _ => PMF.uniformOfFintype (Block × Block)) computation oracle
          touched := by
  induction computation with
  | pure value =>
      intro oracle touched
      exact PMF.bind_const _ _
  | query request next ih =>
      intro oracle touched
      simp only [runFillFlag]
      split
      · rename_i cell consumed
        have marked := mem_touch_of_consumeCell consumed
        simp only [PMF.pure_bind]
        conv_lhs => rw [← uniform_update_eq cell, PMF.bind_map]
        have local_read : ∀ (value : Block × Block) (tape : Tape),
            (if FullTouch planted request (refillAnswer request value) then PMF.pure none else
              match LazyOracle.program request (refillAnswer request value) oracle with
              | none => PMF.pure none
              | some updated => runFillFlag planted
                  (fun cell' => PMF.pure (Function.update tape cell value cell'))
                  (next (refillAnswer request value)) updated (touch request touched)) =
            (if FullTouch planted request (refillAnswer request value) then PMF.pure none else
              match LazyOracle.program request (refillAnswer request value) oracle with
              | none => PMF.pure none
              | some updated => runFillFlag planted (fun cell' => PMF.pure (tape cell'))
                  (next (refillAnswer request value)) updated (touch request touched)) := by
          intro value tape
          split
          · rfl
          · split
            · rfl
            · refine runFillFlag_tape_congr planted _ _ _ _ _ fun cell' notTouched => ?_
              have different : cell' ≠ cell := by
                rintro rfl
                exact notTouched marked
              exact Function.update_of_ne different _ _
        simp only [Function.comp_def, Function.update_self]
        refine (congrArg (PMF.bind (PMF.uniformOfFintype ((Block × Block) × Tape)))
          (funext fun pair => local_read pair.1 pair.2)).trans ?_
        rw [uniform_pair_bind]
        refine congrArg _ (funext fun value => ?_)
        split
        · exact PMF.bind_const _ _
        · split
          · rename_i hprog
            simp only [hprog]
            exact PMF.bind_const _ _
          · rename_i updated hprog
            simp only [hprog]
            exact ih _ _ _
      · rw [PMF.bind_comm]
        refine congrArg _ (funext fun answer => ?_)
        split
        · exact PMF.bind_const _ _
        · exact ih _ _ _

/-- **With fresh uniform answers, the fill runner is the flagged lazy run.** -/
theorem runFillFlag_uniform_eq (planted : LState) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (touched : Set Cell),
      runFillFlag planted (fun _ => PMF.uniformOfFintype (Block × Block)) computation oracle
          touched = runLazyQFlag planted computation oracle := by
  induction computation with
  | pure value => intros; rfl
  | query request next ih =>
      intro oracle touched
      simp only [runFillFlag, runLazyQFlag]
      split
      · rename_i cell consumed
        obtain ⟨input, rfl, _, fresh, _⟩ := consumeCell_spec consumed
        let K : Option ((PublicQuery.hash input : Request).Answer × LState) →
            PMF (Option (_ × LState)) := fun step => match step with
          | none => PMF.pure none
          | some step => if FullTouch planted (.hash input) step.1 then PMF.pure none else
              runLazyQFlag planted (next step.1) step.2
        have left : ((PMF.uniformOfFintype (Block × Block)).bind fun value =>
            if FullTouch planted (.hash input) (refillAnswer (.hash input) value) then PMF.pure none
            else match LazyOracle.program (.hash input) (refillAnswer (.hash input) value) oracle with
            | none => PMF.pure none
            | some updated => runFillFlag planted (fun _ => PMF.uniformOfFintype (Block × Block))
                (next (refillAnswer (.hash input) value)) updated (touch (.hash input) touched)) =
            ((LazyOracle.query (.hash input) oracle).map some).bind K := by
          rw [query_hash_fresh input oracle fresh, PMF.bind_map]
          refine congrArg _ (funext fun value => ?_)
          rw [Function.comp_apply, program_hash_refill, if_pos fresh]
          dsimp only [K, Option.map_some]
          split
          · rfl
          · exact ih _ _ _
        refine left.trans ?_
        rw [PMF.bind_map]
        rfl
      · refine congrArg _ (funext fun answer => ?_)
        split
        · rfl
        · exact ih _ _ _

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
