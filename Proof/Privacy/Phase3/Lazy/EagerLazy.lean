/-
**Phase 3, P4 — the `I^U` tape: from the mask tape to fresh uniform answers.**

Two exact or data-processing steps on the refill runner, for an arbitrary query computation:

* `uniformMaskTape_etvDist_le` — **the per-vector bias, `Σ_v δ_{lane v}`**: the `I^U` tape (the
  `5,584` vectors uniform on `F_p^n`, the tape uniform on the `sampleLane` fibre) is within
  `Σ_{v : VectorSite} laneDelta (lane v)` of a uniform tape. Both are the same fibre kernel behind
  two vector laws (P1's `uniform_eq_bind_fibreLaw`), so the distance is the vectors'
  (`masksOf_etvDist_le`).
* `uniform_bind_runRefill` — **eager = lazy, exactly**: running on a uniform tape is running with a
  fresh uniform answer drawn at each consumed cell. A cell is consumed only when it is not yet
  touched, and it is touched from then on (`runRefill_tape_congr`: the run reads the tape only at
  untouched cells), so each cell is read at most once and its answer is a fresh uniform answer
  independent of everything read before (`uniform_update_eq`).
-/

import Proof.Privacy.Phase3.Lazy.Refill

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.Phase3 (VectorSite MaskVectors masksOf masksOf_surjective fibreLaw
  uniform_eq_bind_fibreLaw masksOf_etvDist_le laneDelta)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The per-vector bias -/

/-- **`I^U`'s tape is `Σ_v δ_{lane v}`-close to a uniform tape.** -/
theorem uniformMaskTape_etvDist_le :
    uniformMaskTape.etvDist (PMF.uniformOfFintype Tape) ≤
      ∑ site : VectorSite, laneDelta site.lane := by
  calc uniformMaskTape.etvDist (PMF.uniformOfFintype Tape)
      = ((PMF.uniformOfFintype MaskVectors).bind
            (fibreLaw (masksOf VectorSite.lane) (masksOf_surjective VectorSite.lane))).etvDist
          (((PMF.uniformOfFintype Tape).map (masksOf VectorSite.lane)).bind
            (fibreLaw (masksOf VectorSite.lane) (masksOf_surjective VectorSite.lane))) := by
        rw [uniformMaskTape, ← uniform_eq_bind_fibreLaw]
    _ ≤ (PMF.uniformOfFintype MaskVectors).etvDist
          ((PMF.uniformOfFintype Tape).map (masksOf VectorSite.lane)) :=
        PMF.etvDist_bind_right_le _ _ _
    _ = ((PMF.uniformOfFintype Tape).map (masksOf VectorSite.lane)).etvDist
          (PMF.uniformOfFintype MaskVectors) := PMF.etvDist_comm _ _
    _ ≤ ∑ site : VectorSite, laneDelta site.lane := masksOf_etvDist_le VectorSite.lane

/-! ### Locality: the run reads the tape only at untouched cells -/

/-- Two tapes that agree at every cell not yet touched give the same run. -/
theorem runRefill_tape_congr (bits : BitInput) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell) (first second : Tape),
      (∀ cell, cell ∉ touched → first cell = second cell) →
      runRefill bits (fun cell => PMF.pure (first cell)) computation oracle record touched =
        runRefill bits (fun cell => PMF.pure (second cell)) computation oracle record touched := by
  induction computation with
  | pure value => intros; rfl
  | query request next ih =>
      intro oracle record touched first second agree
      have later : ∀ cell, cell ∉ touch request touched → first cell = second cell :=
        fun cell notTouched => agree cell fun member => notTouched (subset_touch _ _ member)
      simp only [runRefill]
      split
      · exact ih _ _ _ _ _ _ agree
      · split
        · rename_i cell consumed
          obtain ⟨input, rfl, fresh, _, _⟩ := consumeCell_spec consumed
          rw [agree cell fresh]
          refine congrArg _ (funext fun value => ?_)
          split
          · rfl
          · exact ih _ _ _ _ _ _ later
        · exact congrArg _ (funext fun answer => ih _ _ _ _ _ _ later)

/-! ### Eager = lazy -/

/-- Overwrite one cell: `(v, t) ↦ (t[cell := v], t cell)` is a bijection. -/
def updateEquiv (cell : Cell) : ((Block × Block) × Tape) ≃ (Tape × (Block × Block)) where
  toFun pair := (Function.update pair.2 cell pair.1, pair.2 cell)
  invFun pair := (pair.1 cell, Function.update pair.1 cell pair.2)
  left_inv pair := by
    obtain ⟨value, tape⟩ := pair
    simp
  right_inv pair := by
    obtain ⟨tape, value⟩ := pair
    simp

/-- **A uniform tape is a uniform answer written over a uniform tape at any one cell.** -/
theorem uniform_update_eq (cell : Cell) :
    (PMF.uniformOfFintype ((Block × Block) × Tape)).map
        (fun pair => Function.update pair.2 cell pair.1) =
      PMF.uniformOfFintype Tape := by
  have factor : (fun pair : (Block × Block) × Tape => Function.update pair.2 cell pair.1) =
      Prod.fst ∘ updateEquiv cell := rfl
  rw [factor, ← PMF.map_comp, uniform_equiv (updateEquiv cell), uniform_map_fst]

/-- A uniform pair is two independent uniform draws. -/
theorem uniform_pair_bind {A B C : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (next : A × B → PMF C) :
    (PMF.uniformOfFintype (A × B)).bind next =
      (PMF.uniformOfFintype A).bind fun a => (PMF.uniformOfFintype B).bind fun b => next (a, b) := by
  rw [← uniform_product, PMF.bind_bind]
  congr 1
  funext a
  rw [PMF.bind_map]
  rfl

/-- **Eager = lazy.** A run on a uniform tape is the run that draws a fresh uniform answer at each
consumed cell. -/
theorem uniform_bind_runRefill (bits : BitInput) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell),
      (PMF.uniformOfFintype Tape).bind (fun tape =>
          runRefill bits (fun cell => PMF.pure (tape cell)) computation oracle record touched) =
        runRefill bits (fun _ => PMF.uniformOfFintype (Block × Block)) computation oracle record
          touched := by
  induction computation with
  | pure value =>
      intro oracle record touched
      exact PMF.bind_const _ _
  | query request next ih =>
      intro oracle record touched
      simp only [runRefill]
      split
      · exact ih _ _ _ _
      · split
        · rename_i cell consumed
          have marked := mem_touch_of_consumeCell consumed
          simp only [PMF.pure_bind]
          -- write the uniform tape as a uniform answer over a uniform tape at `cell`
          conv_lhs => rw [← uniform_update_eq cell, PMF.bind_map]
          have local_read : ∀ (value : Block × Block) (tape : Tape),
              (match LazyOracle.program request (refillAnswer request value) oracle with
                | none => PMF.pure none
                | some updated => runRefill bits
                    (fun cell' => PMF.pure (Function.update tape cell value cell'))
                    (next (refillAnswer request value)) updated record
                    (touch request touched)) =
              (match LazyOracle.program request (refillAnswer request value) oracle with
                | none => PMF.pure none
                | some updated => runRefill bits (fun cell' => PMF.pure (tape cell'))
                    (next (refillAnswer request value)) updated record
                    (touch request touched)) := by
            intro value tape
            split
            · rfl
            · refine runRefill_tape_congr bits _ _ _ _ _ _ fun cell' notTouched => ?_
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
          · rename_i hprog
            simp only [hprog]
            exact PMF.bind_const _ _
          · rename_i updated hprog
            simp only [hprog]
            exact ih _ _ _ _
        · rw [PMF.bind_comm]
          exact congrArg _ (funext fun answer => ih _ _ _ _)

end

end Kriterion.ArgoMAC.Phase3.Lazy
