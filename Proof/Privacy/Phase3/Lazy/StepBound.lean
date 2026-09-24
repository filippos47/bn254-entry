/-
**Phase 3, P4 — fresh uniform answers against the lazy oracle: exactly `I`'s run.**

A lazy hash query at an input the table does not hold draws a uniform answer and stores it
(`HashTable.query`); a hash program at such an input stores the given answer
(`LazyOracle.program (.hash _)` needs only a fresh input). So:

* `query_hash_fresh` — **one consumed query.** At a fresh input, programming a uniform answer is
  the lazy hash query, exactly (both are the uniform answer and the table extended by it).
* `runRefill_uniform_eq` — **the whole run**: the intermediate run (`runRefill` with a fresh
  uniform answer per consumed cell) *is* `I`'s run (`Glue.runIntercept`), for an arbitrary query
  computation. There is no answer exclusion (hash answers may collide), so the lazy refill costs
  nothing: `idealRefillError = 0`.

Also here: `query_frame` (a lazy query changes the fixed-key state only at the index it touches)
and the shared-first-draw bound `etvDist_bind_le_of_support`.
-/

import Proof.Privacy.Phase3.Lazy.EagerLazy

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.Phase3 (etvDist_bind_left_le)
open scoped ENNReal

noncomputable section

/-- A shared first draw whose two continuations are `c`-close on its support. -/
theorem etvDist_bind_le_of_support {α β : Type} (p : PMF α) (f g : α → PMF β) (c : ℝ≥0∞)
    (close : ∀ a ∈ p.support, (f a).etvDist (g a) ≤ c) :
    (p.bind f).etvDist (p.bind g) ≤ c := by
  refine le_trans (etvDist_bind_left_le p f g) ?_
  calc (∑' a, (f a).etvDist (g a) * p a) ≤ ∑' a, c * p a := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases zero : p a = 0
        · rw [zero, mul_zero, mul_zero]
        · exact mul_le_mul_left (close a ((PMF.mem_support_iff _ _).mpr zero)) _
    _ = c := by rw [ENNReal.tsum_mul_left, p.tsum_coe, mul_one]

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The frame of a lazy query -/

/-- The fixed-key index a request touches, if any. -/
def touchedIndex : Request → Option FixedIndex
  | .fixedForward index _ => some index
  | .fixedInverse index _ => some index
  | .encForward _ _ => none
  | .encInverse _ _ => none
  | .hash _ => none

/-- A lazy query changes the fixed-key state only at the index it touches. -/
theorem query_frame (request : Request) (oracle : LState)
    (answer : request.Answer × LState)
    (member : answer ∈ (LazyOracle.query request oracle).support) (index : FixedIndex)
    (other : touchedIndex request ≠ some index) : answer.2.fixed index = oracle.fixed index := by
  cases request with
  | fixedForward touched input =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      have different : index ≠ touched := fun same => other (by rw [same]; rfl)
      exact Function.update_of_ne different _ _
  | fixedInverse touched output =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      have different : index ≠ touched := fun same => other (by rw [same]; rfl)
      exact Function.update_of_ne different _ _
  | encForward _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl
  | encInverse _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl
  | hash _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl

/-! ### One hash query, lazily and programmed -/

/-- A hash program stores its answer at a fresh input and fails at a stored one. -/
theorem program_hash_eq (input : BaseField) (value : Block × Block) (oracle : LState) :
    LazyOracle.program (.hash input) value oracle =
      if oracle.hash.lookup input = none then
        some { oracle with
          hash := oracle.hash.program input (Fintype.equivFin (Block × Block) value) }
      else none := rfl

/-- `program_hash_eq` at a refill answer. -/
theorem program_hash_refill (input : BaseField) (value : Block × Block) (oracle : LState) :
    LazyOracle.program (.hash input) (refillAnswer (.hash input) value) oracle =
      if oracle.hash.lookup input = none then
        some { oracle with
          hash := oracle.hash.program input (Fintype.equivFin (Block × Block) value) }
      else none := rfl

/-- A lazy hash query is the table's own query. -/
theorem query_hash_eq (input : BaseField) (oracle : LState) :
    (LazyOracle.query (.hash input) oracle : PMF ((Block × Block) × LState)) =
      (oracle.hash.query Fintype.card_pos input).distribution.map
        (fun answer => ((Fintype.equivFin (Block × Block)).symm answer.1,
          { oracle with hash := answer.2 })) := rfl

/-- A lazy hash query at a stored input returns the stored answer and changes nothing. -/
theorem query_hash_bind_found {β : Type} (input : BaseField) (oracle : LState)
    (value : Fin (Fintype.card (Block × Block))) (found : oracle.hash.lookup input = some value)
    (f : (PublicQuery.hash input : Request).Answer × LState → PMF β) :
    (LazyOracle.query (.hash input) oracle).bind f =
      f ((Fintype.equivFin (Block × Block)).symm value, oracle) := by
  rw [query_hash_eq]
  have table : oracle.hash.query Fintype.card_pos input = .pure (value, oracle.hash) := by
    unfold HashTable.query
    rw [found]
  rw [table]
  simp only [Draw.distribution, PMF.pure_map]
  exact PMF.pure_bind _ _

/-- A lazy hash query at a fresh input draws a uniform answer and stores it. -/
theorem query_hash_bind_fresh {β : Type} (input : BaseField) (oracle : LState)
    (fresh : oracle.hash.lookup input = none)
    (f : (PublicQuery.hash input : Request).Answer × LState → PMF β) :
    (LazyOracle.query (.hash input) oracle).bind f =
      (PMF.uniformOfFintype (Fin (Fintype.card (Block × Block)))).bind fun value =>
        f ((Fintype.equivFin (Block × Block)).symm value,
          { oracle with hash := (input, value) :: oracle.hash }) := by
  rw [query_hash_eq]
  have table : oracle.hash.query Fintype.card_pos input =
      .uniform _ Fintype.card_pos fun value => (value, (input, value) :: oracle.hash) := by
    unfold HashTable.query
    rw [fresh]
  rw [table]
  simp only [Draw.distribution, PMF.map_comp]
  exact PMF.bind_map _ _ _

/-- **One consumed query.** At a fresh input, the lazy hash query is a uniform answer programmed:
the answer is uniform and the table stores it, either way. -/
theorem query_hash_fresh (input : BaseField) (oracle : LState)
    (fresh : oracle.hash.lookup input = none) :
    (LazyOracle.query (.hash input) oracle).map some =
      (PMF.uniformOfFintype (Block × Block)).map fun value =>
        (LazyOracle.program (.hash input) (refillAnswer (.hash input) value) oracle).map
          fun updated => (refillAnswer (.hash input) value, updated) := by
  show (LazyOracle.query (.hash input) oracle : PMF ((Block × Block) × LState)).map some =
      (PMF.uniformOfFintype (Block × Block)).map fun value =>
        (LazyOracle.program (.hash input) value oracle).map fun updated => (value, updated)
  rw [query_hash_eq]
  have table : oracle.hash.query Fintype.card_pos input =
      .uniform _ Fintype.card_pos fun value => (value, (input, value) :: oracle.hash) := by
    unfold HashTable.query
    rw [fresh]
  rw [table]
  simp only [Draw.distribution, PMF.map_comp]
  rw [← uniform_equiv (Fintype.equivFin (Block × Block))]
  erw [PMF.map_comp, PMF.map_comp]
  refine congrArg (fun f => PMF.map f _) (funext fun value => ?_)
  rw [program_hash_eq, if_pos fresh, Option.map_some]
  show some ((Fintype.equivFin (Block × Block)).symm ((Fintype.equivFin (Block × Block)) value),
      ({ oracle with hash := (input, (Fintype.equivFin (Block × Block)) value) :: oracle.hash } :
        LState)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-! ### The whole run -/

/-- **Fresh uniform answers are `I`'s run**, for any query computation: the refill runner drawing
a uniform answer at each consumed cell is the intercepting run, exactly. -/
theorem runRefill_uniform_eq (bits : BitInput) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell),
      runRefill bits (fun _ => PMF.uniformOfFintype (Block × Block)) computation oracle record
          touched = (runIntercept bits computation oracle record).map some := by
  induction computation with
  | pure value =>
      intro oracle record touched
      simp only [runRefill, runIntercept, PMF.pure_map]
  | query request next ih =>
      intro oracle record touched
      simp only [runRefill, runIntercept]
      split
      · rename_i answer intercepted
        simp only [intercepted]
        exact ih _ _ _ _
      · rename_i intercepted
        simp only [intercepted]
        split
        · rename_i cell consumed
          obtain ⟨input, rfl, _, fresh, _⟩ := consumeCell_spec consumed
          let K : Option ((PublicQuery.hash input : Request).Answer × LState) →
              PMF (Option (_ × LState × Record)) := fun step => match step with
            | none => PMF.pure none
            | some step => runRefill bits (fun _ => PMF.uniformOfFintype (Block × Block))
                (next step.1) step.2 record (touch (.hash input) touched)
          have left : ((PMF.uniformOfFintype (Block × Block)).bind fun value =>
              match LazyOracle.program (.hash input) (refillAnswer (.hash input) value) oracle with
              | none => PMF.pure none
              | some updated => runRefill bits (fun _ => PMF.uniformOfFintype (Block × Block))
                  (next (refillAnswer (.hash input) value)) updated record
                  (touch (.hash input) touched)) =
              ((LazyOracle.query (.hash input) oracle).map some).bind K := by
            rw [query_hash_fresh input oracle fresh, PMF.bind_map]
            refine congrArg _ (funext fun value => ?_)
            rw [Function.comp_apply]
            dsimp only [K]
            cases LazyOracle.program (.hash input) (refillAnswer (.hash input) value) oracle <;> rfl
          refine left.trans ?_
          rw [PMF.bind_map, PMF.map_bind]
          exact congrArg _ (funext fun answer => ih _ _ _ _)
        · rw [PMF.map_bind]
          exact congrArg _ (funext fun answer => ih _ _ _ _)

end

end Kriterion.ArgoMAC.Phase3.Lazy
