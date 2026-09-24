/-
**Phase 3, P4 — evaluator unfolding (6): the run never touches a designated input.**

The designated programs of `I^U` fail only against an entry at their own hash input
(`LazyOracle.program (.hash _)` needs only a fresh input). Those entries are exactly the stage-1
entries, because the refill run of the honest evaluation leaves the lookup of every designated
input as it found it (`runRefill_frame`): a designated hash query is intercepted and never reaches
the oracle; a consumed cell is programmed, and a lazy hash query answered, at its own
non-designated input (`program_lookup_frame`, `query_lookup_frame`); a fixed-key or EncPRF query
does not touch the hash table.
-/

import Proof.Privacy.Phase3.Lazy.Designated

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### One step -/

/-- The hash input a request asks, if any. -/
def askedInput : Request → Option BaseField
  | .fixedForward _ _ => none
  | .fixedInverse _ _ => none
  | .encForward _ _ => none
  | .encInverse _ _ => none
  | .hash input => some input

/-- One more entry at another key leaves a lookup as it was. -/
theorem lookup_cons_ne {Value : Type} (table : List (BaseField × Value)) (asked input : BaseField)
    (value : Value) (different : input ≠ asked) :
    ((asked, value) :: table).lookup input = table.lookup input := by
  have unequal : (input == asked) = false := beq_eq_false_iff_ne.mpr different
  simp only [List.lookup, unequal]

/-- **A lazy query changes the hash table only at the input it asks.** -/
theorem query_lookup_frame (request : Request) (oracle : LState)
    (answer : request.Answer × LState)
    (member : answer ∈ (LazyOracle.query request oracle).support) (input : BaseField)
    (other : askedInput request ≠ some input) :
    answer.2.hash.lookup input = oracle.hash.lookup input := by
  cases request with
  | fixedForward _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl
  | fixedInverse _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl
  | encForward _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl
  | encInverse _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl
  | hash asked =>
      obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      have different : input ≠ asked := fun same => other (by rw [same]; rfl)
      show drawn.2.lookup input = oracle.hash.lookup input
      unfold HashTable.query at drawnMember
      split at drawnMember
      · simp only [Draw.distribution, PMF.mem_support_pure_iff] at drawnMember
        rw [drawnMember]
      · obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp drawnMember
        exact lookup_cons_ne _ asked input value different

/-- **A hash program changes the hash table only at its input**, and nothing else. -/
theorem program_lookup_frame (asked : BaseField) (value : Block × Block) (oracle updated : LState)
    (success : LazyOracle.program (.hash asked) value oracle = some updated) :
    updated.fixed = oracle.fixed ∧ updated.enc = oracle.enc ∧
      ∀ input, input ≠ asked → updated.hash.lookup input = oracle.hash.lookup input := by
  rw [program_hash_eq] at success
  split_ifs at success
  cases success
  refine ⟨rfl, rfl, fun input different => ?_⟩
  show (oracle.hash.program asked _).lookup input = _
  rw [HashTable.program_lookup, Function.update_of_ne different]

/-! ### The whole run -/

/-- **The refill run leaves the lookup of every designated input as it found it**, on every
path. -/
theorem runRefill_frame (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell),
      ∀ result ∈ (runRefill bits draw computation oracle record touched).support,
        ∀ value, result = some value → ∀ input, IsDesignated bits input →
          value.2.1.hash.lookup input = oracle.hash.lookup input := by
  induction computation with
  | pure value =>
      intro oracle record touched result member final same input _
      simp only [runRefill, PMF.support_pure, Set.mem_singleton_iff] at member
      subst member
      cases same
      rfl
  | query request next ih =>
      intro oracle record touched result member final same input designated
      simp only [runRefill] at member
      split at member
      · exact ih _ _ _ _ result member final same input designated
      · rename_i notIntercepted
        -- a hash query that is not intercepted asks a non-designated input
        have away : askedInput request ≠ some input := by
          intro hit
          cases request with
          | hash asked =>
              simp only [askedInput, Option.some.injEq] at hit
              subst hit
              rw [interceptAnswer_designated bits designated] at notIntercepted
              exact Option.some_ne_none _ notIntercepted
          | fixedForward _ _ => simp [askedInput] at hit
          | fixedInverse _ _ => simp [askedInput] at hit
          | encForward _ _ => simp [askedInput] at hit
          | encInverse _ _ => simp [askedInput] at hit
        split at member
        · rename_i cell consumed
          obtain ⟨asked, rfl, _, _, _⟩ := consumeCell_spec consumed
          obtain ⟨value, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          split at member
          · simp only [PMF.support_pure, Set.mem_singleton_iff] at member
            subst member
            cases same
          · rename_i updated programmed
            rw [ih _ _ _ _ result member final same input designated]
            exact (program_lookup_frame asked _ oracle updated programmed).2.2 input
              fun equal => away (by rw [equal]; rfl)
        · obtain ⟨answer, answerMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          rw [ih _ _ _ _ result member final same input designated]
          exact query_lookup_frame request oracle answer answerMember input away

end

end Kriterion.ArgoMAC.Phase3.Lazy
