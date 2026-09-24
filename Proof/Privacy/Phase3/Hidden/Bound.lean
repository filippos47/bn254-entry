/-
**Phase 3, P1c — step 3, generic: avoidance along a clean run, and the per-query union bound.**

* `avoid_runLog`: a run whose log touches no entry of `K` keeps the state avoiding `K`;
* `rel_plantAll_of_avoid`: planting a consistent list into a state that avoids it is that state
  with the list as extra entries;
* `touch_mass_le`: **the union bound.** If, for every view value `v` and every answered query `e`,
  the extra set touched by `e` has conditional mass at most `ε` given `view = v`
  (`μ{view = v ∧ e touches} ≤ ε · μ{view = v}`), then a run that depends on the view only and makes
  at most `n` queries touches the extra set with mass at most `n · ε`.
-/

import Proof.Privacy.Phase3.Hidden.Transfer

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open Kriterion.Cryptography
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### Avoidance on one sparse permutation -/

section Sparse

variable {n : ℕ}

/-- `t` stores none of the pairs of `E`, in either coordinate. -/
def SparseAvoid (t : SparsePermutation n) (E : Fin n → Fin n → Prop) : Prop :=
  ∀ x y, E x y → look t x = none ∧ ∀ x', look t x' ≠ some y

theorem SparseAvoid.reverse {t : SparsePermutation n} {E : Fin n → Fin n → Prop}
    (avoid : SparseAvoid t E) : SparseAvoid t.reverse (fun y x => E x y) := by
  intro y x extra
  refine ⟨?_, fun y' found => ?_⟩
  · rcases h : look t.reverse y with _ | x'
    · rfl
    · exact ((avoid x y extra).2 x' (look_reverse.mp h)).elim
  · have := (avoid x y extra).1
    rw [look_reverse.mp found] at this
    cases this

theorem SparseAvoid.forward {s t : SparsePermutation n} {E : Fin n → Fin n → Prop}
    (avoid : SparseAvoid s E) {x y : Fin n} (member : (y, t) ∈ (s.forward x).distribution.support)
    (untouched : ¬ ForwardTouch E x y) : SparseAvoid t E := by
  rcases forward_support s x member with ⟨_, rfl⟩ | ⟨fresh, unused, rfl⟩
  · exact avoid
  · intro a b extra
    have aNe : a ≠ x := fun same => untouched (Or.inl ⟨b, same ▸ extra⟩)
    refine ⟨?_, fun x' found => ?_⟩
    · rw [look_extend s _ fresh unused, if_neg aNe]
      exact (avoid a b extra).1
    · rw [look_extend s _ fresh unused] at found
      split at found
      · cases found
        exact untouched (Or.inr ⟨a, extra⟩)
      · exact (avoid a b extra).2 x' found

theorem SparseAvoid.inverse {s t : SparsePermutation n} {E : Fin n → Fin n → Prop}
    (avoid : SparseAvoid s E) {x y : Fin n} (member : (x, t) ∈ (s.inverse y).distribution.support)
    (untouched : ¬ ForwardTouch (fun y x => E x y) y x) : SparseAvoid t E := by
  rw [inverse_distribution, PMF.support_map] at member
  obtain ⟨⟨x', t'⟩, member', same⟩ := member
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  exact (avoid.reverse.forward member' untouched).reverse

end Sparse

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

theorem Avoid.sparse_fixed {s : LState FixedIndex EncIndex} {K : Extra FixedIndex EncIndex}
    (avoid : Avoid s K) (i : FixedIndex) : SparseAvoid (s.fixed i) (K.fixed i) :=
  fun x y extra => avoid.fixed i x y extra

theorem Avoid.sparse_enc {s : LState FixedIndex EncIndex} {K : Extra FixedIndex EncIndex}
    (avoid : Avoid s K) (i : EncIndex) : SparseAvoid (s.enc i) (K.enc i) :=
  fun x y extra => avoid.enc i x y extra

/-- **One untouching query keeps the avoidance.** -/
theorem avoid_query {s : LState FixedIndex EncIndex} {K : Extra FixedIndex EncIndex}
    (avoid : Avoid s K) (request : PublicQuery FixedIndex EncIndex)
    {answer : request.Answer × LState FixedIndex EncIndex}
    (member : answer ∈ (LazyOracle.query request s).support)
    (untouched : ¬ Touches K ⟨request, answer.1⟩) : Avoid answer.2 K := by
  cases request with
  | fixedForward index input =>
      rw [query_fixedForward, PMF.support_map] at member
      obtain ⟨⟨y, t⟩, member', rfl⟩ := member
      have step := (avoid.sparse_fixed index).forward member' untouched
      refine ⟨fun i x y' extra => ?_, avoid.enc, avoid.hash⟩
      by_cases same : i = index
      · subst same
        simp only [Function.update_self]
        exact step x y' extra
      · simp only [Function.update_of_ne same]
        exact avoid.fixed i x y' extra
  | fixedInverse index output =>
      rw [query_fixedInverse, PMF.support_map] at member
      obtain ⟨⟨x, t⟩, member', rfl⟩ := member
      have step := (avoid.sparse_fixed index).inverse member' untouched
      refine ⟨fun i x' y' extra => ?_, avoid.enc, avoid.hash⟩
      by_cases same : i = index
      · subst same
        simp only [Function.update_self]
        exact step x' y' extra
      · simp only [Function.update_of_ne same]
        exact avoid.fixed i x' y' extra
  | encForward index input =>
      rw [query_encForward, PMF.support_map] at member
      obtain ⟨⟨y, t⟩, member', rfl⟩ := member
      have step := (avoid.sparse_enc index).forward member' untouched
      refine ⟨avoid.fixed, fun i x y' extra => ?_, avoid.hash⟩
      by_cases same : i = index
      · subst same
        simp only [Function.update_self]
        exact step x y' extra
      · simp only [Function.update_of_ne same]
        exact avoid.enc i x y' extra
  | encInverse index output =>
      rw [query_encInverse, PMF.support_map] at member
      obtain ⟨⟨x, t⟩, member', rfl⟩ := member
      have step := (avoid.sparse_enc index).inverse member' untouched
      refine ⟨avoid.fixed, fun i x' y' extra => ?_, avoid.hash⟩
      by_cases same : i = index
      · subst same
        simp only [Function.update_self]
        exact step x' y' extra
      · simp only [Function.update_of_ne same]
        exact avoid.enc i x' y' extra
  | hash key =>
      have notExtra : K.hash key = none := by
        rcases h : K.hash key with _ | c
        · rfl
        · exact (untouched (by show (K.hash key).isSome = true; rw [h]; rfl)).elim
      obtain ⟨a, t⟩ := answer
      change (a, t) ∈ ((s.hash.query Fintype.card_pos key).distribution.map _).support at member
      rw [PMF.support_map] at member
      obtain ⟨⟨code, table⟩, member', same⟩ := member
      simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      refine ⟨avoid.fixed, avoid.enc, fun k c extra => ?_⟩
      have kNe : k ≠ key := by
        intro equal
        rw [equal, notExtra] at extra
        cases extra
      unfold HashTable.query at member'
      split at member'
      · simp only [Draw.distribution, PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
          at member'
        obtain ⟨-, rfl⟩ := member'
        exact avoid.hash k c extra
      · simp only [Draw.distribution, PMF.support_map, Set.mem_image] at member'
        obtain ⟨v, -, same⟩ := member'
        simp only [Prod.mk.injEq] at same
        obtain ⟨-, rfl⟩ := same
        show (s.hash.program key v).lookup k = none
        rw [HashTable.program_lookup, Function.update_of_ne kNe]
        exact avoid.hash k c extra

/-- **A clean run keeps the avoidance.** -/
theorem avoid_runLog {K : Extra FixedIndex EncIndex} {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (s : LState FixedIndex EncIndex) (avoid : Avoid s K)
    (outcome : Result × LState FixedIndex EncIndex × List (Asked FixedIndex EncIndex))
    (member : outcome ∈ (runLog program s).support)
    (clean : ∀ entry ∈ outcome.2.2, ¬ Touches K entry) : Avoid outcome.2.1 K := by
  induction program generalizing s outcome with
  | pure distribution =>
      rw [runLog, PMF.support_map] at member
      obtain ⟨_, _, rfl⟩ := member
      exact avoid
  | query request next ih =>
      rw [runLog, PMF.mem_support_bind_iff] at member
      obtain ⟨answer, answerMember, member⟩ := member
      rw [PMF.support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      have head := clean ⟨request, answer.1⟩ List.mem_cons_self
      have stepAvoid := avoid_query avoid request answerMember head
      exact ih answer.1 answer.2 stepAvoid inner innerMember
        (fun entry member => clean entry (List.mem_cons_of_mem _ member))
  | sample distribution next ih =>
      rw [runLog, PMF.mem_support_bind_iff] at member
      obtain ⟨value, _, member⟩ := member
      exact ih value s avoid outcome member clean

/-- **Planting a consistent list into a state that avoids it.** -/
theorem rel_plantAll_of_avoid (O : PublicOracle FixedIndex EncIndex)
    (entries : List (Asked FixedIndex EncIndex)) (consistent : Consistent O entries)
    (s : LState FixedIndex EncIndex) (avoid : Avoid s (extraOf O entries)) :
    Rel (plantAll entries s) s (extraOf O entries) := by
  classical
  have compat : Compat O entries s := by
    refine ⟨consistent, fun entry member i x y pair => ?_, fun entry member i x y pair => ?_,
      fun entry member key value pair => ?_⟩
    · have avoided := avoid.fixed i x y ⟨entry, member, pair⟩
      refine Or.inr ⟨look_eq_none.mp avoided.1, fun known => ?_⟩
      obtain ⟨x', found⟩ := knownOutput_iff.mp known
      exact avoided.2 x' found
    · have avoided := avoid.enc i x y ⟨entry, member, pair⟩
      refine Or.inr ⟨look_eq_none.mp avoided.1, fun known => ?_⟩
      obtain ⟨x', found⟩ := knownOutput_iff.mp known
      exact avoided.2 x' found
    · left
      apply avoid.hash key (codeOf (O.2.2 key))
      simp only [extraOf]
      rw [if_pos ⟨entry, member, value, pair⟩]
  refine ⟨fun i => ⟨fun x y => ?_, fun x y extra => (avoid.fixed i x y extra).1,
      fun x y extra => (avoid.fixed i x y extra).2⟩,
    fun i => ⟨fun x y => ?_, fun x y extra => (avoid.enc i x y extra).1,
      fun x y extra => (avoid.enc i x y extra).2⟩,
    fun key absent => ?_, fun key value extra => ?_⟩
  · exact plantAll_look O entries s compat i x y
  · exact plantAll_encLook O entries s compat i x y
  · rw [plantAll_hashLookup O entries s compat key]
    have notListed : ¬ ∃ entry ∈ entries, ∃ value, hashPair entry = some (key, value) := by
      intro listed
      simp only [extraOf] at absent
      rw [if_pos listed] at absent
      cases absent
    rw [if_neg (fun both => notListed both.2)]
  · have listed : ∃ entry ∈ entries, ∃ value, hashPair entry = some (key, value) := by
      by_contra notListed
      simp only [extraOf] at extra
      rw [if_neg notListed] at extra
      cases extra
    have storedValue : value = codeOf (O.2.2 key) := by
      simp only [extraOf] at extra
      rw [if_pos listed] at extra
      exact (Option.some.inj extra).symm
    have fresh := avoid.hash key value extra
    refine ⟨?_, fresh⟩
    rw [plantAll_hashLookup O entries s compat key, if_pos ⟨fresh, listed⟩, storedValue]

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
