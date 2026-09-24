/-
**Phase 3, P1c — step 1, generic core: resampling a uniform oracle off an adaptive transcript.**

`resample_joint`: for every query computation `P` and lazy state `s`, drawing an oracle from the
completions of `s`, then a second one from the completions of `s` with `P`'s transcript planted, has
the joint law (transcript, second oracle) of (transcript, first oracle):

```
(compl s).bind (O ↦ (compl (plantAll (T_P O) s)).map (T_P O, ·)) = (compl s).map (O ↦ (T_P O, O)).
```

This is the uniform-tape half of `SwapInvariant` (with `s = empty`, `compl empty` is the uniform
oracle, `public_initial`). It is proved by induction on `P`: `public_step` splits the first query off
the completion, and a lazy answer's state is the planted state up to lookups (`query_semEq_plant`);
completions depend on lookups only (`publicCompletion_congr`).
-/

import Proof.Privacy.Phase3.Hidden.Guess
import Proof.Privacy.Phase3.Glue.OracleLaw
import Construction.QueryMonad

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open Kriterion.Cryptography
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion blockCompletion pairHashCompletion
  indexedKernel finiteKernel_congr public_step)
open scoped ENNReal

noncomputable section

/-! ### Lookup-equal states -/

section Sparse

variable {n : ℕ}

theorem completion_pred_iff (s : SparsePermutation n) (π : Equiv.Perm (Fin n)) :
    (∀ x : {x : Fin n // s.knownInput x}, π x = s.assignment x) ↔
      ∀ x y, look s x = some y → π x = y := by
  constructor
  · intro compatible x y found
    obtain ⟨known, same⟩ := look_eq_some.mp found
    rw [← same]
    exact compatible ⟨x, known⟩
  · intro compatible x
    exact compatible x.1 _ (look_eq_some.mpr ⟨x.2, rfl⟩)

theorem blockCompletion_congr {s s' : SparsePermutation (2 ^ 128)} (same : ∀ x, look s x = look s' x) :
    blockCompletion s = blockCompletion s' := by
  classical
  let equiv : s.Completion ≃ s'.Completion := Equiv.subtypeEquivRight fun π => by
    rw [completion_pred_iff, completion_pred_iff]
    simp only [same]
  unfold blockCompletion
  rw [← Kriterion.ArgoMAC.Phase3.Glue.uniform_equiv equiv, PMF.map_comp]
  congr 1

end Sparse

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **Two states with the same lookups.** -/
structure SemEq (s s' : LState FixedIndex EncIndex) : Prop where
  fixed : ∀ i x, look (s.fixed i) x = look (s'.fixed i) x
  enc : ∀ i x, look (s.enc i) x = look (s'.enc i) x
  hash : ∀ key, s.hash.lookup key = s'.hash.lookup key

theorem SemEq.symm {s s' : LState FixedIndex EncIndex} (same : SemEq s s') : SemEq s' s :=
  ⟨fun i x => (same.fixed i x).symm, fun i x => (same.enc i x).symm, fun key => (same.hash key).symm⟩

theorem bind_support_congr {α β : Type} (p : PMF α) (f g : α → PMF β)
    (same : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases zero : p a = 0
  · simp [zero]
  · rw [same a ((PMF.mem_support_iff _ _).mpr zero)]

theorem SemEq.refl (s : LState FixedIndex EncIndex) : SemEq s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem publicCompletion_congr [Fintype FixedIndex] [Fintype EncIndex]
    {s s' : LState FixedIndex EncIndex} (same : SemEq s s') :
    publicCompletion s = publicCompletion s' := by
  classical
  have fixedEq : indexedKernel blockCompletion s.fixed = indexedKernel blockCompletion s'.fixed := by
    unfold indexedKernel
    rw [finiteKernel_congr blockCompletion blockCompletion _ _
      (fun index => blockCompletion_congr (same.fixed _))]
  have encEq : indexedKernel blockCompletion s.enc = indexedKernel blockCompletion s'.enc := by
    unfold indexedKernel
    rw [finiteKernel_congr blockCompletion blockCompletion _ _
      (fun index => blockCompletion_congr (same.enc _))]
  have hashEq : pairHashCompletion s.hash = pairHashCompletion s'.hash := by
    let equiv : HashTable.Completion s.hash ≃ HashTable.Completion s'.hash :=
      Equiv.subtypeEquivRight fun f => by simp only [same.hash]
    unfold pairHashCompletion
    rw [← Kriterion.ArgoMAC.Phase3.Glue.uniform_equiv equiv, PMF.map_comp]
    congr 1
  unfold publicCompletion
  rw [fixedEq, encEq, hashEq]

/-! ### Planting respects lookups -/

theorem sparse_congr_plant {n : ℕ} {t t' : SparsePermutation n} (same : ∀ z, look t z = look t' z)
    (x y z : Fin n) :
    look (if fresh : ¬ t.knownInput x ∧ ¬ t.knownOutput y then
        extendPair t (room_of_fresh fresh.1) x y else t) z =
      look (if fresh : ¬ t'.knownInput x ∧ ¬ t'.knownOutput y then
        extendPair t' (room_of_fresh fresh.1) x y else t') z := by
  have knownIff : ∀ w, t.knownInput w ↔ t'.knownInput w := fun w => by
    rw [knownInput_iff, knownInput_iff, same]
  have outIff : ∀ w, t.knownOutput w ↔ t'.knownOutput w := fun w => by
    rw [knownOutput_iff, knownOutput_iff]
    simp only [same]
  by_cases fresh : ¬ t.knownInput x ∧ ¬ t.knownOutput y
  · have fresh' : ¬ t'.knownInput x ∧ ¬ t'.knownOutput y :=
      ⟨fun h => fresh.1 ((knownIff x).mpr h), fun h => fresh.2 ((outIff y).mpr h)⟩
    rw [dif_pos fresh, dif_pos fresh', look_extend t _ fresh.1 fresh.2,
      look_extend t' _ fresh'.1 fresh'.2, same]
  · have fresh' : ¬ (¬ t'.knownInput x ∧ ¬ t'.knownOutput y) := fun h =>
      fresh ⟨fun k => h.1 ((knownIff x).mp k), fun k => h.2 ((outIff y).mp k)⟩
    rw [dif_neg fresh, dif_neg fresh', same]

theorem SemEq.plant {s s' : LState FixedIndex EncIndex} (same : SemEq s s')
    (entry : Asked FixedIndex EncIndex) : SemEq (plant s entry) (plant s' entry) := by
  classical
  rcases entry_kinds entry with ⟨i, x, y, pair⟩ | ⟨i, x, y, pair⟩ | ⟨key, value, pair⟩
  · have noEnc : ∀ j a b, encPair entry ≠ some (j, a, b) := by
      obtain ⟨request, answer⟩ := entry
      cases request <;> simp_all [fixedPair, encPair]
    have noHash : hashPair entry = none := by
      obtain ⟨request, answer⟩ := entry
      cases request <;> simp_all [fixedPair, hashPair]
    refine ⟨fun j z => ?_, fun j z => ?_, fun key => ?_⟩
    · by_cases sameIndex : j = i
      · subst sameIndex
        rw [plant_fixed_same s entry pair, plant_fixed_same s' entry pair]
        exact sparse_congr_plant (same.fixed j) x y z
      · have other : ∀ a b, fixedPair entry ≠ some (j, a, b) := fun a b hb => sameIndex (by
          rw [pair] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          exact hb.1.symm)
        rw [plant_fixed_other s entry j other, plant_fixed_other s' entry j other]
        exact same.fixed j z
    · rw [plant_enc_other s entry j (noEnc j), plant_enc_other s' entry j (noEnc j)]
      exact same.enc j z
    · rw [plant_hash_other s entry noHash, plant_hash_other s' entry noHash]
      exact same.hash key
  · have noFixed : ∀ j a b, fixedPair entry ≠ some (j, a, b) := by
      obtain ⟨request, answer⟩ := entry
      cases request <;> simp_all [fixedPair, encPair]
    have noHash : hashPair entry = none := by
      obtain ⟨request, answer⟩ := entry
      cases request <;> simp_all [encPair, hashPair]
    refine ⟨fun j z => ?_, fun j z => ?_, fun key => ?_⟩
    · rw [plant_fixed_other s entry j (noFixed j), plant_fixed_other s' entry j (noFixed j)]
      exact same.fixed j z
    · by_cases sameIndex : j = i
      · subst sameIndex
        rw [plant_enc_same s entry pair, plant_enc_same s' entry pair]
        exact sparse_congr_plant (same.enc j) x y z
      · have other : ∀ a b, encPair entry ≠ some (j, a, b) := fun a b hb => sameIndex (by
          rw [pair] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          exact hb.1.symm)
        rw [plant_enc_other s entry j other, plant_enc_other s' entry j other]
        exact same.enc j z
    · rw [plant_hash_other s entry noHash, plant_hash_other s' entry noHash]
      exact same.hash key
  · have noFixed : ∀ j a b, fixedPair entry ≠ some (j, a, b) := by
      obtain ⟨request, answer⟩ := entry
      cases request <;> simp_all [fixedPair, hashPair]
    have noEnc : ∀ j a b, encPair entry ≠ some (j, a, b) := by
      obtain ⟨request, answer⟩ := entry
      cases request <;> simp_all [encPair, hashPair]
    refine ⟨fun j z => ?_, fun j z => ?_, fun k => ?_⟩
    · rw [plant_fixed_other s entry j (noFixed j), plant_fixed_other s' entry j (noFixed j)]
      exact same.fixed j z
    · rw [plant_enc_other s entry j (noEnc j), plant_enc_other s' entry j (noEnc j)]
      exact same.enc j z
    · rw [plant_hash_lookup s entry pair k, plant_hash_lookup s' entry pair k, same.hash, same.hash]

theorem SemEq.plantAll (entries : List (Asked FixedIndex EncIndex)) :
    ∀ {s s' : LState FixedIndex EncIndex}, SemEq s s' → SemEq (plantAll entries s) (plantAll entries s') := by
  induction entries with
  | nil => exact fun same => same
  | cons entry entries ih =>
      intro s s' same
      rw [plantAll_cons, plantAll_cons]
      exact ih (same.plant entry)

/-! ### A lazy answer's state is the planted state -/

/-- The inverse fresh extension, read forward. -/
theorem look_extend_reverse {n : ℕ} (t : SparsePermutation n) {x y : Fin n}
    (freshX : ¬ t.knownInput x) (freshY : ¬ t.knownOutput y) (z : Fin n) :
    look (extendPair t.reverse (room_of_fresh (s := t.reverse) (x := y) freshY) y x).reverse z =
      look (extendPair t (room_of_fresh freshX) x y) z := by
  rw [look_extend t _ freshX freshY z]
  apply Option.ext
  intro w
  rw [look_reverse, look_extend t.reverse _ freshY freshX w]
  by_cases same : z = x
  · subst same
    rw [if_pos rfl]
    constructor
    · intro found
      split at found
      · rename_i equal
        rw [equal]
      · exact (freshX (knownInput_iff.mpr ⟨w, look_reverse.mp found⟩)).elim
    · intro found
      cases found
      rw [if_pos rfl]
  · rw [if_neg same]
    constructor
    · intro found
      split at found
      · cases found
        exact (same rfl).elim
      · exact look_reverse.mp found
    · intro found
      have ne : w ≠ y := by
        intro equal
        subst equal
        exact freshY (knownOutput_iff.mpr ⟨z, found⟩)
      rw [if_neg ne]
      exact look_reverse.mpr found

theorem codeOf_spec' (key : BN254.BaseField)
    (value : (PublicQuery.hash (FixedIndex := FixedIndex) (EncIndex := EncIndex) key).Answer)
    (s : LState FixedIndex EncIndex) :
    LazyOracle.program (.hash key) value s =
      if s.hash.lookup key = none then some { s with hash := s.hash.program key (codeOf value) }
      else none :=
  codeOf_spec value s key

theorem plant_hash_lookup'' (s : LState FixedIndex EncIndex) (key : BN254.BaseField)
    (value : (PublicQuery.hash (FixedIndex := FixedIndex) (EncIndex := EncIndex) key).Answer)
    (other : BN254.BaseField) :
    (plant s ⟨.hash key, value⟩).hash.lookup other =
      if s.hash.lookup key = none ∧ other = key then some (codeOf value) else s.hash.lookup other :=
  plant_hash_lookup' s key value other

/-- **The state a lazy query leaves is, up to lookups, its answer planted.** -/
theorem query_semEq_plant (request : PublicQuery FixedIndex EncIndex) (s : LState FixedIndex EncIndex)
    (answer : request.Answer × LState FixedIndex EncIndex)
    (member : answer ∈ (LazyOracle.query request s).support) :
    SemEq answer.2 (plant s ⟨request, answer.1⟩) := by
  classical
  cases request with
  | fixedForward index input =>
      rw [query_fixedForward, PMF.support_map] at member
      obtain ⟨⟨y, t⟩, member', rfl⟩ := member
      have pair : fixedPair (⟨.fixedForward index input, BitVec.ofFin y⟩ :
          Asked FixedIndex EncIndex) = some (index, input.toFin, y) := rfl
      refine ⟨fun j z => ?_, fun j z => ?_, fun key => ?_⟩
      · by_cases same : j = index
        · subst same
          rw [plant_fixed_same s _ pair]
          simp only [Function.update_self]
          rcases forward_support (s.fixed j) input.toFin member' with ⟨found, rfl⟩ | ⟨fresh, unused, rfl⟩
          · rw [dif_neg (fun both => both.1 (knownInput_iff.mpr ⟨y, found⟩))]
          · rw [dif_pos ⟨fresh, unused⟩]
        · have other : ∀ a b, fixedPair (⟨.fixedForward index input, BitVec.ofFin y⟩ :
              Asked FixedIndex EncIndex) ≠ some (j, a, b) := fun a b hb => same (by
            rw [pair] at hb
            simp only [Option.some.injEq, Prod.mk.injEq] at hb
            exact hb.1.symm)
          rw [plant_fixed_other s _ j other]
          simp only [Function.update_of_ne same]
      · rw [plant_enc_other s _ j (fun a b hb => by cases hb)]
      · rw [plant_hash_other s _ rfl]
  | fixedInverse index output =>
      rw [query_fixedInverse, PMF.support_map] at member
      obtain ⟨⟨x, t⟩, member', rfl⟩ := member
      rw [inverse_distribution, PMF.support_map] at member'
      obtain ⟨⟨x', t'⟩, member'', same'⟩ := member'
      simp only [Prod.mk.injEq] at same'
      obtain ⟨rfl, rfl⟩ := same'
      have pair : fixedPair (⟨.fixedInverse index output, BitVec.ofFin x'⟩ :
          Asked FixedIndex EncIndex) = some (index, x', output.toFin) := rfl
      refine ⟨fun j z => ?_, fun j z => ?_, fun key => ?_⟩
      · by_cases same : j = index
        · subst same
          rw [plant_fixed_same s _ pair]
          simp only [Function.update_self]
          rcases forward_support (s.fixed j).reverse output.toFin member'' with
            ⟨found, rfl⟩ | ⟨fresh, unused, rfl⟩
          · rw [SparsePermutation.reverse_reverse,
              dif_neg (fun both => both.1 (knownInput_iff.mpr ⟨_, look_reverse.mp found⟩))]
          · rw [dif_pos ⟨unused, fresh⟩]
            exact look_extend_reverse (s.fixed j) unused fresh z
        · have other : ∀ a b, fixedPair (⟨.fixedInverse index output, BitVec.ofFin x'⟩ :
              Asked FixedIndex EncIndex) ≠ some (j, a, b) := fun a b hb => same (by
            rw [pair] at hb
            simp only [Option.some.injEq, Prod.mk.injEq] at hb
            exact hb.1.symm)
          rw [plant_fixed_other s _ j other]
          simp only [Function.update_of_ne same]
      · rw [plant_enc_other s _ j (fun a b hb => by cases hb)]
      · rw [plant_hash_other s _ rfl]
  | encForward index input =>
      rw [query_encForward, PMF.support_map] at member
      obtain ⟨⟨y, t⟩, member', rfl⟩ := member
      have pair : encPair (⟨.encForward index input, BitVec.ofFin y⟩ :
          Asked FixedIndex EncIndex) = some (index, input.toFin, y) := rfl
      refine ⟨fun j z => ?_, fun j z => ?_, fun key => ?_⟩
      · rw [plant_fixed_other s _ j (fun a b hb => by cases hb)]
      · by_cases same : j = index
        · subst same
          rw [plant_enc_same s _ pair]
          simp only [Function.update_self]
          rcases forward_support (s.enc j) input.toFin member' with ⟨found, rfl⟩ | ⟨fresh, unused, rfl⟩
          · rw [dif_neg (fun both => both.1 (knownInput_iff.mpr ⟨y, found⟩))]
          · rw [dif_pos ⟨fresh, unused⟩]
        · have other : ∀ a b, encPair (⟨.encForward index input, BitVec.ofFin y⟩ :
              Asked FixedIndex EncIndex) ≠ some (j, a, b) := fun a b hb => same (by
            rw [pair] at hb
            simp only [Option.some.injEq, Prod.mk.injEq] at hb
            exact hb.1.symm)
          rw [plant_enc_other s _ j other]
          simp only [Function.update_of_ne same]
      · rw [plant_hash_other s _ rfl]
  | encInverse index output =>
      rw [query_encInverse, PMF.support_map] at member
      obtain ⟨⟨x, t⟩, member', rfl⟩ := member
      rw [inverse_distribution, PMF.support_map] at member'
      obtain ⟨⟨x', t'⟩, member'', same'⟩ := member'
      simp only [Prod.mk.injEq] at same'
      obtain ⟨rfl, rfl⟩ := same'
      have pair : encPair (⟨.encInverse index output, BitVec.ofFin x'⟩ :
          Asked FixedIndex EncIndex) = some (index, x', output.toFin) := rfl
      refine ⟨fun j z => ?_, fun j z => ?_, fun key => ?_⟩
      · rw [plant_fixed_other s _ j (fun a b hb => by cases hb)]
      · by_cases same : j = index
        · subst same
          rw [plant_enc_same s _ pair]
          simp only [Function.update_self]
          rcases forward_support (s.enc j).reverse output.toFin member'' with
            ⟨found, rfl⟩ | ⟨fresh, unused, rfl⟩
          · rw [SparsePermutation.reverse_reverse,
              dif_neg (fun both => both.1 (knownInput_iff.mpr ⟨_, look_reverse.mp found⟩))]
          · rw [dif_pos ⟨unused, fresh⟩]
            exact look_extend_reverse (s.enc j) unused fresh z
        · have other : ∀ a b, encPair (⟨.encInverse index output, BitVec.ofFin x'⟩ :
              Asked FixedIndex EncIndex) ≠ some (j, a, b) := fun a b hb => same (by
            rw [pair] at hb
            simp only [Option.some.injEq, Prod.mk.injEq] at hb
            exact hb.1.symm)
          rw [plant_enc_other s _ j other]
          simp only [Function.update_of_ne same]
      · rw [plant_hash_other s _ rfl]
  | hash key =>
      obtain ⟨a, t⟩ := answer
      change (a, t) ∈ ((s.hash.query Fintype.card_pos key).distribution.map _).support at member
      rw [PMF.support_map] at member
      obtain ⟨⟨code, table⟩, member', same⟩ := member
      obtain ⟨answerEq, stateEq⟩ := Prod.ext_iff.mp same
      simp only at answerEq stateEq
      subst stateEq
      unfold HashTable.query at member'
      split at member'
      · rename_i stored found
        simp only [Draw.distribution, PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
          at member'
        obtain ⟨rfl, rfl⟩ := member'
        have failed : plant s ⟨.hash key, a⟩ = s := by
          show (LazyOracle.program (.hash key) a s).getD s = s
          rw [codeOf_spec', if_neg (by rw [found]; exact Option.some_ne_none _)]
          rfl
        show SemEq s (plant s ⟨.hash key, a⟩)
        rw [failed]
        exact SemEq.refl _
      · rename_i absent
        simp only [Draw.distribution, PMF.support_map, Set.mem_image] at member'
        obtain ⟨v, -, same⟩ := member'
        obtain ⟨codeEq, tableEq⟩ := Prod.ext_iff.mp same
        simp only at codeEq tableEq
        subst codeEq
        subst tableEq
        have direct : LazyOracle.program (.hash key) a s =
            some { s with hash := s.hash.program key v } := by
          rw [← answerEq]
          simp only [LazyOracle.program, if_pos absent, Equiv.apply_symm_apply]
        have viaCode := codeOf_spec' key a s
        rw [if_pos absent, direct] at viaCode
        have codeSame : codeOf a = v := by
          have hashes := congrArg (fun st : LState FixedIndex EncIndex => st.hash)
            (Option.some.inj viaCode)
          simp only [HashTable.program, List.cons.injEq, Prod.mk.injEq] at hashes
          exact hashes.1.2.symm
        refine ⟨fun j z => ?_, fun j z => ?_, fun k => ?_⟩
        · show look (s.fixed j) z = look ((plant s ⟨.hash key, a⟩).fixed j) z
          rw [plant_fixed_other s _ j (fun a b hb => by cases hb)]
        · show look (s.enc j) z = look ((plant s ⟨.hash key, a⟩).enc j) z
          rw [plant_enc_other s _ j (fun a b hb => by cases hb)]
        · show ((key, v) :: s.hash).lookup k = (plant s ⟨.hash key, a⟩).hash.lookup k
          rw [plant_hash_lookup'' s key a k, codeSame,
            show ((key, v) :: s.hash) = s.hash.program key v from rfl, HashTable.program_lookup]
          by_cases same : k = key
          · subst same
            simp [absent]
          · simp [same]

/-! ### The resampling law -/

/-- The transcript of a query computation on a complete oracle (`Hybrids.transcript`). -/
def transcriptOf {α : Type} (answer : ∀ query : PublicQuery FixedIndex EncIndex, query.Answer) :
    FreeQuery (publicOracleSpec FixedIndex EncIndex) α → List (Asked FixedIndex EncIndex)
  | .pure _ => []
  | .query request next => ⟨request, answer request⟩ :: transcriptOf answer (next (answer request))

/-- **Resampling a completion off an adaptive transcript preserves it, jointly with the
transcript.** -/
theorem resample_joint [Fintype FixedIndex] [Fintype EncIndex] {α : Type}
    (computation : FreeQuery (publicOracleSpec FixedIndex EncIndex) α) :
    ∀ s : LState FixedIndex EncIndex,
      (publicCompletion s).bind (fun oracle =>
          (publicCompletion (plantAll (transcriptOf (publicAnswer oracle) computation) s)).map
            fun resampled => (transcriptOf (publicAnswer oracle) computation, resampled)) =
        (publicCompletion s).map fun oracle => (transcriptOf (publicAnswer oracle) computation, oracle) := by
  induction computation with
  | pure value =>
      intro s
      simp only [transcriptOf, plantAll_nil]
      exact PMF.bind_const _ _
  | query request next ih =>
      intro s
      simp only [transcriptOf, plantAll_cons]
      have split : ∀ {β : Type} (g : request.Answer → PublicOracle FixedIndex EncIndex → PMF β),
          (publicCompletion s).bind (fun oracle => g (publicAnswer oracle request) oracle) =
            (LazyOracle.query request s).bind fun answer =>
              (publicCompletion answer.2).bind fun oracle => g answer.1 oracle := by
        intro β g
        have step := public_step request s
        have mapped := congrArg (fun law => law.bind fun pair => g pair.1 pair.2) step
        simp only [PMF.bind_map, PMF.bind_bind, Function.comp_def] at mapped
        exact mapped
      rw [split (fun a oracle =>
          (publicCompletion (plantAll (transcriptOf (publicAnswer oracle) (next a))
            (plant s ⟨request, a⟩))).map fun resampled =>
              ((⟨request, a⟩ :: transcriptOf (publicAnswer oracle) (next a) :
                List (Asked FixedIndex EncIndex)), resampled))]
      rw [← PMF.bind_pure_comp]
      simp only [Function.comp_def]
      rw [split (fun a oracle =>
          PMF.pure ((⟨request, a⟩ :: transcriptOf (publicAnswer oracle) (next a) :
            List (Asked FixedIndex EncIndex)), oracle))]
      refine bind_support_congr _ _ _ fun answer member => ?_
      have same := query_semEq_plant request s answer member
      have planted : ∀ oracle : PublicOracle FixedIndex EncIndex,
          publicCompletion (plantAll (transcriptOf (publicAnswer oracle) (next answer.1))
            (plant s ⟨request, answer.1⟩)) =
          publicCompletion (plantAll (transcriptOf (publicAnswer oracle) (next answer.1)) answer.2) :=
        fun oracle => publicCompletion_congr (SemEq.plantAll _ same).symm
      simp_rw [planted]
      have inner := congrArg (PMF.map fun pair : List (Asked FixedIndex EncIndex) ×
          PublicOracle FixedIndex EncIndex =>
        ((⟨request, answer.1⟩ :: pair.1 : List (Asked FixedIndex EncIndex)), pair.2))
        (ih answer.1 answer.2)
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at inner
      rw [inner]
      rfl

/-! ### Completions agree with the planted transcript -/

/-- The oracle agrees with every entry of a list. -/
def AgreesWith (oracle : PublicOracle FixedIndex EncIndex) (entries : List (Asked FixedIndex EncIndex)) :
    Prop :=
  ∀ entry ∈ entries, publicAnswer oracle entry.1 = entry.2

theorem transcriptOf_agrees {α : Type} (oracle : PublicOracle FixedIndex EncIndex)
    (computation : FreeQuery (publicOracleSpec FixedIndex EncIndex) α) :
    AgreesWith oracle (transcriptOf (publicAnswer oracle) computation) := by
  induction computation with
  | pure value => intro entry member; cases member
  | query request next ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · rfl
      · exact ih _ entry member

/-- **An oracle agreeing with a run's transcript runs the same way.** -/
theorem transcriptOf_of_agrees {α : Type} (computation : FreeQuery (publicOracleSpec FixedIndex EncIndex) α)
    (first second : PublicOracle FixedIndex EncIndex)
    (agrees : AgreesWith second (transcriptOf (publicAnswer first) computation)) :
    transcriptOf (publicAnswer second) computation = transcriptOf (publicAnswer first) computation ∧
      computation.eval (publicAnswer second) = computation.eval (publicAnswer first) := by
  induction computation with
  | pure value => exact ⟨rfl, rfl⟩
  | query request next ih =>
      have head : publicAnswer second request = publicAnswer first request :=
        agrees ⟨request, publicAnswer first request⟩ List.mem_cons_self
      have rest := ih (publicAnswer first request)
        (fun entry member => agrees entry (List.mem_cons_of_mem _ member))
      refine ⟨?_, ?_⟩
      · show ⟨request, publicAnswer second request⟩ ::
            transcriptOf (publicAnswer second) (next (publicAnswer second request)) = _
        rw [head, rest.1]
        rfl
      · show (next (publicAnswer second request)).eval (publicAnswer second) =
          (next (publicAnswer first request)).eval (publicAnswer first)
        rw [head]
        exact rest.2

/-- **Every completion of the planted transcript agrees with it** (from `resample_joint`: the
disagreement event has the same mass as for the first oracle, which always agrees). -/
theorem completion_agrees [Fintype FixedIndex] [Fintype EncIndex] {α : Type}
    (computation : FreeQuery (publicOracleSpec FixedIndex EncIndex) α)
    (oracle resampled : PublicOracle FixedIndex EncIndex)
    (member : resampled ∈ (publicCompletion (plantAll (transcriptOf (publicAnswer oracle) computation)
      (LazyOracle.empty : LState FixedIndex EncIndex))).support) :
    AgreesWith resampled (transcriptOf (publicAnswer oracle) computation) := by
  classical
  by_contra disagree
  have law := resample_joint computation (LazyOracle.empty : LState FixedIndex EncIndex)
  let bad : Set (List (Asked FixedIndex EncIndex) × PublicOracle FixedIndex EncIndex) :=
    {pair | ¬ AgreesWith pair.2 pair.1}
  have right : ((publicCompletion (LazyOracle.empty : LState FixedIndex EncIndex)).map
      fun first => (transcriptOf (publicAnswer first) computation, first)).toOuterMeasure bad = 0 := by
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_eq_zero_iff]
    rw [Set.disjoint_left]
    intro first _ inBad
    exact inBad (transcriptOf_agrees first computation)
  have left : ((publicCompletion (LazyOracle.empty : LState FixedIndex EncIndex)).bind fun first =>
      (publicCompletion (plantAll (transcriptOf (publicAnswer first) computation) LazyOracle.empty)).map
        fun second => (transcriptOf (publicAnswer first) computation, second)).toOuterMeasure bad ≠ 0 := by
    rw [PMF.toOuterMeasure_bind_apply]
    intro zero
    have term := ENNReal.tsum_eq_zero.mp zero oracle
    rcases mul_eq_zero.mp term with mass | inner
    · rw [Kriterion.ArgoMAC.Phase3.Glue.public_initial, PMF.uniformOfFintype_apply] at mass
      exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _) mass
    · rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_eq_zero_iff,
        Set.disjoint_left] at inner
      exact inner member disagree
  rw [law] at left
  exact left right


end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
