/-
**Phase 3, P1c — step 2: planting entries in the lazy oracle is identical until they are touched.**

Two lazy-oracle states are related, `Rel s₁ s₂ H`, when `s₁` stores everything `s₂` stores
together with the extra entries `H` (per permutation index a set of pairs, fresh in `s₂` in both
coordinates; for the hash a set of keys unknown to `s₂`). A query **touches** `H` when its input is
an extra input or its fresh answer is an extra output (`Touches`); the answer is part of the test,
so a touch is decided by the query and its answer alone, never by the state.

`runLog` is `LazyOracle.run` with the list of (query, answer) pairs it made (`runLog_run`,
`runLog_length`: at most `budget` of them). The theorem:

`dominate`: for every oracle program, related start states, and continuations `G ≤ F` on related
states, the run from `s₂` **killed at its first touch of `H`** is dominated by the run from `s₁`:

```
E_{runLog P s₂} [ 1{no entry of the log touches H} · G ]  ≤  E_{run P s₁} [ F ].
```

Off the touch, a query at a known input returns the same stored answer in both states; at a fresh
input `s₂` draws uniformly from its unused outputs `U₂ ⊇ U₁`, and every untouching answer lies in
`U₁`, where `s₁` draws with the larger mass `1/|U₁| ≥ 1/|U₂|`; the updated states are related
again. No independence and no probability of the touch is used here: this is the identical-until-bad
coupling of the two lazy runs, as an inequality of sub-probability laws.
-/

import Proof.Privacy.Phase3.Hidden.Sparse

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open Kriterion.Cryptography
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### Inverse queries: the reversed state -/

section Reverse

variable {n : ℕ}

theorem look_reverse {s : SparsePermutation n} {x y : Fin n} :
    look s.reverse y = some x ↔ look s x = some y := by
  constructor
  · intro found
    have := LazyOracle.lookup_inverse s.reverse y x found
    rwa [SparsePermutation.reverse_reverse] at this
  · exact LazyOracle.lookup_inverse s x y

theorem SparseExtra.reverse {s₁ s₂ : SparsePermutation n} {E : Fin n → Fin n → Prop}
    (rel : SparseExtra s₁ s₂ E) : SparseExtra s₁.reverse s₂.reverse (fun y x => E x y) := by
  refine ⟨fun y x => ?_, fun y x extra => ?_, fun y x extra y' found => ?_⟩
  · rw [look_reverse, look_reverse]
    exact rel.look_iff x y
  · rcases h : look s₂.reverse y with _ | x'
    · rfl
    · exact (rel.freshOut x y extra x' (look_reverse.mp h)).elim
  · have := rel.freshIn x y extra
    rw [look_reverse.mp found] at this
    cases this

theorem SparseExtra.of_reverse {s₁ s₂ : SparsePermutation n} {E : Fin n → Fin n → Prop}
    (rel : SparseExtra s₁ s₂ (fun y x => E x y)) : SparseExtra s₁.reverse s₂.reverse E :=
  rel.reverse

theorem inverse_distribution (s : SparsePermutation n) (y : Fin n) :
    (s.inverse y).distribution =
      (s.reverse.forward y).distribution.map (fun pair => (pair.1, pair.2.reverse)) := by
  rw [SparsePermutation.inverse_reverse_forward, Draw.map_distribution]

/-- **One inverse query, off the touch** (the forward step on the reversed states). -/
theorem SparseExtra.inverse_dominate {s₁ s₂ : SparsePermutation n} {E : Fin n → Fin n → Prop}
    (rel : SparseExtra s₁ s₂ E) (y : Fin n)
    (F G : Fin n × SparsePermutation n → ℝ≥0∞)
    (ordered : ∀ x t₁ t₂, SparseExtra t₁ t₂ E → G (x, t₂) ≤ F (x, t₁)) :
    expect (s₂.inverse y).distribution
        (fun answer => by
          classical exact if ForwardTouch (fun y x => E x y) y answer.1 then 0 else G answer) ≤
      expect (s₁.inverse y).distribution F := by
  classical
  rw [inverse_distribution, inverse_distribution, expect_map, expect_map]
  exact rel.reverse.forward_dominate y (fun pair => F (pair.1, pair.2.reverse))
    (fun pair => G (pair.1, pair.2.reverse))
    (fun x t₁ t₂ related => ordered x t₁.reverse t₂.reverse related.of_reverse)

end Reverse

/-! ### The lazy oracle state -/

section State

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- A lazy-oracle state. -/
abbrev LState (FixedIndex EncIndex : Type) := LazyOracle.State FixedIndex EncIndex

/-- A query with its answer. -/
abbrev Asked (FixedIndex EncIndex : Type) :=
  Σ query : PublicQuery FixedIndex EncIndex, query.Answer

/-- The stored form of a hash value. -/
abbrev HashCode := Fin (Fintype.card (Block × Block))

/-- **Extra entries**: pairs per permutation index, and hash keys with their stored values. -/
structure Extra (FixedIndex EncIndex : Type) where
  fixed : FixedIndex → Fin (2 ^ 128) → Fin (2 ^ 128) → Prop
  enc : EncIndex → Fin (2 ^ 128) → Fin (2 ^ 128) → Prop
  hash : BN254.BaseField → Option HashCode

/-- **`s₁` is `s₂` with the extra entries `H`.** -/
structure Rel (s₁ s₂ : LState FixedIndex EncIndex) (H : Extra FixedIndex EncIndex) : Prop where
  fixed : ∀ index, SparseExtra (s₁.fixed index) (s₂.fixed index) (H.fixed index)
  enc : ∀ index, SparseExtra (s₁.enc index) (s₂.enc index) (H.enc index)
  hashAgree : ∀ key, H.hash key = none → s₁.hash.lookup key = s₂.hash.lookup key
  hashExtra : ∀ key value, H.hash key = some value →
    s₁.hash.lookup key = some value ∧ s₂.hash.lookup key = none

/-- **The touch of the extra entries** by one answered query. -/
def Touches (H : Extra FixedIndex EncIndex) : Asked FixedIndex EncIndex → Prop
  | ⟨.fixedForward index input, answer⟩ =>
      ForwardTouch (H.fixed index) input.toFin (BitVec.toFin (w := 128) answer)
  | ⟨.fixedInverse index output, answer⟩ =>
      ForwardTouch (fun y x => H.fixed index x y) output.toFin (BitVec.toFin (w := 128) answer)
  | ⟨.encForward index input, answer⟩ =>
      ForwardTouch (H.enc index) input.toFin (BitVec.toFin (w := 128) answer)
  | ⟨.encInverse index output, answer⟩ =>
      ForwardTouch (fun y x => H.enc index x y) output.toFin (BitVec.toFin (w := 128) answer)
  | ⟨.hash key, _⟩ => (H.hash key).isSome = true

open Classical in
/-- `0` on a touch, `1` otherwise. -/
def untouched (H : Extra FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex) : ℝ≥0∞ :=
  if Touches H entry then 0 else 1

open Classical in
/-- `1` if no entry of the log touches `H`. -/
def cleanWeight (H : Extra FixedIndex EncIndex) (log : List (Asked FixedIndex EncIndex)) : ℝ≥0∞ :=
  if ∀ entry ∈ log, ¬ Touches H entry then 1 else 0

theorem cleanWeight_nil (H : Extra FixedIndex EncIndex) : cleanWeight H [] = 1 := by
  simp [cleanWeight]

theorem cleanWeight_cons (H : Extra FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex)
    (log : List (Asked FixedIndex EncIndex)) :
    cleanWeight H (entry :: log) = untouched H entry * cleanWeight H log := by
  classical
  unfold cleanWeight untouched
  by_cases touch : Touches H entry
  · simp [touch]
  · by_cases rest : ∀ e ∈ log, ¬ Touches H e
    · simp [touch, rest]
    · simp [touch, rest]

theorem untouched_le_one (H : Extra FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex) :
    untouched H entry ≤ 1 := by
  unfold untouched
  split <;> simp

/-! #### One query -/

/-- A fixed-key sparse update keeps the relation. -/
theorem Rel.updateFixed {s₁ s₂ : LState FixedIndex EncIndex} {H : Extra FixedIndex EncIndex}
    (rel : Rel s₁ s₂ H) (index : FixedIndex) {t₁ t₂ : SparsePermutation (2 ^ 128)}
    (related : SparseExtra t₁ t₂ (H.fixed index)) :
    Rel { s₁ with fixed := Function.update s₁.fixed index t₁ }
      { s₂ with fixed := Function.update s₂.fixed index t₂ } H := by
  refine ⟨fun other => ?_, rel.enc, rel.hashAgree, rel.hashExtra⟩
  by_cases same : other = index
  · subst same
    simpa only [Function.update_self] using related
  · simpa only [Function.update_of_ne same] using rel.fixed other

/-- An EncPRF sparse update keeps the relation. -/
theorem Rel.updateEnc {s₁ s₂ : LState FixedIndex EncIndex} {H : Extra FixedIndex EncIndex}
    (rel : Rel s₁ s₂ H) (index : EncIndex) {t₁ t₂ : SparsePermutation (2 ^ 128)}
    (related : SparseExtra t₁ t₂ (H.enc index)) :
    Rel { s₁ with enc := Function.update s₁.enc index t₁ }
      { s₂ with enc := Function.update s₂.enc index t₂ } H := by
  refine ⟨rel.fixed, fun other => ?_, rel.hashAgree, rel.hashExtra⟩
  by_cases same : other = index
  · subst same
    simpa only [Function.update_self] using related
  · simpa only [Function.update_of_ne same] using rel.enc other

/-- A shared hash update at a key that is not extra keeps the relation. -/
theorem Rel.updateHash {s₁ s₂ : LState FixedIndex EncIndex} {H : Extra FixedIndex EncIndex}
    (rel : Rel s₁ s₂ H) {key : BN254.BaseField} (notExtra : H.hash key = none)
    (value : HashCode) :
    Rel { s₁ with hash := (key, value) :: s₁.hash } { s₂ with hash := (key, value) :: s₂.hash } H := by
  refine ⟨rel.fixed, rel.enc, fun other otherNot => ?_, fun other stored extra => ?_⟩
  · show (s₁.hash.program key value).lookup other = (s₂.hash.program key value).lookup other
    rw [HashTable.program_lookup, HashTable.program_lookup]
    by_cases same : other = key
    · subst same
      simp only [Function.update_self]
    · simp only [Function.update_of_ne same]
      exact rel.hashAgree other otherNot
  · show (s₁.hash.program key value).lookup other = some stored ∧
      (s₂.hash.program key value).lookup other = none
    rw [HashTable.program_lookup, HashTable.program_lookup]
    have different : other ≠ key := by
      intro same
      rw [same, notExtra] at extra
      cases extra
    simp only [Function.update_of_ne different]
    exact rel.hashExtra other stored extra

/-- The fixed-key forward query of the lazy oracle, as a map of the sparse draw. -/
theorem query_fixedForward (index : FixedIndex) (input : Block) (s : LState FixedIndex EncIndex) :
    LazyOracle.query (.fixedForward index input) s =
      ((s.fixed index).forward input.toFin).distribution.map
        (β := (PublicQuery.fixedForward (FixedIndex := FixedIndex) (EncIndex := EncIndex) index input).Answer ×
          LState FixedIndex EncIndex)
        (fun answer => (BitVec.ofFin answer.1,
          { s with fixed := Function.update s.fixed index answer.2 })) := rfl

theorem query_fixedInverse (index : FixedIndex) (output : Block) (s : LState FixedIndex EncIndex) :
    LazyOracle.query (.fixedInverse index output) s =
      ((s.fixed index).inverse output.toFin).distribution.map
        (β := (PublicQuery.fixedInverse (FixedIndex := FixedIndex) (EncIndex := EncIndex) index output).Answer ×
          LState FixedIndex EncIndex)
        (fun answer => (BitVec.ofFin answer.1,
          { s with fixed := Function.update s.fixed index answer.2 })) := rfl

theorem query_encForward (index : EncIndex) (input : Block) (s : LState FixedIndex EncIndex) :
    LazyOracle.query (.encForward index input) s =
      ((s.enc index).forward input.toFin).distribution.map
        (β := (PublicQuery.encForward (FixedIndex := FixedIndex) (EncIndex := EncIndex) index input).Answer ×
          LState FixedIndex EncIndex)
        (fun answer => (BitVec.ofFin answer.1,
          { s with enc := Function.update s.enc index answer.2 })) := rfl

theorem query_encInverse (index : EncIndex) (output : Block) (s : LState FixedIndex EncIndex) :
    LazyOracle.query (.encInverse index output) s =
      ((s.enc index).inverse output.toFin).distribution.map
        (β := (PublicQuery.encInverse (FixedIndex := FixedIndex) (EncIndex := EncIndex) index output).Answer ×
          LState FixedIndex EncIndex)
        (fun answer => (BitVec.ofFin answer.1,
          { s with enc := Function.update s.enc index answer.2 })) := rfl

/-- The hash query, for any encoding `code` of the table values (the library's is private). -/
theorem hash_dominate {H : Extra FixedIndex EncIndex} {s₁ s₂ : LState FixedIndex EncIndex}
    (rel : Rel s₁ s₂ H) (key : BN254.BaseField) (notExtra : H.hash key = none) {β : Type}
    (code : Fin (Fintype.card (Block × Block)) → β)
    (F G : β × LState FixedIndex EncIndex → ℝ≥0∞)
    (ordered : ∀ a t₁ t₂, Rel t₁ t₂ H → G (a, t₂) ≤ F (a, t₁)) :
    expect ((s₂.hash.query Fintype.card_pos key).distribution.map
        (fun answer => (code answer.1, { s₂ with hash := answer.2 }))) G ≤
      expect ((s₁.hash.query Fintype.card_pos key).distribution.map
        (fun answer => (code answer.1, { s₁ with hash := answer.2 }))) F := by
  rw [expect_map, expect_map]
  have agree := rel.hashAgree key notExtra
  unfold HashTable.query
  rw [agree]
  rcases found : s₂.hash.lookup key with _ | value
  · simp only [Draw.distribution]
    rw [expect_map, expect_map]
    refine expect_mono _ fun value => ?_
    exact ordered _ _ _ (rel.updateHash notExtra value)
  · simp only [Draw.distribution, expect_pure]
    have same : ({ s₂ with hash := s₂.hash } : LState FixedIndex EncIndex) = s₂ := rfl
    have same₁ : ({ s₁ with hash := s₁.hash } : LState FixedIndex EncIndex) = s₁ := rfl
    rw [same, same₁]
    exact ordered _ _ _ rel

/-- **One query, off the touch.** -/
theorem query_dominate (H : Extra FixedIndex EncIndex) (request : PublicQuery FixedIndex EncIndex)
    {s₁ s₂ : LState FixedIndex EncIndex} (rel : Rel s₁ s₂ H)
    (F G : request.Answer × LState FixedIndex EncIndex → ℝ≥0∞)
    (ordered : ∀ a t₁ t₂, Rel t₁ t₂ H → G (a, t₂) ≤ F (a, t₁)) :
    expect (LazyOracle.query request s₂)
        (fun answer => untouched H ⟨request, answer.1⟩ * G answer) ≤
      expect (LazyOracle.query request s₁) F := by
  classical
  cases request with
  | fixedForward index input =>
      rw [query_fixedForward, query_fixedForward, expect_map, expect_map]
      refine le_trans (le_of_eq ?_) ((rel.fixed index).forward_dominate input.toFin
        (fun pair => F (BitVec.ofFin pair.1,
          { s₁ with fixed := Function.update s₁.fixed index pair.2 }))
        (fun pair => G (BitVec.ofFin pair.1,
          { s₂ with fixed := Function.update s₂.fixed index pair.2 }))
        (fun y t₁ t₂ related => ordered _ _ _ (rel.updateFixed index related)))
      congr 1
      funext pair
      simp only [untouched, Touches]
      split <;> simp_all
  | fixedInverse index output =>
      rw [query_fixedInverse, query_fixedInverse, expect_map, expect_map]
      refine le_trans (le_of_eq ?_) ((rel.fixed index).inverse_dominate output.toFin
        (fun pair => F (BitVec.ofFin pair.1,
          { s₁ with fixed := Function.update s₁.fixed index pair.2 }))
        (fun pair => G (BitVec.ofFin pair.1,
          { s₂ with fixed := Function.update s₂.fixed index pair.2 }))
        (fun y t₁ t₂ related => ordered _ _ _ (rel.updateFixed index related)))
      congr 1
      funext pair
      simp only [untouched, Touches]
      split <;> simp_all
  | encForward index input =>
      rw [query_encForward, query_encForward, expect_map, expect_map]
      refine le_trans (le_of_eq ?_) ((rel.enc index).forward_dominate input.toFin
        (fun pair => F (BitVec.ofFin pair.1,
          { s₁ with enc := Function.update s₁.enc index pair.2 }))
        (fun pair => G (BitVec.ofFin pair.1,
          { s₂ with enc := Function.update s₂.enc index pair.2 }))
        (fun y t₁ t₂ related => ordered _ _ _ (rel.updateEnc index related)))
      congr 1
      funext pair
      simp only [untouched, Touches]
      split <;> simp_all
  | encInverse index output =>
      rw [query_encInverse, query_encInverse, expect_map, expect_map]
      refine le_trans (le_of_eq ?_) ((rel.enc index).inverse_dominate output.toFin
        (fun pair => F (BitVec.ofFin pair.1,
          { s₁ with enc := Function.update s₁.enc index pair.2 }))
        (fun pair => G (BitVec.ofFin pair.1,
          { s₂ with enc := Function.update s₂.enc index pair.2 }))
        (fun y t₁ t₂ related => ordered _ _ _ (rel.updateEnc index related)))
      congr 1
      funext pair
      simp only [untouched, Touches]
      split <;> simp_all
  | hash key =>
      by_cases extra : (H.hash key).isSome = true
      · have zero : ∀ answer : (PublicQuery.hash (FixedIndex := FixedIndex)
            (EncIndex := EncIndex) key).Answer × LState FixedIndex EncIndex,
            untouched H ⟨.hash key, answer.1⟩ * G answer = 0 := by
          intro answer
          unfold untouched
          rw [if_pos (show Touches H ⟨.hash key, answer.1⟩ from extra), zero_mul]
        simp only [zero]
        rw [expect_const]
        exact zero_le
      · have one : ∀ answer : (PublicQuery.hash (FixedIndex := FixedIndex)
            (EncIndex := EncIndex) key).Answer × LState FixedIndex EncIndex,
            untouched H ⟨.hash key, answer.1⟩ * G answer = G answer := by
          intro answer
          unfold untouched
          rw [if_neg (show ¬ Touches H ⟨.hash key, answer.1⟩ from extra), one_mul]
        simp only [one]
        exact hash_dominate rel key (Option.not_isSome_iff_eq_none.mp extra) _ F G ordered

/-! #### The logged run -/

/-- **`LazyOracle.run` with its log** of (query, answer) pairs. -/
def runLog {Result : Type} :
    {budget : ℕ} → OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget →
      LState FixedIndex EncIndex →
        PMF (Result × LState FixedIndex EncIndex × List (Asked FixedIndex EncIndex))
  | _, .pure distribution, state => distribution.map fun result => (result, state, [])
  | _, .query request next, state => (LazyOracle.query request state).bind fun answer =>
      (runLog (next answer.1) answer.2).map fun outcome =>
        (outcome.1, outcome.2.1, ⟨request, answer.1⟩ :: outcome.2.2)
  | _, .sample distribution next, state => distribution.bind fun value =>
      runLog (next value) state

theorem run_pure {Result : Type} {budget : ℕ} (distribution : PMF Result)
    (state : LState FixedIndex EncIndex) :
    LazyOracle.run (.pure (budget := budget) distribution) state =
      distribution.map fun result => (result, state) := rfl

theorem run_query {Result : Type} {budget : ℕ} (request : PublicQuery FixedIndex EncIndex)
    (next : request.Answer → OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : LState FixedIndex EncIndex) :
    LazyOracle.run (.query request next) state =
      (LazyOracle.query request state).bind fun answer => LazyOracle.run (next answer.1) answer.2 :=
  rfl

theorem run_sample {Result : Type} {budget : ℕ} {Sample : Type} (distribution : PMF Sample)
    (next : Sample → OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : LState FixedIndex EncIndex) :
    LazyOracle.run (.sample distribution next) state =
      distribution.bind fun value => LazyOracle.run (next value) state := rfl

/-- Forgetting the log gives the lazy run. -/
theorem runLog_run {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : LState FixedIndex EncIndex) :
    (runLog program state).map (fun outcome => (outcome.1, outcome.2.1)) =
      LazyOracle.run program state := by
  induction program generalizing state with
  | pure distribution =>
      rw [runLog, run_pure, PMF.map_comp]
      rfl
  | query request next ih =>
      rw [runLog, run_query, PMF.map_bind]
      congr 1
      funext answer
      rw [PMF.map_comp, ← ih]
      rfl
  | sample distribution next ih =>
      rw [runLog, run_sample, PMF.map_bind]
      congr 1
      funext value
      exact ih value state

/-- The log has at most `budget` entries. -/
theorem runLog_length {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : LState FixedIndex EncIndex)
    (outcome : Result × LState FixedIndex EncIndex × List (Asked FixedIndex EncIndex))
    (member : outcome ∈ (runLog program state).support) : outcome.2.2.length ≤ budget := by
  induction program generalizing state outcome with
  | pure distribution =>
      rw [runLog, PMF.support_map] at member
      obtain ⟨_, _, rfl⟩ := member
      exact Nat.zero_le _
  | query request next ih =>
      rw [runLog, PMF.mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      rw [PMF.support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      have := ih answer.1 answer.2 inner innerMember
      simp only [List.length_cons]
      omega
  | sample distribution next ih =>
      rw [runLog, PMF.mem_support_bind_iff] at member
      obtain ⟨value, _, member⟩ := member
      exact ih value state outcome member

/-- **The identical-until-touched domination.** -/
theorem dominate (H : Extra FixedIndex EncIndex) {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    {s₁ s₂ : LState FixedIndex EncIndex} (rel : Rel s₁ s₂ H)
    (F G : Result × LState FixedIndex EncIndex → ℝ≥0∞)
    (ordered : ∀ r t₁ t₂, Rel t₁ t₂ H → G (r, t₂) ≤ F (r, t₁)) :
    expect (runLog program s₂) (fun outcome => cleanWeight H outcome.2.2 * G (outcome.1, outcome.2.1)) ≤
      expect (LazyOracle.run program s₁) F := by
  induction program generalizing s₁ s₂ with
  | pure distribution =>
      rw [runLog, run_pure, expect_map, expect_map]
      refine expect_mono _ fun result => ?_
      rw [cleanWeight_nil, one_mul]
      exact ordered result s₁ s₂ rel
  | query request next ih =>
      rw [runLog, run_query, expect_bind, expect_bind]
      refine le_trans (le_of_eq ?_) (query_dominate H request rel
        (fun answer => expect (LazyOracle.run (next answer.1) answer.2) F)
        (fun answer => expect (runLog (next answer.1) answer.2)
          (fun outcome => cleanWeight H outcome.2.2 * G (outcome.1, outcome.2.1)))
        (fun a t₁ t₂ related => ih a related))
      congr 1
      funext answer
      rw [expect_map, ← expect_const_mul]
      congr 1
      funext outcome
      rw [cleanWeight_cons, mul_assoc]
  | sample distribution next ih =>
      rw [runLog, run_sample, expect_bind, expect_bind]
      exact expect_mono _ fun value => ih value rel

end State

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
