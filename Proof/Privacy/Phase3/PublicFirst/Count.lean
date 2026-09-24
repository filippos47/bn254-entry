/-
**Phase 3, P1d — the stage-1 entries and their touch mass.**

`entryCount σ` counts every stored pair of a lazy state (all fixed-key and EncPRF indices, and the
hash table). A query adds at most one (`query_entryCount_le`), so a run of a program with budget `b`
adds at most `b` (`run_entryCount_le`, `runFlag_entryCount_le`): the adversary's first stage, from the
empty oracle, leaves at most `q₁` entries.

`touch_mass_le`: if stage-2 points are drawn from a law `ν` whose every input/output pair at an index
has mass at most `c` (and every hash key at most `c`), the probability that a state's stored pairs
touch them is at most `entryCount σ · c` — the per-entry union bound behind `4q₁/2^128`.
-/

import Proof.Privacy.Phase3.PublicFirst.Plant

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open Cryptography GarbledCircuit
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

variable {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
  [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- Every stored pair of a lazy state. -/
def entryCount (state : LazyOracle.State FixedIndex EncIndex) : ℕ :=
  (∑ index, (state.fixed index).used) + (∑ index, (state.enc index).used) + state.hash.length

theorem sum_update_le {Index : Type} [Fintype Index] [DecidableEq Index]
    (family : Index → SparsePermutation (2 ^ 128)) (index : Index)
    (next : SparsePermutation (2 ^ 128)) (grows : next.used ≤ (family index).used + 1) :
    ∑ other, (Function.update family index next other).used ≤ (∑ other, (family other).used) + 1 := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ index),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ index)]
  have rest : ∑ other ∈ Finset.univ.erase index, (Function.update family index next other).used
      = ∑ other ∈ Finset.univ.erase index, (family other).used :=
    Finset.sum_congr rfl fun other member => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase member)]
  rw [rest, Function.update_self]
  omega

/-- **A query stores at most one pair.** -/
theorem query_entryCount_le (request : PublicQuery FixedIndex EncIndex)
    (state : LazyOracle.State FixedIndex EncIndex) (outcome : request.Answer × LazyOracle.State FixedIndex EncIndex)
    (member : outcome ∈ (LazyOracle.query request state).support) :
    entryCount outcome.2 ≤ entryCount state + 1 := by
  cases request with
  | fixedForward index input =>
    obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have := sum_update_le state.fixed index drawn.2
      ((state.fixed index).forward_used_le input.toFin drawn drawnMember)
    simp only [entryCount]
    omega
  | fixedInverse index output =>
    obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have := sum_update_le state.fixed index drawn.2
      ((state.fixed index).inverse_used_le output.toFin drawn drawnMember)
    simp only [entryCount]
    omega
  | encForward index input =>
    obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have := sum_update_le state.enc index drawn.2
      ((state.enc index).forward_used_le input.toFin drawn drawnMember)
    simp only [entryCount]
    omega
  | encInverse index output =>
    obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have := sum_update_le state.enc index drawn.2
      ((state.enc index).inverse_used_le output.toFin drawn drawnMember)
    simp only [entryCount]
    omega
  | hash input =>
    obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have := HashTable.query_length_le (Fintype.card_pos) state.hash input drawn drawnMember
    simp only [entryCount]
    omega

/-- **A run of budget `b` stores at most `b` pairs.** -/
theorem run_entryCount_le {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget) :
    ∀ (state : LazyOracle.State FixedIndex EncIndex) outcome,
      outcome ∈ (LazyOracle.run program state).support →
        entryCount outcome.2 ≤ entryCount state + budget := by
  induction program with
  | pure distribution =>
    intro state outcome member
    obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Nat.le_add_right _ _
  | query request next ih =>
    intro state outcome member
    simp only [LazyOracle.run, runSampled, PMF.mem_support_bind_iff] at member
    obtain ⟨answer, answerMember, resultMember⟩ := member
    have step := query_entryCount_le request state answer answerMember
    have rest := ih answer.1 answer.2 outcome resultMember
    omega
  | sample distribution next ih =>
    intro state outcome member
    simp only [LazyOracle.run, runSampled, PMF.mem_support_bind_iff] at member
    obtain ⟨value, _, resultMember⟩ := member
    exact ih value state outcome resultMember

/-- The same for the flagged run. -/
theorem runFlag_entryCount_le (planted : LazyOracle.State FixedIndex EncIndex) {Result : Type}
    {budget : ℕ} (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget) :
    ∀ (state : LazyOracle.State FixedIndex EncIndex) (outcome : Result × _),
      some outcome ∈ (runFlag planted program state).support →
        entryCount outcome.2 ≤ entryCount state + budget := by
  classical
  induction program with
  | pure distribution =>
    intro state outcome member
    obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    cases same
    exact Nat.le_add_right _ _
  | query request next ih =>
    intro state outcome member
    simp only [runFlag, PMF.mem_support_bind_iff] at member
    obtain ⟨answer, answerMember, resultMember⟩ := member
    split at resultMember
    · simp at resultMember
    · have step := query_entryCount_le request state answer answerMember
      have rest := ih answer.1 answer.2 outcome resultMember
      omega
  | sample distribution next ih =>
    intro state outcome member
    simp only [runFlag, PMF.mem_support_bind_iff] at member
    obtain ⟨value, _, resultMember⟩ := member
    exact ih value state outcome resultMember

theorem entryCount_empty :
    entryCount (LazyOracle.empty : LazyOracle.State FixedIndex EncIndex) = 0 := by
  simp [entryCount, LazyOracle.empty, SparsePermutation.empty]

/-! ### The union bound over stored pairs -/

theorem card_known {size : ℕ} (state : SparsePermutation size) :
    Fintype.card {x : Fin size // state.knownInput x} = state.used := by
  classical
  have equiv : {x : Fin size // state.knownInput x} ≃ {p : Fin size // p.val < state.used} :=
    state.input.symm.subtypeEquiv fun x => Iff.rfl
  rw [Fintype.card_congr equiv, Fintype.card_fin_lt_of_le state.within]

/-- Stage-2 points, as membership predicates. -/
structure Points (FixedIndex EncIndex : Type) where
  fixedIn : FixedIndex → Block → Prop
  fixedOut : FixedIndex → Block → Prop
  encIn : EncIndex → Block → Prop
  encOut : EncIndex → Block → Prop
  hashIn : BN254.BaseField → Prop

/-- A lazy state's stored pairs touch the points. -/
def Touches (state : LazyOracle.State FixedIndex EncIndex) (points : Points FixedIndex EncIndex) :
    Prop :=
  (∃ i x y, lk (state.fixed i) x = some y ∧
      (points.fixedIn i (BitVec.ofFin x) ∨ points.fixedOut i (BitVec.ofFin y))) ∨
    (∃ i x y, lk (state.enc i) x = some y ∧
      (points.encIn i (BitVec.ofFin x) ∨ points.encOut i (BitVec.ofFin y))) ∨
    (∃ k v, state.hash.lookup k = some v ∧ points.hashIn k)

/-- The value a known input stores. -/
def storedValue {size : ℕ} (state : SparsePermutation size) (x : {x : Fin size // state.knownInput x}) :
    Fin size := state.output (state.input.symm x.val)

theorem lk_known {size : ℕ} {state : SparsePermutation size} {x y : Fin size}
    (found : lk state x = some y) : ∃ known : state.knownInput x, storedValue state ⟨x, known⟩ = y := by
  rw [lk_eq] at found
  split at found
  · rename_i known
    exact ⟨known, Option.some.inj found⟩
  · cases found

theorem sum_known_mass_le {size : ℕ} (state : SparsePermutation size)
    (mass : {x : Fin size // state.knownInput x} → ℝ≥0∞) (c : ℝ≥0∞) (bound : ∀ x, mass x ≤ c) :
    ∑ x, mass x ≤ state.used * c := by
  calc ∑ x, mass x ≤ ∑ _x : {x : Fin size // state.knownInput x}, c :=
        Finset.sum_le_sum fun x _ => bound x
    _ = state.used * c := by
        rw [Finset.sum_const, Finset.card_univ, card_known, nsmul_eq_mul]

theorem list_lookup_mem {K V : Type} [DecidableEq K] :
    ∀ {l : List (K × V)} {k : K} {v : V}, l.lookup k = some v → ∃ pair ∈ l, pair.1 = k
  | [], _, _, found => by simp at found
  | ⟨key, value⟩ :: tail, k, v, found => by
    by_cases same : key = k
    · exact ⟨⟨key, value⟩, List.mem_cons_self, same⟩
    · have rest : tail.lookup k = some v := by
        have different : (k == key) = false := by simpa [beq_iff_eq] using Ne.symm same
        simpa [List.lookup, different] using found
      obtain ⟨pair, member, eq⟩ := list_lookup_mem rest
      exact ⟨pair, List.mem_cons_of_mem _ member, eq⟩

/-- **The touch mass is at most the number of stored pairs times the per-pair mass.** -/
theorem touch_mass_le (state : LazyOracle.State FixedIndex EncIndex)
    (law : PMF (Points FixedIndex EncIndex)) (c : ℝ≥0∞)
    (fixedBound : ∀ i x y, law.toOuterMeasure {p | p.fixedIn i x} +
      law.toOuterMeasure {p | p.fixedOut i y} ≤ c)
    (encBound : ∀ i x y, law.toOuterMeasure {p | p.encIn i x} +
      law.toOuterMeasure {p | p.encOut i y} ≤ c)
    (hashBound : ∀ k, law.toOuterMeasure {p | p.hashIn k} ≤ c) :
    law.toOuterMeasure {p | Touches state p} ≤ entryCount state * c := by
  classical
  let fixedSet (a : Σ i, {x : Fin (2 ^ 128) // (state.fixed i).knownInput x}) :
      Set (Points FixedIndex EncIndex) :=
    {p | p.fixedIn a.1 (BitVec.ofFin a.2.val)} ∪
      {p | p.fixedOut a.1 (BitVec.ofFin (storedValue (state.fixed a.1) a.2))}
  let encSet (a : Σ i, {x : Fin (2 ^ 128) // (state.enc i).knownInput x}) :
      Set (Points FixedIndex EncIndex) :=
    {p | p.encIn a.1 (BitVec.ofFin a.2.val)} ∪
      {p | p.encOut a.1 (BitVec.ofFin (storedValue (state.enc a.1) a.2))}
  let hashSet (j : Fin state.hash.length) : Set (Points FixedIndex EncIndex) :=
    {p | p.hashIn (state.hash.get j).1}
  have cover : {p | Touches state p} ⊆ (⋃ a, fixedSet a) ∪ (⋃ a, encSet a) ∪ (⋃ j, hashSet j) := by
    rintro p (⟨i, x, y, found, hit⟩ | ⟨i, x, y, found, hit⟩ | ⟨k, v, found, hit⟩)
    · obtain ⟨known, value⟩ := lk_known found
      refine Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨⟨i, x, known⟩, ?_⟩))
      rcases hit with hit | hit
      · exact Or.inl hit
      · exact Or.inr (by simp only [Set.mem_ofPred_eq]; rw [value]; exact hit)
    · obtain ⟨known, value⟩ := lk_known found
      refine Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨i, x, known⟩, ?_⟩))
      rcases hit with hit | hit
      · exact Or.inl hit
      · exact Or.inr (by simp only [Set.mem_ofPred_eq]; rw [value]; exact hit)
    · obtain ⟨j, hj⟩ : ∃ j : Fin state.hash.length, (state.hash.get j).1 = k := by
        obtain ⟨pair, member, rfl⟩ := list_lookup_mem found
        obtain ⟨j, hj⟩ := List.get_of_mem member
        exact ⟨j, by rw [hj]⟩
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, by simp only [hashSet, Set.mem_ofPred_eq, hj]; exact hit⟩)
  refine le_trans (MeasureTheory.measure_mono cover) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine le_trans (add_le_add (MeasureTheory.measure_union_le _ _) le_rfl) ?_
  have fixedPart : law.toOuterMeasure (⋃ a, fixedSet a) ≤ (∑ i, (state.fixed i).used : ℕ) * c := by
    refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
    rw [tsum_fintype, Fintype.sum_sigma]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => sum_known_mass_le _ _ c fun x =>
      le_trans (MeasureTheory.measure_union_le _ _) (fixedBound _ _ _)
  have encPart : law.toOuterMeasure (⋃ a, encSet a) ≤ (∑ i, (state.enc i).used : ℕ) * c := by
    refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
    rw [tsum_fintype, Fintype.sum_sigma]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => sum_known_mass_le _ _ c fun x =>
      le_trans (MeasureTheory.measure_union_le _ _) (encBound _ _ _)
  have hashPart : law.toOuterMeasure (⋃ j, hashSet j) ≤ state.hash.length * c := by
    refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
    rw [tsum_fintype]
    calc ∑ j, law.toOuterMeasure (hashSet j) ≤ ∑ _j : Fin state.hash.length, c :=
          Finset.sum_le_sum fun j _ => hashBound _
      _ = state.hash.length * c := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  calc _ ≤ (∑ i, (state.fixed i).used : ℕ) * c + (∑ i, (state.enc i).used : ℕ) * c +
        state.hash.length * c := add_le_add (add_le_add fixedPart encPart) hashPart
    _ = entryCount state * c := by
        simp only [entryCount, Nat.cast_add]
        ring

/-- **The stage-1 touch mass.** A run of budget `b` from the empty oracle, against stage-2 points drawn
after it (from any kernel of its outcome) with per-pair mass at most `c`, touches them with mass at
most `b · c`. -/
theorem run_touch_mass_le {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (law : Result × LazyOracle.State FixedIndex EncIndex → PMF (Points FixedIndex EncIndex))
    (c : ℝ≥0∞)
    (fixedBound : ∀ o i x y, (law o).toOuterMeasure {p | p.fixedIn i x} +
      (law o).toOuterMeasure {p | p.fixedOut i y} ≤ c)
    (encBound : ∀ o i x y, (law o).toOuterMeasure {p | p.encIn i x} +
      (law o).toOuterMeasure {p | p.encOut i y} ≤ c)
    (hashBound : ∀ o k, (law o).toOuterMeasure {p | p.hashIn k} ≤ c) :
    ∑' o, LazyOracle.run program LazyOracle.empty o * (law o).toOuterMeasure {p | Touches o.2 p}
      ≤ budget * c := by
  calc _ ≤ ∑' o, LazyOracle.run program LazyOracle.empty o * (budget * c) := by
        refine ENNReal.tsum_le_tsum fun o => ?_
        by_cases member : o ∈ (LazyOracle.run program LazyOracle.empty).support
        · refine mul_le_mul' le_rfl (le_trans (touch_mass_le o.2 (law o) c (fixedBound o)
            (encBound o) (hashBound o)) (mul_le_mul' ?_ le_rfl))
          have count := run_entryCount_le program LazyOracle.empty o member
          rw [entryCount_empty, zero_add] at count
          exact_mod_cast count
        · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]
    _ = budget * c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
