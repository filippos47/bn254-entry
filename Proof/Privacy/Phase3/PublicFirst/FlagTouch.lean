/-
**Phase 3, P1i — (B), part 1: a flag of a flagged private run is a touch of the unflagged final state.**

The middle game `M'` runs its private stage 2 through flagged runners (`runLazyQFlag`,
`runRefillFlag`, `runFillFlag`, `programAllSkipFlag`): each stops (`none`) at the first question or
program that touches the stage-1 state `σ₁` (`FullTouch`). For the flag mass we compare each with
its **unflagged** run (the same runner against the empty planted state) and charge a flag to the
event that the unflagged run's **final** private state *meets* `σ₁` — some pair of `σ₁` shares an
input or an output with a stored pair of the final state (`Touches σ₁ (pointsOf final)`, P1d's
union-bound event). Nothing is lost:

* a touching question stores the pair it touches with (`query_touch`, `program_touch`,
  `program_hash_touch`);
* a lazy run, a program and every runner only **grow** the state (`Grows`, `query_grows`,
  `program_state_grows`, `program_hash_grows`), and meeting `σ₁` is monotone in growth
  (`touches_grows`).

`runLazyQFlag_le`: for continuation weights `F ≤ G` with `G` saturated on states that meet `σ₁`,
the flagged run weighted by `F` (a flag weighs `1`) is below the unflagged run weighted by `G`.
-/

import Proof.Privacy.Phase3.PublicFirst.Fill
import Proof.Privacy.Phase3.PublicFirst.Count

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open Cryptography GarbledCircuit
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### Growth of one sparse permutation -/

section Sparse

variable {size : ℕ}

/-- A forward query keeps every stored pair. -/
theorem forward_grows (state : SparsePermutation size) (x : Fin size)
    (answer : Fin size × SparsePermutation size)
    (member : answer ∈ (state.forward x).distribution.support) (z w : Fin size)
    (found : lk state z = some w) : lk answer.2 z = some w := by
  unfold SparsePermutation.forward at member
  dsimp only at member
  split at member
  · simp only [Draw.distribution, PMF.mem_support_pure_iff] at member
    subst member
    exact found
  · rename_i fresh
    obtain ⟨rank, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rw [← same]
    dsimp only
    have freshX : ¬ state.knownInput x := fresh
    have freshY : ¬ state.knownOutput (state.output (state.suffix rank)) := by
      show ¬ (state.output.symm (state.output (state.suffix rank))).val < state.used
      rw [Equiv.symm_apply_apply]
      simp [SparsePermutation.suffix]
    have room : state.used < size := by
      have := (state.input.symm x).isLt
      unfold SparsePermutation.knownInput at freshX
      omega
    have shape := lookup_extend state x (state.output (state.suffix rank)) freshX freshY room z
    rw [Equiv.symm_apply_apply] at shape
    rw [shape, if_neg]
    · exact found
    · rintro rfl
      exact freshX ((knownInput_iff state z).mpr (by rw [found]; simp))

/-- An inverse query keeps every stored pair. -/
theorem inverse_grows (state : SparsePermutation size) (y : Fin size)
    (answer : Fin size × SparsePermutation size)
    (member : answer ∈ (state.inverse y).distribution.support) (z w : Fin size)
    (found : lk state z = some w) : lk answer.2 z = some w := by
  unfold SparsePermutation.inverse at member
  dsimp only at member
  split at member
  · simp only [Draw.distribution, PMF.mem_support_pure_iff] at member
    subst member
    exact found
  · rename_i fresh
    obtain ⟨rank, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rw [← same]
    dsimp only
    have freshY : ¬ state.knownOutput y := fresh
    have freshX : ¬ state.knownInput (state.input (state.suffix rank)) := by
      show ¬ (state.input.symm (state.input (state.suffix rank))).val < state.used
      rw [Equiv.symm_apply_apply]
      simp [SparsePermutation.suffix]
    have room : state.used < size := by
      have := (state.output.symm y).isLt
      unfold SparsePermutation.knownOutput at freshY
      omega
    have shape := lookup_extend state (state.input (state.suffix rank)) y freshX freshY room z
    rw [Equiv.symm_apply_apply] at shape
    rw [shape, if_neg]
    · exact found
    · rintro rfl
      exact freshX ((knownInput_iff state _).mpr (by rw [found]; simp))

/-- An inverse query stores the pair it returns. -/
theorem inverse_records (state : SparsePermutation size) (y : Fin size)
    (answer : Fin size × SparsePermutation size)
    (member : answer ∈ (state.inverse y).distribution.support) : lk answer.2 answer.1 = some y := by
  unfold SparsePermutation.inverse at member
  dsimp only at member
  split at member
  · rename_i known
    simp only [Draw.distribution, PMF.mem_support_pure_iff] at member
    subst member
    rw [lk_eq, if_pos]
    · rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    · show (state.input.symm (state.input (state.output.symm y))).val < state.used
      rw [Equiv.symm_apply_apply]
      exact known
  · rename_i fresh
    obtain ⟨rank, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rw [← same]
    dsimp only
    have freshY : ¬ state.knownOutput y := fresh
    have freshX : ¬ state.knownInput (state.input (state.suffix rank)) := by
      show ¬ (state.input.symm (state.input (state.suffix rank))).val < state.used
      rw [Equiv.symm_apply_apply]
      simp [SparsePermutation.suffix]
    have room : state.used < size := by
      have := (state.output.symm y).isLt
      unfold SparsePermutation.knownOutput at freshY
      omega
    have shape := lookup_extend state (state.input (state.suffix rank)) y freshX freshY room
      (state.input (state.suffix rank))
    rw [Equiv.symm_apply_apply] at shape
    rw [shape, if_pos rfl]

/-- A successful program keeps every stored pair. -/
theorem program_grows (state next : SparsePermutation size) (x y : Fin size)
    (success : LazyOracle.permutationProgram state x y = some next) (z w : Fin size)
    (found : lk state z = some w) : lk next z = some w := by
  unfold LazyOracle.permutationProgram at success
  split at success
  · rename_i fresh
    cases success
    have room : state.used < size := by
      have := (state.input.symm x).isLt
      have h := fresh.1
      unfold SparsePermutation.knownInput at h
      omega
    have shape := lookup_extend state x y fresh.1 fresh.2 room z
    rw [shape, if_neg]
    · exact found
    · rintro rfl
      exact fresh.1 ((knownInput_iff state z).mpr (by rw [found]; simp))
  · cases success

end Sparse

/-! ### Stored pairs as points, growth, and meeting a planted state -/

section Generic

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **The stored pairs of a lazy state, as stage-2 points.** -/
def pointsOf (state : LazyOracle.State FixedIndex EncIndex) : Points FixedIndex EncIndex where
  fixedIn i x := lk (state.fixed i) x.toFin ≠ none
  fixedOut i y := ∃ x, lk (state.fixed i) x = some y.toFin
  encIn i x := lk (state.enc i) x.toFin ≠ none
  encOut i y := ∃ x, lk (state.enc i) x = some y.toFin
  hashIn k := state.hash.lookup k ≠ none

/-- **`later` keeps every stored pair of `earlier`.** -/
structure Grows (earlier later : LazyOracle.State FixedIndex EncIndex) : Prop where
  fixed : ∀ i x y, lk (earlier.fixed i) x = some y → lk (later.fixed i) x = some y
  enc : ∀ i x y, lk (earlier.enc i) x = some y → lk (later.enc i) x = some y
  hash : ∀ k v, earlier.hash.lookup k = some v → later.hash.lookup k = some v

theorem Grows.refl (state : LazyOracle.State FixedIndex EncIndex) : Grows state state :=
  ⟨fun _ _ _ found => found, fun _ _ _ found => found, fun _ _ found => found⟩

theorem Grows.trans {first second third : LazyOracle.State FixedIndex EncIndex}
    (one : Grows first second) (two : Grows second third) : Grows first third :=
  ⟨fun i x y found => two.fixed i x y (one.fixed i x y found),
   fun i x y found => two.enc i x y (one.enc i x y found),
   fun k v found => two.hash k v (one.hash k v found)⟩

theorem ne_none_of_grows {size : ℕ} {s t : SparsePermutation size}
    (grow : ∀ x y, lk s x = some y → lk t x = some y) {x : Fin size} (found : lk s x ≠ none) :
    lk t x ≠ none := by
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp found
  rw [grow x y hy]
  simp

/-- **Meeting a planted state is monotone in growth.** -/
theorem touches_grows {planted s s' : LazyOracle.State FixedIndex EncIndex} (grow : Grows s s')
    (hit : Touches planted (pointsOf s)) : Touches planted (pointsOf s') := by
  rcases hit with ⟨i, x, y, found, hit⟩ | ⟨i, x, y, found, hit⟩ | ⟨k, v, found, hit⟩
  · refine Or.inl ⟨i, x, y, found, ?_⟩
    rcases hit with hit | ⟨w, hw⟩
    · exact Or.inl (ne_none_of_grows (grow.fixed i) hit)
    · exact Or.inr ⟨w, grow.fixed i w _ hw⟩
  · refine Or.inr (Or.inl ⟨i, x, y, found, ?_⟩)
    rcases hit with hit | ⟨w, hw⟩
    · exact Or.inl (ne_none_of_grows (grow.enc i) hit)
    · exact Or.inr ⟨w, grow.enc i w _ hw⟩
  · refine Or.inr (Or.inr ⟨k, v, found, ?_⟩)
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hit
    show s'.hash.lookup k ≠ none
    rw [grow.hash k u hu]
    simp

/-- A hash query keeps every stored key. -/
theorem hash_query_grows {n : ℕ} (positive : 0 < n) (table : HashTable BN254.BaseField n)
    (key : BN254.BaseField) (answer : Fin n × HashTable BN254.BaseField n)
    (member : answer ∈ (table.query positive key).distribution.support) :
    (∀ k v, table.lookup k = some v → answer.2.lookup k = some v) ∧ answer.2.lookup key ≠ none := by
  unfold HashTable.query at member
  split at member
  · rename_i value found
    simp only [Draw.distribution, PMF.mem_support_pure_iff] at member
    subst member
    exact ⟨fun _ _ h => h, by rw [found]; simp⟩
  · rename_i missing
    obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rw [← same]
    refine ⟨fun k v found => ?_, by simp [List.lookup]⟩
    have different : (k == key) = false := by
      rw [beq_eq_false_iff_ne]
      rintro rfl
      rw [missing] at found
      cases found
    simp only [List.lookup, different]
    exact found

/-- **A lazy query keeps every stored pair.** -/
theorem query_grows (request : PublicQuery FixedIndex EncIndex)
    (state : LazyOracle.State FixedIndex EncIndex)
    (outcome : request.Answer × LazyOracle.State FixedIndex EncIndex)
    (member : outcome ∈ (LazyOracle.query request state).support) : Grows state outcome.2 := by
  cases request with
  | fixedForward index input =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    refine ⟨fun i x y found => ?_, fun _ _ _ found => found, fun _ _ found => found⟩
    by_cases same : i = index
    · subst same
      simp only [Function.update_self]
      exact forward_grows _ _ answer answerMember x y found
    · simpa [Function.update_of_ne same] using found
  | fixedInverse index output =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    refine ⟨fun i x y found => ?_, fun _ _ _ found => found, fun _ _ found => found⟩
    by_cases same : i = index
    · subst same
      simp only [Function.update_self]
      exact inverse_grows _ _ answer answerMember x y found
    · simpa [Function.update_of_ne same] using found
  | encForward index input =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    refine ⟨fun _ _ _ found => found, fun i x y found => ?_, fun _ _ found => found⟩
    by_cases same : i = index
    · subst same
      simp only [Function.update_self]
      exact forward_grows _ _ answer answerMember x y found
    · simpa [Function.update_of_ne same] using found
  | encInverse index output =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    refine ⟨fun _ _ _ found => found, fun i x y found => ?_, fun _ _ found => found⟩
    by_cases same : i = index
    · subst same
      simp only [Function.update_self]
      exact inverse_grows _ _ answer answerMember x y found
    · simpa [Function.update_of_ne same] using found
  | hash input =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact ⟨fun _ _ _ found => found, fun _ _ _ found => found,
      (hash_query_grows _ state.hash input answer answerMember).1⟩

/-- **A touching lazy question stores the pair it touches with.** -/
theorem query_touch (planted : LazyOracle.State FixedIndex EncIndex)
    (request : PublicQuery FixedIndex EncIndex) (state : LazyOracle.State FixedIndex EncIndex)
    (outcome : request.Answer × LazyOracle.State FixedIndex EncIndex)
    (member : outcome ∈ (LazyOracle.query request state).support)
    (touch : FullTouch planted request outcome.1) : Touches planted (pointsOf outcome.2) := by
  cases request with
  | fixedForward index input =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have stored : lk ((Function.update state.fixed index answer.2) index) input.toFin
        = some answer.1 := by
      rw [Function.update_self]
      exact LazyOracle.forward_lookup _ _ answer answerMember
    simp only [FullTouch, TouchForward] at touch
    rcases touch with hit | hit
    · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hit
      refine Or.inl ⟨index, input.toFin, y, hy, Or.inl ?_⟩
      show lk ((Function.update state.fixed index answer.2) index) (BitVec.ofFin input.toFin).toFin
        ≠ none
      rw [BitVec.toFin_ofFin, stored]
      simp
    · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hit
      refine Or.inl ⟨index, x, answer.1, (lookup_reverse _ x answer.1).mp hx, Or.inr ?_⟩
      exact ⟨input.toFin, by rw [stored, BitVec.toFin_ofFin]⟩
  | fixedInverse index output =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have stored : lk ((Function.update state.fixed index answer.2) index) answer.1
        = some output.toFin := by
      rw [Function.update_self]
      exact inverse_records _ _ answer answerMember
    simp only [FullTouch, TouchForward] at touch
    rcases touch with hit | hit
    · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hit
      refine Or.inl ⟨index, x, output.toFin, (lookup_reverse _ x output.toFin).mp hx, Or.inr ?_⟩
      exact ⟨answer.1, by rw [stored, BitVec.toFin_ofFin]⟩
    · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hit
      refine Or.inl ⟨index, answer.1, y, hy, Or.inl ?_⟩
      show lk ((Function.update state.fixed index answer.2) index) (BitVec.ofFin answer.1).toFin
        ≠ none
      rw [BitVec.toFin_ofFin, stored]
      simp
  | encForward index input =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have stored : lk ((Function.update state.enc index answer.2) index) input.toFin
        = some answer.1 := by
      rw [Function.update_self]
      exact LazyOracle.forward_lookup _ _ answer answerMember
    simp only [FullTouch, TouchForward] at touch
    rcases touch with hit | hit
    · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hit
      refine Or.inr (Or.inl ⟨index, input.toFin, y, hy, Or.inl ?_⟩)
      show lk ((Function.update state.enc index answer.2) index) (BitVec.ofFin input.toFin).toFin
        ≠ none
      rw [BitVec.toFin_ofFin, stored]
      simp
    · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hit
      refine Or.inr (Or.inl ⟨index, x, answer.1, (lookup_reverse _ x answer.1).mp hx, Or.inr ?_⟩)
      exact ⟨input.toFin, by rw [stored, BitVec.toFin_ofFin]⟩
  | encInverse index output =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have stored : lk ((Function.update state.enc index answer.2) index) answer.1
        = some output.toFin := by
      rw [Function.update_self]
      exact inverse_records _ _ answer answerMember
    simp only [FullTouch, TouchForward] at touch
    rcases touch with hit | hit
    · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hit
      refine Or.inr (Or.inl ⟨index, x, output.toFin, (lookup_reverse _ x output.toFin).mp hx,
        Or.inr ?_⟩)
      exact ⟨answer.1, by rw [stored, BitVec.toFin_ofFin]⟩
    · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hit
      refine Or.inr (Or.inl ⟨index, answer.1, y, hy, Or.inl ?_⟩)
      show lk ((Function.update state.enc index answer.2) index) (BitVec.ofFin answer.1).toFin
        ≠ none
      rw [BitVec.toFin_ofFin, stored]
      simp
  | hash input =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    simp only [FullTouch] at touch
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp touch
    exact Or.inr (Or.inr ⟨input, v, hv, (hash_query_grows _ state.hash input answer answerMember).2⟩)

/-- **A successful fixed-key program keeps every stored pair.** -/
theorem program_state_grows (index : FixedIndex) (input output : Block)
    (state updated : LazyOracle.State FixedIndex EncIndex)
    (success : LazyOracle.program (.fixedForward index input) output state = some updated) :
    Grows state updated := by
  simp only [LazyOracle.program, Option.map_eq_some_iff] at success
  obtain ⟨next, programmed, rfl⟩ := success
  refine ⟨fun i x y found => ?_, fun _ _ _ found => found, fun _ _ found => found⟩
  by_cases same : i = index
  · subst same
    simp only [Function.update_self]
    exact program_grows _ _ _ _ programmed x y found
  · simpa [Function.update_of_ne same] using found

/-- **A touching fixed-key program stores the pair it touches with.** -/
theorem program_touch (planted : LazyOracle.State FixedIndex EncIndex) (index : FixedIndex)
    (input output : Block) (state updated : LazyOracle.State FixedIndex EncIndex)
    (success : LazyOracle.program (.fixedForward index input) output state = some updated)
    (touch : FullTouch planted (.fixedForward index input) output) :
    Touches planted (pointsOf updated) := by
  simp only [LazyOracle.program, Option.map_eq_some_iff] at success
  obtain ⟨next, programmed, rfl⟩ := success
  have stored : lk ((Function.update state.fixed index next) index) input.toFin
      = some output.toFin := by
    rw [Function.update_self]
    exact LazyOracle.permutationProgram_lookup _ _ _ _ programmed
  simp only [FullTouch, TouchForward] at touch
  rcases touch with hit | hit
  · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hit
    refine Or.inl ⟨index, input.toFin, y, hy, Or.inl ?_⟩
    show lk ((Function.update state.fixed index next) index) (BitVec.ofFin input.toFin).toFin ≠ none
    rw [BitVec.toFin_ofFin, stored]
    simp
  · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hit
    refine Or.inl ⟨index, x, output.toFin, (lookup_reverse _ x output.toFin).mp hx, Or.inr ?_⟩
    exact ⟨input.toFin, by rw [stored, BitVec.toFin_ofFin]⟩

/-- **A successful hash program keeps every stored pair** (it stores only at a fresh input). -/
theorem program_hash_grows (input : BN254.BaseField) (answer : Block × Block)
    (state updated : LazyOracle.State FixedIndex EncIndex)
    (success : LazyOracle.program (.hash input) answer state = some updated) :
    Grows state updated := by
  simp only [LazyOracle.program] at success
  split_ifs at success with fresh
  cases success
  refine ⟨fun _ _ _ found => found, fun _ _ _ found => found, fun k v found => ?_⟩
  have different : k ≠ input := by
    rintro rfl
    rw [fresh] at found
    cases found
  show (state.hash.program input _).lookup k = some v
  rw [HashTable.program_lookup, Function.update_of_ne different]
  exact found

/-- **A touching hash program stores the key it touches with.** -/
theorem program_hash_touch (planted : LazyOracle.State FixedIndex EncIndex)
    (input : BN254.BaseField) (answer : Block × Block)
    (state updated : LazyOracle.State FixedIndex EncIndex)
    (success : LazyOracle.program (.hash input) answer state = some updated)
    (touch : FullTouch planted (.hash input) answer) :
    Touches planted (pointsOf updated) := by
  simp only [LazyOracle.program] at success
  split_ifs at success with fresh
  cases success
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (show planted.hash.lookup input ≠ none from touch)
  refine Or.inr (Or.inr ⟨input, v, hv, ?_⟩)
  show (state.hash.program input _).lookup input ≠ none
  rw [HashTable.program_lookup, Function.update_self]
  simp

/-- Nothing touches the empty state. -/
theorem not_fullTouch_empty (request : PublicQuery FixedIndex EncIndex) (answer : request.Answer) :
    ¬ FullTouch (LazyOracle.empty : LazyOracle.State FixedIndex EncIndex) request answer := by
  have none_lk : ∀ x : Fin (2 ^ 128), lk (SparsePermutation.empty (2 ^ 128)) x = none := by
    intro x
    rw [lk_eq, if_neg]
    show ¬ _ < 0
    omega
  have none_rev : ∀ x : Fin (2 ^ 128), lk (SparsePermutation.empty (2 ^ 128)).reverse x = none := by
    intro x
    rw [lk_eq, if_neg]
    show ¬ _ < 0
    omega
  intro touch
  cases request with
  | fixedForward index input =>
    rcases touch with hit | hit
    · exact hit (none_lk _)
    · exact hit (none_rev _)
  | fixedInverse index output =>
    rcases touch with hit | hit
    · exact hit (none_rev _)
    · exact hit (none_lk _)
  | encForward index input =>
    rcases touch with hit | hit
    · exact hit (none_lk _)
    · exact hit (none_rev _)
  | encInverse index output =>
    rcases touch with hit | hit
    · exact hit (none_rev _)
    · exact hit (none_lk _)
  | hash input => exact touch rfl

end Generic

/-! ### Flagged runs against unflagged runs -/

section Runs

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **A lazy run only grows the state.** -/
theorem runLazyQ_grows {α : Type} (computation : FreeQuery (publicOracleSpec FixedIndex EncIndex) α) :
    ∀ (state : LazyOracle.State FixedIndex EncIndex) (outcome : α × LazyOracle.State FixedIndex EncIndex),
      outcome ∈ (runLazyQ computation state).support → Grows state outcome.2 := by
  induction computation with
  | pure value =>
    intro state outcome member
    simp only [runLazyQ, PMF.mem_support_pure_iff] at member
    subst member
    exact Grows.refl _
  | query request next ih =>
    intro state outcome member
    simp only [runLazyQ, PMF.mem_support_bind_iff] at member
    obtain ⟨answer, answerMember, rest⟩ := member
    exact (query_grows request state answer answerMember).trans (ih answer.1 answer.2 outcome rest)

/-- The weight of a flagged outcome: a flag weighs `1`. -/
def flagWeight {β : Type} (h : β → ℝ≥0∞) : Option β → ℝ≥0∞
  | none => 1
  | some b => h b

/-- An expectation is at least `1` when its integrand is on the support. -/
theorem one_le_expect {α : Type} (μ : PMF α) (G : α → ℝ≥0∞) (big : ∀ a ∈ μ.support, 1 ≤ G a) :
    1 ≤ ∑' a, μ a * G a := by
  calc (1 : ℝ≥0∞) = ∑' a, μ a * 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ ∑' a, μ a * G a := ENNReal.tsum_le_tsum fun a => by
        by_cases member : a ∈ μ.support
        · exact mul_le_mul' le_rfl (big a member)
        · rw [(PMF.apply_eq_zero_iff μ a).mpr member, zero_mul, zero_mul]

/-- **Extra lazy questions, flagged against unflagged**: a flag weighs `1` and is charged to the
unflagged run's final state meeting `planted`. -/
theorem runLazyQFlag_le (planted : LazyOracle.State FixedIndex EncIndex) {α : Type}
    (F G : α × LazyOracle.State FixedIndex EncIndex → ℝ≥0∞) (le : ∀ o, F o ≤ G o)
    (saturated : ∀ o, Touches planted (pointsOf o.2) → 1 ≤ G o)
    (computation : FreeQuery (publicOracleSpec FixedIndex EncIndex) α) :
    ∀ state, ∑' o, runLazyQFlag planted computation state o * flagWeight F o
      ≤ ∑' o, runLazyQ computation state o * G o := by
  induction computation with
  | pure value =>
    intro state
    simp only [runLazyQFlag, runLazyQ, tsum_pure_mul, flagWeight]
    exact le _
  | query request next ih =>
    intro state
    simp only [runLazyQFlag, runLazyQ]
    rw [tsum_bind_mul, tsum_bind_mul]
    refine ENNReal.tsum_le_tsum fun answer => ?_
    by_cases member : answer ∈ (LazyOracle.query request state).support
    · refine mul_le_mul' le_rfl ?_
      split_ifs with touch
      · rw [tsum_pure_mul]
        refine one_le_expect _ _ fun o reached => saturated o ?_
        exact touches_grows (runLazyQ_grows _ _ o reached)
          (query_touch planted request state answer member touch)
      · exact ih answer.1 answer.2
    · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

end Runs

/-! ### The fill runner and the refill runner -/

section Refill

open BN254 Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Phase3.Glue (interceptAnswer recordAfter)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell consumeCell refillAnswer touch runRefill
  consumeCell_spec)

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The fill runner only grows the state.** -/
theorem runFillFlag_grows (planted : LState) (draw : Cell → PMF (Block × Block)) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (touched : Set Cell) (outcome : α × LState),
      some outcome ∈ (runFillFlag planted draw computation oracle touched).support →
        Grows oracle outcome.2 := by
  induction computation with
  | pure value =>
    intro oracle touched outcome member
    simp only [runFillFlag, PMF.mem_support_pure_iff, Option.some.injEq] at member
    subst member
    exact Grows.refl _
  | query request next ih =>
    intro oracle touched outcome member
    simp only [runFillFlag] at member
    split at member
    · rename_i cell consumed
      obtain ⟨input, rfl, _, _, _⟩ := consumeCell_spec consumed
      simp only [PMF.mem_support_bind_iff] at member
      obtain ⟨value, _, rest⟩ := member
      split at rest
      · simp at rest
      · split at rest
        · simp at rest
        · rename_i updated success
          exact (program_hash_grows input _ oracle updated success).trans (ih _ _ _ _ rest)
    · simp only [PMF.mem_support_bind_iff] at member
      obtain ⟨answer, answerMember, rest⟩ := member
      split at rest
      · simp at rest
      · exact (query_grows request oracle answer answerMember).trans (ih _ _ _ _ rest)

/-- **The fill runner, flagged against unflagged** (the same runner against the empty state). -/
theorem runFillFlag_le (planted : LState) (draw : Cell → PMF (Block × Block)) {α : Type}
    (F G : α × LState → ℝ≥0∞) (le : ∀ o, F o ≤ G o)
    (saturated : ∀ o, Touches planted (pointsOf o.2) → 1 ≤ G o)
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (touched : Set Cell),
      ∑' o, runFillFlag planted draw computation oracle touched o * flagWeight F o
        ≤ ∑' o, runFillFlag LazyOracle.empty draw computation oracle touched o *
            flagWeight G o := by
  induction computation with
  | pure value =>
    intro oracle touched
    simp only [runFillFlag, tsum_pure_mul, flagWeight]
    exact le _
  | query request next ih =>
    intro oracle touched
    simp only [runFillFlag]
    split
    · rename_i cell consumed
      obtain ⟨input, rfl, _, _, _⟩ := consumeCell_spec consumed
      rw [tsum_bind_mul, tsum_bind_mul]
      refine ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl ?_
      rw [if_neg (not_fullTouch_empty _ _)]
      cases success : LazyOracle.program (.hash input) (refillAnswer (.hash input) value) oracle with
      | none =>
        split_ifs <;> simp [flagWeight]
      | some updated =>
        simp only
        split_ifs with hit
        · rw [tsum_pure_mul]
          refine one_le_expect _ _ fun o reached => ?_
          cases o with
          | none => exact le_rfl
          | some o =>
            exact saturated o (touches_grows (runFillFlag_grows _ _ _ _ _ o reached)
              (program_hash_touch planted input _ oracle _ success hit))
        · exact ih _ _ _
    · rw [tsum_bind_mul, tsum_bind_mul]
      refine ENNReal.tsum_le_tsum fun answer => ?_
      by_cases member : answer ∈ (LazyOracle.query request oracle).support
      · refine mul_le_mul' le_rfl ?_
        rw [if_neg (not_fullTouch_empty _ _)]
        split_ifs with hit
        · rw [tsum_pure_mul]
          refine one_le_expect _ _ fun o reached => ?_
          cases o with
          | none => exact le_rfl
          | some o =>
            exact saturated o (touches_grows (runFillFlag_grows _ _ _ _ _ o reached)
              (query_touch planted request oracle answer member hit))
        · exact ih _ _ _
      · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

/-- The weight of a flagged refill outcome: a flag weighs `1`, an abort `0`. -/
def flagWeight2 {β : Type} (h : β → ℝ≥0∞) : Option (Option β) → ℝ≥0∞
  | none => 1
  | some none => 0
  | some (some b) => h b

/-- The weight of an unflagged refill outcome: an abort weighs `1`. -/
def abortWeight {β : Type} (h : β → ℝ≥0∞) : Option β → ℝ≥0∞
  | none => 1
  | some b => h b

/-- **P4's refill runner only grows the state.** -/
theorem runRefill_grows (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell)
      (outcome : α × LState × Record),
      some outcome ∈ (runRefill bits draw computation oracle record touched).support →
        Grows oracle outcome.2.1 := by
  induction computation with
  | pure value =>
    intro oracle record touched outcome member
    simp only [runRefill, PMF.mem_support_pure_iff, Option.some.injEq] at member
    subst member
    exact Grows.refl _
  | query request next ih =>
    intro oracle record touched outcome member
    simp only [runRefill] at member
    split at member
    · exact ih _ _ _ _ _ member
    · split at member
      · rename_i cell consumed
        obtain ⟨input, rfl, _, _, _⟩ := consumeCell_spec consumed
        simp only [PMF.mem_support_bind_iff] at member
        obtain ⟨value, _, rest⟩ := member
        split at rest
        · simp at rest
        · rename_i updated success
          exact (program_hash_grows input _ oracle updated success).trans (ih _ _ _ _ _ rest)
      · simp only [PMF.mem_support_bind_iff] at member
        obtain ⟨answer, answerMember, rest⟩ := member
        exact (query_grows request oracle answer answerMember).trans (ih _ _ _ _ _ rest)

/-- **The refill runner, flagged against P4's unflagged `runRefill`.** -/
theorem runRefillFlag_le (planted : LState) (bits : BitInput) (draw : Cell → PMF (Block × Block))
    {α : Type} (F G : α × LState × Record → ℝ≥0∞) (le : ∀ o, F o ≤ G o)
    (saturated : ∀ o, Touches planted (pointsOf o.2.1) → 1 ≤ G o)
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell),
      ∑' o, runRefillFlag planted bits draw computation oracle record touched o * flagWeight2 F o
        ≤ ∑' o, runRefill bits draw computation oracle record touched o * abortWeight G o := by
  induction computation with
  | pure value =>
    intro oracle record touched
    simp only [runRefillFlag, runRefill, tsum_pure_mul, flagWeight2, abortWeight]
    exact le _
  | query request next ih =>
    intro oracle record touched
    simp only [runRefillFlag, runRefill]
    cases intercept : interceptAnswer bits request with
    | some answer => exact ih answer oracle _ touched
    | none =>
      simp only
      cases consumed : consumeCell touched oracle request with
      | some cell =>
        obtain ⟨input, rfl, _, _, _⟩ := consumeCell_spec consumed
        simp only
        rw [tsum_bind_mul, tsum_bind_mul]
        refine ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl ?_
        cases success : LazyOracle.program (.hash input) (refillAnswer (.hash input) value) oracle
          with
        | none =>
          split_ifs <;> simp [flagWeight2, abortWeight]
        | some updated =>
          simp only
          split_ifs with hit
          · rw [tsum_pure_mul]
            refine one_le_expect _ _ fun o reached => ?_
            cases o with
            | none => exact le_rfl
            | some o =>
              exact saturated o (touches_grows (runRefill_grows _ _ _ _ _ _ o reached)
                (program_hash_touch planted input _ oracle _ success hit))
          · exact ih _ _ _ _
      | none =>
        simp only
        rw [tsum_bind_mul, tsum_bind_mul]
        refine ENNReal.tsum_le_tsum fun answer => ?_
        by_cases member : answer ∈ (LazyOracle.query request oracle).support
        · refine mul_le_mul' le_rfl ?_
          split_ifs with hit
          · rw [tsum_pure_mul]
            refine one_le_expect _ _ fun o reached => ?_
            cases o with
            | none => exact le_rfl
            | some o =>
              exact saturated o (touches_grows (runRefill_grows _ _ _ _ _ _ o reached)
                (query_touch planted request oracle answer member hit))
          · exact ih _ _ _ _
        · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

end Refill

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
