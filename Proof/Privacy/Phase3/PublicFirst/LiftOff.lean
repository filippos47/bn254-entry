/-
**Phase 3, P1j — the lift, part 4: state plumbing for the per-input core.**

Generic facts about private runs and merges that the per-input core `LiftCore` needs on both sides:

* **meeting is symmetric** (`touches_symm`) and **lookup-determined** (`pointsOf_congr`,
  `untouched_congr`);
* **the merge is lookup-determined** (`fullRel_congr`, `mergeChoice_congr`): `mergeChoice` is a
  choice over the states related to the private one, and the relation reads the private state only
  through its lookups;
* **a step adds exactly its own pair** (`forward_new`, `touches_update_fixed/enc`,
  `touches_after_query`, `touches_after_program`): the converse of P1i's `query_touch`;
* **a flagged fill is its unflagged run on the untouched outcomes** (`runFillFlag_some_le`): the
  flag-down mass of `runFillFlag σ₁` is at most the unflagged run's mass times the indicator that
  the final private state does not meet `σ₁`.
-/

import Proof.Privacy.Phase3.PublicFirst.LiftTV

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Request AllQ consumeCell refillAnswer touch)
open scoped ENNReal

noncomputable section

/-! ### 1. Meeting and merging are lookup-determined -/

section Generic

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **Meeting is symmetric.** -/
theorem touches_symm (first second : LazyOracle.State FixedIndex EncIndex)
    (hit : Touches first (pointsOf second)) : Touches second (pointsOf first) := by
  rcases hit with ⟨i, x, y, found, hitIn | ⟨w, hw⟩⟩ | ⟨i, x, y, found, hitIn | ⟨w, hw⟩⟩ |
      ⟨k, v, found, hitIn⟩
  · have hitIn' : lk (second.fixed i) x ≠ none := by
      simpa [pointsOf, BitVec.toFin_ofFin] using hitIn
    obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.mp hitIn'
    refine Or.inl ⟨i, x, y', hy', Or.inl ?_⟩
    show lk (first.fixed i) (BitVec.ofFin x).toFin ≠ none
    rw [BitVec.toFin_ofFin, found]
    simp
  · refine Or.inl ⟨i, w, y, ?_, Or.inr ⟨x, ?_⟩⟩
    · simpa [BitVec.toFin_ofFin] using hw
    · rw [BitVec.toFin_ofFin]
      exact found
  · have hitIn' : lk (second.enc i) x ≠ none := by
      simpa [pointsOf, BitVec.toFin_ofFin] using hitIn
    obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.mp hitIn'
    refine Or.inr (Or.inl ⟨i, x, y', hy', Or.inl ?_⟩)
    show lk (first.enc i) (BitVec.ofFin x).toFin ≠ none
    rw [BitVec.toFin_ofFin, found]
    simp
  · refine Or.inr (Or.inl ⟨i, w, y, ?_, Or.inr ⟨x, ?_⟩⟩)
    · simpa [BitVec.toFin_ofFin] using hw
    · rw [BitVec.toFin_ofFin]
      exact found
  · have hitIn' : second.hash.lookup k ≠ none := hitIn
    obtain ⟨v', hv'⟩ := Option.ne_none_iff_exists'.mp hitIn'
    refine Or.inr (Or.inr ⟨k, v', hv', ?_⟩)
    show first.hash.lookup k ≠ none
    rw [found]
    simp

/-- **A state's points are its lookups.** -/
theorem pointsOf_congr {first second : LazyOracle.State FixedIndex EncIndex}
    (same : SameLookups first second) : pointsOf first = pointsOf second := by
  have fixedEq : ∀ i, lk (first.fixed i) = lk (second.fixed i) := fun i => funext (same.fixed i)
  have encEq : ∀ i, lk (first.enc i) = lk (second.enc i) := fun i => funext (same.enc i)
  have hashEq : ∀ k, first.hash.lookup k = second.hash.lookup k := same.hash
  unfold pointsOf
  congr 1
  · funext i x
    rw [fixedEq i]
  · funext i y
    rw [fixedEq i]
  · funext i x
    rw [encEq i]
  · funext i y
    rw [encEq i]
  · funext k
    rw [hashEq k]

theorem untouched_congr (planted : LazyOracle.State FixedIndex EncIndex)
    {first second : LazyOracle.State FixedIndex EncIndex} (same : SameLookups first second) :
    untouched planted first = untouched planted second := by
  unfold untouched
  rw [pointsOf_congr same]

theorem sparseRel_congr {size : ℕ} {sF sL sL' : SparsePermutation size}
    {D Dinv : Fin size → Option (Fin size)} (same : ∀ z, lk sL z = lk sL' z)
    (rel : SparseRel sF sL D Dinv) : SparseRel sF sL' D Dinv where
  lookup z := by rw [← same z]; exact rel.lookup z
  inverse := rel.inverse
  freshInput z planted := by rw [← same z]; exact rel.freshInput z planted
  freshOutput y planted w := by rw [← same w]; exact rel.freshOutput y planted w

/-- **The merge relation reads the private state through its lookups.** -/
theorem fullRel_congr {planted sF sL sL' : LazyOracle.State FixedIndex EncIndex}
    (same : SameLookups sL sL') (rel : FullRel planted sF sL) : FullRel planted sF sL' where
  fixed i := sparseRel_congr (fun z => same.fixed i z) (rel.fixed i)
  enc i := sparseRel_congr (fun z => same.enc i z) (rel.enc i)
  hash := ⟨fun k => by rw [rel.hash.lookup k, same.hash k],
    fun k hit => by rw [← same.hash k]; exact rel.hash.fresh k hit⟩

/-- **The merge is lookup-determined** (it is a choice over the same set of states). -/
theorem mergeChoice_congr (planted : LazyOracle.State FixedIndex EncIndex)
    {sL sL' : LazyOracle.State FixedIndex EncIndex} (same : SameLookups sL sL') :
    mergeChoice planted sL = mergeChoice planted sL' := by
  unfold mergeChoice
  congr 1
  funext merged
  exact propext ⟨fullRel_congr same, fullRel_congr same.symm⟩

/-! ### 2. A step adds exactly its own pair -/

/-- `next` is `old` with at most the pair `x ↦ y` added. -/
def AddsPair {size : ℕ} (old next : SparsePermutation size) (x y : Fin size) : Prop :=
  ∀ z w, lk next z = some w → lk old z = some w ∨ (z = x ∧ w = y)

theorem addsPair_forward {size : ℕ} (state : SparsePermutation size) (x : Fin size)
    (answer : Fin size × SparsePermutation size)
    (member : answer ∈ (state.forward x).distribution.support) :
    AddsPair state answer.2 x answer.1 := by
  intro z w found
  unfold SparsePermutation.forward at member
  dsimp only at member
  split at member
  · simp only [Draw.distribution, PMF.mem_support_pure_iff] at member
    subst member
    exact Or.inl found
  · rename_i fresh
    obtain ⟨rank, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rw [← same] at found ⊢
    dsimp only at found ⊢
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
    rw [shape] at found
    split at found
    · rename_i hz
      exact Or.inr ⟨hz, (Option.some.inj found).symm⟩
    · exact Or.inl found

theorem addsPair_program {size : ℕ} {state next : SparsePermutation size} {x y : Fin size}
    (success : LazyOracle.permutationProgram state x y = some next) : AddsPair state next x y := by
  intro z w found
  rw [lk_permutationProgram success z] at found
  split at found
  · rename_i hz
    exact Or.inr ⟨hz, (Option.some.inj found).symm⟩
  · exact Or.inl found

/-- A meeting after a fixed-key update is an old meeting or the new pair's own touch. -/
theorem touches_update_fixed (planted old : LazyOracle.State FixedIndex EncIndex) (index : FixedIndex)
    (next : SparsePermutation (2 ^ 128)) (x y : Fin (2 ^ 128)) (adds : AddsPair (old.fixed index) next x y)
    (hit : Touches planted (pointsOf { old with fixed := Function.update old.fixed index next })) :
    Touches planted (pointsOf old) ∨
      TouchForward (lk (planted.fixed index)) (lk (planted.fixed index).reverse) x y := by
  rcases hit with ⟨i, x0, y0, found, hitIn | ⟨w, hw⟩⟩ | encHit | hashHit
  · have hitIn' : lk ((Function.update old.fixed index next) i) x0 ≠ none := by
      simpa [pointsOf, BitVec.toFin_ofFin] using hitIn
    by_cases same : i = index
    · subst same
      rw [Function.update_self] at hitIn'
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hitIn'
      rcases adds x0 w hw with old' | ⟨rfl, _⟩
      · left
        refine Or.inl ⟨i, x0, y0, found, Or.inl ?_⟩
        show lk (old.fixed i) (BitVec.ofFin x0).toFin ≠ none
        rw [BitVec.toFin_ofFin, old']
        simp
      · right
        left
        rw [found]
        simp
    · left
      refine Or.inl ⟨i, x0, y0, found, Or.inl ?_⟩
      show lk (old.fixed i) (BitVec.ofFin x0).toFin ≠ none
      rw [BitVec.toFin_ofFin]
      simpa [Function.update_of_ne same] using hitIn'
  · have hw' : lk ((Function.update old.fixed index next) i) w = some y0 := by
      simpa [BitVec.toFin_ofFin] using hw
    by_cases same : i = index
    · subst same
      rw [Function.update_self] at hw'
      rcases adds w y0 hw' with old' | ⟨_, rfl⟩
      · left
        exact Or.inl ⟨i, x0, y0, found, Or.inr ⟨w, by rw [BitVec.toFin_ofFin]; exact old'⟩⟩
      · right
        right
        rw [(lookup_reverse _ x0 y0).mpr found]
        simp
    · left
      refine Or.inl ⟨i, x0, y0, found, Or.inr ⟨w, ?_⟩⟩
      rw [BitVec.toFin_ofFin]
      simpa [Function.update_of_ne same] using hw'
  · exact Or.inl (Or.inr (Or.inl encHit))
  · exact Or.inl (Or.inr (Or.inr hashHit))

/-- The same after an EncPRF update. -/
theorem touches_update_enc (planted old : LazyOracle.State FixedIndex EncIndex) (index : EncIndex)
    (next : SparsePermutation (2 ^ 128)) (x y : Fin (2 ^ 128)) (adds : AddsPair (old.enc index) next x y)
    (hit : Touches planted (pointsOf { old with enc := Function.update old.enc index next })) :
    Touches planted (pointsOf old) ∨
      TouchForward (lk (planted.enc index)) (lk (planted.enc index).reverse) x y := by
  rcases hit with fixedHit | ⟨i, x0, y0, found, hitIn | ⟨w, hw⟩⟩ | hashHit
  · exact Or.inl (Or.inl fixedHit)
  · have hitIn' : lk ((Function.update old.enc index next) i) x0 ≠ none := by
      simpa [pointsOf, BitVec.toFin_ofFin] using hitIn
    by_cases same : i = index
    · subst same
      rw [Function.update_self] at hitIn'
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hitIn'
      rcases adds x0 w hw with old' | ⟨rfl, _⟩
      · left
        refine Or.inr (Or.inl ⟨i, x0, y0, found, Or.inl ?_⟩)
        show lk (old.enc i) (BitVec.ofFin x0).toFin ≠ none
        rw [BitVec.toFin_ofFin, old']
        simp
      · right
        left
        rw [found]
        simp
    · left
      refine Or.inr (Or.inl ⟨i, x0, y0, found, Or.inl ?_⟩)
      show lk (old.enc i) (BitVec.ofFin x0).toFin ≠ none
      rw [BitVec.toFin_ofFin]
      simpa [Function.update_of_ne same] using hitIn'
  · have hw' : lk ((Function.update old.enc index next) i) w = some y0 := by
      simpa [BitVec.toFin_ofFin] using hw
    by_cases same : i = index
    · subst same
      rw [Function.update_self] at hw'
      rcases adds w y0 hw' with old' | ⟨_, rfl⟩
      · left
        exact Or.inr (Or.inl ⟨i, x0, y0, found, Or.inr ⟨w, by rw [BitVec.toFin_ofFin]; exact old'⟩⟩)
      · right
        right
        rw [(lookup_reverse _ x0 y0).mpr found]
        simp
    · left
      refine Or.inr (Or.inl ⟨i, x0, y0, found, Or.inr ⟨w, ?_⟩⟩)
      rw [BitVec.toFin_ofFin]
      simpa [Function.update_of_ne same] using hw'
  · exact Or.inl (Or.inr (Or.inr hashHit))

/-- A forward or hash question (the only kinds the programs ask). -/
def NoInverse : PublicQuery FixedIndex EncIndex → Prop
  | .fixedInverse _ _ => False
  | .encInverse _ _ => False
  | _ => True

/-- **After a lazy forward question, a meeting is an old meeting or the question's own touch.** -/
theorem touches_after_query (planted : LazyOracle.State FixedIndex EncIndex)
    (request : PublicQuery FixedIndex EncIndex) (forward : NoInverse request)
    (state : LazyOracle.State FixedIndex EncIndex)
    (outcome : request.Answer × LazyOracle.State FixedIndex EncIndex)
    (member : outcome ∈ (LazyOracle.query request state).support)
    (hit : Touches planted (pointsOf outcome.2)) :
    Touches planted (pointsOf state) ∨ FullTouch planted request outcome.1 := by
  cases request with
  | fixedForward index input =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rcases touches_update_fixed planted state index answer.2 input.toFin answer.1
        (addsPair_forward _ _ answer answerMember) hit with old | new
    · exact Or.inl old
    · right
      simpa [FullTouch, BitVec.toFin_ofFin] using new
  | fixedInverse _ _ => exact forward.elim
  | encForward index input =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rcases touches_update_enc planted state index answer.2 input.toFin answer.1
        (addsPair_forward _ _ answer answerMember) hit with old | new
    · exact Or.inl old
    · right
      simpa [FullTouch, BitVec.toFin_ofFin] using new
  | encInverse _ _ => exact forward.elim
  | hash input =>
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rcases hit with fixedHit | encHit | ⟨k, v, found, hitIn⟩
    · exact Or.inl (Or.inl fixedHit)
    · exact Or.inl (Or.inr (Or.inl encHit))
    · have hitIn' : answer.2.lookup k ≠ none := hitIn
      unfold HashTable.query at answerMember
      split at answerMember
      · simp only [Draw.distribution, PMF.mem_support_pure_iff] at answerMember
        subst answerMember
        exact Or.inl (Or.inr (Or.inr ⟨k, v, found, hitIn'⟩))
      · obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        rw [← same] at hitIn'
        by_cases hk : k = input
        · subst hk
          right
          show planted.hash.lookup k ≠ none
          rw [found]
          simp
        · have different : (k == input) = false := by simpa [beq_iff_eq] using hk
          simp only [List.lookup, different] at hitIn'
          exact Or.inl (Or.inr (Or.inr ⟨k, v, found, hitIn'⟩))

/-- **After a forward program, a meeting is an old meeting or the program's own touch.** -/
theorem touches_after_program (planted : LazyOracle.State FixedIndex EncIndex)
    (request : PublicQuery FixedIndex EncIndex) (forward : NoInverse request)
    (answer : request.Answer) (state updated : LazyOracle.State FixedIndex EncIndex)
    (success : LazyOracle.program request answer state = some updated)
    (hit : Touches planted (pointsOf updated)) :
    Touches planted (pointsOf state) ∨ FullTouch planted request answer := by
  cases request with
  | fixedForward index input =>
    simp only [LazyOracle.program, Option.map_eq_some_iff] at success
    obtain ⟨next, programmed, rfl⟩ := success
    rcases touches_update_fixed planted state index next input.toFin answer.toFin
        (addsPair_program programmed) hit with old | new
    · exact Or.inl old
    · exact Or.inr new
  | fixedInverse _ _ => exact forward.elim
  | encForward index input =>
    simp only [LazyOracle.program, Option.map_eq_some_iff] at success
    obtain ⟨next, programmed, rfl⟩ := success
    rcases touches_update_enc planted state index next input.toFin answer.toFin
        (addsPair_program programmed) hit with old | new
    · exact Or.inl old
    · exact Or.inr new
  | encInverse _ _ => exact forward.elim
  | hash input =>
    simp only [LazyOracle.program] at success
    split at success
    · rename_i fresh
      simp only [Option.some.injEq] at success
      subst success
      rcases hit with fixedHit | encHit | ⟨k, v, found, hitIn⟩
      · exact Or.inl (Or.inl fixedHit)
      · exact Or.inl (Or.inr (Or.inl encHit))
      · by_cases hk : k = input
        · subst hk
          right
          show planted.hash.lookup k ≠ none
          rw [found]
          simp
        · have different : (k == input) = false := by simpa [beq_iff_eq] using hk
          have hitIn' : state.hash.lookup k ≠ none := by
            have := hitIn
            simp only [pointsOf, HashTable.program, List.lookup, different] at this
            exact this
          exact Or.inl (Or.inr (Or.inr ⟨k, v, found, hitIn'⟩))
    · cases success

end Generic

/-! ### 3. A flagged fill is its unflagged run on the untouched outcomes -/

section Fill

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

theorem untouched_eq_one {planted state : LState} (fresh : ¬ Touches planted (pointsOf state)) :
    untouched planted state = 1 := by
  unfold untouched
  rw [if_neg fresh]

/-- Nothing meets the empty oracle. -/
theorem not_touches_empty (planted : LState) :
    ¬ Touches planted (pointsOf (LazyOracle.empty : LState)) := by
  rintro (⟨i, x, y, _, hitIn | ⟨w, hw⟩⟩ | ⟨i, x, y, _, hitIn | ⟨w, hw⟩⟩ | ⟨k, v, _, hitIn⟩)
  · exact hitIn (lk_empty _)
  · have none : lk ((LazyOracle.empty : LState).fixed i) w = none := lk_empty w
    rw [none] at hw
    cases hw
  · exact hitIn (lk_empty _)
  · have none : lk ((LazyOracle.empty : LState).enc i) w = none := lk_empty w
    rw [none] at hw
    cases hw
  · exact hitIn rfl

/-- **A flagged fill, flag-down, is at most its unflagged run on the outcomes whose final state
does not meet the flag.** -/
theorem runFillFlag_some_le (planted : LState) (draw : Cell → PMF (Block × Block)) {α : Type}
    {computation : FreeQuery Programs.Spec α} (forward : AllQ NoInverse computation) :
    ∀ (oracle : LState) (touched : Set Cell), ¬ Touches planted (pointsOf oracle) →
      ∀ outcome, runFillFlag planted draw computation oracle touched (some outcome)
        ≤ runFillFlag LazyOracle.empty draw computation oracle touched (some outcome)
          * untouched planted outcome.2 := by
  induction forward with
  | pure value =>
    intro oracle touched fresh outcome
    simp only [runFillFlag]
    by_cases same : outcome = (value, oracle)
    · subst same
      rw [untouched_eq_one fresh, mul_one]
    · rw [PMF.pure_apply, if_neg (fun h => same (Option.some.inj h)), zero_mul]
  | query request next here _ ih =>
    intro oracle touched fresh outcome
    simp only [runFillFlag]
    split
    · rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_right]
      refine ENNReal.tsum_le_tsum fun limb => ?_
      rw [mul_assoc]
      refine mul_le_mul' le_rfl ?_
      by_cases hit : FullTouch planted request (refillAnswer request limb)
      · rw [if_pos hit, PMF.pure_apply, if_neg (by simp)]
        exact zero_le
      · rw [if_neg hit, if_neg (not_fullTouch_empty _ _)]
        cases programmed : LazyOracle.program request (refillAnswer request limb) oracle with
        | none =>
          simp only [PMF.pure_apply, reduceCtorEq, if_false, zero_le]
        | some updated =>
          dsimp only
          have fresh' : ¬ Touches planted (pointsOf updated) := fun hitU =>
            (touches_after_program planted request here _ oracle updated programmed hitU).elim
              fresh hit
          exact ih _ updated _ fresh' outcome
    · rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_right]
      refine ENNReal.tsum_le_tsum fun answer => ?_
      rw [mul_assoc]
      by_cases member : answer ∈ (LazyOracle.query request oracle).support
      · refine mul_le_mul' le_rfl ?_
        by_cases hit : FullTouch planted request answer.1
        · rw [if_pos hit, PMF.pure_apply, if_neg (by simp)]
          exact zero_le
        · rw [if_neg hit, if_neg (not_fullTouch_empty _ _)]
          have fresh' : ¬ Touches planted (pointsOf answer.2) := fun hitU =>
            (touches_after_query planted request here oracle answer member hitU).elim fresh hit
          exact ih _ answer.2 _ fresh' outcome
      · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

end Fill

/-! ### 4. Planting a list on `σ₁` is planting it privately, then merging -/

section Plant

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- A touching program fails on the side that holds the planted pairs. -/
theorem sparse_touch_reject {size : ℕ} {sF sL : SparsePermutation size}
    {D Dinv : Fin size → Option (Fin size)} (rel : SparseRel sF sL D Dinv) {x y : Fin size}
    (touch : TouchForward D Dinv x y) : LazyOracle.permutationProgram sF x y = none := by
  refine LazyOracle.permutationProgram_reject sF x y ?_
  rcases touch with hitIn | hitOut
  · left
    rw [knownInput_iff, rel.lookup]
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hitIn
    rw [hw]
    simp
  · right
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp hitOut
    rw [knownOutput_iff]
    exact ⟨z, by rw [rel.lookup, (rel.inverse z y).mpr hz]; rfl⟩

/-- **An EncPRF program off a touch**: lockstep (P1e's `program_fixed_rel`, at the EncPRF
component). -/
theorem program_enc_rel {planted sF sL : LazyOracle.State FixedIndex EncIndex}
    (rel : FullRel planted sF sL) (index : EncIndex) (input answer : Block)
    (notTouch : ¬ FullTouch planted (.encForward index input) answer) :
    (∃ tF tL, LazyOracle.program (.encForward index input) answer sF = some tF ∧
        LazyOracle.program (.encForward index input) answer sL = some tL ∧
        FullRel planted tF tL) ∨
      (LazyOracle.program (.encForward index input) answer sF = none ∧
        LazyOracle.program (.encForward index input) answer sL = none) := by
  classical
  have r := rel.enc index
  simp only [FullTouch, TouchForward, not_or, not_not] at notTouch
  obtain ⟨freshD, freshDinv⟩ := notTouch
  have inputIff : (sF.enc index).knownInput input.toFin ↔ (sL.enc index).knownInput input.toFin := by
    rw [knownInput_iff, knownInput_iff, r.lookup, freshD, overlay_none]
  have outputIff : (sF.enc index).knownOutput answer.toFin ↔
      (sL.enc index).knownOutput answer.toFin := by
    constructor
    · intro known
      rcases r.knownOutput_F known with inL | planted'
      · exact inL
      · exact absurd freshDinv planted'
    · exact r.knownOutput_L
  simp only [LazyOracle.program, LazyOracle.permutationProgram]
  by_cases fresh : ¬ (sL.enc index).knownInput input.toFin ∧
      ¬ (sL.enc index).knownOutput answer.toFin
  · have freshF : ¬ (sF.enc index).knownInput input.toFin ∧
        ¬ (sF.enc index).knownOutput answer.toFin := by
      rw [inputIff, outputIff]; exact fresh
    left
    rw [dif_pos freshF, dif_pos fresh]
    refine ⟨_, _, rfl, rfl, ⟨rel.fixed, fun other => ?_, rel.hash⟩⟩
    by_cases same : other = index
    · subst same
      simp only [Function.update_self]
      exact r.extend input.toFin answer.toFin freshD fresh.1 freshF.1 fresh.2 freshF.2 freshDinv _ _
    · simpa [Function.update_of_ne same] using rel.enc other
  · have staleF : ¬ (¬ (sF.enc index).knownInput input.toFin ∧
        ¬ (sF.enc index).knownOutput answer.toFin) := by
      rw [inputIff, outputIff]; exact fresh
    right
    rw [dif_neg staleF, dif_neg fresh]
    exact ⟨rfl, rfl⟩

/-- A successful forward or hash program grows the state and stores a pair touching whatever its
request touches. -/
theorem program_grows_touch (planted : LazyOracle.State FixedIndex EncIndex)
    (request : PublicQuery FixedIndex EncIndex) (forward : NoInverse request) (answer : request.Answer)
    (state updated : LazyOracle.State FixedIndex EncIndex)
    (success : LazyOracle.program request answer state = some updated) :
    Grows state updated ∧ (FullTouch planted request answer → Touches planted (pointsOf updated)) := by
  cases request with
  | fixedForward index input =>
    exact ⟨program_state_grows index input answer state updated success,
      program_touch planted index input answer state updated success⟩
  | fixedInverse _ _ => exact forward.elim
  | encForward index input =>
    simp only [LazyOracle.program, Option.map_eq_some_iff] at success
    obtain ⟨next, programmed, rfl⟩ := success
    have shape := lk_permutationProgram programmed
    have freshX : ¬ (state.enc index).knownInput input.toFin := by
      have := (permutationProgram_isSome_iff _ _ _).mp (by rw [programmed]; rfl)
      exact this.1
    refine ⟨⟨fun _ _ _ found => found, fun i x y found => ?_, fun _ _ found => found⟩, ?_⟩
    · by_cases same : i = index
      · subst same
        simp only [Function.update_self]
        rw [shape x, if_neg]
        · exact found
        · rintro rfl
          exact freshX ((knownInput_iff _ _).mpr (by rw [found]; simp))
      · simpa [Function.update_of_ne same] using found
    · intro touch
      have stored : lk ((Function.update state.enc index next) index) input.toFin
          = some answer.toFin := by
        rw [Function.update_self, shape input.toFin, if_pos rfl]
      simp only [FullTouch, TouchForward] at touch
      rcases touch with hit | hit
      · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hit
        refine Or.inr (Or.inl ⟨index, input.toFin, y, hy, Or.inl ?_⟩)
        show lk ((Function.update state.enc index next) index) (BitVec.ofFin input.toFin).toFin ≠ none
        rw [BitVec.toFin_ofFin, stored]
        simp
      · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hit
        refine Or.inr (Or.inl ⟨index, x, answer.toFin, (lookup_reverse _ x _).mp hx,
          Or.inr ⟨input.toFin, ?_⟩⟩)
        rw [stored, BitVec.toFin_ofFin]
  | encInverse _ _ => exact forward.elim
  | hash input =>
    simp only [LazyOracle.program] at success
    split at success
    · rename_i fresh
      simp only [Option.some.injEq] at success
      subst success
      refine ⟨⟨fun _ _ _ found => found, fun _ _ _ found => found, fun k v found => ?_⟩, ?_⟩
      · have different : (k == input) = false := by
          rw [beq_eq_false_iff_ne]
          rintro rfl
          rw [fresh] at found
          cases found
        simp only [HashTable.program, List.lookup, different]
        exact found
      · intro touch
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (show planted.hash.lookup input ≠ none from touch)
        refine Or.inr (Or.inr ⟨input, v, hv, ?_⟩)
        show (HashTable.program state.hash input _).lookup input ≠ none
        simp [HashTable.program]
    · cases success

/-- **One planted entry, in lockstep**: if the private program, when it succeeds, leaves no meeting
with `planted`, planting on both sides keeps the relation. -/
theorem plantEntry_rel {planted sF sL : LazyOracle.State FixedIndex EncIndex}
    (rel : FullRel planted sF sL) (entry : Entry FixedIndex EncIndex) (forward : NoInverse entry.1)
    (clean : ∀ tL, LazyOracle.program entry.1 entry.2 sL = some tL →
      ¬ Touches planted (pointsOf tL)) :
    FullRel planted (plantEntry sF entry) (plantEntry sL entry) := by
  obtain ⟨request, answer⟩ := entry
  by_cases touch : FullTouch planted request answer
  · have failL : LazyOracle.program request answer sL = none := by
      cases programmed : LazyOracle.program request answer sL with
      | none => rfl
      | some tL =>
        exact absurd ((program_grows_touch planted request forward answer sL tL programmed).2 touch)
          (clean tL programmed)
    have failF : LazyOracle.program request answer sF = none := by
      cases request with
      | fixedForward index input =>
        simp only [LazyOracle.program, Option.map_eq_none_iff]
        exact sparse_touch_reject (rel.fixed index) touch
      | fixedInverse _ _ => exact forward.elim
      | encForward index input =>
        simp only [LazyOracle.program, Option.map_eq_none_iff]
        exact sparse_touch_reject (rel.enc index) touch
      | encInverse _ _ => exact forward.elim
      | hash input =>
        simp only [LazyOracle.program]
        rw [if_neg]
        rw [rel.hash.lookup input]
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (show planted.hash.lookup input ≠ none from touch)
        rw [hv]
        simp
    simp only [plantEntry, failL, failF, Option.getD_none]
    exact rel
  · cases request with
    | fixedForward index input =>
      rcases program_fixed_rel rel index input answer touch with
        ⟨tF, tL, successF, successL, related⟩ | ⟨failF, failL⟩
      · simp only [plantEntry, successF, successL, Option.getD_some]
        exact related
      · simp only [plantEntry, failF, failL, Option.getD_none]
        exact rel
    | fixedInverse _ _ => exact forward.elim
    | encForward index input =>
      rcases program_enc_rel rel index input answer touch with
        ⟨tF, tL, successF, successL, related⟩ | ⟨failF, failL⟩
      · simp only [plantEntry, successF, successL, Option.getD_some]
        exact related
      · simp only [plantEntry, failF, failL, Option.getD_none]
        exact rel
    | encInverse _ _ => exact forward.elim
    | hash input =>
      have notPlanted : planted.hash.lookup input = none := not_not.mp touch
      have same : sF.hash.lookup input = sL.hash.lookup input := by
        rw [rel.hash.lookup, notPlanted, overlay_none]
      simp only [plantEntry, LazyOracle.program]
      by_cases freshL : sL.hash.lookup input = none
      · rw [if_pos (same.trans freshL), if_pos freshL]
        simp only [Option.getD_some]
        refine ⟨rel.fixed, rel.enc, ?_⟩
        exact rel.hash.cons input _ notPlanted
      · rw [if_neg (fun h => freshL (same.symm.trans h)), if_neg freshL]
        simp only [Option.getD_none]
        exact rel

/-- Planting only grows the state. -/
theorem plantAll_grows (entries : List (Entry FixedIndex EncIndex))
    (forward : ∀ entry ∈ entries, NoInverse entry.1) :
    ∀ state, Grows state (plantAll entries state) := by
  induction entries with
  | nil => intro state; exact Grows.refl state
  | cons entry rest ih =>
    intro state
    have head : Grows state (plantEntry state entry) := by
      unfold plantEntry
      cases programmed : LazyOracle.program entry.1 entry.2 state with
      | none => exact Grows.refl state
      | some updated =>
        exact (program_grows_touch state entry.1 (forward entry (List.mem_cons_self ..)) entry.2
          state updated programmed).1
    exact head.trans (ih (fun e member => forward e (List.mem_cons_of_mem _ member)) _)

/-- **Planting a list on `σ₁`, in lockstep with planting it privately**, as long as the private
result does not meet `σ₁`. -/
theorem plantAll_rel (planted : LazyOracle.State FixedIndex EncIndex)
    (entries : List (Entry FixedIndex EncIndex)) (forward : ∀ entry ∈ entries, NoInverse entry.1) :
    ∀ sF sL, FullRel planted sF sL → ¬ Touches planted (pointsOf (plantAll entries sL)) →
      FullRel planted (plantAll entries sF) (plantAll entries sL) := by
  induction entries with
  | nil => intro sF sL rel _; exact rel
  | cons entry rest ih =>
    intro sF sL rel clean
    have forwardRest : ∀ e ∈ rest, NoInverse e.1 := fun e member =>
      forward e (List.mem_cons_of_mem _ member)
    refine ih forwardRest _ _ (plantEntry_rel rel entry (forward entry (List.mem_cons_self ..))
      fun tL programmed hit => clean ?_) clean
    have grow := plantAll_grows rest forwardRest (plantEntry sL entry)
    have same : plantEntry sL entry = tL := by
      unfold plantEntry
      rw [programmed, Option.getD_some]
    rw [same] at grow
    rw [plantAll_cons, same]
    exact touches_grows grow hit

end Plant

/-! ### 5. The per-input core off the curve, from the off-curve law -/

section Core

open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source)
open Kriterion.ArgoMAC.Phase3.Lazy (uniformMaskTape EncAt LaneAt evalLaneM_allQ)

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
  [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A lane's questions are forward fixed-key or hash questions. -/
theorem noInverse_of_laneAt (lane : Lane) (request : Request) (inside : ∃ c, LaneAt lane c request) :
    NoInverse request := by
  obtain ⟨_, inside⟩ := inside
  cases request with
  | fixedForward _ _ => trivial
  | fixedInverse _ _ => rcases inside with fixedAt | hashIn <;> contradiction
  | encForward _ _ => trivial
  | encInverse _ _ => rcases inside with fixedAt | hashIn <;> contradiction
  | hash _ => trivial

theorem noInverse_of_enc (request : Request) (inside : EncAt request) : NoInverse request := by
  cases request with
  | fixedForward _ _ => trivial
  | fixedInverse _ _ => exact inside.elim
  | encForward _ _ => trivial
  | encInverse _ _ => exact inside.elim
  | hash _ => trivial

/-- The designed off-curve questions are forward. -/
theorem designedOffM_noInverse (table : Public) (bits : BitInput) (mac : InputMac)
    (first : Block) : AllQ NoInverse (designedOffM table bits mac first) := by
  unfold designedOffM systemAM
  refine ((padsM_allQ _).mono noInverse_of_enc).bind fun _ => ?_
  refine ((evalLaneM_allQ _ _ _ _ _).mono (noInverse_of_laneAt .curveX)).bind fun _ => ?_
  exact ((evalLaneM_allQ _ _ _ _ _).mono (noInverse_of_laneAt .curveY)).bind fun _ => .pure _

theorem designedShadow_offCurve (scalar : NonZeroScalar) (source : Stage1Source)
    (input : AffineInput) (coin : (designedShadow scalar).Coin) :
    (designedShadow scalar).offCurve source input coin =
      designedOffM source.publicValue (Lamport.restore input (sourceLabels source input)).input
        (Lamport.restore input (sourceLabels source input)).inputMac coin.2 := rfl

/-- **The designed shadow's private state off the curve, unflagged**: its coin, the mask tape, and
the fill of the pads and system A from the empty oracle. -/
def offPrivate (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput) :
    PMF (Option (Unit × LState)) :=
  (designedShadow scalar).law.bind fun coin =>
    uniformMaskTape.bind fun tape =>
      runFillFlag LazyOracle.empty (fun cell => PMF.pure (tape cell))
        ((designedShadow scalar).offCurve source input coin) LazyOracle.empty ∅

/-- The upper game's entries at an input: the EncPRF entries, then the designed ones. -/
def upperEntries (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) : List (Entry FixedIndex EncPRF.PermutationIndex) :=
  encEntries scalar tape ++ designedInstall scalar tape (Scheme.scheme.garble parameter scalar tape).1
    input (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)

/-- **The off-curve law** — the content of the lift off the curve: jointly with the published
value and the labels, the designed shadow's private state is dominated in law (for every
lookup-invariant weight) by the lookups of the garbler's EncPRF and designed entries planted on the
empty oracle (they are equal: `lawOff`, in `LawsOff.lean`, proves the `≤` from an equality
chain). -/
def LawOff (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) : Prop :=
  ∀ Ψ : Public → LamportSignature → LState → ℝ≥0∞,
    (∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second) →
    ∑' source, PMF.uniformOfFintype Stage1Source source *
        ∑' r, offPrivate scalar source input r *
          (match r with
            | none => 0
            | some x => Ψ source.publicValue (sourceLabels source input) x.2)
      ≤ ∑' tape, swappedChallengeTape tape *
          Ψ (Scheme.scheme.garble parameter scalar tape).1
            (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)
            (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty)

/-- The flag-down weight of an unflagged off-curve outcome: untouched, then the adversary. -/
def offWeight (planted : LState) {budget : ℕ}
    (decide : OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (b : Bool) : Option (Unit × LState) → ℝ≥0∞
  | none => 0
  | some x => untouched planted x.2 * ((LazyOracle.run (decide) (mergeChoice planted x.2)).map
      Prod.fst) b

/-- **`M'` off the curve, flag-down, is at most the unflagged private run's untouched outcomes.** -/
theorem middleWeight_off_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (off : Scheme.scheme.function scalar input = none) (planted : LState) {budget : ℕ}
    (decide : Public → LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (b : Bool) :
    middleWeight uniformMaskTape (designedShadow scalar) scalar source input planted decide b ≤
      ∑' r, offPrivate scalar source input r *
        offWeight planted (decide source.publicValue (sourceLabels source input)) b r := by
  unfold middleWeight offPrivate
  rw [off]
  simp only [middleStage2Fill]
  rw [tsum_bind_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun coin => mul_le_mul' le_rfl ?_
  rw [tsum_bind_mul, tsum_bind_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
  refine ENNReal.tsum_le_tsum fun r => ?_
  rcases r with _ | x
  · simp only [tsum_pure_mul, contM, mul_zero, zero_le]
  · have forward : AllQ NoInverse ((designedShadow scalar).offCurve source input coin) := by
      rw [designedShadow_offCurve]
      exact designedOffM_noInverse _ _ _ _
    have step := runFillFlag_some_le planted (fun cell => PMF.pure (tape cell)) forward
      LazyOracle.empty ∅ (not_touches_empty planted) x
    have reveal : ¬ (designedShadow scalar).revealOff source input coin x.2 := fun h => h
    simp only [reveal, if_false, tsum_pure_mul, contM, contHW, offWeight]
    rw [← mul_assoc]
    exact mul_le_mul' step le_rfl

/-- The garbler's entries are forward or hash questions. -/
theorem upperEntries_noInverse (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) : ∀ entry ∈ upperEntries parameter scalar tape input, NoInverse entry.1 := by
  intro entry member
  have inTranscript : entry ∈ garblerTranscript scalar tape := by
    rcases List.mem_append.mp member with enc | designed
    · exact (List.mem_filter.mp enc).1
    · exact (List.mem_filter.mp designed).1
  have good := garblerTranscript_good scalar tape entry inTranscript
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward _ _ => trivial
  | fixedInverse _ _ => exact good.elim
  | encForward _ _ => trivial
  | encInverse _ _ => exact good.elim
  | hash _ => trivial

/-- **The upper game's stage 2 is above the planted-then-merged entries** (pointwise). -/
theorem upper_ge_planted (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (planted : LState) {budget : ℕ}
    (decide : Public → LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (b : Bool) :
    untouched planted (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) *
        ((LazyOracle.run (decide (Scheme.scheme.garble parameter scalar tape).1
            (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input))
          (mergeChoice planted
            (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty))).map Prod.fst) b
      ≤ upperWeight designedInstall parameter scalar tape input planted decide b := by
  set entries := upperEntries parameter scalar tape input with entriesEq
  by_cases hit : Touches planted (pointsOf (plantAll entries LazyOracle.empty))
  · unfold untouched
    rw [if_pos hit, zero_mul]
    exact zero_le
  · rw [untouched_eq_one hit, one_mul]
    unfold upperWeight
    have split : ∀ state, plantAll entries state = installAll (designedInstall scalar tape
        (Scheme.scheme.garble parameter scalar tape).1 input
        (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input))
          (plantAll (encEntries scalar tape) state) := by
      intro state
      rw [entriesEq]
      unfold upperEntries plantAll
      rw [List.foldl_append]
      rfl
    have encFresh : untouched (plantAll (encEntries scalar tape) LazyOracle.empty) planted = 1 := by
      refine untouched_eq_one fun encHit => hit ?_
      have grow : Grows (plantAll (encEntries scalar tape) LazyOracle.empty)
          (plantAll entries LazyOracle.empty) := by
        rw [split]
        exact plantAll_grows _ (fun e member => upperEntries_noInverse parameter scalar tape input e
          (List.mem_append_right _ member)) _
      exact touches_grows grow (touches_symm _ _ encHit)
    rw [encFresh, one_mul]
    have rel := plantAll_rel planted entries (upperEntries_noInverse parameter scalar tape input)
      planted LazyOracle.empty (fullRel_base planted) hit
    have same : SameLookups (mergeChoice planted (plantAll entries LazyOracle.empty))
        (installAll (designedInstall scalar tape (Scheme.scheme.garble parameter scalar tape).1 input
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input))
          (plantAll (encEntries scalar tape) planted)) := by
      rw [← split planted]
      exact mergeChoice_sameLookups rel
    exact le_of_eq (run_map_fst_congr _ same ▸ rfl)

/-- **The per-input core off the curve, from the off-curve law.** -/
theorem liftCore_off (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (off : Scheme.scheme.function scalar input = none) (law : LawOff parameter scalar input)
    (planted : LState) (budget : ℕ)
    (decide : Public → LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (weight : Public → ℝ≥0∞) (b : Bool) :
    ∑' source, PMF.uniformOfFintype Stage1Source source *
        (weight source.publicValue *
          middleWeight uniformMaskTape (designedShadow scalar) scalar source input planted decide b)
      ≤ ∑' tape, swappedChallengeTape tape *
        (weight (Scheme.scheme.garble parameter scalar tape).1 *
          upperWeight designedInstall parameter scalar tape input planted decide b) := by
  let Ψ : Public → LamportSignature → LState → ℝ≥0∞ := fun table labels state =>
    weight table * (untouched planted state *
      ((LazyOracle.run (decide table labels) (mergeChoice planted state)).map Prod.fst) b)
  have invariant : ∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second := by
    intro table labels first second same
    simp only [Ψ, untouched_congr planted same, mergeChoice_congr planted same]
  calc ∑' source, PMF.uniformOfFintype Stage1Source source *
        (weight source.publicValue *
          middleWeight uniformMaskTape (designedShadow scalar) scalar source input planted decide b)
      ≤ ∑' source, PMF.uniformOfFintype Stage1Source source *
          ∑' r, offPrivate scalar source input r *
            (match r with
              | none => 0
              | some x => Ψ source.publicValue (sourceLabels source input) x.2) := by
        refine ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl ?_
        refine le_trans (mul_le_mul' le_rfl
          (middleWeight_off_le scalar source input off planted decide b)) (le_of_eq ?_)
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun r => ?_
        rcases r with _ | x
        · simp [offWeight]
        · simp only [offWeight, Ψ]
          ring
    _ ≤ ∑' tape, swappedChallengeTape tape *
          Ψ (Scheme.scheme.garble parameter scalar tape).1
            (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)
            (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) :=
        law Ψ invariant
    _ ≤ _ := by
        refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
        exact mul_le_mul' le_rfl (upper_ge_planted parameter scalar tape input planted decide b)

end Core

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
