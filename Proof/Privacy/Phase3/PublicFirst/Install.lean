/-
**Phase 3, P1d — installing entries, through lookups.**

`plantEntry`/`plantAll` are `Hybrids.installEntry`/`installAll` at any index types (they agree
definitionally at Plan B's, `installAll_eq`): program an entry, and skip it if the program fails.

* `sameLookups_of_forward` — the forward lookups (and hash lookups) determine all lookups;
* `plantEntry_congr` / `plantAll_congr` — installation respects `SameLookups`: whether a program
  succeeds, and what it adds, is read off the lookups;
* `plantAll_enc_overlay` — **installing EncPRF entries on a state `s` overlays, at the lookup level,
  what the same entries install on the empty state**, provided those pairs are fresh in `s`;
* `encRel_sameLookups` — hence on `EncRel (plantAll E empty) sF sL` the state planted first and the
  state planted later have the same lookups: `SameLookups sF (plantAll E sL)`.
-/

import Proof.Privacy.Phase3.PublicFirst.Plant
import Proof.Privacy.Phase3.Hybrids

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open Cryptography GarbledCircuit
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- Program one entry; skip it if the program fails. -/
def plantEntry (state : LazyOracle.State FixedIndex EncIndex)
    (entry : Entry FixedIndex EncIndex) : LazyOracle.State FixedIndex EncIndex :=
  (LazyOracle.program entry.1 entry.2 state).getD state

/-- Program a list of entries in order. -/
def plantAll (entries : List (Entry FixedIndex EncIndex))
    (state : LazyOracle.State FixedIndex EncIndex) : LazyOracle.State FixedIndex EncIndex :=
  entries.foldl plantEntry state

theorem installAll_eq (entries : List (Entry Kriterion.ArgoMAC.PlanB.FixedIndex
    EncPRF.PermutationIndex)) (state) :
    installAll entries state = plantAll entries state := rfl

@[simp] theorem plantAll_nil (state : LazyOracle.State FixedIndex EncIndex) :
    plantAll [] state = state := rfl

@[simp] theorem plantAll_cons (entry : Entry FixedIndex EncIndex) (rest)
    (state : LazyOracle.State FixedIndex EncIndex) :
    plantAll (entry :: rest) state = plantAll rest (plantEntry state entry) := rfl

/-! ### Lookups of one sparse permutation -/

variable {size : ℕ}

theorem lk_reverse_congr {first second : SparsePermutation size}
    (same : ∀ x, lk first x = lk second x) (y : Fin size) :
    lk first.reverse y = lk second.reverse y := by
  apply Option.ext
  intro x
  rw [lookup_reverse, lookup_reverse, same]

theorem knownInput_congr {first second : SparsePermutation size}
    (same : ∀ x, lk first x = lk second x) (x : Fin size) :
    first.knownInput x ↔ second.knownInput x := by
  rw [knownInput_iff, knownInput_iff, same]

theorem knownOutput_congr {first second : SparsePermutation size}
    (same : ∀ x, lk first x = lk second x) (y : Fin size) :
    first.knownOutput y ↔ second.knownOutput y := by
  rw [knownOutput_iff, knownOutput_iff]
  simp only [same]

/-- A permutation program, at the lookup level. -/
theorem lk_permutationProgram {state next : SparsePermutation size} {x y : Fin size}
    (success : LazyOracle.permutationProgram state x y = some next) (z : Fin size) :
    lk next z = if z = x then some y else lk state z := by
  unfold LazyOracle.permutationProgram at success
  split at success
  · rename_i fresh
    cases success
    exact lookup_extend state x y fresh.1 fresh.2 _ z
  · cases success

theorem permutationProgram_isSome_iff (state : SparsePermutation size) (x y : Fin size) :
    (LazyOracle.permutationProgram state x y).isSome ↔
      ¬ state.knownInput x ∧ ¬ state.knownOutput y := by
  unfold LazyOracle.permutationProgram
  split
  · rename_i fresh
    simp [fresh]
  · rename_i stale
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact stale

/-- Two sparse permutations with the same lookups take a program alike. -/
theorem permutationProgram_congr {first second : SparsePermutation size}
    (same : ∀ z, lk first z = lk second z) (x y : Fin size) :
    (∃ nf ns, LazyOracle.permutationProgram first x y = some nf ∧
        LazyOracle.permutationProgram second x y = some ns ∧ ∀ z, lk nf z = lk ns z) ∨
      (LazyOracle.permutationProgram first x y = none ∧
        LazyOracle.permutationProgram second x y = none) := by
  have iff : (LazyOracle.permutationProgram first x y).isSome ↔
      (LazyOracle.permutationProgram second x y).isSome := by
    rw [permutationProgram_isSome_iff, permutationProgram_isSome_iff, knownInput_congr same,
      knownOutput_congr same]
  cases hf : LazyOracle.permutationProgram first x y with
  | none =>
    right
    refine ⟨rfl, ?_⟩
    rw [hf] at iff
    cases hs : LazyOracle.permutationProgram second x y with
    | none => rfl
    | some _ => rw [hs] at iff; simp at iff
  | some nf =>
    left
    rw [hf] at iff
    cases hs : LazyOracle.permutationProgram second x y with
    | none => rw [hs] at iff; simp at iff
    | some ns =>
      refine ⟨nf, ns, rfl, rfl, fun z => ?_⟩
      rw [lk_permutationProgram hf, lk_permutationProgram hs, same]

/-! ### Whole states -/

omit [DecidableEq FixedIndex] [DecidableEq EncIndex] in
theorem lk_empty (z : Fin (2 ^ 128)) : lk (SparsePermutation.empty (2 ^ 128)) z = none := by
  rw [lk_eq, if_neg]
  show ¬ _ < 0
  omega

/-- **The forward lookups determine all lookups.** -/
theorem sameLookups_of_forward {s t : LazyOracle.State FixedIndex EncIndex}
    (fixed : ∀ i z, lk (s.fixed i) z = lk (t.fixed i) z)
    (enc : ∀ i z, lk (s.enc i) z = lk (t.enc i) z)
    (hash : ∀ k, s.hash.lookup k = t.hash.lookup k) : SameLookups s t := by
  intro request
  cases request with
  | fixedForward index input =>
    exact congrArg (Option.map BitVec.ofFin) (fixed index input.toFin)
  | fixedInverse index output =>
    exact congrArg (Option.map BitVec.ofFin) (lk_reverse_congr (fixed index) output.toFin)
  | encForward index input =>
    exact congrArg (Option.map BitVec.ofFin) (enc index input.toFin)
  | encInverse index output =>
    exact congrArg (Option.map BitVec.ofFin) (lk_reverse_congr (enc index) output.toFin)
  | hash input =>
    exact congrArg (Option.map _) (hash input)

theorem sameLookups_update_fixed {s t : LazyOracle.State FixedIndex EncIndex}
    (same : SameLookups s t) (index : FixedIndex) (nf ns : SparsePermutation (2 ^ 128))
    (sameNew : ∀ z, lk nf z = lk ns z) :
    SameLookups { s with fixed := Function.update s.fixed index nf }
      { t with fixed := Function.update t.fixed index ns } := by
  refine sameLookups_of_forward (fun i z => ?_) (fun i z => same.enc i z) (fun k => same.hash k)
  by_cases at_ : i = index
  · subst at_; simp [sameNew]
  · simp [Function.update_of_ne at_, same.fixed i z]

theorem sameLookups_update_enc {s t : LazyOracle.State FixedIndex EncIndex}
    (same : SameLookups s t) (index : EncIndex) (nf ns : SparsePermutation (2 ^ 128))
    (sameNew : ∀ z, lk nf z = lk ns z) :
    SameLookups { s with enc := Function.update s.enc index nf }
      { t with enc := Function.update t.enc index ns } := by
  refine sameLookups_of_forward (fun i z => same.fixed i z) (fun i z => ?_) (fun k => same.hash k)
  by_cases at_ : i = index
  · subst at_; simp [sameNew]
  · simp [Function.update_of_ne at_, same.enc i z]

/-- **Installation respects `SameLookups`.** -/
theorem plantEntry_congr {s t : LazyOracle.State FixedIndex EncIndex} (same : SameLookups s t)
    (entry : Entry FixedIndex EncIndex) : SameLookups (plantEntry s entry) (plantEntry t entry) := by
  obtain ⟨request, answer⟩ := entry
  unfold plantEntry
  cases request with
  | fixedForward index input =>
    simp only [LazyOracle.program]
    rcases permutationProgram_congr (same.fixed index) input.toFin answer.toFin with
      ⟨nf, ns, hf, hs, sameNew⟩ | ⟨hf, hs⟩
    · rw [hf, hs]; exact sameLookups_update_fixed same index nf ns sameNew
    · rw [hf, hs]; exact same
  | fixedInverse index output =>
    simp only [LazyOracle.program]
    rcases permutationProgram_congr (same.fixed index) answer.toFin output.toFin with
      ⟨nf, ns, hf, hs, sameNew⟩ | ⟨hf, hs⟩
    · rw [hf, hs]; exact sameLookups_update_fixed same index nf ns sameNew
    · rw [hf, hs]; exact same
  | encForward index input =>
    simp only [LazyOracle.program]
    rcases permutationProgram_congr (same.enc index) input.toFin answer.toFin with
      ⟨nf, ns, hf, hs, sameNew⟩ | ⟨hf, hs⟩
    · rw [hf, hs]; exact sameLookups_update_enc same index nf ns sameNew
    · rw [hf, hs]; exact same
  | encInverse index output =>
    simp only [LazyOracle.program]
    rcases permutationProgram_congr (same.enc index) answer.toFin output.toFin with
      ⟨nf, ns, hf, hs, sameNew⟩ | ⟨hf, hs⟩
    · rw [hf, hs]; exact sameLookups_update_enc same index nf ns sameNew
    · rw [hf, hs]; exact same
  | hash input =>
    simp only [LazyOracle.program]
    rw [same.hash input]
    split
    · refine sameLookups_of_forward (fun i z => same.fixed i z) (fun i z => same.enc i z)
        (fun k => ?_)
      simp only [Option.getD_some]
      rw [HashTable.program_lookup, HashTable.program_lookup]
      simp only [Function.update_apply, same.hash k]
    · exact same

theorem plantAll_congr (entries : List (Entry FixedIndex EncIndex)) :
    ∀ {s t : LazyOracle.State FixedIndex EncIndex}, SameLookups s t →
      SameLookups (plantAll entries s) (plantAll entries t) := by
  induction entries with
  | nil => intro s t same; exact same
  | cons entry rest ih => intro s t same; exact ih (plantEntry_congr same entry)

/-! ### EncPRF entries: planting later overlays planting on the empty state -/

/-- The pair an EncPRF entry programs (`none` for other kinds). -/
def encPair : Entry FixedIndex EncIndex → Option (EncIndex × Block × Block)
  | ⟨.encForward index input, answer⟩ => some (index, input, answer)
  | ⟨.encInverse index output, answer⟩ => some (index, answer, output)
  | _ => none

/-- The state components an EncPRF entry changes. -/
theorem plantEntry_enc (state : LazyOracle.State FixedIndex EncIndex)
    (entry : Entry FixedIndex EncIndex) (index : EncIndex) (x y : Block)
    (pair : encPair entry = some (index, x, y)) :
    plantEntry state entry = (match LazyOracle.permutationProgram (state.enc index) x.toFin y.toFin with
      | some next => { state with enc := Function.update state.enc index next }
      | none => state) := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | encForward index' input =>
    simp only [encPair, Option.some.injEq, Prod.mk.injEq] at pair
    obtain ⟨rfl, rfl, rfl⟩ := pair
    unfold plantEntry
    simp only [LazyOracle.program]
    generalize LazyOracle.permutationProgram (state.enc index') x.toFin y.toFin = result
    cases result <;> rfl
  | encInverse index' output =>
    simp only [encPair, Option.some.injEq, Prod.mk.injEq] at pair
    obtain ⟨rfl, rfl, rfl⟩ := pair
    unfold plantEntry
    simp only [LazyOracle.program]
    generalize LazyOracle.permutationProgram (state.enc index') x.toFin y.toFin = result
    cases result <;> rfl
  | fixedForward _ _ => simp [encPair] at pair
  | fixedInverse _ _ => simp [encPair] at pair
  | hash _ => simp [encPair] at pair

/-- Installation never forgets a pair. -/
theorem plantAll_enc_mono (entries : List (Entry FixedIndex EncIndex))
    (encOnly : ∀ entry ∈ entries, (encPair entry).isSome) :
    ∀ (state : LazyOracle.State FixedIndex EncIndex) index z w,
      lk (state.enc index) z = some w → lk ((plantAll entries state).enc index) z = some w := by
  induction entries with
  | nil => intro state index z w found; exact found
  | cons entry rest ih =>
    intro state index z w found
    refine ih (fun e member => encOnly e (List.mem_cons_of_mem _ member)) _ index z w ?_
    obtain ⟨⟨j, x, y⟩, pair⟩ := Option.isSome_iff_exists.mp (encOnly entry List.mem_cons_self)
    rw [plantEntry_enc state entry j x y pair]
    split
    · rename_i next program
      by_cases same : index = j
      · subst same
        simp only [Function.update_self]
        rw [lk_permutationProgram program]
        have different : z ≠ x.toFin := by
          intro equal
          have fresh := (permutationProgram_isSome_iff _ _ _).mp (by rw [program]; rfl)
          exact fresh.1 ((knownInput_iff _ _).mpr (by rw [← equal, found]; simp))
        rw [if_neg different, found]
      · simp only [Function.update_of_ne same]
        exact found
    · exact found

/-- The lockstep invariant: `S` is the base `s` with `P`'s EncPRF pairs overlaid. -/
structure Overlaid (s P S : LazyOracle.State FixedIndex EncIndex) : Prop where
  fixed : S.fixed = s.fixed
  hash : S.hash = s.hash
  enc : ∀ index z, lk (S.enc index) z = overlay (lk (P.enc index) z) (lk (s.enc index) z)

/-- The pairs of `P` are fresh in `s`. -/
def FreshIn (s P : LazyOracle.State FixedIndex EncIndex) : Prop :=
  ∀ index z w, lk (P.enc index) z = some w →
    lk (s.enc index) z = none ∧ ∀ v, lk (s.enc index) v ≠ some w

/-- **Lockstep installation.** -/
theorem plantAll_overlaid (s : LazyOracle.State FixedIndex EncIndex)
    (entries : List (Entry FixedIndex EncIndex))
    (encOnly : ∀ entry ∈ entries, (encPair entry).isSome) :
    ∀ P S, Overlaid s P S → FreshIn s (plantAll entries P) →
      Overlaid s (plantAll entries P) (plantAll entries S) := by
  induction entries with
  | nil => intro P S inv _; exact inv
  | cons entry rest ih =>
    intro P S inv fresh
    have restOnly : ∀ e ∈ rest, (encPair e).isSome :=
      fun e member => encOnly e (List.mem_cons_of_mem _ member)
    refine ih restOnly _ _ ?_ fresh
    obtain ⟨⟨j, x, y⟩, pair⟩ := Option.isSome_iff_exists.mp (encOnly entry List.mem_cons_self)
    rw [plantEntry_enc P entry j x y pair, plantEntry_enc S entry j x y pair]
    cases hP : LazyOracle.permutationProgram (P.enc j) x.toFin y.toFin with
    | some nextP =>
      dsimp only
      -- the pair is in the final planted state, hence fresh in `s`
      have inFinal : lk ((plantAll rest { P with enc := Function.update P.enc j nextP }).enc j)
          x.toFin = some y.toFin := by
        refine plantAll_enc_mono rest restOnly _ j _ _ ?_
        simp only [Function.update_self]
        rw [lk_permutationProgram hP, if_pos rfl]
      have freshP := (permutationProgram_isSome_iff _ _ _).mp (by rw [hP]; rfl)
      have freshS : ¬ (S.enc j).knownInput x.toFin ∧ ¬ (S.enc j).knownOutput y.toFin := by
        have inFinal' : lk ((plantAll (entry :: rest) P).enc j) x.toFin = some y.toFin := by
          rw [plantAll_cons, plantEntry_enc P entry j x y pair, hP]
          exact inFinal
        obtain ⟨sNone, sOut⟩ := fresh j _ _ inFinal'
        constructor
        · rw [knownInput_iff, inv.enc, sNone]
          have : lk (P.enc j) x.toFin = none := by
            by_contra known
            exact freshP.1 ((knownInput_iff _ _).mpr known)
          rw [this]
          simp
        · rw [knownOutput_iff]
          rintro ⟨v, found⟩
          rw [inv.enc] at found
          cases hv : lk (P.enc j) v with
          | some w =>
            rw [hv, overlay_some] at found
            cases found
            exact freshP.2 ((knownOutput_iff _ _).mpr ⟨v, hv⟩)
          | none =>
            rw [hv, overlay_none] at found
            exact sOut v found
      have hS : (LazyOracle.permutationProgram (S.enc j) x.toFin y.toFin).isSome :=
        (permutationProgram_isSome_iff _ _ _).mpr freshS
      obtain ⟨nextS, hS'⟩ := Option.isSome_iff_exists.mp hS
      simp only [hS']
      refine ⟨inv.fixed, inv.hash, fun index z => ?_⟩
      by_cases same : index = j
      · subst same
        simp only [Function.update_self]
        rw [lk_permutationProgram hS', lk_permutationProgram hP, inv.enc]
        by_cases at_ : z = x.toFin
        · rw [if_pos at_, if_pos at_, overlay_some]
        · rw [if_neg at_, if_neg at_]
      · simp only [Function.update_of_ne same]
        exact inv.enc index z
    | none =>
      dsimp only
      have staleP := hP
      have staleS : LazyOracle.permutationProgram (S.enc j) x.toFin y.toFin = none := by
        have notFresh : ¬ (¬ (P.enc j).knownInput x.toFin ∧ ¬ (P.enc j).knownOutput y.toFin) := by
          intro freshP
          have := (permutationProgram_isSome_iff _ _ _).mpr freshP
          rw [hP] at this
          cases this
        cases hS : LazyOracle.permutationProgram (S.enc j) x.toFin y.toFin with
        | none => rfl
        | some nextS =>
          exfalso
          have freshS := (permutationProgram_isSome_iff _ _ _).mp (by rw [hS]; rfl)
          apply notFresh
          constructor
          · intro known
            apply freshS.1
            rw [knownInput_iff, inv.enc]
            obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp ((knownInput_iff _ _).mp known)
            rw [hw, overlay_some]
            simp
          · intro known
            apply freshS.2
            obtain ⟨v, hv⟩ := (knownOutput_iff _ _).mp known
            exact (knownOutput_iff _ _).mpr ⟨v, by rw [inv.enc, hv, overlay_some]⟩
      simp only [staleS]
      exact inv

theorem empty_enc_lk (index : EncIndex) (z : Fin (2 ^ 128)) :
    lk ((LazyOracle.empty : LazyOracle.State FixedIndex EncIndex).enc index) z = none :=
  lk_empty z

/-- **The planted state's relation to the empty one**, for EncPRF entries. -/
theorem encRel_base (entries : List (Entry FixedIndex EncIndex))
    (encOnly : ∀ entry ∈ entries, (encPair entry).isSome) :
    EncRel (plantAll entries LazyOracle.empty) (plantAll entries LazyOracle.empty)
      LazyOracle.empty := by
  have inv := plantAll_overlaid (LazyOracle.empty : LazyOracle.State FixedIndex EncIndex) entries
    encOnly LazyOracle.empty LazyOracle.empty
    ⟨rfl, rfl, fun index z => by rw [empty_enc_lk, overlay_none]⟩
    (fun index z w _ => ⟨empty_enc_lk index z, fun v => by rw [empty_enc_lk]; simp⟩)
  refine ⟨inv.fixed, inv.hash, fun index => ⟨fun z => ?_, fun z y => ?_, fun z _ => ?_,
    fun y _ w => ?_⟩⟩
  · rw [empty_enc_lk]
    cases lk ((plantAll entries LazyOracle.empty).enc index) z <;> rfl
  · exact (lookup_reverse _ z y).symm
  · exact empty_enc_lk index z
  · rw [empty_enc_lk]; simp

/-- **Planted first and planted later have the same lookups.** -/
theorem encRel_sameLookups (entries : List (Entry FixedIndex EncIndex))
    (encOnly : ∀ entry ∈ entries, (encPair entry).isSome)
    {sF sL : LazyOracle.State FixedIndex EncIndex}
    (rel : EncRel (plantAll entries LazyOracle.empty) sF sL) :
    SameLookups sF (plantAll entries sL) := by
  have inv := plantAll_overlaid sL entries encOnly LazyOracle.empty sL
    ⟨rfl, rfl, fun index z => by rw [empty_enc_lk, overlay_none]⟩
    (fun index z w found => ⟨(rel.enc index).freshInput z (by rw [found]; simp),
      fun v => (rel.enc index).freshOutput w
        (by rw [(lookup_reverse _ z w).mpr found]; simp) v⟩)
  refine sameLookups_of_forward (fun i z => ?_) (fun i z => ?_) (fun k => ?_)
  · rw [rel.fixed, ← inv.fixed]
  · rw [(rel.enc i).lookup, inv.enc]
  · rw [rel.hash, ← inv.hash]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
