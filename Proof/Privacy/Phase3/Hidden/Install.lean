/-
**Phase 3, P1c — planting a transcript into the lazy oracle.**

`plant` / `plantAll` are `Hybrids.installEntry` / `Hybrids.installAll` (a failed program is
skipped), stated for any index types. For an entry list that is **consistent with one eager oracle
`O`** (every answer is `O`'s, as in a transcript), planted into a state that either already stores
each pair or has it fresh (`Compat`):

* `plantAll_look`, `plantAll_encLook`, `plantAll_hashLookup`: the planted state stores exactly the
  old pairs and the list's pairs (hash values in the library's stored form `codeOf`);
* `plantAll_transfer`: if `s₁` is `s₂` with extra entries `H`, and every listed entry is stored in
  `s₁`, then `s₁` is `plantAll L s₂` with the extra entries `H` minus the list (`dropAll`).
-/

import Proof.Privacy.Phase3.Hidden.Relation

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open Kriterion.Cryptography
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- Plant one entry (a failed program is skipped). -/
def plant (s : LState FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex) :
    LState FixedIndex EncIndex :=
  (LazyOracle.program entry.1 entry.2 s).getD s

/-- Plant a list of entries, in order. -/
def plantAll (entries : List (Asked FixedIndex EncIndex)) (s : LState FixedIndex EncIndex) :
    LState FixedIndex EncIndex :=
  entries.foldl plant s

theorem plantAll_nil (s : LState FixedIndex EncIndex) : plantAll [] s = s := rfl

theorem plantAll_cons (entry : Asked FixedIndex EncIndex) (entries : List (Asked FixedIndex EncIndex))
    (s : LState FixedIndex EncIndex) : plantAll (entry :: entries) s = plantAll entries (plant s entry) :=
  rfl

/-! ### The pair an entry stores -/

/-- The fixed-key pair of an entry. -/
def fixedPair : Asked FixedIndex EncIndex → Option (FixedIndex × Fin (2 ^ 128) × Fin (2 ^ 128))
  | ⟨.fixedForward index input, answer⟩ => some (index, input.toFin, BitVec.toFin (w := 128) answer)
  | ⟨.fixedInverse index output, answer⟩ =>
      some (index, BitVec.toFin (w := 128) answer, output.toFin)
  | _ => none

/-- The EncPRF pair of an entry. -/
def encPair : Asked FixedIndex EncIndex → Option (EncIndex × Fin (2 ^ 128) × Fin (2 ^ 128))
  | ⟨.encForward index input, answer⟩ => some (index, input.toFin, BitVec.toFin (w := 128) answer)
  | ⟨.encInverse index output, answer⟩ =>
      some (index, BitVec.toFin (w := 128) answer, output.toFin)
  | _ => none

/-- The hash key and value of an entry. -/
def hashPair : Asked FixedIndex EncIndex → Option (BN254.BaseField × (Block × Block))
  | ⟨.hash key, answer⟩ => some (key, answer)
  | _ => none

/-- The stored form of a hash value (the library's private encoding, read off one program). -/
def codeOf (value : Block × Block) : HashCode :=
  (((LazyOracle.program (FixedIndex := Unit) (EncIndex := Unit) (.hash 0) value
    LazyOracle.empty).getD LazyOracle.empty).hash.lookup 0).getD 0

theorem program_fixedForward (s : LState FixedIndex EncIndex) (index : FixedIndex) (input answer : Block) :
    LazyOracle.program (.fixedForward index input) answer s =
      (LazyOracle.permutationProgram (s.fixed index) input.toFin answer.toFin).map
        (fun next => { s with fixed := Function.update s.fixed index next }) := rfl

theorem program_fixedInverse (s : LState FixedIndex EncIndex) (index : FixedIndex) (output answer : Block) :
    LazyOracle.program (.fixedInverse index output) answer s =
      (LazyOracle.permutationProgram (s.fixed index) answer.toFin output.toFin).map
        (fun next => { s with fixed := Function.update s.fixed index next }) := rfl

theorem program_encForward (s : LState FixedIndex EncIndex) (index : EncIndex) (input answer : Block) :
    LazyOracle.program (.encForward index input) answer s =
      (LazyOracle.permutationProgram (s.enc index) input.toFin answer.toFin).map
        (fun next => { s with enc := Function.update s.enc index next }) := rfl

theorem program_encInverse (s : LState FixedIndex EncIndex) (index : EncIndex) (output answer : Block) :
    LazyOracle.program (.encInverse index output) answer s =
      (LazyOracle.permutationProgram (s.enc index) answer.toFin output.toFin).map
        (fun next => { s with enc := Function.update s.enc index next }) := rfl

/-! ### One planted entry -/

theorem plant_fixed (s : LState FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex)
    {index : FixedIndex} {x y : Fin (2 ^ 128)} (pair : fixedPair entry = some (index, x, y)) :
    plant s entry =
      if fresh : ¬ (s.fixed index).knownInput x ∧ ¬ (s.fixed index).knownOutput y then
        { s with
          fixed := Function.update s.fixed index (extendPair (s.fixed index) (room_of_fresh fresh.1) x y) }
      else s := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index' input =>
      change Block at answer
      simp only [fixedPair, Option.some.injEq, Prod.mk.injEq] at pair
      obtain ⟨rfl, rfl, rfl⟩ := pair
      unfold plant
      rw [program_fixedForward]
      unfold LazyOracle.permutationProgram
      by_cases fresh : ¬ (s.fixed index').knownInput input.toFin ∧ ¬ (s.fixed index').knownOutput answer.toFin
      · rw [dif_pos fresh, dif_pos fresh]
        rfl
      · rw [dif_neg fresh, dif_neg fresh]
        rfl
  | fixedInverse index' output =>
      change Block at answer
      simp only [fixedPair, Option.some.injEq, Prod.mk.injEq] at pair
      obtain ⟨rfl, rfl, rfl⟩ := pair
      unfold plant
      rw [program_fixedInverse]
      unfold LazyOracle.permutationProgram
      by_cases fresh : ¬ (s.fixed index').knownInput answer.toFin ∧ ¬ (s.fixed index').knownOutput output.toFin
      · rw [dif_pos fresh, dif_pos fresh]
        rfl
      · rw [dif_neg fresh, dif_neg fresh]
        rfl
  | encForward _ _ => simp [fixedPair] at pair
  | encInverse _ _ => simp [fixedPair] at pair
  | hash _ => simp [fixedPair] at pair

theorem plant_enc (s : LState FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex)
    {index : EncIndex} {x y : Fin (2 ^ 128)} (pair : encPair entry = some (index, x, y)) :
    plant s entry =
      if fresh : ¬ (s.enc index).knownInput x ∧ ¬ (s.enc index).knownOutput y then
        { s with
          enc := Function.update s.enc index (extendPair (s.enc index) (room_of_fresh fresh.1) x y) }
      else s := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | encForward index' input =>
      change Block at answer
      simp only [encPair, Option.some.injEq, Prod.mk.injEq] at pair
      obtain ⟨rfl, rfl, rfl⟩ := pair
      unfold plant
      rw [program_encForward]
      unfold LazyOracle.permutationProgram
      by_cases fresh : ¬ (s.enc index').knownInput input.toFin ∧ ¬ (s.enc index').knownOutput answer.toFin
      · rw [dif_pos fresh, dif_pos fresh]
        rfl
      · rw [dif_neg fresh, dif_neg fresh]
        rfl
  | encInverse index' output =>
      change Block at answer
      simp only [encPair, Option.some.injEq, Prod.mk.injEq] at pair
      obtain ⟨rfl, rfl, rfl⟩ := pair
      unfold plant
      rw [program_encInverse]
      unfold LazyOracle.permutationProgram
      by_cases fresh : ¬ (s.enc index').knownInput answer.toFin ∧ ¬ (s.enc index').knownOutput output.toFin
      · rw [dif_pos fresh, dif_pos fresh]
        rfl
      · rw [dif_neg fresh, dif_neg fresh]
        rfl
  | fixedForward _ _ => simp [encPair] at pair
  | fixedInverse _ _ => simp [encPair] at pair
  | hash _ => simp [encPair] at pair

theorem plant_fixed_same (s : LState FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex)
    {index : FixedIndex} {x y : Fin (2 ^ 128)} (pair : fixedPair entry = some (index, x, y)) :
    (plant s entry).fixed index =
      if fresh : ¬ (s.fixed index).knownInput x ∧ ¬ (s.fixed index).knownOutput y then
        extendPair (s.fixed index) (room_of_fresh fresh.1) x y else s.fixed index := by
  rw [plant_fixed s entry pair]
  split
  · simp only [Function.update_self]
  · rfl

theorem plant_enc_same (s : LState FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex)
    {index : EncIndex} {x y : Fin (2 ^ 128)} (pair : encPair entry = some (index, x, y)) :
    (plant s entry).enc index =
      if fresh : ¬ (s.enc index).knownInput x ∧ ¬ (s.enc index).knownOutput y then
        extendPair (s.enc index) (room_of_fresh fresh.1) x y else s.enc index := by
  rw [plant_enc s entry pair]
  split
  · simp only [Function.update_self]
  · rfl

theorem program_hash_spec (value : Block × Block) : ∃ code : HashCode,
    ∀ {F E : Type} [DecidableEq F] [DecidableEq E] (s : LState F E) (key : BN254.BaseField),
      LazyOracle.program (.hash key) value s =
        if s.hash.lookup key = none then some { s with hash := s.hash.program key code } else none :=
  ⟨_, fun _ _ => by simp only [LazyOracle.program]; rfl⟩

theorem codeOf_spec (value : Block × Block) {F E : Type} [DecidableEq F] [DecidableEq E]
    (s : LState F E) (key : BN254.BaseField) :
    LazyOracle.program (.hash key) value s =
      if s.hash.lookup key = none then some { s with hash := s.hash.program key (codeOf value) }
      else none := by
  obtain ⟨code, spec⟩ := program_hash_spec value
  have same : codeOf value = code := by
    unfold codeOf
    rw [spec, if_pos (show (LazyOracle.empty : LState Unit Unit).hash.lookup 0 = none from rfl)]
    show ((HashTable.program [] 0 code).lookup 0).getD 0 = code
    rw [HashTable.program_lookup, Function.update_self]
    rfl
  rw [same]
  exact spec s key

theorem plant_hash_lookup' (s : LState FixedIndex EncIndex) (key : BN254.BaseField)
    (value : Block × Block) (other : BN254.BaseField) :
    (plant s ⟨.hash key, value⟩).hash.lookup other =
      if s.hash.lookup key = none ∧ other = key then some (codeOf value) else s.hash.lookup other := by
  unfold plant
  rw [codeOf_spec]
  by_cases fresh : s.hash.lookup key = none
  · rw [if_pos fresh]
    simp only [Option.getD_some]
    show (s.hash.program key (codeOf value)).lookup other = _
    rw [HashTable.program_lookup]
    by_cases same : other = key
    · subst same
      simp [fresh]
    · simp [same, Function.update_of_ne same]
  · rw [if_neg fresh, Option.getD_none, if_neg (fun both => fresh both.1)]

theorem plant_hash_lookup (s : LState FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex)
    {key : BN254.BaseField} {value : Block × Block} (pair : hashPair entry = some (key, value))
    (other : BN254.BaseField) :
    (plant s entry).hash.lookup other =
      if s.hash.lookup key = none ∧ other = key then some (codeOf value) else s.hash.lookup other := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | hash key' =>
      simp only [hashPair, Option.some.injEq, Prod.mk.injEq] at pair
      rcases pair with ⟨rfl, rfl⟩
      exact plant_hash_lookup' s _ _ other
  | fixedForward _ _ => simp [hashPair] at pair
  | fixedInverse _ _ => simp [hashPair] at pair
  | encForward _ _ => simp [hashPair] at pair
  | encInverse _ _ => simp [hashPair] at pair

theorem plant_fixed_other (s : LState FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex)
    (index : FixedIndex) (none : ∀ x y, fixedPair entry ≠ some (index, x, y)) :
    (plant s entry).fixed index = s.fixed index := by
  obtain ⟨request, answer⟩ := entry
  unfold plant
  cases request with
  | fixedForward index' input =>
      change Block at answer
      have different : index ≠ index' := fun same => none input.toFin answer.toFin (by rw [same]; rfl)
      rw [program_fixedForward]
      cases LazyOracle.permutationProgram (s.fixed index') input.toFin answer.toFin <;>
        simp [Function.update_of_ne different]
  | fixedInverse index' output =>
      change Block at answer
      have different : index ≠ index' := fun same => none answer.toFin output.toFin (by rw [same]; rfl)
      rw [program_fixedInverse]
      cases LazyOracle.permutationProgram (s.fixed index') answer.toFin output.toFin <;>
        simp [Function.update_of_ne different]
  | encForward index' input =>
      change Block at answer
      rw [program_encForward]
      cases LazyOracle.permutationProgram (s.enc index') input.toFin answer.toFin <;> rfl
  | encInverse index' output =>
      change Block at answer
      rw [program_encInverse]
      cases LazyOracle.permutationProgram (s.enc index') answer.toFin output.toFin <;> rfl
  | hash key =>
      change Block × Block at answer
      rw [codeOf_spec]
      split <;> rfl

theorem plant_enc_other (s : LState FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex)
    (index : EncIndex) (none : ∀ x y, encPair entry ≠ some (index, x, y)) :
    (plant s entry).enc index = s.enc index := by
  obtain ⟨request, answer⟩ := entry
  unfold plant
  cases request with
  | encForward index' input =>
      change Block at answer
      have different : index ≠ index' := fun same => none input.toFin answer.toFin (by rw [same]; rfl)
      rw [program_encForward]
      cases LazyOracle.permutationProgram (s.enc index') input.toFin answer.toFin <;>
        simp [Function.update_of_ne different]
  | encInverse index' output =>
      change Block at answer
      have different : index ≠ index' := fun same => none answer.toFin output.toFin (by rw [same]; rfl)
      rw [program_encInverse]
      cases LazyOracle.permutationProgram (s.enc index') answer.toFin output.toFin <;>
        simp [Function.update_of_ne different]
  | fixedForward index' input =>
      change Block at answer
      rw [program_fixedForward]
      cases LazyOracle.permutationProgram (s.fixed index') input.toFin answer.toFin <;> rfl
  | fixedInverse index' output =>
      change Block at answer
      rw [program_fixedInverse]
      cases LazyOracle.permutationProgram (s.fixed index') answer.toFin output.toFin <;> rfl
  | hash key =>
      change Block × Block at answer
      rw [codeOf_spec]
      split <;> rfl

theorem plant_hash_other (s : LState FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex)
    (none : hashPair entry = Option.none) : (plant s entry).hash = s.hash := by
  obtain ⟨request, answer⟩ := entry
  unfold plant
  cases request with
  | fixedForward index input =>
      change Block at answer
      rw [program_fixedForward]
      cases LazyOracle.permutationProgram (s.fixed index) input.toFin answer.toFin <;> rfl
  | fixedInverse index output =>
      change Block at answer
      rw [program_fixedInverse]
      cases LazyOracle.permutationProgram (s.fixed index) answer.toFin output.toFin <;> rfl
  | encForward index input =>
      change Block at answer
      rw [program_encForward]
      cases LazyOracle.permutationProgram (s.enc index) input.toFin answer.toFin <;> rfl
  | encInverse index output =>
      change Block at answer
      rw [program_encInverse]
      cases LazyOracle.permutationProgram (s.enc index) answer.toFin output.toFin <;> rfl
  | hash key => simp [hashPair] at none

theorem fixedPair_unique {entry : Asked FixedIndex EncIndex} {i i' : FixedIndex}
    {x y x' y' : Fin (2 ^ 128)} (first : fixedPair entry = some (i, x, y))
    (second : fixedPair entry = some (i', x', y')) : i = i' ∧ x = x' ∧ y = y' := by
  rw [first, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at second
  exact second

/-! ### A sparse state after planting one pair -/

/-- Planting a pair `(x, y)` into a sparse permutation that already stores it or has it fresh. -/
theorem sparse_plant_look {n : ℕ} (t : SparsePermutation n) {x y : Fin n}
    (compat : look t x = some y ∨ (¬ t.knownInput x ∧ ¬ t.knownOutput y)) (z : Fin n) :
    look (if fresh : ¬ t.knownInput x ∧ ¬ t.knownOutput y then
        extendPair t (room_of_fresh fresh.1) x y else t) z =
      if z = x then some y else look t z := by
  split
  · rename_i fresh
    exact look_extend t _ fresh.1 fresh.2 z
  · rename_i notFresh
    rcases compat with present | fresh
    · by_cases same : z = x
      · subst same
        rw [if_pos rfl, present]
      · rw [if_neg same]
    · exact (notFresh fresh).elim

/-! ### Consistency and compatibility -/

/-- Every entry's answer is `O`'s. -/
def Consistent (O : PublicOracle FixedIndex EncIndex) (entries : List (Asked FixedIndex EncIndex)) :
    Prop :=
  ∀ entry ∈ entries, entry.2 = publicAnswer O entry.1

theorem fixedPair_oracle {O : PublicOracle FixedIndex EncIndex} {entry : Asked FixedIndex EncIndex}
    (consistent : entry.2 = publicAnswer O entry.1) {i : FixedIndex} {x y : Fin (2 ^ 128)}
    (pair : fixedPair entry = some (i, x, y)) :
    O.1.permutation i (BitVec.ofFin x) = BitVec.ofFin y := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index input =>
      simp only [fixedPair, Option.some.injEq, Prod.mk.injEq] at pair
      obtain ⟨rfl, rfl, rfl⟩ := pair
      exact consistent.symm
  | fixedInverse index output =>
      simp only [fixedPair, Option.some.injEq, Prod.mk.injEq] at pair
      obtain ⟨rfl, rfl, rfl⟩ := pair
      have : (O.1.permutation index).symm output = answer := consistent.symm
      show O.1.permutation index answer = output
      rw [← this, Equiv.apply_symm_apply]
  | encForward _ _ => simp [fixedPair] at pair
  | encInverse _ _ => simp [fixedPair] at pair
  | hash _ => simp [fixedPair] at pair

theorem encPair_oracle {O : PublicOracle FixedIndex EncIndex} {entry : Asked FixedIndex EncIndex}
    (consistent : entry.2 = publicAnswer O entry.1) {i : EncIndex} {x y : Fin (2 ^ 128)}
    (pair : encPair entry = some (i, x, y)) :
    O.2.1.permutation i (BitVec.ofFin x) = BitVec.ofFin y := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | encForward index input =>
      simp only [encPair, Option.some.injEq, Prod.mk.injEq] at pair
      obtain ⟨rfl, rfl, rfl⟩ := pair
      exact consistent.symm
  | encInverse index output =>
      simp only [encPair, Option.some.injEq, Prod.mk.injEq] at pair
      obtain ⟨rfl, rfl, rfl⟩ := pair
      have : (O.2.1.permutation index).symm output = answer := consistent.symm
      show O.2.1.permutation index answer = output
      rw [← this, Equiv.apply_symm_apply]
  | fixedForward _ _ => simp [encPair] at pair
  | fixedInverse _ _ => simp [encPair] at pair
  | hash _ => simp [encPair] at pair

theorem hashPair_oracle {O : PublicOracle FixedIndex EncIndex} {entry : Asked FixedIndex EncIndex}
    (consistent : entry.2 = publicAnswer O entry.1) {key : BN254.BaseField} {value : Block × Block}
    (pair : hashPair entry = some (key, value)) : value = O.2.2 key := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | hash key' =>
      simp only [hashPair, Option.some.injEq, Prod.mk.injEq] at pair
      obtain ⟨rfl, rfl⟩ := pair
      exact consistent
  | fixedForward _ _ => simp [hashPair] at pair
  | fixedInverse _ _ => simp [hashPair] at pair
  | encForward _ _ => simp [hashPair] at pair
  | encInverse _ _ => simp [hashPair] at pair

/-- **Each listed pair is stored in `s` or fresh there**, and every stored hash value at a listed
key is `O`'s. -/
structure Compat (O : PublicOracle FixedIndex EncIndex) (entries : List (Asked FixedIndex EncIndex))
    (s : LState FixedIndex EncIndex) : Prop where
  consistent : Consistent O entries
  fixed : ∀ entry ∈ entries, ∀ i x y, fixedPair entry = some (i, x, y) →
    look (s.fixed i) x = some y ∨ (¬ (s.fixed i).knownInput x ∧ ¬ (s.fixed i).knownOutput y)
  enc : ∀ entry ∈ entries, ∀ i x y, encPair entry = some (i, x, y) →
    look (s.enc i) x = some y ∨ (¬ (s.enc i).knownInput x ∧ ¬ (s.enc i).knownOutput y)
  hash : ∀ entry ∈ entries, ∀ key value, hashPair entry = some (key, value) →
    s.hash.lookup key = none ∨ s.hash.lookup key = some (codeOf (O.2.2 key))

theorem bitvec_toFin_injective {x y : Fin (2 ^ 128)}
    (same : (BitVec.ofFin x : Block) = BitVec.ofFin y) : x = y := by
  have := congrArg BitVec.toFin same
  simpa using this

/-- One planted entry keeps the rest compatible. -/
theorem Compat.plant {O : PublicOracle FixedIndex EncIndex} {entry : Asked FixedIndex EncIndex}
    {entries : List (Asked FixedIndex EncIndex)} {s : LState FixedIndex EncIndex}
    (compat : Compat O (entry :: entries) s) : Compat O entries (plant s entry) := by
  have headConsistent := compat.consistent entry List.mem_cons_self
  refine ⟨fun e member => compat.consistent e (List.mem_cons_of_mem _ member), ?_, ?_, ?_⟩
  · intro e member i x y pair
    have old := compat.fixed e (List.mem_cons_of_mem _ member) i x y pair
    have eOracle := fixedPair_oracle (compat.consistent e (List.mem_cons_of_mem _ member)) pair
    rcases h : fixedPair entry with _ | ⟨i', x', y'⟩
    · rw [plant_fixed_other s entry i (fun a b hb => by rw [h] at hb; cases hb)]
      exact old
    · by_cases sameIndex : i = i'
      · rw [← sameIndex] at h
        have headOracle := fixedPair_oracle headConsistent h
        have headCompat := compat.fixed entry List.mem_cons_self i x' y' h
        rw [plant_fixed_same s entry h]
        have lookPlanted := sparse_plant_look (s.fixed i) headCompat
        by_cases sameX : x = x'
        · subst sameX
          have : y = y' := by
            rw [headOracle] at eOracle
            exact (bitvec_toFin_injective eOracle).symm
          subst this
          left
          rw [lookPlanted, if_pos rfl]
        · have sameY : y ≠ y' := by
            intro equal
            subst equal
            rw [← headOracle] at eOracle
            exact sameX (bitvec_toFin_injective ((O.1.permutation i).injective eOracle))
          rcases old with present | ⟨freshX, freshY⟩
          · left
            rw [lookPlanted, if_neg sameX]
            exact present
          · right
            constructor
            · rw [knownInput_iff]
              rintro ⟨w, found⟩
              rw [lookPlanted, if_neg sameX] at found
              exact freshX (knownInput_iff.mpr ⟨w, found⟩)
            · rw [knownOutput_iff]
              rintro ⟨w, found⟩
              rw [lookPlanted] at found
              split at found
              · cases found
                exact sameY rfl
              · exact freshY (knownOutput_iff.mpr ⟨w, found⟩)
      · rw [plant_fixed_other s entry i (fun a b hb => by
          rw [h] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          exact sameIndex hb.1.symm)]
        exact old
  · intro e member i x y pair
    have old := compat.enc e (List.mem_cons_of_mem _ member) i x y pair
    have eOracle := encPair_oracle (compat.consistent e (List.mem_cons_of_mem _ member)) pair
    rcases h : encPair entry with _ | ⟨i', x', y'⟩
    · rw [plant_enc_other s entry i (fun a b hb => by rw [h] at hb; cases hb)]
      exact old
    · by_cases sameIndex : i = i'
      · rw [← sameIndex] at h
        have headOracle := encPair_oracle headConsistent h
        have headCompat := compat.enc entry List.mem_cons_self i x' y' h
        rw [plant_enc_same s entry h]
        have lookPlanted := sparse_plant_look (s.enc i) headCompat
        by_cases sameX : x = x'
        · subst sameX
          have : y = y' := by
            rw [headOracle] at eOracle
            exact (bitvec_toFin_injective eOracle).symm
          subst this
          left
          rw [lookPlanted, if_pos rfl]
        · have sameY : y ≠ y' := by
            intro equal
            subst equal
            rw [← headOracle] at eOracle
            exact sameX (bitvec_toFin_injective ((O.2.1.permutation i).injective eOracle))
          rcases old with present | ⟨freshX, freshY⟩
          · left
            rw [lookPlanted, if_neg sameX]
            exact present
          · right
            constructor
            · rw [knownInput_iff]
              rintro ⟨w, found⟩
              rw [lookPlanted, if_neg sameX] at found
              exact freshX (knownInput_iff.mpr ⟨w, found⟩)
            · rw [knownOutput_iff]
              rintro ⟨w, found⟩
              rw [lookPlanted] at found
              split at found
              · cases found
                exact sameY rfl
              · exact freshY (knownOutput_iff.mpr ⟨w, found⟩)
      · rw [plant_enc_other s entry i (fun a b hb => by
          rw [h] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          exact sameIndex hb.1.symm)]
        exact old
  · intro e member key value pair
    have old := compat.hash e (List.mem_cons_of_mem _ member) key value pair
    rcases h : hashPair entry with _ | ⟨key', value'⟩
    · rw [plant_hash_other s entry h]
      exact old
    · rw [plant_hash_lookup s entry h]
      have headValue := hashPair_oracle headConsistent h
      split
      · rename_i both
        obtain ⟨_, rfl⟩ := both
        right
        rw [headValue]
      · exact old

/-- **The planted state stores exactly the old pairs and the listed pairs.** -/
theorem plantAll_look (O : PublicOracle FixedIndex EncIndex) (entries : List (Asked FixedIndex EncIndex))
    (s : LState FixedIndex EncIndex) (compat : Compat O entries s) (i : FixedIndex) (x y : Fin (2 ^ 128)) :
    look ((plantAll entries s).fixed i) x = some y ↔
      look (s.fixed i) x = some y ∨ ∃ entry ∈ entries, fixedPair entry = some (i, x, y) := by
  induction entries generalizing s with
  | nil => simp [plantAll_nil]
  | cons entry entries ih =>
      rw [plantAll_cons, ih (plant s entry) compat.plant]
      have headConsistent := compat.consistent entry List.mem_cons_self
      rcases h : fixedPair entry with _ | ⟨i', x', y'⟩
      · rw [plant_fixed_other s entry i (fun a b hb => by rw [h] at hb; cases hb)]
        constructor
        · rintro (found | ⟨e, member, pair⟩)
          · exact Or.inl found
          · exact Or.inr ⟨e, List.mem_cons_of_mem _ member, pair⟩
        · rintro (found | ⟨e, member, pair⟩)
          · exact Or.inl found
          · rcases List.mem_cons.mp member with rfl | member
            · rw [h] at pair; cases pair
            · exact Or.inr ⟨e, member, pair⟩
      · by_cases sameIndex : i = i'
        · rw [← sameIndex] at h
          have headCompat := compat.fixed entry List.mem_cons_self i x' y' h
          rw [plant_fixed_same s entry h, sparse_plant_look (s.fixed i) headCompat]
          constructor
          · rintro (found | ⟨e, member, pair⟩)
            · split at found
              · rename_i same
                cases found
                subst same
                exact Or.inr ⟨entry, List.mem_cons_self, h⟩
              · exact Or.inl found
            · exact Or.inr ⟨e, List.mem_cons_of_mem _ member, pair⟩
          · rintro (found | ⟨e, member, pair⟩)
            · left
              split
              · rename_i same
                subst same
                rcases headCompat with present | ⟨freshX, _⟩
                · rw [present] at found
                  exact found
                · exact (freshX (knownInput_iff.mpr ⟨y, found⟩)).elim
              · exact found
            · rcases List.mem_cons.mp member with rfl | member
              · obtain ⟨-, rfl, rfl⟩ := fixedPair_unique h pair
                left
                rw [if_pos rfl]
              · exact Or.inr ⟨e, member, pair⟩
        · rw [plant_fixed_other s entry i (fun a b hb => by
            rw [h] at hb
            simp only [Option.some.injEq, Prod.mk.injEq] at hb
            exact sameIndex hb.1.symm)]
          constructor
          · rintro (found | ⟨e, member, pair⟩)
            · exact Or.inl found
            · exact Or.inr ⟨e, List.mem_cons_of_mem _ member, pair⟩
          · rintro (found | ⟨e, member, pair⟩)
            · exact Or.inl found
            · rcases List.mem_cons.mp member with rfl | member
              · rw [h] at pair
                simp only [Option.some.injEq, Prod.mk.injEq] at pair
                exact (sameIndex pair.1.symm).elim
              · exact Or.inr ⟨e, member, pair⟩

/-- The same for the EncPRF permutations. -/
theorem plantAll_encLook (O : PublicOracle FixedIndex EncIndex)
    (entries : List (Asked FixedIndex EncIndex))
    (s : LState FixedIndex EncIndex) (compat : Compat O entries s) (i : EncIndex) (x y : Fin (2 ^ 128)) :
    look ((plantAll entries s).enc i) x = some y ↔
      look (s.enc i) x = some y ∨ ∃ entry ∈ entries, encPair entry = some (i, x, y) := by
  induction entries generalizing s with
  | nil => simp [plantAll_nil]
  | cons entry entries ih =>
      rw [plantAll_cons, ih (plant s entry) compat.plant]
      rcases h : encPair entry with _ | ⟨i', x', y'⟩
      · rw [plant_enc_other s entry i (fun a b hb => by rw [h] at hb; cases hb)]
        constructor
        · rintro (found | ⟨e, member, pair⟩)
          · exact Or.inl found
          · exact Or.inr ⟨e, List.mem_cons_of_mem _ member, pair⟩
        · rintro (found | ⟨e, member, pair⟩)
          · exact Or.inl found
          · rcases List.mem_cons.mp member with rfl | member
            · rw [h] at pair; cases pair
            · exact Or.inr ⟨e, member, pair⟩
      · by_cases sameIndex : i = i'
        · rw [← sameIndex] at h
          have headCompat := compat.enc entry List.mem_cons_self i x' y' h
          rw [plant_enc_same s entry h, sparse_plant_look (s.enc i) headCompat]
          constructor
          · rintro (found | ⟨e, member, pair⟩)
            · split at found
              · rename_i same
                cases found
                subst same
                exact Or.inr ⟨entry, List.mem_cons_self, h⟩
              · exact Or.inl found
            · exact Or.inr ⟨e, List.mem_cons_of_mem _ member, pair⟩
          · rintro (found | ⟨e, member, pair⟩)
            · left
              split
              · rename_i same
                subst same
                rcases headCompat with present | ⟨freshX, _⟩
                · rw [present] at found
                  exact found
                · exact (freshX (knownInput_iff.mpr ⟨y, found⟩)).elim
              · exact found
            · rcases List.mem_cons.mp member with rfl | member
              · have := h.symm.trans pair
                simp only [Option.some.injEq, Prod.mk.injEq] at this
                obtain ⟨-, rfl, rfl⟩ := this
                left
                rw [if_pos rfl]
              · exact Or.inr ⟨e, member, pair⟩
        · rw [plant_enc_other s entry i (fun a b hb => by
            rw [h] at hb
            simp only [Option.some.injEq, Prod.mk.injEq] at hb
            exact sameIndex hb.1.symm)]
          constructor
          · rintro (found | ⟨e, member, pair⟩)
            · exact Or.inl found
            · exact Or.inr ⟨e, List.mem_cons_of_mem _ member, pair⟩
          · rintro (found | ⟨e, member, pair⟩)
            · exact Or.inl found
            · rcases List.mem_cons.mp member with rfl | member
              · rw [h] at pair
                simp only [Option.some.injEq, Prod.mk.injEq] at pair
                exact (sameIndex pair.1.symm).elim
              · exact Or.inr ⟨e, member, pair⟩

/-- The hash lookups after planting. -/
theorem plantAll_hashLookup (O : PublicOracle FixedIndex EncIndex)
    (entries : List (Asked FixedIndex EncIndex))
    (s : LState FixedIndex EncIndex) (compat : Compat O entries s) (key : BN254.BaseField) :
    (plantAll entries s).hash.lookup key =
      if s.hash.lookup key = none ∧ ∃ entry ∈ entries, ∃ value, hashPair entry = some (key, value)
      then some (codeOf (O.2.2 key)) else s.hash.lookup key := by
  induction entries generalizing s with
  | nil => simp [plantAll_nil]
  | cons entry entries ih =>
      rw [plantAll_cons, ih (plant s entry) compat.plant]
      have headConsistent := compat.consistent entry List.mem_cons_self
      rcases h : hashPair entry with _ | ⟨key', value'⟩
      · rw [plant_hash_other s entry h]
        congr 1
        apply propext
        constructor
        · rintro ⟨fresh, e, member, value, pair⟩
          exact ⟨fresh, e, List.mem_cons_of_mem _ member, value, pair⟩
        · rintro ⟨fresh, e, member, value, pair⟩
          rcases List.mem_cons.mp member with rfl | member
          · rw [h] at pair; cases pair
          · exact ⟨fresh, e, member, value, pair⟩
      · have headValue := hashPair_oracle headConsistent h
        rw [plant_hash_lookup s entry h key]
        by_cases same : key = key'
        · subst same
          by_cases fresh : s.hash.lookup key = none
          · simp only [fresh, true_and, if_true]
            have : ∃ e ∈ entry :: entries, ∃ value, hashPair e = some (key, value) :=
              ⟨entry, List.mem_cons_self, value', h⟩
            simp only [this, if_true, headValue]
            simp
          · simp only [fresh, false_and, if_false]
        · have iff : (∃ e ∈ entry :: entries, ∃ value, hashPair e = some (key, value)) ↔
              ∃ e ∈ entries, ∃ value, hashPair e = some (key, value) := by
            constructor
            · rintro ⟨e, member, value, pair⟩
              rcases List.mem_cons.mp member with rfl | member
              · rw [h] at pair
                simp only [Option.some.injEq, Prod.mk.injEq] at pair
                exact (same pair.1.symm).elim
              · exact ⟨e, member, value, pair⟩
            · rintro ⟨e, member, value, pair⟩
              exact ⟨e, List.mem_cons_of_mem _ member, value, pair⟩
          simp only [same, and_false, if_false, iff]

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
