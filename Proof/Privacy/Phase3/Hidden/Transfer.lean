/-
**Phase 3, P1c — moving planted entries between the extra set and the state.**

* `extraOf O L`: the entries of a list as an extra set (hash values in stored form);
* `rel_plantAll_of_avoid`: planting a consistent list into a state that avoids its entries gives
  exactly that state with the list as extra entries;
* `plantAll_transfer`: if `s₁` is `s₂` with extra entries `H` and every listed entry is stored in
  `s₁`, then `s₁` is `plantAll L s₂` with `H` minus the list (`dropAll`);
* `avoid_runLog`: a run whose log never touches `K` keeps the state avoiding `K`.
-/

import Proof.Privacy.Phase3.Hidden.Install

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open Kriterion.Cryptography
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

section Sparse

variable {n : ℕ}

theorem SparseExtra.congr {s₁ s₂ : SparsePermutation n} {E E' : Fin n → Fin n → Prop}
    (rel : SparseExtra s₁ s₂ E) (same : ∀ x y, E x y ↔ E' x y) : SparseExtra s₁ s₂ E' :=
  ⟨fun x y => by rw [← same]; exact rel.look_iff x y,
    fun x y extra => rel.freshIn x y ((same x y).mpr extra),
    fun x y extra => rel.freshOut x y ((same x y).mpr extra)⟩

/-- Moving a stored extra pair into `s₂`. -/
theorem SparseExtra.move {s₁ s₂ : SparsePermutation n} {E : Fin n → Fin n → Prop}
    (rel : SparseExtra s₁ s₂ E) {x y : Fin n} (stored : look s₁ x = some y) :
    SparseExtra s₁
      (if fresh : ¬ s₂.knownInput x ∧ ¬ s₂.knownOutput y then
        extendPair s₂ (room_of_fresh fresh.1) x y else s₂)
      (fun z w => E z w ∧ ¬ (z = x ∧ w = y)) := by
  have functional : ∀ z w, look s₁ z = some w → z = x → w = y := by
    intro z w found same
    subst same
    rw [stored] at found
    exact (Option.some.inj found).symm
  have injective : ∀ z w, look s₁ z = some w → w = y → z = x := by
    intro z w found same
    subst same
    exact look_injective found stored
  rcases (rel.look_iff x y).mp stored with present | extra
  · have notFresh : ¬ (¬ s₂.knownInput x ∧ ¬ s₂.knownOutput y) :=
      fun fresh => fresh.1 (knownInput_iff.mpr ⟨y, present⟩)
    rw [dif_neg notFresh]
    refine ⟨fun z w => ?_, fun z w extra => rel.freshIn z w extra.1,
      fun z w extra => rel.freshOut z w extra.1⟩
    rw [rel.look_iff z w]
    constructor
    · rintro (found | extraZ)
      · exact Or.inl found
      · by_cases pair : z = x ∧ w = y
        · obtain ⟨rfl, rfl⟩ := pair
          exact Or.inl present
        · exact Or.inr ⟨extraZ, pair⟩
    · rintro (found | ⟨extraZ, _⟩)
      · exact Or.inl found
      · exact Or.inr extraZ
  · have fresh : ¬ s₂.knownInput x ∧ ¬ s₂.knownOutput y :=
      ⟨look_eq_none.mp (rel.freshIn x y extra),
        fun known => by
          obtain ⟨z, found⟩ := knownOutput_iff.mp known
          exact rel.freshOut x y extra z found⟩
    rw [dif_pos fresh]
    refine ⟨fun z w => ?_, fun z w extraZ => ?_, fun z w extraZ z' found => ?_⟩
    · rw [look_extend s₂ _ fresh.1 fresh.2]
      constructor
      · intro found
        by_cases same : z = x
        · subst same
          rw [if_pos rfl, functional z w found rfl]
          exact Or.inl rfl
        · rw [if_neg same]
          rcases (rel.look_iff z w).mp found with found | extraZ
          · exact Or.inl found
          · exact Or.inr ⟨extraZ, fun pair => same pair.1⟩
      · rintro (found | ⟨extraZ, _⟩)
        · split at found
          · rename_i same
            subst same
            cases found
            exact stored
          · exact (rel.look_iff z w).mpr (Or.inl found)
        · exact (rel.look_iff z w).mpr (Or.inr extraZ)
    · rw [look_extend s₂ _ fresh.1 fresh.2]
      have ne : z ≠ x := by
        intro same
        subst same
        have storedZ := (rel.look_iff z w).mpr (Or.inr extraZ.1)
        exact extraZ.2 ⟨rfl, functional z w storedZ rfl⟩
      rw [if_neg ne]
      exact rel.freshIn z w extraZ.1
    · rw [look_extend s₂ _ fresh.1 fresh.2] at found
      split at found
      · cases found
        have storedZ := (rel.look_iff z y).mpr (Or.inr extraZ.1)
        exact extraZ.2 ⟨injective z y storedZ rfl, rfl⟩
      · exact rel.freshOut z w extraZ.1 z' found

end Sparse

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-! ### Extra sets from entry lists -/

open Classical in
/-- **The entries of a list, as an extra set.** -/
def extraOf (O : PublicOracle FixedIndex EncIndex) (entries : List (Asked FixedIndex EncIndex)) :
    Extra FixedIndex EncIndex where
  fixed i x y := ∃ entry ∈ entries, fixedPair entry = some (i, x, y)
  enc i x y := ∃ entry ∈ entries, encPair entry = some (i, x, y)
  hash key := if ∃ entry ∈ entries, ∃ value, hashPair entry = some (key, value)
    then some (codeOf (O.2.2 key)) else none

open Classical in
/-- `H` minus the entries of a list. -/
def dropAll (H : Extra FixedIndex EncIndex) (entries : List (Asked FixedIndex EncIndex)) :
    Extra FixedIndex EncIndex where
  fixed i x y := H.fixed i x y ∧ ¬ ∃ entry ∈ entries, fixedPair entry = some (i, x, y)
  enc i x y := H.enc i x y ∧ ¬ ∃ entry ∈ entries, encPair entry = some (i, x, y)
  hash key := if ∃ entry ∈ entries, ∃ value, hashPair entry = some (key, value) then none
    else H.hash key

/-- Two extra sets with the same entries. -/
structure Extra.Equiv (H H' : Extra FixedIndex EncIndex) : Prop where
  fixed : ∀ i x y, H.fixed i x y ↔ H'.fixed i x y
  enc : ∀ i x y, H.enc i x y ↔ H'.enc i x y
  hash : ∀ key, H.hash key = H'.hash key

theorem Extra.Equiv.symm {H H' : Extra FixedIndex EncIndex} (same : Extra.Equiv H H') :
    Extra.Equiv H' H :=
  ⟨fun i x y => (same.fixed i x y).symm, fun i x y => (same.enc i x y).symm,
    fun key => (same.hash key).symm⟩

theorem Rel.congr {s₁ s₂ : LState FixedIndex EncIndex} {H H' : Extra FixedIndex EncIndex}
    (rel : Rel s₁ s₂ H) (same : Extra.Equiv H H') : Rel s₁ s₂ H' :=
  ⟨fun i => (rel.fixed i).congr (same.fixed i), fun i => (rel.enc i).congr (same.enc i),
    fun key none => rel.hashAgree key ((same.hash key).trans none),
    fun key value extra => rel.hashExtra key value ((same.hash key).trans extra)⟩

theorem dropAll_nil (H : Extra FixedIndex EncIndex) : Extra.Equiv (dropAll H []) H := by
  classical
  refine ⟨fun i x y => ?_, fun i x y => ?_, fun key => ?_⟩ <;> simp [dropAll]

theorem dropAll_cons (H : Extra FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex)
    (entries : List (Asked FixedIndex EncIndex)) :
    Extra.Equiv (dropAll (dropAll H [entry]) entries) (dropAll H (entry :: entries)) := by
  classical
  refine ⟨fun i x y => ?_, fun i x y => ?_, fun key => ?_⟩
  · simp only [dropAll, List.mem_cons, List.mem_singleton, exists_eq_or_imp, List.not_mem_nil,
      or_false, exists_eq_left, not_or, and_assoc]
  · simp only [dropAll, List.mem_cons, List.mem_singleton, exists_eq_or_imp, List.not_mem_nil,
      or_false, exists_eq_left, not_or, and_assoc]
  · simp only [dropAll, List.mem_cons, List.mem_singleton, exists_eq_or_imp, List.not_mem_nil,
      or_false, exists_eq_left]
    by_cases first : ∃ value, hashPair entry = some (key, value)
    · simp [first]
    · by_cases rest : ∃ e ∈ entries, ∃ value, hashPair e = some (key, value)
      · simp [first, rest]
      · simp [first, rest]

/-! ### Stored entries and the transfer -/

/-- The entry's pair is stored in `s`. -/
structure StoredIn (s : LState FixedIndex EncIndex) (entry : Asked FixedIndex EncIndex) : Prop where
  fixed : ∀ i x y, fixedPair entry = some (i, x, y) → look (s.fixed i) x = some y
  enc : ∀ i x y, encPair entry = some (i, x, y) → look (s.enc i) x = some y
  hash : ∀ key value, hashPair entry = some (key, value) → s.hash.lookup key = some (codeOf value)

theorem entry_kinds (entry : Asked FixedIndex EncIndex) :
    (∃ i x y, fixedPair entry = some (i, x, y)) ∨ (∃ i x y, encPair entry = some (i, x, y)) ∨
      ∃ key value, hashPair entry = some (key, value) := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward i x => exact Or.inl ⟨_, _, _, rfl⟩
  | fixedInverse i y => exact Or.inl ⟨_, _, _, rfl⟩
  | encForward i x => exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
  | encInverse i y => exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
  | hash key => exact Or.inr (Or.inr ⟨_, _, rfl⟩)

/-- **One entry moved from the extra set into `s₂`.** -/
theorem Rel.planted {s₁ s₂ : LState FixedIndex EncIndex} {H : Extra FixedIndex EncIndex}
    (rel : Rel s₁ s₂ H) {entry : Asked FixedIndex EncIndex} (stored : StoredIn s₁ entry) :
    Rel s₁ (plant s₂ entry) (dropAll H [entry]) := by
  classical
  rcases entry_kinds entry with ⟨i, x, y, pair⟩ | ⟨i, x, y, pair⟩ | ⟨key, value, pair⟩
  · have noEnc : ∀ j a b, encPair entry ≠ some (j, a, b) := by
      obtain ⟨request, answer⟩ := entry
      cases request <;> simp_all [fixedPair, encPair]
    have noHash : hashPair entry = none := by
      obtain ⟨request, answer⟩ := entry
      cases request <;> simp_all [fixedPair, hashPair]
    refine ⟨fun j => ?_, fun j => ?_, fun key absent => ?_, fun key c extra => ?_⟩
    · by_cases same : j = i
      · subst same
        rw [plant_fixed_same s₂ entry pair]
        refine ((rel.fixed j).move (stored.fixed j x y pair)).congr fun z w => ?_
        simp only [dropAll, List.mem_singleton, exists_eq_left, pair, Option.some.injEq,
          Prod.mk.injEq, true_and]
        constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁, fun ⟨a, b⟩ => h₂ ⟨a.symm, b.symm⟩⟩
      · rw [plant_fixed_other s₂ entry j (fun a b hb => same (by
          rw [pair] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          exact hb.1.symm))]
        refine (rel.fixed j).congr fun z w => ?_
        simp only [dropAll, List.mem_singleton, exists_eq_left, pair, Option.some.injEq,
          Prod.mk.injEq]
        constructor
        · exact fun h => ⟨h, fun both => same both.1.symm⟩
        · exact fun h => h.1
    · rw [plant_enc_other s₂ entry j (noEnc j)]
      refine (rel.enc j).congr fun z w => ?_
      simp only [dropAll, List.mem_singleton, exists_eq_left, noEnc j z w, not_false_eq_true,
        and_true]
    · have hashSame : (plant s₂ entry).hash = s₂.hash := plant_hash_other s₂ entry noHash
      rw [hashSame]
      apply rel.hashAgree
      simpa [dropAll, noHash] using absent
    · have hashSame : (plant s₂ entry).hash = s₂.hash := plant_hash_other s₂ entry noHash
      rw [hashSame]
      apply rel.hashExtra
      simpa [dropAll, noHash] using extra
  · have noFixed : ∀ j a b, fixedPair entry ≠ some (j, a, b) := by
      obtain ⟨request, answer⟩ := entry
      cases request <;> simp_all [fixedPair, encPair]
    have noHash : hashPair entry = none := by
      obtain ⟨request, answer⟩ := entry
      cases request <;> simp_all [encPair, hashPair]
    refine ⟨fun j => ?_, fun j => ?_, fun key absent => ?_, fun key c extra => ?_⟩
    · rw [plant_fixed_other s₂ entry j (noFixed j)]
      refine (rel.fixed j).congr fun z w => ?_
      simp only [dropAll, List.mem_singleton, exists_eq_left, noFixed j z w, not_false_eq_true,
        and_true]
    · by_cases same : j = i
      · subst same
        rw [plant_enc_same s₂ entry pair]
        refine ((rel.enc j).move (stored.enc j x y pair)).congr fun z w => ?_
        simp only [dropAll, List.mem_singleton, exists_eq_left, pair, Option.some.injEq,
          Prod.mk.injEq, true_and]
        constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁, fun ⟨a, b⟩ => h₂ ⟨a.symm, b.symm⟩⟩
      · rw [plant_enc_other s₂ entry j (fun a b hb => same (by
          rw [pair] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          exact hb.1.symm))]
        refine (rel.enc j).congr fun z w => ?_
        simp only [dropAll, List.mem_singleton, exists_eq_left, pair, Option.some.injEq,
          Prod.mk.injEq]
        constructor
        · exact fun h => ⟨h, fun both => same both.1.symm⟩
        · exact fun h => h.1
    · have hashSame : (plant s₂ entry).hash = s₂.hash := plant_hash_other s₂ entry noHash
      rw [hashSame]
      apply rel.hashAgree
      simpa [dropAll, noHash] using absent
    · have hashSame : (plant s₂ entry).hash = s₂.hash := plant_hash_other s₂ entry noHash
      rw [hashSame]
      apply rel.hashExtra
      simpa [dropAll, noHash] using extra
  · have noFixed : ∀ j a b, fixedPair entry ≠ some (j, a, b) := by
      obtain ⟨request, answer⟩ := entry
      cases request <;> simp_all [fixedPair, hashPair]
    have noEnc : ∀ j a b, encPair entry ≠ some (j, a, b) := by
      obtain ⟨request, answer⟩ := entry
      cases request <;> simp_all [encPair, hashPair]
    have storedKey := stored.hash key value pair
    have dropHash : ∀ k, (dropAll H [entry]).hash k = if k = key then none else H.hash k := by
      intro k
      simp only [dropAll, List.mem_singleton, exists_eq_left, pair, Option.some.injEq,
        Prod.mk.injEq, exists_and_right, exists_eq, and_true]
      by_cases same : k = key
      · simp [same]
      · simp [same, Ne.symm same]
    refine ⟨fun j => ?_, fun j => ?_, fun k absent => ?_, fun k c extra => ?_⟩
    · rw [plant_fixed_other s₂ entry j (noFixed j)]
      refine (rel.fixed j).congr fun z w => ?_
      simp only [dropAll, List.mem_singleton, exists_eq_left, noFixed j z w, not_false_eq_true,
        and_true]
    · rw [plant_enc_other s₂ entry j (noEnc j)]
      refine (rel.enc j).congr fun z w => ?_
      simp only [dropAll, List.mem_singleton, exists_eq_left, noEnc j z w, not_false_eq_true,
        and_true]
    · rw [plant_hash_lookup s₂ entry pair k]
      by_cases same : k = key
      · subst same
        by_cases fresh : s₂.hash.lookup k = none
        · rw [if_pos ⟨fresh, rfl⟩]
          exact storedKey
        · rw [if_neg (fun both => fresh both.1)]
          rcases h : H.hash k with _ | c
          · exact rel.hashAgree k h
          · exact (fresh (rel.hashExtra k c h).2).elim
      · rw [if_neg (fun both => same both.2)]
        rw [dropHash k, if_neg same] at absent
        exact rel.hashAgree k absent
    · rw [dropHash k] at extra
      by_cases same : k = key
      · rw [if_pos same] at extra
        cases extra
      · rw [if_neg same] at extra
        rw [plant_hash_lookup s₂ entry pair k, if_neg (fun both => same both.2)]
        exact rel.hashExtra k c extra

/-- **The transfer.** -/
theorem plantAll_transfer {s₁ : LState FixedIndex EncIndex} (entries : List (Asked FixedIndex EncIndex))
    (stored : ∀ entry ∈ entries, StoredIn s₁ entry) :
    ∀ {s₂ : LState FixedIndex EncIndex} {H : Extra FixedIndex EncIndex}, Rel s₁ s₂ H →
      Rel s₁ (plantAll entries s₂) (dropAll H entries) := by
  induction entries with
  | nil =>
      intro s₂ H rel
      exact rel.congr (dropAll_nil H).symm
  | cons entry entries ih =>
      intro s₂ H rel
      rw [plantAll_cons]
      have step := rel.planted (stored entry List.mem_cons_self)
      exact (ih (fun e member => stored e (List.mem_cons_of_mem _ member)) step).congr
        (dropAll_cons H entry entries)

/-! ### Avoiding a set -/

/-- `s` avoids the entries of `K`: none of their inputs, outputs or hash keys is stored. -/
structure Avoid (s : LState FixedIndex EncIndex) (K : Extra FixedIndex EncIndex) : Prop where
  fixed : ∀ i x y, K.fixed i x y → look (s.fixed i) x = none ∧ ∀ x', look (s.fixed i) x' ≠ some y
  enc : ∀ i x y, K.enc i x y → look (s.enc i) x = none ∧ ∀ x', look (s.enc i) x' ≠ some y
  hash : ∀ key value, K.hash key = some value → s.hash.lookup key = none

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
