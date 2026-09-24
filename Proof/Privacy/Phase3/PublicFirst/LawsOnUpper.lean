/-
**Phase 3, P1p — `LawOn`, the upper side: the planted entries and the shadow's view.**

`LawOn`'s upper side runs the on-curve shadow (`shadowOnM`) lazily on `σ`, the garbler's EncPRF and
designed entries planted on the empty oracle. Here:

* the planted list is consistent and every planted entry is stored as planted (`upper_consistent`,
  `upper_stored`);
* `onView`: the shadow's transcript on an oracle `O`, planted on the empty oracle;
* step (B), every planted entry is a question of the shadow run on a completion `O` of `σ`, with
  `O`'s answer, is `LawsOnCover.upper_covers`; so planting the transcript on `σ` or on the empty
  oracle gives the same lookups (`plantAll_sub`).

Generic tools: `completion_stored` (a completion answers a stored question as stored),
`plantAll_sub` (planting a consistent list over a planted consistent sub-list changes no lookup).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnReach
import Proof.Privacy.Phase3.PublicFirst.LawsPrivate
import Proof.Privacy.Phase3.PublicFirst.Stored

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion public_step)
open Kriterion.ArgoMAC.Phase3.Lazy (LState AllQ)
open scoped ENNReal

noncomputable section

/-! ### 1. Generic tools -/

section Generic

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

theorem look_empty (z : Fin (2 ^ 128)) : Hidden.look (SparsePermutation.empty (2 ^ 128)) z = none :=
  lk_empty z

theorem emptyFixed (i : FI) :
    (LazyOracle.empty : LazyOracle.State FI EI).fixed i = SparsePermutation.empty _ := rfl

theorem emptyEnc (i : EI) :
    (LazyOracle.empty : LazyOracle.State FI EI).enc i = SparsePermutation.empty _ := rfl

theorem emptyHash (key : BN254.BaseField) :
    (LazyOracle.empty : LazyOracle.State FI EI).hash.lookup key = none := rfl

theorem plantAll_eq_hidden (entries : List (Entry FI EI)) (s : LazyOracle.State FI EI) :
    plantAll entries s = Hidden.plantAll entries s := rfl

/-- A consistent list is compatible with the empty oracle. -/
theorem compat_empty (O : PublicOracle FI EI) (list : List (Entry FI EI))
    (consistent : Hidden.Consistent O list) :
    Hidden.Compat O list (LazyOracle.empty : LazyOracle.State FI EI) := by
  refine ⟨consistent, ?_, ?_, ?_⟩
  · intro _ _ i x y _
    right
    refine ⟨fun known => ?_, fun known => ?_⟩
    · obtain ⟨w, found⟩ := Hidden.knownInput_iff.mp known
      rw [emptyFixed, look_empty] at found
      cases found
    · obtain ⟨w, found⟩ := Hidden.knownOutput_iff.mp known
      rw [emptyFixed, look_empty] at found
      cases found
  · intro _ _ i x y _
    right
    refine ⟨fun known => ?_, fun known => ?_⟩
    · obtain ⟨w, found⟩ := Hidden.knownInput_iff.mp known
      rw [emptyEnc, look_empty] at found
      cases found
    · obtain ⟨w, found⟩ := Hidden.knownOutput_iff.mp known
      rw [emptyEnc, look_empty] at found
      cases found
  · intro _ _ key _ _
    left
    rfl

/-- The pairs a consistent list plants on the empty oracle. -/
theorem look_plantAll_empty (O : PublicOracle FI EI) (list : List (Entry FI EI))
    (consistent : Hidden.Consistent O list) (i : FI) (x y : Fin (2 ^ 128)) :
    Hidden.look ((plantAll list LazyOracle.empty).fixed i) x = some y ↔
      ∃ e ∈ list, Hidden.fixedPair e = some (i, x, y) := by
  rw [plantAll_eq_hidden, Hidden.plantAll_look O list LazyOracle.empty (compat_empty O list consistent),
    emptyFixed, look_empty]
  constructor
  · rintro (absurd | found)
    · cases absurd
    · exact found
  · exact Or.inr

theorem encLook_plantAll_empty (O : PublicOracle FI EI) (list : List (Entry FI EI))
    (consistent : Hidden.Consistent O list) (i : EI) (x y : Fin (2 ^ 128)) :
    Hidden.look ((plantAll list LazyOracle.empty).enc i) x = some y ↔
      ∃ e ∈ list, Hidden.encPair e = some (i, x, y) := by
  rw [plantAll_eq_hidden, Hidden.plantAll_encLook O list LazyOracle.empty (compat_empty O list consistent),
    emptyEnc, look_empty]
  constructor
  · rintro (absurd | found)
    · cases absurd
    · exact found
  · exact Or.inr

theorem hashLookup_plantAll_empty (O : PublicOracle FI EI) (list : List (Entry FI EI))
    (consistent : Hidden.Consistent O list) (key : BN254.BaseField) :
    (plantAll list LazyOracle.empty).hash.lookup key =
      if ∃ e ∈ list, ∃ value, Hidden.hashPair e = some (key, value) then
        some (Hidden.codeOf (O.2.2 key)) else none := by
  rw [plantAll_eq_hidden, Hidden.plantAll_hashLookup O list LazyOracle.empty
    (compat_empty O list consistent), emptyHash]
  simp only [true_and]

/-- **Planting a consistent list over a planted consistent sub-list changes no lookup.** -/
theorem plantAll_sub (O : PublicOracle FI EI) (small large : List (Entry FI EI))
    (smallConsistent : Hidden.Consistent O small) (largeConsistent : Hidden.Consistent O large)
    (sub : ∀ e ∈ small, e ∈ large) :
    SameLookups (plantAll large (plantAll small LazyOracle.empty)) (plantAll large LazyOracle.empty) := by
  have lookSmall := look_plantAll_empty O small smallConsistent
  have encSmall := encLook_plantAll_empty O small smallConsistent
  have hashSmall := hashLookup_plantAll_empty O small smallConsistent
  have compat : Hidden.Compat O large (plantAll small LazyOracle.empty) := by
    refine ⟨largeConsistent, ?_, ?_, ?_⟩
    · intro e member i x y pair
      have eOracle := Hidden.fixedPair_oracle (largeConsistent e member) pair
      by_cases known : ((plantAll small LazyOracle.empty).fixed i).knownInput x
      · left
        obtain ⟨y', found⟩ := Hidden.knownInput_iff.mp known
        obtain ⟨e', member', pair'⟩ := (lookSmall i x y').mp found
        have e'Oracle := Hidden.fixedPair_oracle (smallConsistent e' member') pair'
        rw [eOracle] at e'Oracle
        rw [found, Hidden.bitvec_toFin_injective e'Oracle]
      · right
        refine ⟨known, fun knownOut => known ?_⟩
        obtain ⟨x', found⟩ := Hidden.knownOutput_iff.mp knownOut
        obtain ⟨e', member', pair'⟩ := (lookSmall i x' y).mp found
        have e'Oracle := Hidden.fixedPair_oracle (smallConsistent e' member') pair'
        rw [← eOracle] at e'Oracle
        have same : x' = x :=
          Hidden.bitvec_toFin_injective ((O.1.permutation i).injective e'Oracle)
        subst same
        exact Hidden.knownInput_iff.mpr ⟨y, found⟩
    · intro e member i x y pair
      have eOracle := Hidden.encPair_oracle (largeConsistent e member) pair
      by_cases known : ((plantAll small LazyOracle.empty).enc i).knownInput x
      · left
        obtain ⟨y', found⟩ := Hidden.knownInput_iff.mp known
        obtain ⟨e', member', pair'⟩ := (encSmall i x y').mp found
        have e'Oracle := Hidden.encPair_oracle (smallConsistent e' member') pair'
        rw [eOracle] at e'Oracle
        rw [found, Hidden.bitvec_toFin_injective e'Oracle]
      · right
        refine ⟨known, fun knownOut => known ?_⟩
        obtain ⟨x', found⟩ := Hidden.knownOutput_iff.mp knownOut
        obtain ⟨e', member', pair'⟩ := (encSmall i x' y).mp found
        have e'Oracle := Hidden.encPair_oracle (smallConsistent e' member') pair'
        rw [← eOracle] at e'Oracle
        have same : x' = x :=
          Hidden.bitvec_toFin_injective ((O.2.1.permutation i).injective e'Oracle)
        subst same
        exact Hidden.knownInput_iff.mpr ⟨y, found⟩
    · intro e member key value pair
      rw [hashSmall key]
      split
      · right; rfl
      · left; rfl
  have large₀ := compat_empty O large largeConsistent
  refine sameLookups_of_forward (fun i z => ?_) (fun i z => ?_) (fun key => ?_)
  · apply Option.ext
    intro y
    change Hidden.look _ z = some y ↔ Hidden.look _ z = some y
    rw [plantAll_eq_hidden large, Hidden.plantAll_look O large _ compat i z y, lookSmall,
      look_plantAll_empty O large largeConsistent]
    constructor
    · rintro (⟨e, member, pair⟩ | found)
      · exact ⟨e, sub e member, pair⟩
      · exact found
    · exact Or.inr
  · apply Option.ext
    intro y
    change Hidden.look _ z = some y ↔ Hidden.look _ z = some y
    rw [plantAll_eq_hidden large, Hidden.plantAll_encLook O large _ compat i z y, encSmall,
      encLook_plantAll_empty O large largeConsistent]
    constructor
    · rintro (⟨e, member, pair⟩ | found)
      · exact ⟨e, sub e member, pair⟩
      · exact found
    · exact Or.inr
  · rw [plantAll_eq_hidden large, Hidden.plantAll_hashLookup O large _ compat key, hashSmall key,
      hashLookup_plantAll_empty O large largeConsistent key]
    by_cases inSmall : ∃ e ∈ small, ∃ value, Hidden.hashPair e = some (key, value)
    · have inLarge : ∃ e ∈ large, ∃ value, Hidden.hashPair e = some (key, value) := by
        obtain ⟨e, member, value, pair⟩ := inSmall
        exact ⟨e, sub e member, value, pair⟩
      rw [if_pos inSmall, if_pos inLarge, if_neg (fun h => by simp at h)]
    · rw [if_neg inSmall]
      simp only [true_and]

end Generic

/-! ### 2. Stored answers, transcripts and completions -/

section Stored

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A programmed hash value reads back. -/
theorem lookup_program_hash (s s' : LState) (key : BaseField) (value : Block × Block)
    (programmed : LazyOracle.program (.hash key) value s = some s') :
    LazyOracle.lookup (.hash key) s' = some value := by
  simp only [LazyOracle.program] at programmed
  split at programmed
  · cases programmed
    simp only [LazyOracle.lookup]
    rw [HashTable.program_lookup, Function.update_self]
    exact congrArg some (Equiv.symm_apply_apply _ value)
  · cases programmed

/-- A stored hash code of a value reads back as the value. -/
theorem lookup_hash_codeOf (s : LState) (key : BaseField) (value : Block × Block)
    (found : s.hash.lookup key = some (Hidden.codeOf value)) :
    LazyOracle.lookup (.hash key) s = some value := by
  have spec := Hidden.codeOf_spec value (LazyOracle.empty : LState) (0 : BaseField)
  rw [if_pos (show (LazyOracle.empty : LState).hash.lookup 0 = none from rfl)] at spec
  have back := lookup_program_hash _ _ 0 value spec
  simp only [LazyOracle.lookup] at back ⊢
  rw [HashTable.program_lookup, Function.update_self] at back
  rw [found]
  exact back

/-- **A consistent forward list planted on the empty oracle stores each of its entries.** -/
theorem stored_of_mem (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (list : List (Entry FixedIndex EncPRF.PermutationIndex)) (consistent : Hidden.Consistent O list)
    (forward : ∀ e ∈ list, NoInverse e.1) (e : Entry FixedIndex EncPRF.PermutationIndex)
    (member : e ∈ list) : StoredAs (plantAll list LazyOracle.empty) e := by
  have noInverse := forward e member
  obtain ⟨q, a⟩ := e
  unfold StoredAs
  cases q with
  | fixedForward i x =>
      have look := (look_plantAll_empty O list consistent i x.toFin (BitVec.toFin a)).mpr
        ⟨_, member, rfl⟩
      simp only [LazyOracle.lookup]
      rw [show LazyOracle.permutationLookup ((plantAll list LazyOracle.empty).fixed i) x.toFin =
        some (BitVec.toFin a) from look]
      rfl
  | fixedInverse _ _ => exact noInverse.elim
  | encForward i x =>
      have look := (encLook_plantAll_empty O list consistent i x.toFin (BitVec.toFin a)).mpr
        ⟨_, member, rfl⟩
      simp only [LazyOracle.lookup]
      rw [show LazyOracle.permutationLookup ((plantAll list LazyOracle.empty).enc i) x.toFin =
        some (BitVec.toFin a) from look]
      rfl
  | encInverse _ _ => exact noInverse.elim
  | hash key =>
      have value : a = O.2.2 key :=
        Hidden.hashPair_oracle (entry := ⟨.hash key, a⟩) (consistent _ member) (key := key)
          (value := a) rfl
      have found : (plantAll list LazyOracle.empty).hash.lookup key = some (Hidden.codeOf a) := by
        rw [hashLookup_plantAll_empty O list consistent key, if_pos ⟨_, member, a, rfl⟩, value]
      exact lookup_hash_codeOf _ key a found

/-- Every transcript entry carries the answer function's answer. -/
theorem mem_of_asks {α : Type} (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (P : FreeQuery Programs.Spec α) {q : PublicQuery FixedIndex EncPRF.PermutationIndex}
    (asks : Asks ans P q) : (⟨q, ans q⟩ : Entry FixedIndex EncPRF.PermutationIndex) ∈ transcript ans P := by
  unfold Asks at asks
  rw [← transcript_eq_transcriptOf] at asks
  obtain ⟨⟨q', a⟩, member, same⟩ := List.mem_map.mp asks
  simp only at same
  subst same
  have answer := transcript_mem ans P _ member
  simp only at answer
  subst answer
  exact member

theorem asks_of_mem {α : Type} (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (P : FreeQuery Programs.Spec α) {e : Entry FixedIndex EncPRF.PermutationIndex}
    (member : e ∈ Hidden.transcriptOf ans P) : Asks ans P e.1 :=
  List.mem_map.mpr ⟨e, member, rfl⟩

/-- Every question on every path of an `AllQ` program satisfies its predicate. -/
theorem queryOnly_of_allQ {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop} {α : Type}
    {c : FreeQuery Programs.Spec α} (holds : AllQ S c) : Hidden.QueryOnly S c := by
  induction holds with
  | pure value => exact .pure value
  | query request next here _ ih => exact .query request next here ih

theorem queryOnly_mono {S S' : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop} {α : Type}
    {c : FreeQuery Programs.Spec α} (holds : Hidden.QueryOnly S c) (weaker : ∀ q, S q → S' q) :
    Hidden.QueryOnly S' c := by
  induction holds with
  | pure value => exact .pure value
  | query request next here _ ih => exact .query request next (weaker _ here) ih

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]

/-- **A completion answers a stored question as stored.** -/
theorem completion_stored {s : LState} {O : PublicOracle FixedIndex EncPRF.PermutationIndex}
    (member : O ∈ (publicCompletion s).support) {q : PublicQuery FixedIndex EncPRF.PermutationIndex}
    {a : q.Answer} (stored : StoredAs s ⟨q, a⟩) : publicAnswer O q = a := by
  have step := public_step q s
  rw [query_of_stored stored, PMF.pure_bind] at step
  have mem : publicHandler id q O ∈ ((publicCompletion s).map (publicHandler id q)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨O, member, rfl⟩
  rw [step] at mem
  obtain ⟨c, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp mem
  exact (congrArg Prod.fst same).symm

end Stored

/-! ### 3. The upper side -/

section Upper

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
  [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The view**: the shadow's transcript on an eager oracle, planted on the empty oracle. -/
def onView (table : Public) (bits : BitInput) (mac : InputMac)
    (O : PublicOracle FixedIndex EncPRF.PermutationIndex) : LState :=
  plantAll (transcript (publicAnswer O) (shadowOnM table bits mac)) LazyOracle.empty

theorem mem_garbler_of_upper (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (e : Entry FixedIndex EncPRF.PermutationIndex)
    (member : e ∈ upperEntries parameter scalar tape input) : e ∈ garblerTranscript scalar tape := by
  rcases List.mem_append.mp member with enc | designed
  · exact (List.mem_filter.mp enc).1
  · exact (List.mem_filter.mp designed).1

/-- The garbler's entries are the tape's answers. -/
theorem upper_consistent (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) : Hidden.Consistent tape.2 (upperEntries parameter scalar tape input) :=
  fun e member => (transcript_mem (publicAnswer tape.2) _ e
    (mem_garbler_of_upper parameter scalar tape input e member)).symm

/-- **The upper state stores every planted entry.** -/
theorem upper_stored (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (e : Entry FixedIndex EncPRF.PermutationIndex)
    (member : e ∈ upperEntries parameter scalar tape input) :
    StoredAs (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) e :=
  stored_of_mem tape.2 _ (upper_consistent parameter scalar tape input)
    (upperEntries_noInverse parameter scalar tape input) e member

end Upper

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
