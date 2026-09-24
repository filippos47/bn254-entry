/-
**Phase 3, P1c — the two-stage comparison, generic.**

Three two-stage lazy games against one adversary (`first`, then `second r` on the first stage's
result), for one fixed tape:

* `eagerPlanted` — stage 1 from `s₁` (the whole transcript planted), stage 2 continues;
* `lateInstalled vis` — stage 1 from `s₂` (the transcript minus the extra entries `H`), then the
  entries `vis r` planted at the input choice, stage 2;
* `flaggedMass vis' b` — `lateInstalled vis'`, killed at a stage-1 touch of `H` or a stage-2 touch
  of `H` minus `vis' r`, at outcome `b`.

`eagerPlanted_ge` and `lateInstalled_ge`: **both** `eagerPlanted` and `lateInstalled vis` dominate
`flaggedMass vis'` whenever `vis' r ⊆ vis r ⊆` the extra entries (as lists of an eager oracle `O`'s
answers). `flagged_total_ge`: the flagged mass misses at most the two touch masses.
-/

import Proof.Privacy.Phase3.Hidden.Union

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open Kriterion.Cryptography
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-! ### Touch monotonicity and avoidance monotonicity -/

/-- `H` is contained in `H'`. -/
structure Extra.Le (H H' : Extra FixedIndex EncIndex) : Prop where
  fixed : ∀ i x y, H.fixed i x y → H'.fixed i x y
  enc : ∀ i x y, H.enc i x y → H'.enc i x y
  hash : ∀ key, (H.hash key).isSome = true → (H'.hash key).isSome = true

theorem touches_mono {H H' : Extra FixedIndex EncIndex} (le : Extra.Le H H')
    (entry : Asked FixedIndex EncIndex) (touch : Touches H entry) : Touches H' entry := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward i x =>
      rcases touch with ⟨y, h⟩ | ⟨x', h⟩
      · exact Or.inl ⟨y, le.fixed _ _ _ h⟩
      · exact Or.inr ⟨x', le.fixed _ _ _ h⟩
  | fixedInverse i y =>
      rcases touch with ⟨x, h⟩ | ⟨y', h⟩
      · exact Or.inl ⟨x, le.fixed _ _ _ h⟩
      · exact Or.inr ⟨y', le.fixed _ _ _ h⟩
  | encForward i x =>
      rcases touch with ⟨y, h⟩ | ⟨x', h⟩
      · exact Or.inl ⟨y, le.enc _ _ _ h⟩
      · exact Or.inr ⟨x', le.enc _ _ _ h⟩
  | encInverse i y =>
      rcases touch with ⟨x, h⟩ | ⟨y', h⟩
      · exact Or.inl ⟨x, le.enc _ _ _ h⟩
      · exact Or.inr ⟨y', le.enc _ _ _ h⟩
  | hash key => exact le.hash key touch

theorem cleanWeight_anti {H H' : Extra FixedIndex EncIndex} (le : Extra.Le H H')
    (log : List (Asked FixedIndex EncIndex)) : cleanWeight H' log ≤ cleanWeight H log := by
  classical
  unfold cleanWeight
  by_cases clean' : ∀ entry ∈ log, ¬ Touches H' entry
  · rw [if_pos clean', if_pos fun entry member touch => clean' entry member (touches_mono le entry touch)]
  · rw [if_neg clean']
    exact zero_le

theorem Avoid.mono {s : LState FixedIndex EncIndex} {K K' : Extra FixedIndex EncIndex}
    (avoid : Avoid s K') (le : Extra.Le K K') (sameHash : ∀ key value, K.hash key = some value →
      ∃ value', K'.hash key = some value') : Avoid s K :=
  ⟨fun i x y h => avoid.fixed i x y (le.fixed i x y h), fun i x y h => avoid.enc i x y (le.enc i x y h),
    fun key value h => by
      obtain ⟨value', h'⟩ := sameHash key value h
      exact avoid.hash key value' h'⟩

theorem cleanWeight_le_one (H : Extra FixedIndex EncIndex) (log : List (Asked FixedIndex EncIndex)) :
    cleanWeight H log ≤ 1 := by
  classical
  unfold cleanWeight
  split <;> simp

theorem cleanWeight_eq_one {H : Extra FixedIndex EncIndex} {log : List (Asked FixedIndex EncIndex)}
    (ne : cleanWeight H log ≠ 0) : ∀ entry ∈ log, ¬ Touches H entry := by
  classical
  unfold cleanWeight at ne
  split at ne
  · assumption
  · exact (ne rfl).elim

/-! ### Sublists of the extra entries -/

/-- Every listed entry is in `big`. -/
def Within (small big : List (Asked FixedIndex EncIndex)) : Prop := ∀ entry ∈ small, entry ∈ big

theorem extraOf_le {O : PublicOracle FixedIndex EncIndex} {small big : List (Asked FixedIndex EncIndex)}
    (within : Within small big) : Extra.Le (extraOf O small) (extraOf O big) := by
  classical
  refine ⟨fun i x y ⟨e, m, p⟩ => ⟨e, within e m, p⟩, fun i x y ⟨e, m, p⟩ => ⟨e, within e m, p⟩,
    fun key h => ?_⟩
  simp only [extraOf] at h ⊢
  split at h
  · rename_i listed
    obtain ⟨e, m, v, p⟩ := listed
    rw [if_pos ⟨e, within e m, v, p⟩]
    rfl
  · cases h

theorem extraOf_hash_some {O : PublicOracle FixedIndex EncIndex} {small big : List (Asked FixedIndex EncIndex)}
    (within : Within small big) (key : BN254.BaseField) (value : HashCode)
    (h : (extraOf O small).hash key = some value) :
    (extraOf O big).hash key = some value := by
  classical
  simp only [extraOf] at h ⊢
  split at h
  · rename_i listed
    obtain ⟨e, m, v, p⟩ := listed
    rw [if_pos ⟨e, within e m, v, p⟩]
    exact h
  · cases h

theorem dropAll_le_dropAll {O : PublicOracle FixedIndex EncIndex}
    {small big vis : List (Asked FixedIndex EncIndex)} (within : Within small big) :
    Extra.Le (dropAll (extraOf O small) vis) (dropAll (extraOf O big) vis) := by
  classical
  have le := extraOf_le (O := O) within
  refine ⟨fun i x y h => ⟨le.fixed i x y h.1, h.2⟩, fun i x y h => ⟨le.enc i x y h.1, h.2⟩,
    fun key h => ?_⟩
  simp only [dropAll] at h ⊢
  split at h
  · cases h
  · rename_i notListed
    rw [if_neg notListed]
    exact le.hash key h

/-- Entries of `extraOf O L` with `L` consistent are stored in any state related to a state by it. -/
theorem storedIn_of_rel {O : PublicOracle FixedIndex EncIndex} {L : List (Asked FixedIndex EncIndex)}
    (consistent : Consistent O L) {s₁ s₂ : LState FixedIndex EncIndex}
    (rel : Rel s₁ s₂ (extraOf O L)) {entry : Asked FixedIndex EncIndex} (member : entry ∈ L) :
    StoredIn s₁ entry := by
  classical
  refine ⟨fun i x y pair => ?_, fun i x y pair => ?_, fun key value pair => ?_⟩
  · exact ((rel.fixed i).look_iff x y).mpr (Or.inr ⟨entry, member, pair⟩)
  · exact ((rel.enc i).look_iff x y).mpr (Or.inr ⟨entry, member, pair⟩)
  · have extra : (extraOf O L).hash key = some (codeOf (O.2.2 key)) := by
      simp only [extraOf]
      rw [if_pos ⟨entry, member, value, pair⟩]
    rw [hashPair_oracle (consistent entry member) pair]
    exact (rel.hashExtra key _ extra).1

/-! ### The three games at one tape -/

variable {Result : Type} {budget₁ budget₂ : ℕ}
  (first : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget₁)
  (second : Result → OracleProgram (publicOracleSpec FixedIndex EncIndex) Bool budget₂)

/-- The mass at `b` of a final run. -/
def atBool (p : PMF (Bool × LState FixedIndex EncIndex)) (b : Bool) : ℝ≥0∞ :=
  expect p fun outcome => if outcome.1 = b then 1 else 0

/-- Stage 1 from `s₁`, stage 2 continuing. -/
def eagerPlanted (s₁ : LState FixedIndex EncIndex) (b : Bool) : ℝ≥0∞ :=
  expect (LazyOracle.run first s₁) fun r => atBool (LazyOracle.run (second r.1) r.2) b

/-- Stage 1 from `s₂`, `vis` planted at the input choice, stage 2. -/
def lateInstalled (s₂ : LState FixedIndex EncIndex)
    (vis : Result → List (Asked FixedIndex EncIndex)) (b : Bool) : ℝ≥0∞ :=
  expect (LazyOracle.run first s₂) fun r => atBool (LazyOracle.run (second r.1) (plantAll (vis r.1) r.2)) b

/-- The flagged mass: `lateInstalled vis'` killed at a stage-1 touch of `H` or a stage-2 touch
of `H` minus `vis'`. -/
def flaggedMass (s₂ : LState FixedIndex EncIndex) (H : Extra FixedIndex EncIndex)
    (vis' : Result → List (Asked FixedIndex EncIndex)) (b : Bool) : ℝ≥0∞ :=
  expect (runLog first s₂) fun o =>
    cleanWeight H o.2.2 *
      expect (runLog (second o.1) (plantAll (vis' o.1) o.2.1)) fun o₂ =>
        cleanWeight (dropAll H (vis' o.1)) o₂.2.2 * (if o₂.1 = b then 1 else 0)

theorem expect_runLog {Result' : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result' budget)
    (s : LState FixedIndex EncIndex) (f : Result' × LState FixedIndex EncIndex → ℝ≥0∞) :
    expect (runLog program s) (fun o => f (o.1, o.2.1)) = expect (LazyOracle.run program s) f := by
  rw [← runLog_run, expect_map]

/-- **The eager-planted game dominates the flagged mass.** -/
theorem eagerPlanted_ge (O : PublicOracle FixedIndex EncIndex) (L : List (Asked FixedIndex EncIndex))
    (consistent : Consistent O L) {s₁ s₂ : LState FixedIndex EncIndex}
    (rel : Rel s₁ s₂ (extraOf O L)) (vis' : Result → List (Asked FixedIndex EncIndex))
    (within : ∀ r, Within (vis' r) L) (b : Bool) :
    flaggedMass first second s₂ (extraOf O L) vis' b ≤ eagerPlanted first second s₁ b := by
  unfold flaggedMass eagerPlanted
  refine dominate (extraOf O L) first rel
    (fun r => atBool (LazyOracle.run (second r.1) r.2) b)
    (fun r => expect (runLog (second r.1) (plantAll (vis' r.1) r.2)) fun o₂ =>
      cleanWeight (dropAll (extraOf O L) (vis' r.1)) o₂.2.2 * (if o₂.1 = b then 1 else 0))
    (fun r t₁ t₂ related => ?_)
  have moved := plantAll_transfer (vis' r) (fun e member =>
    storedIn_of_rel consistent related (within r e member)) related
  exact dominate _ (second r) moved (fun p => if p.1 = b then 1 else 0)
    (fun p => if p.1 = b then 1 else 0) (fun _ _ _ _ => le_rfl)

/-- **The late-installed game dominates the flagged mass**, for any `vis ⊇ vis'` inside the extra
entries, when `s₂` avoids them. -/
theorem lateInstalled_ge (O : PublicOracle FixedIndex EncIndex) (L : List (Asked FixedIndex EncIndex))
    (consistent : Consistent O L) {s₂ : LState FixedIndex EncIndex}
    (avoid : Avoid s₂ (extraOf O L)) (vis vis' : Result → List (Asked FixedIndex EncIndex))
    (visWithin : ∀ r, Within (vis r) L) (within : ∀ r, Within (vis' r) (vis r)) (b : Bool) :
    flaggedMass first second s₂ (extraOf O L) vis' b ≤ lateInstalled first second s₂ vis b := by
  unfold flaggedMass lateInstalled
  rw [← expect_runLog first s₂]
  refine expect_mono_support _ fun o member => ?_
  by_cases clean : cleanWeight (extraOf O L) o.2.2 = 0
  · rw [clean, zero_mul]
    exact zero_le
  · have noTouch := cleanWeight_eq_one clean
    have avoidEnd := avoid_runLog first s₂ avoid o member noTouch
    have visConsistent : Consistent O (vis o.1) := fun e m => consistent e (visWithin o.1 e m)
    have avoidVis : Avoid o.2.1 (extraOf O (vis o.1)) :=
      avoidEnd.mono (extraOf_le (visWithin o.1))
        fun key value h => ⟨value, extraOf_hash_some (visWithin o.1) key value h⟩
    have planted := rel_plantAll_of_avoid O (vis o.1) visConsistent o.2.1 avoidVis
    have moved := plantAll_transfer (vis' o.1) (fun e member =>
      storedIn_of_rel visConsistent planted (within o.1 e member)) planted
    refine le_trans (mul_le_of_le_one_left zero_le (cleanWeight_le_one _ _)) ?_
    refine le_trans (expect_mono _ fun o₂ => mul_le_mul' (cleanWeight_anti
      (dropAll_le_dropAll (O := O) (fun e m => visWithin o.1 e m)) o₂.2.2) le_rfl) ?_
    exact dominate _ (second o.1) moved (fun p => if p.1 = b then 1 else 0)
      (fun p => if p.1 = b then 1 else 0) (fun _ _ _ _ => le_rfl)

theorem expect_one_sub {α : Type} (p : PMF α) {f : α → ℝ≥0∞} (le : ∀ a, f a ≤ 1) :
    expect p (fun a => 1 - f a) = 1 - expect p f := by
  have split : expect p (fun a => 1 - f a) + expect p f = 1 := by
    rw [← expect_add]
    rw [show (fun a => 1 - f a + f a) = fun _ => (1 : ℝ≥0∞) from
      funext fun a => tsub_add_cancel_of_le (le a)]
    exact expect_const _ 1
  have finite : expect p f ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (expect_mono p le) (le_of_eq (expect_const p 1)))
  exact ENNReal.eq_sub_of_add_eq finite split

theorem expect_le_one {α : Type} (p : PMF α) {f : α → ℝ≥0∞} (le : ∀ a, f a ≤ 1) :
    expect p f ≤ 1 :=
  le_trans (expect_mono p le) (le_of_eq (expect_const p 1))

theorem cleanWeight_cases (H : Extra FixedIndex EncIndex) (log : List (Asked FixedIndex EncIndex)) :
    cleanWeight H log = 0 ∨ cleanWeight H log = 1 := by
  classical
  unfold cleanWeight
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The two outcomes of the flagged mass together. -/
theorem flagged_sum (s₂ : LState FixedIndex EncIndex) (H : Extra FixedIndex EncIndex)
    (vis' : Result → List (Asked FixedIndex EncIndex)) :
    flaggedMass first second s₂ H vis' true + flaggedMass first second s₂ H vis' false =
      expect (runLog first s₂) fun o => cleanWeight H o.2.2 *
        expect (runLog (second o.1) (plantAll (vis' o.1) o.2.1))
          fun o₂ => cleanWeight (dropAll H (vis' o.1)) o₂.2.2 := by
  unfold flaggedMass
  rw [← expect_add]
  congr 1
  funext o
  rw [← mul_add, ← expect_add]
  congr 2
  funext o₂
  cases o₂.1 <;> simp

/-- **The flagged total misses at most the two touch masses.** -/
theorem flagged_total_ge (s₂ : LState FixedIndex EncIndex) (H : Extra FixedIndex EncIndex)
    (vis' : Result → List (Asked FixedIndex EncIndex)) :
    1 - (flaggedMass first second s₂ H vis' true + flaggedMass first second s₂ H vis' false) ≤
      expect (runLog first s₂) (fun o => 1 - cleanWeight H o.2.2) +
        expect (runLog first s₂) (fun o =>
          expect (runLog (second o.1) (plantAll (vis' o.1) o.2.1))
            fun o₂ => 1 - cleanWeight (dropAll H (vis' o.1)) o₂.2.2) := by
  rw [flagged_sum]
  have innerLe : ∀ o : Result × LState FixedIndex EncIndex × List (Asked FixedIndex EncIndex),
      expect (runLog (second o.1) (plantAll (vis' o.1) o.2.1))
        (fun o₂ => cleanWeight (dropAll H (vis' o.1)) o₂.2.2) ≤ 1 :=
    fun o => expect_le_one _ fun o₂ => cleanWeight_le_one _ _
  have productLe : ∀ o : Result × LState FixedIndex EncIndex × List (Asked FixedIndex EncIndex),
      cleanWeight H o.2.2 * expect (runLog (second o.1) (plantAll (vis' o.1) o.2.1))
        (fun o₂ => cleanWeight (dropAll H (vis' o.1)) o₂.2.2) ≤ 1 :=
    fun o => le_trans (mul_le_mul' (cleanWeight_le_one _ _) (innerLe o)) (le_of_eq (one_mul 1))
  rw [← expect_one_sub _ productLe, ← expect_add]
  refine expect_mono _ fun o => ?_
  rw [expect_one_sub _ fun o₂ => cleanWeight_le_one _ _]
  rcases cleanWeight_cases H o.2.2 with zero | one
  · rw [zero, zero_mul, tsub_zero]
    exact le_self_add
  · rw [one, one_mul, tsub_self, zero_add]

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
