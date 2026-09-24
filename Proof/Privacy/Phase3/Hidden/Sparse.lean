/-
**Phase 3, P1c — the lazy oracle's sparse permutations, read semantically.**

A `SparsePermutation` stores its known pairs as two lists of transpositions; two states with the
same known pairs behave identically. This module reads a state through its lookup
(`LazyOracle.permutationLookup`) and proves the three facts the identical-until-touched lemma
(`Hidden/Relation.lean`) needs:

* `knownInput_iff`, `knownOutput_iff`: an input (output) is known iff some stored pair has it;
* `look_extend`: a fresh extension adds exactly its pair;
* `forward_fresh_expect`: a forward query at a fresh input is uniform on the unused outputs, and
  records exactly the answered pair.

`SparseExtra s₁ s₂ E` says that `s₁` is `s₂` together with the extra pairs `E`, fresh in both
coordinates. `SparseExtra.forward_dominate` is the one-query step of the lemma: off the touch of
`E` (the query's input is an extra input, or its fresh answer is an extra output), the query law of
`s₂` is dominated by that of `s₁`, and the two updated states are again related.
-/

import Cryptography.LazyOracle

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open Kriterion.Cryptography
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### Expectations -/

/-- The expectation of a nonnegative function under a law. -/
def expect {α : Type} (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * f a

theorem expect_pure {α : Type} (a : α) (f : α → ℝ≥0∞) : expect (PMF.pure a) f = f a := by
  unfold expect
  rw [tsum_eq_single a]
  · simp
  · intro b hb
    simp [PMF.pure_apply, hb]

theorem expect_bind {α β : Type} (p : PMF α) (q : α → PMF β) (f : β → ℝ≥0∞) :
    expect (p.bind q) f = expect p (fun a => expect (q a) f) := by
  unfold expect
  simp only [PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right, mul_assoc, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

theorem expect_map {α β : Type} (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    expect (p.map g) f = expect p (fun a => f (g a)) := by
  rw [PMF.map, expect_bind]
  simp only [Function.comp_apply, expect_pure]

theorem expect_mono {α : Type} (p : PMF α) {f g : α → ℝ≥0∞} (le : ∀ a, f a ≤ g a) :
    expect p f ≤ expect p g :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (le a)

theorem expect_mono_support {α : Type} (p : PMF α) {f g : α → ℝ≥0∞}
    (le : ∀ a ∈ p.support, f a ≤ g a) : expect p f ≤ expect p g := by
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases zero : p a = 0
  · rw [zero, zero_mul, zero_mul]
  · exact mul_le_mul' le_rfl (le a ((PMF.mem_support_iff _ _).mpr zero))

theorem expect_add {α : Type} (p : PMF α) (f g : α → ℝ≥0∞) :
    expect p (fun a => f a + g a) = expect p f + expect p g := by
  unfold expect
  simp_rw [mul_add]
  exact ENNReal.tsum_add

theorem expect_const {α : Type} (p : PMF α) (c : ℝ≥0∞) : expect p (fun _ => c) = c := by
  unfold expect
  rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem expect_const_mul {α : Type} (p : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    expect p (fun a => c * f a) = c * expect p f := by
  unfold expect
  simp_rw [← mul_assoc, mul_comm (p _) c, mul_assoc]
  exact ENNReal.tsum_mul_left

theorem expect_uniform {α : Type} [Fintype α] [Nonempty α] (f : α → ℝ≥0∞) :
    expect (PMF.uniformOfFintype α) f = (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ a, f a := by
  unfold expect
  rw [tsum_fintype, Finset.mul_sum]
  simp only [PMF.uniformOfFintype_apply]

/-! ### Reading a sparse permutation through its lookup -/

section Sparse

variable {n : ℕ}

/-- The stored answer at an input. -/
abbrev look (s : SparsePermutation n) (x : Fin n) : Option (Fin n) :=
  LazyOracle.permutationLookup s x

theorem look_eq_some {s : SparsePermutation n} {x y : Fin n} :
    look s x = some y ↔ s.knownInput x ∧ s.output (s.input.symm x) = y := by
  unfold look LazyOracle.permutationLookup
  split
  · rename_i known
    simp [known]
  · rename_i unknown
    simp [unknown]

theorem look_eq_none {s : SparsePermutation n} {x : Fin n} :
    look s x = none ↔ ¬ s.knownInput x := by
  unfold look LazyOracle.permutationLookup
  split <;> simp_all

theorem knownInput_iff {s : SparsePermutation n} {x : Fin n} :
    s.knownInput x ↔ ∃ y, look s x = some y := by
  constructor
  · intro known
    exact ⟨_, look_eq_some.mpr ⟨known, rfl⟩⟩
  · rintro ⟨y, found⟩
    exact (look_eq_some.mp found).1

theorem knownOutput_iff {s : SparsePermutation n} {y : Fin n} :
    s.knownOutput y ↔ ∃ x, look s x = some y := by
  constructor
  · intro known
    refine ⟨s.input (s.output.symm y), look_eq_some.mpr ⟨?_, ?_⟩⟩
    · show (s.input.symm (s.input (s.output.symm y))).val < s.used
      rw [Equiv.symm_apply_apply]
      exact known
    · rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  · rintro ⟨x, found⟩
    obtain ⟨known, same⟩ := look_eq_some.mp found
    show (s.output.symm y).val < s.used
    rw [← same, Equiv.symm_apply_apply]
    exact known

/-- The stored pairs are injective on the known inputs. -/
theorem look_injective {s : SparsePermutation n} {x x' y : Fin n} (first : look s x = some y)
    (second : look s x' = some y) : x = x' := by
  obtain ⟨_, same⟩ := look_eq_some.mp first
  obtain ⟨_, same'⟩ := look_eq_some.mp second
  have : s.input.symm x = s.input.symm x' := s.output.injective (same.trans same'.symm)
  exact s.input.symm.injective this

/-- The number of known outputs is `used`. -/
theorem card_knownOutput (s : SparsePermutation n) :
    Fintype.card {y : Fin n // s.knownOutput y} = s.used := by
  have shift : {y : Fin n // s.knownOutput y} ≃ {position : Fin n // position < s.used} :=
    Equiv.subtypeEquiv s.output.symm fun _ => Iff.rfl
  rw [Fintype.card_congr shift, Fintype.card_fin_lt_of_le s.within]

theorem room_of_fresh {s : SparsePermutation n} {x : Fin n} (fresh : ¬ s.knownInput x) :
    s.used < n := by
  have := (s.input.symm x).isLt
  unfold SparsePermutation.knownInput at fresh
  omega

theorem extend_input_symm (s : SparsePermutation n) (room : s.used < n) (ip op z : Fin n) :
    (s.extend room ip op).input.symm z = Equiv.swap ⟨s.used, room⟩ ip (s.input.symm z) := by
  show ((Equiv.swap (⟨s.used, room⟩ : Fin n) ip).trans (swaps s.inputs)).symm z = _
  rw [Equiv.symm_trans_apply, Equiv.symm_swap]
  rfl

theorem extend_output_apply (s : SparsePermutation n) (room : s.used < n) (ip op q : Fin n) :
    (s.extend room ip op).output q = s.output (Equiv.swap ⟨s.used, room⟩ op q) := rfl

/-- The state after answering a fresh `x` with a fresh `y`. -/
def extendPair (s : SparsePermutation n) (room : s.used < n) (x y : Fin n) : SparsePermutation n :=
  s.extend room (s.input.symm x) (s.output.symm y)

theorem look_of_known {s : SparsePermutation n} {z : Fin n} (known : s.knownInput z) :
    look s z = some (s.output (s.input.symm z)) :=
  look_eq_some.mpr ⟨known, rfl⟩

theorem look_of_unknown {s : SparsePermutation n} {z : Fin n} (unknown : ¬ s.knownInput z) :
    look s z = none :=
  look_eq_none.mpr unknown

/-- **A fresh extension adds exactly its pair.** -/
theorem look_extend (s : SparsePermutation n) (room : s.used < n) {x y : Fin n}
    (freshX : ¬ s.knownInput x) (freshY : ¬ s.knownOutput y) (z : Fin n) :
    look (extendPair s room x y) z = if z = x then some y else look s z := by
  have ipFresh : ¬ (s.input.symm x).val < s.used := freshX
  have opFresh : ¬ (s.output.symm y).val < s.used := freshY
  set u : Fin n := ⟨s.used, room⟩ with hu
  have extUsed : (extendPair s room x y).used = s.used + 1 := rfl
  have extIn : ∀ w, (extendPair s room x y).input.symm w = Equiv.swap u (s.input.symm x)
      (s.input.symm w) := fun w => extend_input_symm s room _ _ w
  have extOut : ∀ q, (extendPair s room x y).output q = s.output (Equiv.swap u (s.output.symm y) q) :=
    fun q => extend_output_apply s room _ _ q
  have knownExt : ∀ w, (extendPair s room x y).knownInput w ↔
      (Equiv.swap u (s.input.symm x) (s.input.symm w)).val < s.used + 1 := by
    intro w
    show ((extendPair s room x y).input.symm w).val < (extendPair s room x y).used ↔ _
    rw [extIn, extUsed]
  by_cases same : z = x
  · subst same
    rw [if_pos rfl]
    have known : (extendPair s room z y).knownInput z := by
      rw [knownExt, Equiv.swap_apply_right]
      show s.used < s.used + 1
      omega
    rw [look_of_known known, extIn, Equiv.swap_apply_right, extOut, Equiv.swap_apply_left,
      Equiv.apply_symm_apply]
  · rw [if_neg same]
    have pNe : s.input.symm z ≠ s.input.symm x := fun h => same (s.input.symm.injective h)
    by_cases atU : s.input.symm z = u
    · have ipNe : s.input.symm x ≠ u := fun h => pNe (atU.trans h.symm)
      have ipVal : (s.input.symm x).val ≠ s.used := fun h => ipNe (Fin.ext h)
      have unknownExt : ¬ (extendPair s room x y).knownInput z := by
        rw [knownExt, atU, Equiv.swap_apply_left]
        omega
      have unknownOld : ¬ s.knownInput z := by
        show ¬ (s.input.symm z).val < s.used
        rw [atU]
        show ¬ s.used < s.used
        omega
      rw [look_of_unknown unknownExt, look_of_unknown unknownOld]
    · have valNe : (s.input.symm z).val ≠ s.used := fun h => atU (Fin.ext h)
      have fixes : Equiv.swap u (s.input.symm x) (s.input.symm z) = s.input.symm z :=
        Equiv.swap_apply_of_ne_of_ne atU pNe
      by_cases old : s.knownInput z
      · have oldVal : (s.input.symm z).val < s.used := old
        have knownE : (extendPair s room x y).knownInput z := by
          rw [knownExt, fixes]
          omega
        have opNe : s.input.symm z ≠ s.output.symm y := by
          intro h
          rw [h] at oldVal
          exact opFresh oldVal
        rw [look_of_known knownE, look_of_known old, extIn, fixes, extOut,
          Equiv.swap_apply_of_ne_of_ne atU opNe]
      · have oldVal : ¬ (s.input.symm z).val < s.used := old
        have unknownE : ¬ (extendPair s room x y).knownInput z := by
          rw [knownExt, fixes]
          omega
        rw [look_of_unknown unknownE, look_of_unknown old]

/-- A forward query at a known input returns the stored answer and keeps the state. -/
theorem forward_known (s : SparsePermutation n) {x y : Fin n} (found : look s x = some y) :
    (s.forward x).distribution = PMF.pure (y, s) := by
  rw [LazyOracle.lookup_forward s x y found]
  rfl

/-- **A forward query at a fresh input**: uniform on the unused outputs, recording that pair. -/
theorem forward_fresh_expect (s : SparsePermutation n) {x : Fin n} (fresh : ¬ s.knownInput x)
    (f : Fin n × SparsePermutation n → ℝ≥0∞) :
    expect (s.forward x).distribution f =
      (Fintype.card {y : Fin n // ¬ s.knownOutput y} : ℝ≥0∞)⁻¹ *
        ∑ y : {y : Fin n // ¬ s.knownOutput y}, f (y.1, extendPair s (room_of_fresh fresh) x y.1) := by
  have room := room_of_fresh fresh
  have unknown : ¬ (s.input.symm x).val < s.used := fresh
  have : Nonempty (Fin (n - s.used)) := ⟨⟨0, by omega⟩⟩
  have : Nonempty {y : Fin n // ¬ s.knownOutput y} := ⟨s.unusedOutputEquiv ⟨0, by omega⟩⟩
  have law : (s.forward x).distribution =
      (PMF.uniformOfFintype {y : Fin n // ¬ s.knownOutput y}).map
        (fun y => (y.1, extendPair s room x y.1)) := by
    rw [← s.unusedOutput_uniform room, PMF.map_comp]
    unfold SparsePermutation.forward
    simp only [dif_neg unknown, Draw.distribution]
    congr 1
    funext rank
    simp only [Function.comp_apply, SparsePermutation.unusedOutputEquiv, Equiv.coe_fn_mk,
      extendPair, Equiv.symm_apply_apply]
  rw [law, expect_map, expect_uniform]

/-! ### Extra pairs -/

/-- **`s₁` is `s₂` together with the extra pairs `E`**, which are fresh in `s₂` in both
coordinates. -/
structure SparseExtra (s₁ s₂ : SparsePermutation n) (E : Fin n → Fin n → Prop) : Prop where
  look_iff : ∀ x y, look s₁ x = some y ↔ look s₂ x = some y ∨ E x y
  freshIn : ∀ x y, E x y → look s₂ x = none
  freshOut : ∀ x y, E x y → ∀ x', look s₂ x' ≠ some y

/-- The touch of the extra pairs by a forward query `x ↦ a`. -/
def ForwardTouch (E : Fin n → Fin n → Prop) (x a : Fin n) : Prop :=
  (∃ y, E x y) ∨ (∃ x', E x' a)

theorem SparseExtra.known_of_known {s₁ s₂ : SparsePermutation n} {E : Fin n → Fin n → Prop}
    (rel : SparseExtra s₁ s₂ E) {x y : Fin n} (found : look s₂ x = some y) :
    look s₁ x = some y :=
  (rel.look_iff x y).mpr (Or.inl found)

/-- An output is unused in `s₁` iff it is unused in `s₂` and not an extra output. -/
theorem SparseExtra.unusedOutput_iff {s₁ s₂ : SparsePermutation n} {E : Fin n → Fin n → Prop}
    (rel : SparseExtra s₁ s₂ E) (y : Fin n) :
    ¬ s₁.knownOutput y ↔ ¬ s₂.knownOutput y ∧ ¬ ∃ x', E x' y := by
  rw [knownOutput_iff, knownOutput_iff]
  constructor
  · intro unused
    refine ⟨fun ⟨x, found⟩ => unused ⟨x, rel.known_of_known found⟩,
      fun ⟨x, extra⟩ => unused ⟨x, (rel.look_iff x y).mpr (Or.inr extra)⟩⟩
  · rintro ⟨unused, notExtra⟩ ⟨x, found⟩
    rcases (rel.look_iff x y).mp found with found | extra
    · exact unused ⟨x, found⟩
    · exact notExtra ⟨x, extra⟩

theorem SparseExtra.freshInput {s₁ s₂ : SparsePermutation n} {E : Fin n → Fin n → Prop}
    (rel : SparseExtra s₁ s₂ E) {x : Fin n} (notExtra : ¬ ∃ y, E x y)
    (fresh : ¬ s₂.knownInput x) : ¬ s₁.knownInput x := by
  rw [knownInput_iff] at fresh ⊢
  rintro ⟨y, found⟩
  rcases (rel.look_iff x y).mp found with found | extra
  · exact fresh ⟨y, found⟩
  · exact notExtra ⟨y, extra⟩

/-- A shared fresh pair keeps the relation. -/
theorem SparseExtra.extend {s₁ s₂ : SparsePermutation n} {E : Fin n → Fin n → Prop}
    (rel : SparseExtra s₁ s₂ E) {x y : Fin n} (room₁ : s₁.used < n) (room₂ : s₂.used < n)
    (fresh₁ : ¬ s₁.knownInput x) (unused₁ : ¬ s₁.knownOutput y)
    (fresh₂ : ¬ s₂.knownInput x) (unused₂ : ¬ s₂.knownOutput y) :
    SparseExtra (extendPair s₁ room₁ x y) (extendPair s₂ room₂ x y) E := by
  have notExtraIn : ¬ ∃ y', E x y' := fun ⟨y', extra⟩ =>
    fresh₁ (knownInput_iff.mpr ⟨y', (rel.look_iff x y').mpr (Or.inr extra)⟩)
  have notExtraOut : ¬ ∃ x', E x' y := ((rel.unusedOutput_iff y).mp unused₁).2
  refine ⟨fun z w => ?_, fun z w extra => ?_, fun z w extra z' => ?_⟩
  · rw [look_extend s₁ room₁ fresh₁ unused₁, look_extend s₂ room₂ fresh₂ unused₂]
    by_cases same : z = x
    · subst same
      rw [if_pos rfl, if_pos rfl]
      constructor
      · exact fun h => Or.inl h
      · rintro (h | extra)
        · exact h
        · exact (notExtraIn ⟨w, extra⟩).elim
    · simp only [if_neg same]
      exact rel.look_iff z w
  · rw [look_extend s₂ room₂ fresh₂ unused₂]
    have ne : z ≠ x := fun same => notExtraIn ⟨w, same ▸ extra⟩
    rw [if_neg ne]
    exact rel.freshIn z w extra
  · rw [look_extend s₂ room₂ fresh₂ unused₂]
    split
    · intro h
      cases h
      exact notExtraOut ⟨z, extra⟩
    · exact rel.freshOut z w extra z'

/-- **One forward query, off the touch.** If `s₁` is `s₂` with the extra pairs `E`, then the
forward law of `s₂`, killed where it touches `E`, is dominated by the forward law of `s₁`, for any
two continuations ordered on related states. -/
theorem SparseExtra.forward_dominate {s₁ s₂ : SparsePermutation n} {E : Fin n → Fin n → Prop}
    (rel : SparseExtra s₁ s₂ E) (x : Fin n)
    (F G : Fin n × SparsePermutation n → ℝ≥0∞)
    (ordered : ∀ y t₁ t₂, SparseExtra t₁ t₂ E → G (y, t₂) ≤ F (y, t₁)) :
    expect (s₂.forward x).distribution
        (fun answer => by classical exact if ForwardTouch E x answer.1 then 0 else G answer) ≤
      expect (s₁.forward x).distribution F := by
  classical
  by_cases extraIn : ∃ y, E x y
  · refine le_trans (le_of_eq ?_) zero_le
    have : ∀ answer : Fin n × SparsePermutation n,
        (if ForwardTouch E x answer.1 then 0 else G answer) = 0 :=
      fun answer => if_pos (Or.inl extraIn)
    simp only [this]
    exact (expect_const _ 0)
  by_cases known : s₂.knownInput x
  · obtain ⟨y, found⟩ := knownInput_iff.mp known
    rw [forward_known s₂ found, forward_known s₁ (rel.known_of_known found), expect_pure,
      expect_pure]
    split
    · exact zero_le
    · exact ordered y s₁ s₂ rel
  · have fresh₁ := rel.freshInput extraIn known
    rw [forward_fresh_expect s₂ known, forward_fresh_expect s₁ fresh₁]
    have card : Fintype.card {y : Fin n // ¬ s₁.knownOutput y} ≤
        Fintype.card {y : Fin n // ¬ s₂.knownOutput y} :=
      Fintype.card_subtype_mono _ _ fun y unused => ((rel.unusedOutput_iff y).mp unused).1
    have cardPos : 0 < Fintype.card {y : Fin n // ¬ s₁.knownOutput y} := by
      rw [Fintype.card_subtype_compl, card_knownOutput, Fintype.card_fin]
      have := room_of_fresh fresh₁
      omega
    have inverse : (Fintype.card {y : Fin n // ¬ s₂.knownOutput y} : ℝ≥0∞)⁻¹ ≤
        (Fintype.card {y : Fin n // ¬ s₁.knownOutput y} : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr card)
    refine mul_le_mul' inverse ?_
    rw [← Finset.sum_subtype (Finset.univ.filter fun y => ¬ s₂.knownOutput y) (by simp)
        (fun y => if ForwardTouch E x y then 0 else
          G (y, extendPair s₂ (room_of_fresh known) x y)),
      ← Finset.sum_subtype (Finset.univ.filter fun y => ¬ s₁.knownOutput y) (by simp)
        (fun y => F (y, extendPair s₁ (room_of_fresh fresh₁) x y)),
      Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_le_sum fun y _ => ?_
    by_cases unused₂ : ¬ s₂.knownOutput y
    · rw [if_pos unused₂]
      by_cases touch : ForwardTouch E x y
      · rw [if_pos touch]
        exact zero_le
      · rw [if_neg touch]
        have notExtraOut : ¬ ∃ x', E x' y := fun h => touch (Or.inr h)
        have unused₁ : ¬ s₁.knownOutput y := (rel.unusedOutput_iff y).mpr ⟨unused₂, notExtraOut⟩
        rw [if_pos unused₁]
        exact ordered y _ _ (rel.extend _ _ fresh₁ unused₁ known unused₂)
    · rw [if_neg unused₂]
      exact zero_le

end Sparse

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open Kriterion.Cryptography
open Kriterion.ArgoMAC.Security.OperationalOracle

noncomputable section

variable {n : ℕ}

/-- **The support of a forward query**: a stored answer and the same state, or a fresh unused
answer and the state recording that pair. -/
theorem forward_support (s : SparsePermutation n) (x : Fin n) {y : Fin n}
    {t : SparsePermutation n} (member : (y, t) ∈ (s.forward x).distribution.support) :
    (look s x = some y ∧ t = s) ∨
      ∃ fresh : ¬ s.knownInput x, ¬ s.knownOutput y ∧ t = extendPair s (room_of_fresh fresh) x y := by
  by_cases known : s.knownInput x
  · obtain ⟨z, found⟩ := knownInput_iff.mp known
    rw [forward_known s found, PMF.support_pure] at member
    cases member
    exact Or.inl ⟨found, rfl⟩
  · right
    refine ⟨known, ?_⟩
    have unknown : ¬ (s.input.symm x).val < s.used := known
    unfold SparsePermutation.forward at member
    simp only [dif_neg unknown, Draw.distribution, PMF.support_map, Set.mem_image] at member
    obtain ⟨rank, _, same⟩ := member
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    refine ⟨?_, ?_⟩
    · show ¬ (s.output.symm (s.output (s.suffix rank))).val < s.used
      rw [Equiv.symm_apply_apply]
      simp [SparsePermutation.suffix]
    · unfold extendPair
      rw [Equiv.symm_apply_apply]

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
