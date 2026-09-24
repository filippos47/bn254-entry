/-
**Phase 3, P1d — a sparse permutation through its lookups.**

The library's `SparsePermutation` stores its pairs as two transposition lists; the planting argument
reasons about the lookup map it represents, `LazyOracle.permutationLookup`:

* `lookup_extend` — a fresh pair (unknown input, unknown output) updates the lookup at one point;
* `knownOutput_iff` / `knownInput_iff` — the known outputs are the lookup's range;
* `forward_fresh_eq` — a fresh forward query is a uniform unknown output, recorded by `extend`
  (`SparsePermutation.unusedOutput_uniform`);
* `lookup_reverse` — the reversed state's lookup is the inverse lookup map.
-/

import Proof.Privacy.Phase3.PublicFirst.Lookup

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open Cryptography
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

variable {size : ℕ}

theorem input_apply_extend (state : SparsePermutation size) (room : state.used < size)
    (p q a : Fin size) :
    (state.extend room p q).input a = state.input (Equiv.swap ⟨state.used, room⟩ p a) := rfl

theorem output_apply_extend (state : SparsePermutation size) (room : state.used < size)
    (p q a : Fin size) :
    (state.extend room p q).output a = state.output (Equiv.swap ⟨state.used, room⟩ q a) := rfl

theorem input_symm_extend (state : SparsePermutation size) (room : state.used < size)
    (p q z : Fin size) :
    (state.extend room p q).input.symm z = Equiv.swap ⟨state.used, room⟩ p (state.input.symm z) := by
  apply (state.extend room p q).input.injective
  rw [Equiv.apply_symm_apply, input_apply_extend, Equiv.swap_apply_self, Equiv.apply_symm_apply]

theorem output_symm_extend (state : SparsePermutation size) (room : state.used < size)
    (p q z : Fin size) :
    (state.extend room p q).output.symm z = Equiv.swap ⟨state.used, room⟩ q (state.output.symm z) := by
  apply (state.extend room p q).output.injective
  rw [Equiv.apply_symm_apply, output_apply_extend, Equiv.swap_apply_self, Equiv.apply_symm_apply]

theorem extend_used (state : SparsePermutation size) (room : state.used < size) (p q : Fin size) :
    (state.extend room p q).used = state.used + 1 := rfl

/-- The lookup of a state. -/
abbrev lk (state : SparsePermutation size) (x : Fin size) : Option (Fin size) :=
  LazyOracle.permutationLookup state x

theorem lk_eq (state : SparsePermutation size) (x : Fin size) :
    lk state x = if state.knownInput x then some (state.output (state.input.symm x)) else none := rfl

theorem knownInput_iff (state : SparsePermutation size) (x : Fin size) :
    state.knownInput x ↔ lk state x ≠ none := by
  rw [lk_eq]
  split <;> simp_all

/-- The known outputs are the range of the lookup. -/
theorem knownOutput_iff (state : SparsePermutation size) (y : Fin size) :
    state.knownOutput y ↔ ∃ x, lk state x = some y := by
  constructor
  · intro known
    refine ⟨state.input (state.output.symm y), ?_⟩
    rw [lk_eq, if_pos (by
      show (state.input.symm (state.input (state.output.symm y))).val < state.used
      rw [Equiv.symm_apply_apply]
      exact known)]
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  · rintro ⟨x, found⟩
    rw [lk_eq] at found
    split at found
    · rename_i known
      cases found
      show (state.output.symm (state.output (state.input.symm x))).val < state.used
      rw [Equiv.symm_apply_apply]
      exact known
    · cases found

/-- The position bookkeeping of a fresh extension. -/
theorem extend_position (state : SparsePermutation size) (x y : Fin size)
    (freshX : ¬ state.knownInput x) (freshY : ¬ state.knownOutput y) (room : state.used < size)
    (z : Fin size) :
    let e := state.extend room (state.input.symm x) (state.output.symm y)
    (z = x → (e.input.symm z).val < state.used + 1 ∧ e.output (e.input.symm z) = y) ∧
    (z ≠ x → state.knownInput z →
      (e.input.symm z).val < state.used + 1 ∧
        e.output (e.input.symm z) = state.output (state.input.symm z)) ∧
    (z ≠ x → ¬ state.knownInput z → ¬ (e.input.symm z).val < state.used + 1) := by
  classical
  intro e
  set U : Fin size := ⟨state.used, room⟩
  set p := state.input.symm x
  set q := state.output.symm y
  have pFresh : state.used ≤ p.val := Nat.le_of_not_gt freshX
  have qFresh : state.used ≤ q.val := Nat.le_of_not_gt freshY
  have symmEq : e.input.symm z = Equiv.swap U p (state.input.symm z) :=
    input_symm_extend state room p q z
  refine ⟨fun same => ?_, fun same old => ?_, fun same notOld => ?_⟩
  · subst same
    rw [symmEq]
    show (Equiv.swap U p p).val < state.used + 1 ∧
      state.output (Equiv.swap U q (Equiv.swap U p p)) = y
    rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
    exact ⟨by show state.used < state.used + 1; omega, Equiv.apply_symm_apply _ _⟩
  · have oldVal : (state.input.symm z).val < state.used := old
    have rp : state.input.symm z ≠ p := fun equal => same (state.input.symm.injective equal)
    have rU : state.input.symm z ≠ U := fun equal => by
      have := congrArg Fin.val equal
      simp [U] at this
      omega
    have rq : state.input.symm z ≠ q := fun equal => by
      have := congrArg Fin.val equal
      omega
    rw [symmEq, Equiv.swap_apply_of_ne_of_ne rU rp]
    refine ⟨by omega, ?_⟩
    show state.output (Equiv.swap U q (state.input.symm z)) = state.output (state.input.symm z)
    rw [Equiv.swap_apply_of_ne_of_ne rU rq]
  · have notOldVal : ¬ (state.input.symm z).val < state.used := notOld
    have rp : state.input.symm z ≠ p := fun equal => same (state.input.symm.injective equal)
    rw [symmEq]
    by_cases atU : state.input.symm z = U
    · rw [atU, Equiv.swap_apply_left]
      have pU : p ≠ U := fun equal => rp (atU.trans equal.symm)
      have pVal : p.val ≠ state.used := fun h => pU (Fin.ext h)
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne atU rp]
      have rVal : (state.input.symm z).val ≠ state.used := fun h => atU (Fin.ext h)
      omega

/-- **A fresh pair updates the lookup at one point.** -/
theorem lookup_extend (state : SparsePermutation size) (x y : Fin size)
    (freshX : ¬ state.knownInput x) (freshY : ¬ state.knownOutput y) (room : state.used < size)
    (z : Fin size) :
    lk (state.extend room (state.input.symm x) (state.output.symm y)) z
      = if z = x then some y else lk state z := by
  classical
  obtain ⟨atX, atOld, atNew⟩ := extend_position state x y freshX freshY room z
  have knownEq (w : Fin size) : (state.extend room (state.input.symm x)
      (state.output.symm y)).knownInput w ↔
      ((state.extend room (state.input.symm x) (state.output.symm y)).input.symm w).val
        < state.used + 1 := Iff.rfl
  rw [lk_eq, lk_eq]
  by_cases same : z = x
  · obtain ⟨known, value⟩ := atX same
    rw [if_pos ((knownEq z).mpr known), if_pos same, value]
  · rw [if_neg same]
    by_cases old : state.knownInput z
    · obtain ⟨known, value⟩ := atOld same old
      rw [if_pos ((knownEq z).mpr known), if_pos old, value]
    · rw [if_neg (fun known => atNew same old ((knownEq z).mp known)), if_neg old]

/-- The unknown outputs of a state. -/
abbrev Unknown (state : SparsePermutation size) := {y : Fin size // ¬ state.knownOutput y}

/-- **A fresh forward query is a uniform unknown output, recorded by `extend`.** -/
theorem forward_fresh_eq (state : SparsePermutation size) (x : Fin size)
    (fresh : ¬ state.knownInput x) :
    ∃ (room : state.used < size) (_ : Nonempty (Unknown state)),
      (state.forward x).distribution =
        (PMF.uniformOfFintype (Unknown state)).map fun y =>
          (y.val, state.extend room (state.input.symm x) (state.output.symm y.val)) := by
  have room : state.used < size := by
    have := (state.input.symm x).isLt
    unfold SparsePermutation.knownInput at fresh
    omega
  haveI : Nonempty (Fin (size - state.used)) := ⟨⟨0, by omega⟩⟩
  haveI nonempty : Nonempty (Unknown state) := ⟨state.unusedOutputEquiv ⟨0, by omega⟩⟩
  refine ⟨room, nonempty, ?_⟩
  rw [← state.unusedOutput_uniform room, PMF.map_comp]
  unfold SparsePermutation.forward
  simp only [SparsePermutation.knownInput] at fresh
  rw [dif_neg fresh]
  simp only [Draw.distribution]
  congr 1
  funext rank
  simp only [Function.comp_apply, SparsePermutation.unusedOutputEquiv, Equiv.coe_fn_mk,
    Equiv.symm_apply_apply]

/-- The reversed state's lookup is the inverse lookup map. -/
theorem lookup_reverse (state : SparsePermutation size) (x y : Fin size) :
    lk state.reverse y = some x ↔ lk state x = some y := by
  rw [lk_eq, lk_eq]
  simp only [SparsePermutation.knownInput]
  show (if (state.output.symm y).val < state.used then some (state.input (state.output.symm y))
      else none) = some x ↔
    (if (state.input.symm x).val < state.used then some (state.output (state.input.symm x))
      else none) = some y
  constructor
  · intro found
    split at found
    · rename_i known
      cases found
      rw [Equiv.symm_apply_apply, if_pos known, Equiv.apply_symm_apply]
    · cases found
  · intro found
    split at found
    · rename_i known
      cases found
      rw [Equiv.symm_apply_apply, if_pos known, Equiv.apply_symm_apply]
    · cases found

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
