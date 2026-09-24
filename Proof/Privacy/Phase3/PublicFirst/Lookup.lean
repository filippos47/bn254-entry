/-
**Phase 3, P1d — a lazy state is its lookups.**

The library's `LazyOracle.State` stores each sparse permutation as two transposition lists in
insertion order, so two states holding the same pairs are in general different values. Everything
the adversary can observe is the eager completion (`Glue.public_run_result`), and the completion
reads a state only through its lookups:

* `completion_pred_iff` — a permutation completes a sparse permutation iff it agrees with every
  lookup;
* `blockCompletion_congr`, `pairHashCompletion_congr`, `finiteKernel_congr'`, `indexedKernel_congr'`
  — the completion kernels depend on the lookups only;
* `publicCompletion_congr` / `run_map_fst_congr` — **two lazy states with the same lookups give
  every oracle program the same result law** (`SameLookups`).
-/

import Proof.Privacy.Phase3.PublicFirst.Overlap
import Proof.Privacy.Phase3.Glue.OracleLaw

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open Cryptography GarbledCircuit
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (blockCompletion pairHashCompletion finiteKernel indexedKernel
  publicCompletion public_run_result uniform_equiv)
open scoped ENNReal

noncomputable section

/-! ### One sparse permutation -/

/-- A permutation completes a sparse permutation iff it agrees with every lookup. -/
theorem completion_pred_iff {size : ℕ} (state : SparsePermutation size) (π : Equiv.Perm (Fin size)) :
    (∀ x : {x : Fin size // state.knownInput x}, π x = state.assignment x) ↔
      ∀ x y, LazyOracle.permutationLookup state x = some y → π x = y := by
  constructor
  · intro compatible x y found
    unfold LazyOracle.permutationLookup at found
    split at found
    · rename_i known
      cases found
      exact compatible ⟨x, known⟩
    · cases found
  · intro agree x
    apply agree
    unfold LazyOracle.permutationLookup
    rw [if_pos x.property]
    rfl

/-- The completion of a sparse permutation depends on its lookups only. -/
theorem blockCompletion_congr {first second : SparsePermutation (2 ^ 128)}
    (same : ∀ x, LazyOracle.permutationLookup first x = LazyOracle.permutationLookup second x) :
    blockCompletion first = blockCompletion second := by
  classical
  let equiv : first.Completion ≃ second.Completion :=
    { toFun := fun π => ⟨π.val, (completion_pred_iff second π.val).mpr fun x y found =>
          (completion_pred_iff first π.val).mp π.property x y ((same x).trans found)⟩
      invFun := fun π => ⟨π.val, (completion_pred_iff first π.val).mpr fun x y found =>
          (completion_pred_iff second π.val).mp π.property x y ((same x).symm.trans found)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold blockCompletion
  rw [← uniform_equiv equiv, PMF.map_comp]
  rfl

/-- The completion of a hash table depends on its lookups only. -/
theorem pairHashCompletion_congr {first second : HashTable BN254.BaseField
    Kriterion.ArgoMAC.Phase3.Glue.hashSize}
    (same : ∀ key, first.lookup key = second.lookup key) :
    pairHashCompletion first = pairHashCompletion second := by
  classical
  let equiv : first.Completion ≃ second.Completion :=
    { toFun := fun f => ⟨f.val, fun key value found => f.property key value ((same key).trans found)⟩
      invFun := fun f => ⟨f.val, fun key value found =>
          f.property key value ((same key).symm.trans found)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold pairHashCompletion
  rw [← uniform_equiv equiv, PMF.map_comp]
  rfl

/-- A family kernel depends on the local kernels' values only. -/
theorem finiteKernel_congr' {Sparse Eager : Type} (kernel : Sparse → PMF Eager) :
    {count : ℕ} → (first second : Fin count → Sparse) →
      (∀ index, kernel (first index) = kernel (second index)) →
        finiteKernel kernel first = finiteKernel kernel second
  | 0, _, _, _ => rfl
  | count + 1, first, second, same => by
      unfold finiteKernel
      rw [same 0, finiteKernel_congr' kernel (Fin.tail first) (Fin.tail second)
        fun index => same index.succ]

theorem indexedKernel_congr' {Index Sparse Eager : Type} [Fintype Index]
    (kernel : Sparse → PMF Eager) (first second : Index → Sparse)
    (same : ∀ index, kernel (first index) = kernel (second index)) :
    indexedKernel kernel first = indexedKernel kernel second := by
  unfold indexedKernel
  rw [finiteKernel_congr' kernel _ _ fun index => same _]

/-! ### Whole states -/

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- Two lazy states answer every lookup alike. -/
def SameLookups (first second : LazyOracle.State FixedIndex EncIndex) : Prop :=
  ∀ request : PublicQuery FixedIndex EncIndex,
    LazyOracle.lookup request first = LazyOracle.lookup request second

theorem SameLookups.refl (state : LazyOracle.State FixedIndex EncIndex) : SameLookups state state :=
  fun _ => rfl

theorem SameLookups.symm {first second : LazyOracle.State FixedIndex EncIndex}
    (same : SameLookups first second) : SameLookups second first := fun request => (same request).symm

theorem SameLookups.trans {first second third : LazyOracle.State FixedIndex EncIndex}
    (one : SameLookups first second) (two : SameLookups second third) : SameLookups first third :=
  fun request => (one request).trans (two request)

theorem ofFin_map_injective {first second : Option (Fin (2 ^ 128))}
    (same : first.map BitVec.ofFin = second.map BitVec.ofFin) : first = second := by
  cases first <;> cases second <;> simp_all

/-- Forward lookups of a sparse permutation, read off the state's lookups. -/
theorem SameLookups.fixed {first second : LazyOracle.State FixedIndex EncIndex}
    (same : SameLookups first second) (index : FixedIndex) (x : Fin (2 ^ 128)) :
    LazyOracle.permutationLookup (first.fixed index) x
      = LazyOracle.permutationLookup (second.fixed index) x := by
  have lookup := same (.fixedForward index (BitVec.ofFin x))
  simp only [LazyOracle.lookup] at lookup
  exact ofFin_map_injective lookup

theorem SameLookups.enc {first second : LazyOracle.State FixedIndex EncIndex}
    (same : SameLookups first second) (index : EncIndex) (x : Fin (2 ^ 128)) :
    LazyOracle.permutationLookup (first.enc index) x
      = LazyOracle.permutationLookup (second.enc index) x := by
  have lookup := same (.encForward index (BitVec.ofFin x))
  simp only [LazyOracle.lookup] at lookup
  exact ofFin_map_injective lookup

theorem SameLookups.hash {first second : LazyOracle.State FixedIndex EncIndex}
    (same : SameLookups first second) (key : BN254.BaseField) :
    first.hash.lookup key = second.hash.lookup key := by
  have lookup := same (.hash key)
  simp only [LazyOracle.lookup] at lookup
  exact Option.map_injective (Equiv.injective _) lookup

variable [Fintype FixedIndex] [Fintype EncIndex]

/-- **The completion depends on the lookups only.** -/
theorem publicCompletion_congr {first second : LazyOracle.State FixedIndex EncIndex}
    (same : SameLookups first second) : publicCompletion first = publicCompletion second := by
  unfold publicCompletion
  rw [indexedKernel_congr' blockCompletion first.fixed second.fixed
      (fun index => blockCompletion_congr (same.fixed index)),
    indexedKernel_congr' blockCompletion first.enc second.enc
      (fun index => blockCompletion_congr (same.enc index)),
    pairHashCompletion_congr same.hash]

/-- **Two states with the same lookups give every program the same result law.** -/
theorem run_map_fst_congr {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    {first second : LazyOracle.State FixedIndex EncIndex} (same : SameLookups first second) :
    (LazyOracle.run program first).map Prod.fst = (LazyOracle.run program second).map Prod.fst := by
  rw [← public_run_result, ← public_run_result, publicCompletion_congr same]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
