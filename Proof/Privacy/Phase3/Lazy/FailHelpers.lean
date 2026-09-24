/-
**Phase 3, P4b — counting helpers for the per-prefix failure bound.**

* `sum_knownInput_xor`: a sparse permutation with `n` entries has exactly `n` known inputs, also
  after an XOR shift of the argument.
* `sum_stored_xor`: an input family has `hashCount` stored inputs, also after an XOR shift of the
  label.
* `forwardAnswer_sum_le`: at a label fresh at the index, the answer of a lazy forward query has
  point masses at most `1/(2^128 − used)`, so it charges any observable of the answer that much
  per unit of its total.
-/

import Proof.Privacy.Phase3.Lazy.Decompose

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### Counting known entries -/

/-- `#{y : Fin N | y < u} = u` for `u ≤ N`. -/
theorem sum_fin_lt (N u : ℕ) (small : u ≤ N) :
    ∑ y : Fin N, (if y.val < u then (1 : ℝ≥0∞) else 0) = u := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < u then (1 : ℝ≥0∞) else 0) N,
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have filtered : (Finset.range N).filter (fun k => k < u) = Finset.range u := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [filtered, Finset.card_range]

/-- A permutation of `Fin N` preserves the count of a predicate on values below `u`. -/
theorem sum_perm_lt (N u : ℕ) (small : u ≤ N) (perm : Equiv.Perm (Fin N)) :
    ∑ x : Fin N, (if (perm x).val < u then (1 : ℝ≥0∞) else 0) = u := by
  rw [Equiv.sum_comp perm (fun y : Fin N => if y.val < u then (1 : ℝ≥0∞) else 0)]
  exact sum_fin_lt N u small

/-- `a ↦ (c xor a).toFin` is a bijection `Block ≃ Fin (2^128)`. -/
def xorFinEquiv (c : Block) : Block ≃ Fin (2 ^ 128) where
  toFun a := (c ^^^ a).toFin
  invFun y := c ^^^ BitVec.ofFin y
  left_inv a := by
    show c ^^^ BitVec.ofFin (c ^^^ a).toFin = a
    rw [BitVec.ofFin_toFin, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  right_inv y := by
    show (c ^^^ (c ^^^ BitVec.ofFin y)).toFin = y
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- **A sparse permutation with `n` entries has `n` known inputs**, after any XOR shift. -/
theorem sum_knownInput_xor (state : SparsePermutation (2 ^ 128)) (c : Block) :
    ∑' a : Block, (if state.knownInput (c ^^^ a).toFin then (1 : ℝ≥0∞) else 0) = state.used := by
  rw [tsum_fintype]
  rw [Fintype.sum_equiv (xorFinEquiv c) (fun a => if state.knownInput (c ^^^ a).toFin then
      (1 : ℝ≥0∞) else 0) (fun y => if state.knownInput y then (1 : ℝ≥0∞) else 0) (fun a => rfl)]
  exact sum_perm_lt _ _ state.within state.input.symm

section Stored

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **An input family has `hashCount` stored inputs**, after any XOR shift of the label. -/
theorem sum_stored_xor (family : Block → BaseField) (c : Block) (oracle : LState) :
    ∑' a : Block, (if oracle.hash.lookup (family (c ^^^ a)) ≠ none then (1 : ℝ≥0∞) else 0) =
      hashCount family oracle := by
  classical
  rw [tsum_fintype]
  rw [Fintype.sum_equiv (xorEquiv c) (fun a => if oracle.hash.lookup (family (c ^^^ a)) ≠ none then
      (1 : ℝ≥0∞) else 0) (fun b => if oracle.hash.lookup (family b) ≠ none then (1 : ℝ≥0∞) else 0)
      (fun a => by simp only [xorEquiv, Equiv.coe_fn_mk, BitVec.xor_comm a c])]
  rw [Finset.sum_boole]
  rfl

end Stored

/-! ### A fresh forward answer charges `1/(2^128 − used)` -/

/-- The charge of one fresh answer at a sparse permutation. -/
def freshCharge (state : SparsePermutation (2 ^ 128)) : ℝ≥0∞ :=
  (((2 ^ 128 - state.used : ℕ) : ℝ≥0∞))⁻¹

section Fresh

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **At a fresh label, the answer's law charges `freshCharge` per unit of an observable of the
answer.** -/
theorem forwardAnswer_sum_le (index : FixedIndex) (label : Block) (oracle : LState)
    (fresh : ¬ (oracle.fixed index).knownInput label.toFin) (f : Block → ℝ≥0∞) :
    ∑' answer, (forwardAnswer index label oracle) answer * f answer.1 ≤
      freshCharge (oracle.fixed index) * ∑' a, f a := by
  rw [← tsum_map_mul, forwardAnswer_fst, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_right ?_ zero_le
  rw [fresh_answer_apply _ _ fresh]
  split
  · exact zero_le
  · exact le_rfl

/-- A forward query does not change the EncPRF and hash parts. -/
theorem forwardAnswer_encHash (index : FixedIndex) (label : Block) (oracle : LState)
    (answer : Block × LState) (member : answer ∈ (forwardAnswer index label oracle).support) :
    answer.2.enc = oracle.enc ∧ answer.2.hash = oracle.hash := by
  unfold forwardAnswer at member
  simp only [LazyOracle.query] at member
  obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  exact ⟨rfl, rfl⟩

end Fresh

/-! ### Union bounds -/

theorem indicator_exists_le {γ : Type} [Fintype γ] (P : γ → Prop) [DecidablePred P]
    [Decidable (∃ t, P t)] :
    (if ∃ t, P t then (1 : ℝ≥0∞) else 0) ≤ ∑ t, if P t then (1 : ℝ≥0∞) else 0 := by
  split
  · rename_i found
    obtain ⟨t, holds⟩ := found
    calc (1 : ℝ≥0∞) = if P t then 1 else 0 := by rw [if_pos holds]
      _ ≤ ∑ t, if P t then (1 : ℝ≥0∞) else 0 :=
        Finset.single_le_sum (f := fun t => if P t then (1 : ℝ≥0∞) else 0)
          (fun _ _ => zero_le) (Finset.mem_univ t)
  · exact zero_le

end

end Kriterion.ArgoMAC.Phase3.Lazy
