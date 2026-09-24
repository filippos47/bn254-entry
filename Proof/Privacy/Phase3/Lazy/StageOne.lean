/-
**Phase 3, P4 — the adversary's first stage: its prefix average and its entries.**

* `stageOneMean` — the average over `I`'s prefix (the simulator's stage 1, then the adversary's
  first stage on the lazy oracle) of a function of the oracle state it leaves. It loses mass only to
  stage-1 aborts (`stageOne_mass_le`), so a constant averages to at most itself
  (`stageOneMean_const_le`), and it commutes with finite sums (`stageOneMean_sum`).
* `entryPotential family` — the entries at an injective family of fixed-key indices plus every hash
  entry. A lazy query adds at most one entry, at the one index it touches or to the hash table
  (`query_entryPotential_le`, from the library's `forward_used_le` / `inverse_used_le` /
  `HashTable.query_length_le`), so a run of a program with query budget `b` adds at most `b`
  (`run_entryPotential_le`). The adversary's first stage starts from the empty oracle (Plan B's
  stage 1 makes no oracle call), so it leaves at most `q₁` such entries on average
  (`stageOneMean_entryPotential_le`), and at most `q₁` at any one index (`run_used_le`).
* `hashCount` — the stored inputs of an injective input family; at most the table's length
  (`hashCount_le_length`).
-/

import Proof.Privacy.Phase3.Lazy.GameBound

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

section Mean

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **The average over `I`'s prefix** (the simulator's stage 1, then the adversary's first stage
on the lazy oracle) of a function of the oracle state it leaves. -/
def stageOneMean (adversary : PlanBAdversary Unit) (parameter : ℕ) (value : LState → ℝ≥0∞) :
    ℝ≥0∞ :=
  ∑' first, (planBAbstractSimulator idealSamplers).stage1 parameter LazyOracle.empty (some first) *
    ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter first.1 ())
      first.2.2) chosen * value chosen.2

/-- The prefix loses mass only to stage-1 aborts. -/
theorem stageOne_mass_le (parameter : ℕ) :
    (∑' first, (planBAbstractSimulator idealSamplers).stage1 parameter LazyOracle.empty
      (some first)) ≤ 1 :=
  le_trans (ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective _) _)
    (le_of_eq (PMF.tsum_coe _))

/-- **A constant averages to at most itself.** -/
theorem stageOneMean_const_le (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (constant : ℝ≥0∞) : stageOneMean adversary parameter (fun _ => constant) ≤ constant := by
  unfold stageOneMean
  simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc _ ≤ 1 * constant := by
        gcongr
        exact stageOne_mass_le parameter
    _ = constant := one_mul _

/-- A finite sum commutes with the average. -/
theorem stageOneMean_sum {Site : Type} [Fintype Site] (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (value : Site → LState → ℝ≥0∞) :
    stageOneMean adversary parameter (fun oracle => ∑ site, value site oracle) =
      ∑ site, stageOneMean adversary parameter (value site) := by
  unfold stageOneMean
  simp only [Finset.mul_sum]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun first => ?_
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp only [Finset.mul_sum]

end Mean

/-! ### Stage-1 entries -/

section Entries

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The stage-1 entries** at an injective family of fixed-key indices, plus every hash entry. -/
def entryPotential {S : Type} [Fintype S] (family : S → FixedIndex) (oracle : LState) : ℕ :=
  ∑ site, (oracle.fixed (family site)).used + oracle.hash.length

/-- Replacing one sparse permutation by one at most one entry larger raises the family's entries
by at most one: at most one site names that index. -/
theorem sum_update_used_le {S : Type} [Fintype S] (family : S → FixedIndex)
    (injective : Function.Injective family) (fixed : FixedIndex → SparsePermutation (2 ^ 128))
    (index : FixedIndex) (next : SparsePermutation (2 ^ 128))
    (grow : next.used ≤ (fixed index).used + 1) :
    ∑ site, (Function.update fixed index next (family site)).used ≤
      ∑ site, (fixed (family site)).used + 1 := by
  classical
  have termwise : ∀ site, (Function.update fixed index next (family site)).used ≤
      (fixed (family site)).used + (if family site = index then 1 else 0) := by
    intro site
    by_cases same : family site = index
    · rw [same, Function.update_self, if_pos rfl]
      exact grow
    · rw [Function.update_of_ne same, if_neg same, Nat.add_zero]
  have atMostOne : (∑ site, (if family site = index then 1 else 0 : ℕ)) ≤ 1 := by
    by_cases found : ∃ named, family named = index
    · obtain ⟨named, named_eq⟩ := found
      have reindex : ∀ site, (if family site = index then 1 else 0 : ℕ) =
          if site = named then 1 else 0 := by
        intro site
        by_cases same : site = named
        · rw [if_pos same, if_pos (same ▸ named_eq)]
        · rw [if_neg same, if_neg fun equal => same (injective (equal.trans named_eq.symm))]
      rw [Finset.sum_congr rfl fun site _ => reindex site, Finset.sum_ite_eq' Finset.univ named,
        if_pos (Finset.mem_univ _)]
    · rw [Finset.sum_eq_zero fun site _ => if_neg fun hit => found ⟨site, hit⟩]
      exact Nat.zero_le _
  calc (∑ site, (Function.update fixed index next (family site)).used)
      ≤ ∑ site, ((fixed (family site)).used + (if family site = index then 1 else 0)) :=
        Finset.sum_le_sum fun site _ => termwise site
    _ = ∑ site, (fixed (family site)).used +
          ∑ site, (if family site = index then 1 else 0 : ℕ) := Finset.sum_add_distrib
    _ ≤ ∑ site, (fixed (family site)).used + 1 := Nat.add_le_add_left atMostOne _

/-- **A lazy query adds at most one entry.** -/
theorem query_entryPotential_le {S : Type} [Fintype S] (family : S → FixedIndex)
    (injective : Function.Injective family) (request : Request) (oracle : LState)
    (answer : request.Answer × LState)
    (member : answer ∈ (LazyOracle.query request oracle).support) :
    entryPotential family answer.2 ≤ entryPotential family oracle + 1 := by
  unfold entryPotential
  cases request with
  | fixedForward index input =>
      obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      have step := sum_update_used_le family injective oracle.fixed index drawn.2
        ((oracle.fixed index).forward_used_le input.toFin drawn drawnMember)
      show ∑ site, (Function.update oracle.fixed index drawn.2 (family site)).used +
        oracle.hash.length ≤ _
      omega
  | fixedInverse index output =>
      obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      have step := sum_update_used_le family injective oracle.fixed index drawn.2
        ((oracle.fixed index).inverse_used_le output.toFin drawn drawnMember)
      show ∑ site, (Function.update oracle.fixed index drawn.2 (family site)).used +
        oracle.hash.length ≤ _
      omega
  | encForward _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact Nat.le_succ _
  | encInverse _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact Nat.le_succ _
  | hash input =>
      obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      have step := HashTable.query_length_le Fintype.card_pos oracle.hash input drawn drawnMember
      show ∑ site, (oracle.fixed (family site)).used + drawn.2.length ≤ _
      omega

/-- **A program with query budget `b` adds at most `b` entries.** -/
theorem run_entryPotential_le {S : Type} [Fintype S] (family : S → FixedIndex)
    (injective : Function.Injective family) {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Result budget) :
    ∀ (oracle : LState) (result : Result × LState),
      result ∈ (LazyOracle.run program oracle).support →
        entryPotential family result.2 ≤ entryPotential family oracle + budget := by
  induction program with
  | pure distribution =>
      intro oracle result member
      simp only [LazyOracle.run, runSampled] at member
      obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact Nat.le_add_right _ _
  | query request next ih =>
      intro oracle result member
      simp only [LazyOracle.run, runSampled] at member
      obtain ⟨answer, answerMember, resultMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      have step := query_entryPotential_le family injective request oracle answer answerMember
      have rest := ih answer.1 answer.2 result resultMember
      omega
  | sample distribution next ih =>
      intro oracle result member
      simp only [LazyOracle.run, runSampled] at member
      obtain ⟨value, _, resultMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      exact ih value oracle result resultMember

/-- The empty oracle has no entries. -/
theorem entryPotential_empty {S : Type} [Fintype S] (family : S → FixedIndex) :
    entryPotential family (LazyOracle.empty : LState) = 0 := by
  unfold entryPotential
  show ∑ site, (LazyOracle.empty.fixed (family site) : SparsePermutation (2 ^ 128)).used + 0 = 0
  rw [Nat.add_zero]
  exact Finset.sum_eq_zero fun _ _ => rfl

/-- A single index carries at most `q₁` entries after the adversary's first stage. -/
theorem run_used_le (adversary : PlanBAdversary Unit) (parameter : ℕ) (circuit : Public)
    (chosen : (AffineInput × adversary.State) × LState)
    (member : chosen ∈ (LazyOracle.run (adversary.chooseInput parameter circuit ())
      LazyOracle.empty).support) (index : FixedIndex) :
    (chosen.2.fixed index).used ≤ adversary.firstQueryBudget parameter := by
  have used := run_entryPotential_le (fun _ : Unit => index) (fun _ _ _ => rfl)
    (adversary.chooseInput parameter circuit ()) LazyOracle.empty chosen member
  rw [entryPotential_empty, Nat.zero_add] at used
  unfold entryPotential at used
  simp only [Finset.univ_unique, Finset.sum_singleton] at used
  omega

/-- A stored key is a key of the table. -/
theorem mem_keys_of_lookup {Key Value : Type} [DecidableEq Key] :
    ∀ (table : List (Key × Value)) (key : Key), table.lookup key ≠ none →
      key ∈ table.map Prod.fst
  | [], _, found => (found rfl).elim
  | (first, value) :: rest, key, found => by
      by_cases same : key = first
      · exact List.mem_cons.mpr (Or.inl same)
      · refine List.mem_cons_of_mem _ (mem_keys_of_lookup rest key ?_)
        have different : (key == first) = false := beq_eq_false_iff_ne.mpr same
        simpa only [List.lookup, different] using found

/-- The stored inputs of an input family. -/
def hashCount {X : Type} [Fintype X] (family : X → BaseField) (oracle : LState) : ℕ := by
  classical
  exact (Finset.univ.filter fun x => oracle.hash.lookup (family x) ≠ none).card

/-- **An injective input family has at most as many stored inputs as the table has entries.** -/
theorem hashCount_le_length {X : Type} [Fintype X] (family : X → BaseField)
    (injective : Function.Injective family) (oracle : LState) :
    hashCount family oracle ≤ oracle.hash.length := by
  classical
  unfold hashCount
  refine (Finset.card_le_card_of_injOn family (t := (oracle.hash.map Prod.fst).toFinset)
    (fun x member => ?_) fun first _ second _ same => injective same).trans
    ((List.toFinset_card_le _).trans (List.length_map _).le)
  exact List.mem_toFinset.mpr (mem_keys_of_lookup _ _ (Finset.mem_filter.mp member).2)

end Entries

section Average

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **The prefix average of the entries is at most `q₁`.** Plan B's stage 1 leaves the empty
oracle, and the adversary's first stage adds at most `q₁` entries. -/
theorem stageOneMean_entryPotential_le {S : Type} [Fintype S] (family : S → FixedIndex)
    (injective : Function.Injective family) (adversary : PlanBAdversary Unit) (parameter : ℕ) :
    stageOneMean adversary parameter (fun oracle => (entryPotential family oracle : ℝ≥0∞)) ≤
      (adversary.firstQueryBudget parameter : ℝ≥0∞) := by
  refine le_trans ?_ (stageOneMean_const_le adversary parameter _)
  unfold stageOneMean
  refine ENNReal.tsum_le_tsum fun first => ?_
  by_cases zero : (planBAbstractSimulator idealSamplers).stage1 parameter LazyOracle.empty
      (some first) = 0
  · rw [zero, zero_mul, zero_mul]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  -- stage 1 of Plan B leaves the empty oracle
  have member : some first ∈ ((planBAbstractSimulator idealSamplers).stage1 parameter
      LazyOracle.empty).support := (PMF.mem_support_iff _ _).mpr zero
  obtain ⟨source, _, sourceEq⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  have emptyOracle : first.2.2 = LazyOracle.empty := by
    cases source with
    | none => cases sourceEq
    | some source =>
        simp only [Option.map_some] at sourceEq
        rw [← Option.some.inj sourceEq]
  refine ENNReal.tsum_le_tsum fun chosen => ?_
  by_cases chosenZero : (LazyOracle.run (adversary.chooseInput parameter first.1 ())
      first.2.2) chosen = 0
  · rw [chosenZero, zero_mul, zero_mul]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  have bound := run_entryPotential_le family injective (adversary.chooseInput parameter first.1 ())
    first.2.2 chosen ((PMF.mem_support_iff _ _).mpr chosenZero)
  rw [emptyOracle, entryPotential_empty, Nat.zero_add] at bound
  show (entryPotential family chosen.2 : ℝ≥0∞) ≤ (adversary.firstQueryBudget parameter : ℝ≥0∞)
  exact_mod_cast bound

end Average

end

end Kriterion.ArgoMAC.Phase3.Lazy
