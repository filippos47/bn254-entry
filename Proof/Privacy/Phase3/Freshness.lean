/-
**Phase 3, P1, item 4 — the input-freshness bound of note §2.3, with the union over the switch.**

`B-review.md` (2): the note's `Pr[E* ∈ dom_i] ≤ n_i / (2^128 − n)` is false as stated, because the
adversary chooses `j* = α₀ xor 1` through its input `u` *after* stage 1, so "the" designated input
is selected by the view. The fix is a union over the candidate switches.

Phase 4: a designated program is a **hash** program `hash (scaleInput pointX 0 j* i E*) := …`, one
per limb `i < 362` of the designated vector. A hash program needs only a fresh *input*
(`LazyOracle.program (.hash _)`), so the bound is on the input side only: the program of limb `i`
fails exactly when the adversary's stage 1 stored the input `scaleInput pointX 0 j* i E*`, i.e.
when `E*` is one of the stage-1 labels at the candidate site `(i, j*)` (`Glue.CandidateSite`).

### What is proved

* `selection_hit_le` — **the union.** For any selection rule (any function of the outcome), the
  selected candidate hits its set with probability at most the sum over all candidates.
* `selection_hit_counterexample` — **the unmultiplied bound is false.** Three candidates, each
  hitting with probability `1/3`, and a selection rule that hits with probability `1`: the union
  factor (the number of candidates) is attained, so no marginal per-candidate bound survives an
  adaptive choice without it.
* `designatedSwitch_bijective` — **the candidate count is `2 ^ firstChunkBits = 4`, not `3`.** As
  the adversary's `α₀` ranges over the four switches of chunk 0, `j* = α₀ xor 1` ranges over all
  four. The review's `3` counts the inactive switches of one *fixed* `α₀`.
* `Glue.candidateIndex_injective` — the `4 · 362 = 1448` candidate sites (limb × chunk-0 switch)
  name pairwise distinct hash inputs at every label: a hash input decodes to at most one
  (site, label) (`sum_siteDomain_le`).
* `aggregate_hit_le` — **the honest constant.** If each (limb, candidate) hit has mass at most
  `ε · E[n_s]` at its own site `s` (`n_s` = stage-1 labels stored at `s`, `ε = 1/(2^128 − q₁)` from
  the candidate label's min-entropy), and the entries total at most `q₁`, then the input-freshness
  abort mass over **all** 362 designated programs is at most `ε · q₁`. The per-limb union costs a
  factor `4` only against a per-limb maximum; summed over the distinct candidate sites it costs
  nothing. So:

```
per limb:   Pr[E* stored at (i, j*)] ≤ Σ_{k<4} ε · E[n_{(i,k)}]      (union over 4 switches)
aggregate:  Pr[∃ i, E* stored at (i, j*)] ≤ ε · q₁ = q₁ / (2^128 − q₁)   (coefficient 1)
```

**Stated per query** (`perQuery_hit_le`, `planB_perQuery_freshness_le`): each stage-1 hash query
names one input, and an input is the candidate input of at most one (site, label)
(`Glue.candidateIndex_injective`); the collision mass is `≤ ε` per query, `≤ q₁ · ε` in all. The
union over the candidate switches would price a limb at `4`; the per-query coefficient is `1`. There
is no output part.
-/

import Proof.Privacy.Phase3.Glue.AbstractSimulator

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Phase3.Glue (CandidateSite candidateIndex candidateIndex_injective
  chunkZero twoPow_chunkWidth_chunkZero)
open scoped ENNReal

noncomputable section

/-! ### The union over an adaptively selected candidate -/

/-- **The union over the candidates.** Whatever rule selects the candidate — here any function of
the outcome, so in particular the adversary's choice of `u` after its stage-1 queries — the
selected candidate hits its set with probability at most the sum over all candidates. -/
theorem selection_hit_le {Ω A K : Type} [Fintype K] (law : PMF Ω) (select : Ω → K)
    (candidate : K → Ω → A) (hitSet : K → Ω → Set A) :
    law.toOuterMeasure {ω | candidate (select ω) ω ∈ hitSet (select ω) ω}
      ≤ ∑ k, law.toOuterMeasure {ω | candidate k ω ∈ hitSet k ω} := by
  have cover : {ω | candidate (select ω) ω ∈ hitSet (select ω) ω}
      ⊆ ⋃ k, {ω | candidate k ω ∈ hitSet k ω} := fun ω hit =>
    Set.mem_iUnion.mpr ⟨select ω, hit⟩
  exact le_trans (MeasureTheory.measure_mono cover) (MeasureTheory.measure_iUnion_fintype_le _ _)

/-- **The unmultiplied bound is false.** Three candidates hit with probability `1/3` each; the
selection "the one that hits" hits with probability `1`. -/
theorem selection_hit_counterexample :
    ∃ (law : PMF (Fin 3)) (select : Fin 3 → Fin 3) (candidate : Fin 3 → Fin 3 → Bool),
      (∀ k, law.toOuterMeasure {ω | candidate k ω = true} = 3⁻¹) ∧
      law.toOuterMeasure {ω | candidate (select ω) ω = true} = 1 := by
  refine ⟨PMF.uniformOfFintype (Fin 3), id, fun k ω => decide (k = ω), fun k => ?_, ?_⟩
  · have single : {ω : Fin 3 | decide (k = ω) = true} = {k} := by
      ext ω; simp [eq_comm]
    rw [single, PMF.toOuterMeasure_uniformOfFintype_apply]
    simp
  · have everything : {ω : Fin 3 | decide (id ω = ω) = true} = Set.univ := by
      ext ω; simp
    rw [everything, PMF.toOuterMeasure_apply_fintype]
    simp
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-! ### The Plan B candidates -/

/-- `j* = α₀ xor 1` is a bijection of the four switches: every switch is a candidate. -/
theorem designatedSwitch_bijective :
    Function.Bijective fun switch : Fin 4 => (⟨switch.val ^^^ 1, by
      have := switch.isLt
      exact Nat.xor_lt_two_pow (n := 2) this (by norm_num)⟩ : Fin 4) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, rfl⟩
  intro first second same
  have values := congrArg Fin.val same
  simp only at values
  apply Fin.ext
  have := congrArg (· ^^^ 1) values
  simpa [Nat.xor_assoc] using this

/-- There are `2 ^ firstChunkBits = 4` candidate switches per limb. -/
theorem candidateCount : Fintype.card (Fin (2 ^ chunkWidth chunkZero)) = 4 := by
  rw [Fintype.card_fin, twoPow_chunkWidth_chunkZero]

/-! ### The aggregate bound -/

/-- The expected number of stage-1 entries at an index. -/
def expectedCount {Ω Index A : Type} (law : PMF Ω) (domain : Index → Ω → Finset A)
    (index : Index) : ℝ≥0∞ :=
  ∑' ω, law ω * ((domain index ω).card : ℝ≥0∞)

/-- **The aggregate input-freshness bound.** Distinct candidate indices; each (slot, candidate)
hit at most `ε` times the expected stage-1 count at its own index; at most `total` entries in all.
Then the selected candidates of all slots hit with total mass at most `ε · total`, for **any**
selection rule. -/
theorem aggregate_hit_le {Ω Slot K Index A : Type} [Fintype Slot] [Fintype K] [Fintype Index]
    (law : PMF Ω) (select : Slot → Ω → K) (index : Slot → K → Index)
    (distinct : Function.Injective fun pair : Slot × K => index pair.1 pair.2)
    (candidate : Slot → K → Ω → A) (domain : Index → Ω → Finset A) (ε : ℝ≥0∞) (total : ℕ)
    (fresh : ∀ slot k, law.toOuterMeasure {ω | candidate slot k ω ∈ domain (index slot k) ω}
      ≤ ε * expectedCount law domain (index slot k))
    (bounded : ∀ ω, ∑ i, (domain i ω).card ≤ total) :
    law.toOuterMeasure
        {ω | ∃ slot, candidate slot (select slot ω) ω ∈ domain (index slot (select slot ω)) ω}
      ≤ ε * total := by
  classical
  have union : {ω | ∃ slot, candidate slot (select slot ω) ω ∈ domain (index slot (select slot ω)) ω}
      = ⋃ slot, {ω | candidate slot (select slot ω) ω ∈ domain (index slot (select slot ω)) ω} := by
    ext ω; simp
  rw [union]
  refine le_trans (MeasureTheory.measure_iUnion_fintype_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun slot _ => selection_hit_le law (select slot)
    (candidate slot) (fun k ω => (domain (index slot k) ω : Set A))) ?_
  refine le_trans (Finset.sum_le_sum fun slot _ => Finset.sum_le_sum fun k _ => fresh slot k) ?_
  -- regroup: the candidate indices are distinct, so their expected counts sum to at most the
  -- expected total
  have perOutcome : ∀ ω, (∑ slot, ∑ k, ((domain (index slot k) ω).card : ℝ≥0∞)) ≤ total := by
    intro ω
    have regroup : (∑ slot, ∑ k, (domain (index slot k) ω).card)
        = ∑ pair : Slot × K, (domain (index pair.1 pair.2) ω).card := by
      rw [← Finset.sum_product']; rfl
    have image : (∑ pair : Slot × K, (domain (index pair.1 pair.2) ω).card)
        ≤ ∑ i, (domain i ω).card := by
      rw [← Finset.sum_image (f := fun i => (domain i ω).card)
        (fun first _ second _ same => distinct same)]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have natBound := le_trans (le_of_eq regroup) (le_trans image (bounded ω))
    exact_mod_cast natBound
  have swap : (∑ slot, ∑ k, ∑' ω, law ω * ((domain (index slot k) ω).card : ℝ≥0∞))
      = ∑' ω, ∑ slot, ∑ k, law ω * ((domain (index slot k) ω).card : ℝ≥0∞) := by
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine Finset.sum_congr rfl fun slot _ => ?_
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  calc (∑ slot, ∑ k, ε * expectedCount law domain (index slot k))
      = ε * ∑' ω, law ω * (∑ slot, ∑ k, ((domain (index slot k) ω).card : ℝ≥0∞)) := by
        simp only [expectedCount, ← Finset.mul_sum]
        rw [swap]
        simp only [Finset.mul_sum]
    _ ≤ ε * ∑' ω, law ω * (total : ℝ≥0∞) := by
        gcongr with ω
        exact perOutcome ω
    _ = ε * total := by rw [ENNReal.tsum_mul_right, law.tsum_coe, one_mul]

/-- The stage-1 labels at a candidate site: the labels whose candidate input is stored. -/
def siteDomain {Ω : Type} (stored : Ω → Finset BaseField) (site : CandidateSite) (ω : Ω) :
    Finset Block :=
  (stored ω).preimage (candidateIndex site) fun _ _ _ _ same =>
    congrArg Prod.snd (candidateIndex_injective (a₁ := (site, _)) (a₂ := (site, _)) same)

/-- **The stored candidate labels number at most the stored inputs**: distinct (site, label) pairs
name distinct inputs (`Glue.candidateIndex_injective`). -/
theorem sum_siteDomain_le {Ω : Type} (stored : Ω → Finset BaseField) (ω : Ω) :
    ∑ site, (siteDomain stored site ω).card ≤ (stored ω).card := by
  classical
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn (fun pair => candidateIndex pair.1 pair.2)
    (fun pair member => ?_) (fun first _ second _ same => ?_)
  · obtain ⟨-, inside⟩ := Finset.mem_sigma.mp member
    exact Finset.mem_preimage.mp inside
  · have pairEq := candidateIndex_injective (a₁ := (first.1, first.2)) (a₂ := (second.1, second.2))
      same
    simp only [Prod.mk.injEq] at pairEq
    exact Sigma.ext pairEq.1 (heq_of_eq pairEq.2)

/-- **§2.3 fixed, at Plan B, on the hash inputs.** Whatever switch `j*` the adversary's input
selects for each of the `362` limbs, if every (limb, candidate switch) label hits the stage-1 hash
domain at its own candidate input with mass at most `ε` times the expected number of stage-1 labels
at that candidate site, and stage 1 stores at most `q₁` inputs, then the input-freshness failures
of all `362` programs have total mass at most `ε · q₁` — with `ε = 1 / (2^128 − q₁)` this is
`q₁ / (2^128 − q₁)`. -/
theorem planB_inputFreshness_le {Ω : Type} (law : PMF Ω)
    (select : Fin (limbCount .pointX) → Ω → Fin (2 ^ chunkWidth chunkZero))
    (candidate : Fin (limbCount .pointX) → Fin (2 ^ chunkWidth chunkZero) → Ω → Block)
    (stored : Ω → Finset BaseField) (ε : ℝ≥0∞) (stageOneQueries : ℕ)
    (fresh : ∀ limb switch, law.toOuterMeasure
        {ω | candidateIndex (limb, switch) (candidate limb switch ω) ∈ stored ω}
      ≤ ε * expectedCount law (siteDomain stored) (limb, switch))
    (bounded : ∀ ω, (stored ω).card ≤ stageOneQueries) :
    law.toOuterMeasure {ω | ∃ limb, candidateIndex (limb, select limb ω)
        (candidate limb (select limb ω) ω) ∈ stored ω}
      ≤ ε * stageOneQueries := by
  have same : ∀ (limb : Fin (limbCount .pointX)) (switch : Fin (2 ^ chunkWidth chunkZero)) (ω : Ω),
      candidate limb switch ω ∈ siteDomain stored (limb, switch) ω ↔
        candidateIndex (limb, switch) (candidate limb switch ω) ∈ stored ω :=
    fun _ _ _ => Finset.mem_preimage
  have event : {ω | ∃ limb, candidateIndex (limb, select limb ω)
      (candidate limb (select limb ω) ω) ∈ stored ω} =
      {ω | ∃ limb, candidate limb (select limb ω) ω ∈
        siteDomain stored (limb, select limb ω) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, same]
  rw [event]
  refine aggregate_hit_le law select (fun limb switch => (limb, switch))
    (fun _ _ equal => equal) candidate (siteDomain stored) ε stageOneQueries
    (fun limb switch => ?_) fun ω => (sum_siteDomain_le stored ω).trans (bounded ω)
  have hit : {ω | candidate limb switch ω ∈ siteDomain stored (limb, switch) ω} =
      {ω | candidateIndex (limb, switch) (candidate limb switch ω) ∈ stored ω} := by
    ext ω
    exact same limb switch ω
  rw [hit]
  exact fresh limb switch

/-! ### The per-query form

The union over the candidate switches (`selection_hit_le`) is the wrong book-keeping for the
constant: it prices each limb at `4` candidates. The right one is **per stage-1 query**. A query
names one hash input, and a candidate input names its limb, its switch and its label
(`Glue.candidateIndex_injective`), so every input is the candidate input of at most one
(site, label): a query can collide with **one** candidate label only. Hence the collision mass is
at most `ε` per query, and `q₁ · ε` in all, for every selection rule. -/

/-- **The per-query collision bound.** Stage 1 makes `q` queries `(index, input)`. If each query
collides with the candidate label that owns its index with probability at most `ε`, then — for any
rule selecting each slot's switch after stage 1 — some slot's selected candidate is among the
stage-1 inputs at its own index with probability at most `q · ε`. -/
theorem perQuery_hit_le {Ω Slot K Index A : Type} (law : PMF Ω) (select : Slot → Ω → K)
    (index : Slot → K → Index) (candidate : Slot → K → Ω → A) (q : ℕ)
    (queries : Ω → Fin q → Index × A) (ε : ℝ≥0∞)
    (perQuery : ∀ t : Fin q, law.toOuterMeasure {ω | ∃ slot k,
        index slot k = (queries ω t).1 ∧ candidate slot k ω = (queries ω t).2} ≤ ε) :
    law.toOuterMeasure {ω | ∃ slot t, (queries ω t).1 = index slot (select slot ω)
        ∧ (queries ω t).2 = candidate slot (select slot ω) ω}
      ≤ q * ε := by
  have cover : {ω | ∃ slot t, (queries ω t).1 = index slot (select slot ω)
        ∧ (queries ω t).2 = candidate slot (select slot ω) ω}
      ⊆ ⋃ t, {ω | ∃ slot k, index slot k = (queries ω t).1 ∧ candidate slot k ω = (queries ω t).2} := by
    rintro ω ⟨slot, t, hitIndex, hitInput⟩
    exact Set.mem_iUnion.mpr ⟨t, slot, select slot ω, hitIndex.symm, hitInput.symm⟩
  refine le_trans (MeasureTheory.measure_mono cover)
    (le_trans (MeasureTheory.measure_iUnion_fintype_le _ _) ?_)
  refine le_trans (Finset.sum_le_sum fun t _ => perQuery t) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **§2.3 at Plan B, per query.** The 362 designated programs' input-freshness failures have total
mass at most `q₁ · ε` (`ε = 1/(2^128 − q₁)` from the candidate label's min-entropy before each
query): coefficient `1` per stage-1 hash query, whatever switch `j*` the adversary's input
selects. The per-query hypothesis concerns one input against all candidate labels; by
`Glue.candidateIndex_injective` at most one of them can meet it. -/
theorem planB_perQuery_freshness_le {Ω : Type} (law : PMF Ω)
    (select : Fin (limbCount .pointX) → Ω → Fin (2 ^ chunkWidth chunkZero))
    (candidate : Fin (limbCount .pointX) → Fin (2 ^ chunkWidth chunkZero) → Ω → Block)
    (stageOneQueries : ℕ) (queries : Ω → Fin stageOneQueries → BaseField) (ε : ℝ≥0∞)
    (perQuery : ∀ t, law.toOuterMeasure {ω | ∃ limb switch,
        candidateIndex (limb, switch) (candidate limb switch ω) = queries ω t} ≤ ε) :
    law.toOuterMeasure {ω | ∃ limb t,
        queries ω t = candidateIndex (limb, select limb ω) (candidate limb (select limb ω) ω)}
      ≤ stageOneQueries * ε := by
  have bound := perQuery_hit_le law select (fun _ _ => ())
    (fun limb switch ω => candidateIndex (limb, switch) (candidate limb switch ω))
    stageOneQueries (fun ω t => ((), queries ω t)) ε fun t => by
      simpa only [true_and] using perQuery t
  simpa only [true_and] using bound

end

end Kriterion.ArgoMAC.Security.Phase3
