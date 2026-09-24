/-
This file proves the correctness of one chunk's `scale-hot` join (plan
`2026-09-17-planB.md`, Task 15, first statement).

The evaluator holds the closed switches' masks and recovers the open switch's label from the
published join. Folding the recovered labels against `iota` (Lemma 6.1) therefore returns the
garbler's own output mask `O_c[e] = sum_j iota(j) * Y_{c,j}[e]` plus `iota(alpha) * s_c[e]` --
the scalar enters through the active switch alone, and nothing else survives.

Every sum is a `Finset.sum` over `Finset.univ : Finset (Fin (2 ^ width))` and is never
unfolded, enumerated or decided (Rule O).
-/

import Construction.PGS.ScaleHot

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-! ### The algebra of a single updated summand -/

/-- Replacing one summand of a weighted sum shifts the sum by the weight times the change. -/
private theorem sum_weighted_update {R : Type*} [CommRing R] {size : Nat} (alpha : Fin size)
    (weight mask : Fin size → R) (replacement : R) :
    (∑ index : Fin size, weight index * (if index = alpha then replacement else mask index))
      = (∑ index : Fin size, weight index * mask index)
        + weight alpha * (replacement - mask alpha) := by
  have body : ∀ index : Fin size,
      weight index * (if index = alpha then replacement else mask index)
        = weight index * mask index
          + (if index = alpha then weight index * (replacement - mask index) else 0) := by
    intro index
    by_cases hit : index = alpha
    · subst hit
      rw [if_pos rfl, if_pos rfl]
      ring
    · rw [if_neg hit, if_neg hit, add_zero]
  rw [Finset.sum_congr rfl fun index _ => body index, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ alpha fun index => weight index * (replacement - mask index),
    if_pos (Finset.mem_univ alpha)]

/-! ### The join is correct for every tape -/

/-- **Correctness of one chunk's join.** The evaluator's fold of the recovered switch labels is
the chunk value times the scalar, offset by the garbler's output mask. -/
theorem evalScale_garbleScale (hashOracle : EncPRF.HashOracle)
    (lane : Lane) (chunk : Fin chunkCount) (width : Nat) (hot : HotLabels width)
    (alpha : Fin (2 ^ width)) (scalar : Fin (laneCount lane) → BaseField)
    (element : Fin (laneCount lane)) :
    evalScale hashOracle lane chunk width hot alpha
        (garbleScale hashOracle lane chunk width hot scalar) element
      = outputMask hashOracle lane chunk width hot element + iota _ alpha * scalar element := by
  simp only [evalScale, garbleScale, maskTotal, outputMask]
  rw [sum_weighted_update alpha (fun switch => iota _ switch)
    (fun switch => switchMask hashOracle lane chunk switch.val (hot switch) element)]
  have open_wire :
      ((∑ switch : Fin (2 ^ width),
            switchMask hashOracle lane chunk switch.val (hot switch) element) + scalar element
          - ∑ other ∈ Finset.univ.erase alpha,
              switchMask hashOracle lane chunk other.val (hot other) element)
        - switchMask hashOracle lane chunk alpha.val (hot alpha) element = scalar element := by
    rw [← Finset.add_sum_erase _
      (fun switch : Fin (2 ^ width) =>
        switchMask hashOracle lane chunk switch.val (hot switch) element) (Finset.mem_univ alpha)]
    ring
  rw [open_wire]

/-! ### The join only reads the closed switches' labels -/

/-- **The closed switches are all the evaluator touches.** Two one-hot label families that agree
off the active switch give the same fold: at the active switch the evaluator does not hash its
label at all, it solves for it from the published join.

This is what lets the end-to-end proof feed the *evaluator's* labels into a statement proved
about the *garbler's*: `evalHot_garbleHot` makes the two agree exactly off the live entry. -/
theorem switchMask_agrees_off_active (hashOracle : EncPRF.HashOracle)
    (lane : Lane) (chunk : Fin chunkCount) (width : Nat) (held garbled : HotLabels width)
    (alpha : Fin (2 ^ width)) (agree : ∀ switch, switch ≠ alpha → held switch = garbled switch)
    (join : Fin (laneCount lane) → BaseField) :
    evalScale hashOracle lane chunk width held alpha join
      = evalScale hashOracle lane chunk width garbled alpha join := by
  funext element
  simp only [evalScale]
  refine Finset.sum_congr rfl ?_
  intro switch _
  by_cases active : switch = alpha
  · subst active
    rw [if_pos rfl, if_pos rfl]
    congr 2
    refine Finset.sum_congr rfl ?_
    intro other member
    rw [agree other (Finset.ne_of_mem_erase member)]
  · rw [if_neg active, if_neg active, agree switch active]

end Kriterion.ArgoMAC.PlanB
