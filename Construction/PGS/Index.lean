/-
This file defines the Plan B fixed-key permutation index.
One independent uniform permutation is named per (gate, output block); nothing is shared and
no tweak is ever applied, so the construction queries each index at most once.
The plan source is `2026-09-17-planB.md`, section D.6.

The `scale-hot` switch masks are no longer fixed-key gates: each switch mask vector is drawn
from one batch of hash queries (`Construction/PGS/BatchSampler.lean`), so the index carries only
the `bin-to-hot` fold gates and the doubling-exception gadget.
-/

import Construction.ArgoMAC.EncPRF
import Construction.PGS.Elements

namespace Kriterion.ArgoMAC.PlanB

open Cryptography

/-- The public fixed-key permutation index of the projectivized garbling scheme.

The `hot` family is deliberately rectangular: at fold step `j` only `2 ^ j` one-hot entries
exist, and the chunks are `2`, `5` or `4` bits wide, so a chunk uses two, five or four of the
`chunkBits = 5` fold steps. Unqueried indices cost nothing in the error budget and buy a derived
`Fintype` with no dependent arguments. -/
inductive FixedIndex
  /-- `bin-to-hot` fold masks: **two** independent permutations per one-hot entry per fold
  step, named by the `half` bit. The repaired fold step (Task 34a) is the sum of the two
  permutation images `π_{i₀}(Z) ^^^ π_{i₁}(Z)`, so that neither the step material nor its free
  XOR with the parent is a single permutation image. -/
  | hot (lane : Lane) (chunk : Fin chunkCount) (fold : Fin chunkBits)
      (entry : Fin (2 ^ chunkBits)) (half : Bool)
  /-- Exception gadget: one permutation per (digit, coordinate, label position, label bit).
  The bit names which of the position's two labels the permutation is asked at, so the garbler,
  which digests the labels of two exceptional inputs per digit, still asks each index at one
  point only: the label of its bit. The evaluator asks the index of its own bit. -/
  | gadget (digit : Fin digitCount) (coord : Coord) (position : Fin coordinateBits) (bit : Bool)
deriving DecidableEq, Fintype

/-- The encryption-PRF index is unchanged from the baseline: the gate protects the 508 input
labels, not the per-element offsets. -/
abbrev EncIndex := EncPRF.PermutationIndex

/-- `#FixedIndex = 4 * 52 * 5 * 2 ^ 5 * 2 + 91 * 2 * 254 * 2 = 66560 + 92456`.

The `hot` family runs over the **four** lanes (two switch systems on each of the two
coordinates), not the two coordinates, and carries the extra `half : Bool` of the repaired
two-image fold step. The count is *not* a scored metric and enters no error term: the budget
counts construction queries per index, and each of the two halves is still queried exactly once.

The proof goes through the derived proxy equivalence and the cardinality of finite products
and sums; no element of the type is ever enumerated. -/
theorem card_fixedIndex : Fintype.card FixedIndex = 159016 := by
  rw [← Fintype.card_congr FixedIndex.proxyTypeEquiv]
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, card_lane, card_coord, Fintype.card_bool]
  norm_num [chunkCount, chunkBits, digitCount, coordinateBits]

/-- `#EncIndex = 2 * 254`. -/
theorem card_encIndex : Fintype.card EncIndex = 508 := by
  rw [Fintype.card_prod, Fintype.card_fin]
  rfl

/-- The `hot` index of a fold step, taking the step and the entry as natural numbers.
Both arguments are in range at every call site of the fold (`fold < chunkBits` because the
widest chunk is `chunkBits` wide, and `entry < 2 ^ fold ≤ 2 ^ (chunkBits - 1)`), so the
reduction never identifies two distinct gates. -/
def hotIndexNat (lane : Lane) (chunk : Fin chunkCount) (fold entry : Nat) (half : Bool) :
    FixedIndex :=
  .hot lane chunk ⟨fold % chunkBits, Nat.mod_lt _ chunkBits_pos⟩
    ⟨entry % 2 ^ chunkBits, Nat.mod_lt _ twoPowChunkBits_pos⟩ half

theorem hotIndexNat_eq (lane : Lane) (chunk : Fin chunkCount) (fold entry : Nat)
    (half : Bool) (hfold : fold < chunkBits) (hentry : entry < 2 ^ chunkBits) :
    hotIndexNat lane chunk fold entry half
      = .hot lane chunk ⟨fold, hfold⟩ ⟨entry, hentry⟩ half := by
  simp only [hotIndexNat, Nat.mod_eq_of_lt hfold, Nat.mod_eq_of_lt hentry]

/-- Two fold gates of paid levels are equal only at the same (lane, chunk, level, entry, half). -/
theorem hotIndexNat_inj {lane lane' : Lane} {chunk chunk' : Fin chunkCount} {n n' e e' : Nat}
    {half half' : Bool} (small : n < chunkBits) (small' : n' < chunkBits)
    (entry : e < 2 ^ chunkBits) (entry' : e' < 2 ^ chunkBits)
    (same : hotIndexNat lane chunk n e half = hotIndexNat lane' chunk' n' e' half') :
    lane = lane' ∧ chunk = chunk' ∧ n = n' ∧ e = e' ∧ half = half' := by
  rw [hotIndexNat_eq lane chunk n e half small entry,
    hotIndexNat_eq lane' chunk' n' e' half' small' entry'] at same
  simp only [FixedIndex.hot.injEq, Fin.mk.injEq] at same
  exact same

end Kriterion.ArgoMAC.PlanB
