/-
This file proves plan B's end-to-end join correctness (plan
`2026-09-17-planB.md`, Task 15, second statement).

For every tape, every global correlation `delta`, every Lamport key and every coordinate value,
the evaluator's fold of one coordinate's switch system returns exactly `slope * value + offset`,
with the offset the garbler's own output mask `O[e]` -- the value the row layer absorbs into the
published constants for 0 bytes.

Three ingredients meet here:

* `evalHot_garbleHot` (Task 7): the evaluator's one-hot labels agree with the garbler's off the
  live entry, and differ by `delta` on it;
* `switchMask_agrees_off_active` / `evalScale_garbleScale` (Task 15, `ScaleHot.lean`): the join
  fold only reads the closed switches, and returns `O_c[e] + iota(alpha) * s_c[e]`;
* `chunk_recomposition` (Task 13): the `chunkCount` chunk indices, weighted by
  `2 ^ chunkOffset c`, recompose the coordinate -- unreduced, because `p < 2 ^ 254`.

There are no side conditions beyond the free-XOR key relation, which is what the garbler's own
label sampler establishes.
-/

import Construction.PGS.AffineFp
import Proof.Correctness.CanonicalBits
import Proof.Correctness.PGS.OneHot
import Proof.Correctness.PGS.ScaleHot

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-! ### The chunk-local views are slices of the coordinate -/

/-- Bit `position` of chunk `c` is bit `chunkOffset c + position` of the coordinate. -/
theorem chunkValue_bit (bits : BitVec coordinateBits) (c : Fin chunkCount)
    (position : Fin (chunkWidth c)) :
    (chunkValue bits c)[position] = bits[chunkBitIndex c position] := by
  rw [Fin.getElem_fin, Fin.getElem_fin, BitVec.getElem_eq_testBit_toNat,
    BitVec.getElem_eq_testBit_toNat, chunkValue, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow,
    decide_eq_true position.isLt, Bool.true_and, Nat.testBit_shiftRight]
  rfl

/-- Selecting the coordinate's labels and then slicing a chunk out is the same as selecting that
chunk's labels from that chunk's key. -/
theorem chunkLabels_selectBits (bitKey : Fin coordinateBits → Block × Block)
    (bits : BitVec coordinateBits) (c : Fin chunkCount) :
    chunkLabels (selectBits bitKey bits) c
      = selectBits (chunkKey bitKey c) (chunkValue bits c) := by
  funext position
  show (if bits[chunkBitIndex c position] then (bitKey (chunkBitIndex c position)).2
      else (bitKey (chunkBitIndex c position)).1)
    = if (chunkValue bits c)[position] then (chunkKey bitKey c position).2
      else (chunkKey bitKey c position).1
  rw [chunkValue_bit]
  rfl

/-- The free-XOR key relation survives the slicing. -/
theorem chunkKey_correlated (bitKey : Fin coordinateBits → Block × Block) (delta : Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (c : Fin chunkCount) :
    ∀ position, (chunkKey bitKey c position).2 = (chunkKey bitKey c position).1 ^^^ delta :=
  fun position => correlated (chunkBitIndex c position)

/-! ### One chunk of the coordinate -/

/-- The evaluator's one-hot labels of chunk `c` agree with the garbler's on every closed
switch. On the live one they differ by `delta`, and the evaluator never hashes that one. -/
theorem evalHot_agrees_off_active {oracle : PermutationOracle FixedIndex Block} {lane : Lane}
    {delta : Block} {bitKey : Fin coordinateBits → Block × Block}
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (bits : BitVec coordinateBits) (c : Fin chunkCount) (switch : Fin (2 ^ chunkWidth c))
    (closed : switch ≠ chunkOf bits c) :
    evalHot oracle lane c (chunkWidth c) (garbleChunk oracle lane delta bitKey c).2
        (selectBits (chunkKey bitKey c) (chunkValue bits c)) (chunkValue bits c) switch
      = (garbleChunk oracle lane delta bitKey c).1 switch := by
  have inactive : binToHot (chunkWidth c) (chunkValue bits c) switch = false := by
    rw [binToHot_eq_ite, decide_eq_false]
    intro hit
    exact closed (Fin.ext (by rw [hit, chunkValue_toNat]))
  simp only [garbleChunk]
  rw [evalHot_garbleHot oracle lane c (chunkWidth c) delta (chunkKey bitKey c)
    (chunkKey_correlated bitKey delta correlated c) (chunkValue bits c) switch, inactive]
  simp only [Bool.false_eq_true, if_false]
  exact BitVec.xor_zero

/-! ### The coordinate, end to end -/

/-- **Correctness of the join, end to end.** For every tape and every coordinate value, the
evaluator obtains exactly `slope * value + offset`, with the offset the garbler's own `O`. -/
theorem evalCoord_garbleCoord (oracle : PermutationOracle FixedIndex Block)
    (hashOracle : EncPRF.HashOracle) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (slopes : Fin (laneCount lane) → BaseField) (value : BaseField)
    (element : Fin (laneCount lane)) :
    evalCoord oracle hashOracle lane
        (garbleCoord oracle hashOracle lane delta bitKey slopes).1
        (garbleCoord oracle hashOracle lane delta bitKey slopes).2
        (coordWord value) (selectBits bitKey (coordWord value)) element
      = slopes element * value + offsets oracle hashOracle lane delta bitKey element := by
  have chunkTerm : ∀ c : Fin chunkCount,
      evalScale hashOracle lane c (chunkWidth c)
          (evalHot oracle lane c (chunkWidth c)
            (hotSlice (garbleCoord oracle hashOracle lane delta bitKey slopes).1 c)
            (chunkLabels (selectBits bitKey (coordWord value)) c)
            (chunkValue (coordWord value) c))
          (chunkOf (coordWord value) c)
          ((garbleCoord oracle hashOracle lane delta bitKey slopes).2 c) element
        = outputMask hashOracle lane c (chunkWidth c)
            (garbleChunk oracle lane delta bitKey c).1 element
          + iota _ (chunkOf (coordWord value) c) * chunkScalar slopes c element := by
    intro c
    rw [show (garbleCoord oracle hashOracle lane delta bitKey slopes).1
        = hotJoins oracle lane delta bitKey from rfl,
      hotSlice_hotJoins, chunkLabels_selectBits,
      switchMask_agrees_off_active hashOracle lane c (chunkWidth c) _
        (garbleChunk oracle lane delta bitKey c).1 (chunkOf (coordWord value) c)
        (fun switch closed =>
          evalHot_agrees_off_active correlated (coordWord value) c switch closed),
      show (garbleCoord oracle hashOracle lane delta bitKey slopes).2 c
        = garbleScale hashOracle lane c (chunkWidth c) (garbleChunk oracle lane delta bitKey c).1
            (chunkScalar slopes c) from rfl,
      evalScale_garbleScale]
  have weighted : (∑ c : Fin chunkCount,
      iota _ (chunkOf (coordWord value) c) * chunkScalar slopes c element)
        = slopes element * value := by
    have step : ∀ c : Fin chunkCount,
        iota _ (chunkOf (coordWord value) c) * chunkScalar slopes c element
          = slopes element
            * ((2 : BaseField) ^ chunkOffset c * iota _ (chunkOf (coordWord value) c)) := by
      intro c
      simp only [chunkScalar]
      ring
    rw [Finset.sum_congr rfl fun c _ => step c, ← Finset.mul_sum, chunk_recomposition]
  simp only [evalCoord, offsets]
  rw [Finset.sum_congr rfl fun c _ => chunkTerm c, Finset.sum_add_distrib, weighted]
  ring

end Kriterion.ArgoMAC.PlanB
