/-
**Phase 3, P1h — what the evaluator asks: one lane.**

`Asks ans P q`: the program `P`, run on the answers `ans`, asks the question `q`. It passes to a bind
from either side (`Asks.bind_left`, `Asks.bind_right` at the first stage's value) and to a loop from
any iteration (`Asks.vector`).

**One lane of the evaluator asks every garbler question the evaluator is meant to hold** — on
every tape, with the lane's published fold joins and the selected labels of a free-XOR key:

* `asks_evalLane_hot`: every fold gate of every paid step `1 ≤ n < b_c` at an **inactive** parent,
  at the garbler's own level-`n` label (`evalFold_off`, from `evalFold_garbleFold` at `n` steps: the
  evaluator's label equals the garbler's off the active entry);
* `asks_evalLane_scale`: every hash limb of every **inactive** switch, at the garbler's own
  one-hot label (`evalHot_agrees_off_active`).
-/

import Proof.Privacy.Phase3.Hidden.StageTwoShift
import Proof.Correctness.PGS.Row

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden

noncomputable section

/-! ### Asked questions -/

/-- `P` asks `q` on the answers `ans`. -/
def Asks {α : Type} (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (P : FreeQuery Programs.Spec α) (q : PublicQuery FixedIndex EncPRF.PermutationIndex) : Prop :=
  q ∈ (Hidden.transcriptOf ans P).map Sigma.fst

namespace Asks

variable {α β : Type} {ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer}
  {q : PublicQuery FixedIndex EncPRF.PermutationIndex}

theorem ask' (q : PublicQuery FixedIndex EncPRF.PermutationIndex) :
    Asks ans (FreeQuery.ask (spec := Programs.Spec) q) q := by
  show q ∈ [q]
  exact List.mem_singleton_self q

theorem bind_left {P : FreeQuery Programs.Spec α} {f : α → FreeQuery Programs.Spec β}
    (asks : Asks ans P q) : Asks ans (P >>= f) q := by
  unfold Asks at *
  rw [transcriptOf_bind, List.map_append]
  exact List.mem_append_left _ asks

theorem bind_right {P : FreeQuery Programs.Spec α} {f : α → FreeQuery Programs.Spec β}
    (asks : Asks ans (f (P.eval ans)) q) : Asks ans (P >>= f) q := by
  unfold Asks at *
  rw [transcriptOf_bind, List.map_append]
  exact List.mem_append_right _ asks

theorem vector : ∀ (count : Nat) {P : Fin count → FreeQuery Programs.Spec α} (i : Fin count),
    Asks ans (P i) q → Asks ans (FreeQuery.vector count P) q
  | 0, _, i, _ => i.elim0
  | count + 1, P, i, asks => by
      show Asks ans (FreeQuery.vector count (fun index => P index.castSucc) >>= fun values =>
          P (Fin.last count) >>= fun value => Pure.pure (values.push value)) q
      by_cases last : i = Fin.last count
      · subst last
        exact bind_right (bind_left asks)
      · have small : i.val < count := by
          have := i.isLt
          have : i.val ≠ count := fun h => last (Fin.ext h)
          omega
        have cast : (⟨i.val, small⟩ : Fin count).castSucc = i := Fin.ext rfl
        refine bind_left (vector count (P := fun index => P index.castSucc) ⟨i.val, small⟩ ?_)
        rw [cast]
        exact asks

/-- A Davies–Meyer gate asks its question. -/
theorem hashM (index : FixedIndex) (label : Block) :
    Asks ans (Programs.hashM index label) (.fixedForward index label) :=
  bind_left (ask' _)

end Asks

/-! ### One chunk of the evaluator -/

theorem labelAt_select_chunk (bitKey : Fin PlanB.coordinateBits → Block × Block) (delta : Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (bits : BitVec PlanB.coordinateBits) (k : Fin chunkCount) (step : Nat)
    (inRange : step < chunkWidth k) :
    labelAt (chunkLabels (selectBits bitKey bits) k) step =
      labelAt (fun position => (chunkKey bitKey k position).1) step ^^^
        (if (chunkValue bits k).toNat.testBit step then delta else 0) := by
  rw [chunkLabels_selectBits]
  have bitEq : (chunkValue bits k)[(⟨step, inRange⟩ : Fin (chunkWidth k))] =
      (chunkValue bits k).toNat.testBit step :=
    BitVec.getElem_eq_testBit_toNat (chunkValue bits k) step inRange
  simp only [labelAt, dif_pos inRange, selectBits, ← bitEq]
  by_cases bit : (chunkValue bits k)[(⟨step, inRange⟩ : Fin (chunkWidth k))] = true
  · rw [if_pos bit, if_pos bit, chunkKey_correlated bitKey delta correlated]
  · rw [if_neg bit, if_neg bit, bxor_zero]

/-- Once computed, a fold join never changes. -/
theorem garbleFold_join_stable (O : PermutationOracle FixedIndex Block) (lane : Lane)
    (k : Fin chunkCount) (delta : Block) (zeroLabel : Nat → Block) (n step : Nat)
    (small : step < n) : ∀ m, n ≤ m → (garbleFold O lane k delta zeroLabel m).2 step =
      (garbleFold O lane k delta zeroLabel n).2 step
  | 0, le => by
      obtain rfl : n = 0 := by omega
      rfl
  | m + 1, le => by
      by_cases eq : n = m + 1
      · subst eq
        rfl
      · show (if step = m then _ else (garbleFold O lane k delta zeroLabel m).2 step) = _
        rw [if_neg (by omega)]
        exact garbleFold_join_stable O lane k delta zeroLabel n step small m (by omega)

/-- **The evaluator's level-`n` labels are the garbler's off the active parent.** -/
theorem evalFold_off (O : PermutationOracle FixedIndex Block) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (bits : BitVec PlanB.coordinateBits) (k : Fin chunkCount) (n : Nat) (small : n ≤ chunkWidth k)
    (r : Fin (2 ^ n)) (off : r.val ≠ (chunkOf bits k).val % 2 ^ n) :
    evalFold O lane k (chunkValue bits k).toNat (labelAt (chunkLabels (selectBits bitKey bits) k))
        (joinAt (hotSlice (hotJoins O lane delta bitKey) k)) n r =
      (garbleFold O lane k delta (labelAt fun p => (chunkKey bitKey k p).1) n).1 r := by
  rw [evalFold_garbleFold O lane k delta (labelAt fun p => (chunkKey bitKey k p).1)
    (labelAt (chunkLabels (selectBits bitKey bits) k)) (chunkValue bits k).toNat n
    (joinAt (hotSlice (hotJoins O lane delta bitKey) k))
    (fun step below => labelAt_select_chunk bitKey delta correlated bits k step (by omega))
    (fun step below => by
      rw [hotSlice_hotJoins]
      show joinAt (garbleHot O lane k (chunkWidth k) delta
        fun p => (chunkKey bitKey k p).1).2 step = _
      rw [joinAt_garbleHot O lane k (chunkWidth k) delta _ step (by omega)]
      exact garbleFold_join_stable O lane k delta _ n step below (chunkWidth k) small) r]
  have notHit : ¬ (r.val = (chunkValue bits k).toNat % 2 ^ n) := by
    rw [chunkValue_toNat]
    exact off
  rw [if_neg notHit, bxor_zero]

/-- The fold of more than `n` levels asks every non-active step-`n` gate at the evaluator's
level-`n` label. -/
theorem asks_evalFoldM (O : Oracle) (lane : Lane) (k : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) (n : Nat) (r : Fin (2 ^ n)) (half : Bool)
    (off : r ≠ activeAt value n) :
    ∀ steps, n + 1 ≤ steps → Asks (publicAnswer O)
      (Programs.evalFoldM lane k value bitLabel join steps)
      (.fixedForward (hotIndexNat lane k n r.val half) (evalFold O.1 lane k value bitLabel join n
          r))
  | 0, small => absurd small (by omega)
  | steps + 1, small => by
      show Asks _ (Programs.evalFoldM lane k value bitLabel join steps >>= fun previous =>
          Programs.evalStepM lane k steps (bitLabel steps) (join steps) (activeAt value steps)
            previous >>= fun right => Pure.pure (extendLevel steps previous right)) _
      by_cases last : steps = n
      · subst last
        refine Asks.bind_right (Asks.bind_left ?_)
        rw [Programs.eval_evalFoldM]
        unfold Programs.evalStepM
        refine Asks.bind_left (Asks.vector _ r ?_)
        simp only [if_neg off]
        unfold Programs.foldMaskM
        cases half
        · exact Asks.bind_left (Asks.hashM _ _)
        · exact Asks.bind_right (Asks.bind_left (Asks.hashM _ _))
      · exact Asks.bind_left
          (asks_evalFoldM O lane k value bitLabel join n r half off steps (by omega))

/-- A switch's mask asks every hash limb at its label. -/
theorem asks_switchMaskM (O : Oracle) (lane : Lane) (k : Fin chunkCount) (switch : Nat)
    (label : Block) (limb : Fin (limbCount lane)) :
    Asks (publicAnswer O) (Programs.switchMaskM lane k switch label)
      (.hash (scaleInput lane k switch limb.val label)) := by
  unfold Programs.switchMaskM
  exact Asks.bind_left (Asks.vector _ limb (Asks.ask' _))

/-- **One chunk asks every inactive fold gate, at the garbler's point.** -/
theorem asks_evalChunk_hot (O : Oracle) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec PlanB.coordinateBits)
    (k : Fin chunkCount) (n : Nat) (small : n < chunkWidth k) (r : Fin (2 ^ n)) (half : Bool)
    (off : r.val ≠ (chunkOf bits k).val % 2 ^ n) :
    Asks (publicAnswer O)
      (Programs.evalChunkM lane (hotJoins O.1 lane delta bitKey) scale bits
        (selectBits bitKey bits) k)
      (.fixedForward (hotIndexNat lane k n r.val half)
        ((garbleFold O.1 lane k delta (labelAt fun p => (chunkKey bitKey k p).1) n).1 r)) := by
  unfold Programs.evalChunkM
  refine Asks.bind_left ?_
  have notActive : r ≠ activeAt (chunkValue bits k).toNat n := by
    intro same
    apply off
    rw [same]
    show (chunkValue bits k).toNat % 2 ^ n = _
    rw [chunkValue_toNat]
  have asks := asks_evalFoldM O lane k (chunkValue bits k).toNat
    (labelAt (chunkLabels (selectBits bitKey bits) k))
    (joinAt (hotSlice (hotJoins O.1 lane delta bitKey) k)) n r half notActive (chunkWidth k)
    (by omega)
  rw [evalFold_off O.1 lane delta bitKey correlated bits k n small.le r off] at asks
  exact asks

/-- **One chunk asks every hash limb of every inactive switch, at the garbler's label.** -/
theorem asks_evalChunk_scale (O : Oracle) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec PlanB.coordinateBits)
    (k : Fin chunkCount) (j : Fin (2 ^ chunkWidth k)) (limb : Fin (limbCount lane))
    (off : j ≠ chunkOf bits k) :
    Asks (publicAnswer O)
      (Programs.evalChunkM lane (hotJoins O.1 lane delta bitKey) scale bits
        (selectBits bitKey bits) k)
      (.hash (scaleInput lane k j.val limb.val ((garbleChunk O.1 lane delta bitKey k).1 j))) := by
  unfold Programs.evalChunkM
  refine Asks.bind_right (Asks.bind_left ?_)
  have hot : (Programs.evalFoldM lane k (chunkValue bits k).toNat
      (labelAt (chunkLabels (selectBits bitKey bits) k))
      (joinAt (hotSlice (hotJoins O.1 lane delta bitKey) k)) (chunkWidth k)).eval (publicAnswer O)
        j = (garbleChunk O.1 lane delta bitKey k).1 j := by
    rw [Programs.eval_evalFoldM]
    show evalHot O.1 lane k (chunkWidth k) (hotSlice (hotJoins O.1 lane delta bitKey) k)
      (chunkLabels (selectBits bitKey bits) k) (chunkValue bits k) j = _
    rw [hotSlice_hotJoins, chunkLabels_selectBits]
    exact evalHot_agrees_off_active correlated bits k j off
  unfold Programs.evalMasksM
  refine Asks.bind_left (Asks.vector _ j ?_)
  simp only [if_neg off]
  rw [← hot]
  exact asks_switchMaskM O lane k j.val _ limb

/-- **One lane asks every inactive fold gate.** -/
theorem asks_evalLane_hot (O : Oracle) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec PlanB.coordinateBits)
    (k : Fin chunkCount) (n : Nat) (small : n < chunkWidth k) (r : Fin (2 ^ n)) (half : Bool)
    (off : r.val ≠ (chunkOf bits k).val % 2 ^ n) :
    Asks (publicAnswer O)
      (Programs.evalLaneM lane (hotJoins O.1 lane delta bitKey) scale bits (selectBits bitKey bits))
      (.fixedForward (hotIndexNat lane k n r.val half)
        ((garbleFold O.1 lane k delta (labelAt fun p => (chunkKey bitKey k p).1) n).1 r)) :=
  Asks.bind_left (Asks.vector _ k
    (asks_evalChunk_hot O lane delta bitKey correlated scale bits k n small r half off))

/-- **One lane asks every hash limb of every inactive switch.** -/
theorem asks_evalLane_scale (O : Oracle) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec PlanB.coordinateBits)
    (k : Fin chunkCount) (j : Fin (2 ^ chunkWidth k)) (limb : Fin (limbCount lane))
    (off : j ≠ chunkOf bits k) :
    Asks (publicAnswer O)
      (Programs.evalLaneM lane (hotJoins O.1 lane delta bitKey) scale bits (selectBits bitKey bits))
      (.hash (scaleInput lane k j.val limb.val ((garbleChunk O.1 lane delta bitKey k).1 j))) :=
  Asks.bind_left (Asks.vector _ k
    (asks_evalChunk_scale O lane delta bitKey correlated scale bits k j limb off))

end

end Kriterion.ArgoMAC.Security.Phase3
