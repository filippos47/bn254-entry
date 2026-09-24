/-
**Phase 3, P1l — the two laws, part 4: system A asks each fixed-key index and each limb once.**

`systemAM` (the evaluator's two curve lanes) asks forward fixed-key questions and hash limbs only,
each at most once and all of the two curve lanes (`once_systemAM`): per (lane, chunk), at every paid
fold step `n < b_c` (`b_c ∈ {2, 4}`), both halves of every gate off the step's active parent
(`once_evalFoldM`), and the `limbCount ℓ` limbs of every switch off the active one
(`once_evalMasksM`). Hence (`LawsFill.runFill_once`) its fill run from a state empty at the curve
lanes' gates and limbs is its run on a uniform table.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsFill

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Phase3.Lazy (Cell)
open scoped ENNReal

noncomputable section

/-! ### Index and limb sets -/

/-- The fold gates of one lane. -/
def onceLaneSet (lane : Lane) : Set FixedIndex :=
  {index | ∃ chunk fold entry half, index = FixedIndex.hot lane chunk fold entry half}

/-- The switch-mask limbs of one lane. -/
def onceCellSet (lane : Lane) : Set Cell := {cell | cell.1.lane = lane}

/-- The switch-mask limbs of one (lane, chunk). -/
def chunkCellSet (lane : Lane) (chunk : Fin chunkCount) : Set Cell :=
  {cell | cell.1.lane = lane ∧ cell.1.chunk = chunk}

/-- A computation followed by a pure step. -/
theorem OnceIn.map {α β : Type} {X : Set FixedIndex} {Y : Set Cell}
    {c : FreeQuery Programs.Spec α} (once : OnceIn X Y c) (g : α → β) :
    OnceIn X Y (c >>= fun v => Pure.pure (g v)) :=
  (once.bind (fun v => OnceIn.pure' ∅ ∅ (g v)) (Set.disjoint_empty X)
    (Set.disjoint_empty Y)).mono (by simp) (by simp)

/-! ### The fold, at every chunk width -/

theorem once_foldMaskM (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat) (label : Block)
    (small : step < chunkBits) (entrySmall : entry < 2 ^ chunkBits) :
    OnceIn (gateSet lane chunk step entry) ∅ (Programs.foldMaskM lane chunk step entry label) := by
  have apart : Disjoint ({hotIndexNat lane chunk step entry false} : Set FixedIndex)
      {hotIndexNat lane chunk step entry true} := by
    rw [Set.disjoint_singleton]
    intro same
    exact Bool.false_ne_true (hotIndexNat_inj small small entrySmall entrySmall same).2.2.2.2
  have whole := (OnceIn.hashM (hotIndexNat lane chunk step entry false) label).bind
    (fun first => (OnceIn.hashM (hotIndexNat lane chunk step entry true) label).map
      (fun second => first ^^^ second)) apart (Set.disjoint_empty ∅)
  refine whole.mono ?_ (by simp)
  rintro i (same | same)
  · exact ⟨false, same⟩
  · exact ⟨true, same⟩

theorem once_evalStepM (lane : Lane) (chunk : Fin chunkCount) (step : Nat) (bitLabel join : Block)
    (active : Fin (2 ^ step)) (parent : Fin (2 ^ step) → Block) (small : step < chunkBits) :
    OnceIn (levelSet lane chunk step) ∅
      (Programs.evalStepM lane chunk step bitLabel join active parent) := by
  have entryBound : ∀ e : Fin (2 ^ step), e.val < 2 ^ chunkBits := fun e =>
    lt_of_lt_of_le e.isLt (Nat.pow_le_pow_right (by norm_num) small.le)
  have each := OnceIn.vector (2 ^ step) (fun e => gateSet lane chunk step e.val) (fun _ => ∅)
    (fun e => if e = active then Pure.pure 0 else
      Programs.foldMaskM lane chunk step e.val (parent e))
    (fun e => OnceIn.ite _ _ _ _ _
      (once_foldMaskM lane chunk step e.val (parent e) small (entryBound e)))
    (fun e e' different => by
      rw [Set.disjoint_left]
      rintro i ⟨h, rfl⟩ ⟨h', same⟩
      exact different (Fin.ext (hotIndexNat_inj small small (entryBound e) (entryBound e')
        same).2.2.2.1))
    (fun _ _ _ => Set.disjoint_empty _)
  unfold Programs.evalStepM
  refine (each.map _).mono ?_ (by simp)
  intro i member
  obtain ⟨e, ⟨half, rfl⟩⟩ := Set.mem_iUnion.mp member
  exact ⟨e.val, half, e.isLt, rfl⟩

/-- **A chunk's fold asks each gate of its paid steps at most once.** -/
theorem once_evalFoldM (lane : Lane) (chunk : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) : ∀ n, n ≤ chunkBits →
      OnceIn (foldSet lane chunk n) ∅ (Programs.evalFoldM lane chunk value bitLabel join n)
  | 0, _ => OnceIn.pure' _ _ _
  | n + 1, bound => by
      have prefixOnce := once_evalFoldM lane chunk value bitLabel join n (by omega)
      have whole := prefixOnce.bind (fun previous => (once_evalStepM lane chunk n (bitLabel n)
        (join n) (activeAt value n) previous (by omega)).map (extendLevel n previous)) (by
          rw [Set.disjoint_left]
          rintro i ⟨k, hk, e, half, he, rfl⟩ ⟨e', half', he', same⟩
          have ek : e < 2 ^ chunkBits :=
            lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) (by omega))
          have en : e' < 2 ^ chunkBits :=
            lt_of_lt_of_le he' (Nat.pow_le_pow_right (by norm_num) (by omega))
          have := (hotIndexNat_inj (by omega) (by omega) ek en same).2.2.1
          omega) (Set.disjoint_empty ∅)
      unfold Programs.evalFoldM
      refine whole.mono ?_ (by simp)
      rintro i (⟨k, hk, rest⟩ | rest)
      · exact ⟨k, by omega, rest⟩
      · exact ⟨n, by omega, rest⟩

/-! ### The masks -/

/-- **A chunk's masks ask each limb of its inactive switches at most once.** -/
theorem once_evalMasksM (lane : Lane) (chunk : Fin chunkCount) (hot : HotLabels (chunkWidth chunk))
    (alpha : Fin (2 ^ chunkWidth chunk)) :
    OnceIn ∅ (chunkCellSet lane chunk)
      (Programs.evalMasksM lane chunk (chunkWidth chunk) hot alpha) := by
  have each := OnceIn.vector (2 ^ chunkWidth chunk) (fun _ => ∅)
    (fun switch => {cell : Cell | cell.1 = ⟨lane, chunk, switch⟩})
    (fun switch => if switch = alpha then Pure.pure (Vector.ofFn fun _ => 0) else
      Programs.switchMaskM lane chunk switch.val (hot switch))
    (fun switch => OnceIn.ite _ _ _ _ _ (OnceIn.switchMaskM lane chunk switch (hot switch)))
    (fun _ _ _ => Set.disjoint_empty _)
    (fun switch switch' different => by
      rw [Set.disjoint_left]
      intro cell inside inside'
      rw [Set.mem_ofPred_eq] at inside inside'
      rw [inside] at inside'
      exact different (eq_of_heq (Security.Phase3.VectorSite.mk.inj inside').2.2))
  unfold Programs.evalMasksM
  refine (each.map _).mono (by simp) ?_
  intro cell member
  obtain ⟨switch, same⟩ := Set.mem_iUnion.mp member
  rw [Set.mem_ofPred_eq] at same
  exact ⟨by rw [same], by rw [same]⟩

/-! ### One chunk, one lane, system A -/

theorem once_evalChunkM (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (chunk : Fin chunkCount) :
    OnceIn (foldSet lane chunk (chunkWidth chunk)) (chunkCellSet lane chunk)
      (Programs.evalChunkM lane joins scale bits labels chunk) := by
  have fold := once_evalFoldM lane chunk (chunkValue bits chunk).toNat
    (labelAt (chunkLabels labels chunk)) (joinAt (hotSlice joins chunk)) (chunkWidth chunk)
    (chunkWidth_le chunk)
  unfold Programs.evalChunkM
  exact (fold.bind (fun hot => (once_evalMasksM lane chunk hot (chunkOf bits chunk)).map _)
    (Set.disjoint_empty _) (Set.empty_disjoint _)).mono (by simp) (by simp)

/-- **A lane of the evaluator asks each fold gate and each limb of its lane at most once.** -/
theorem once_evalLaneM (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    OnceIn (onceLaneSet lane) (onceCellSet lane)
      (Programs.evalLaneM lane joins scale bits labels) := by
  unfold Programs.evalLaneM
  refine (OnceIn.map (OnceIn.vector chunkCount (fun c => foldSet lane c (chunkWidth c))
    (chunkCellSet lane) _ (once_evalChunkM lane joins scale bits labels) (fun c c' different => ?_)
    (fun c c' different => ?_)) _).mono ?_ ?_
  · rw [Set.disjoint_left]
    rintro i ⟨n, hn, e, half, he, rfl⟩ ⟨n', hn', e', half', he', same⟩
    have bound : ∀ k, k < chunkBits → 2 ^ k ≤ 2 ^ chunkBits :=
      fun k h => Nat.pow_le_pow_right (by norm_num) h.le
    have small := lt_of_lt_of_le hn (chunkWidth_le c)
    have small' := lt_of_lt_of_le hn' (chunkWidth_le c')
    exact different (hotIndexNat_inj small small' (lt_of_lt_of_le he (bound n small))
      (lt_of_lt_of_le he' (bound n' small')) same).2.1
  · rw [Set.disjoint_left]
    rintro cell ⟨_, inside⟩ ⟨_, inside'⟩
    exact different (inside.symm.trans inside')
  · intro i member
    obtain ⟨c, inside⟩ := Set.mem_iUnion.mp member
    obtain ⟨fold, entry, half, rfl⟩ := hot_of_foldSet inside
    exact ⟨c, fold, entry, half, rfl⟩
  · intro cell member
    obtain ⟨c, inside, _⟩ := Set.mem_iUnion.mp member
    exact inside

variable [FieldCertificate]

/-- **System A asks each fold gate and each limb of the curve lanes at most once.** -/
theorem once_systemAM (table : Public) (bits : BitInput) (mac : InputMac) :
    OnceIn (onceLaneSet .curveX ∪ onceLaneSet .curveY) (onceCellSet .curveX ∪ onceCellSet .curveY)
      (systemAM table bits mac) := by
  have lanesX : Disjoint (onceLaneSet Lane.curveX) (onceLaneSet Lane.curveY) := by
    rw [Set.disjoint_left]
    rintro i ⟨c, f, e, h, rfl⟩ ⟨c', f', e', h', same⟩
    simp only [FixedIndex.hot.injEq] at same
    cases same.1
  have lanesY : Disjoint (onceCellSet Lane.curveX) (onceCellSet Lane.curveY) := by
    rw [Set.disjoint_left]
    intro cell inside inside'
    have same : Lane.curveX = Lane.curveY := inside.symm.trans inside'
    cases same
  unfold systemAM
  exact (once_evalLaneM .curveX table.curveXHot _ (Pipeline.coordBits bits .x)
    (Pipeline.macLabels mac .x)).bind (fun _ => (once_evalLaneM .curveY table.curveYHot _
      (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y)).map fun _ => ()) lanesX lanesY

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
