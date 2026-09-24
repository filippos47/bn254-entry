/-
**Phase 3, P1r — `LawOn`, step (E), part 1: the evaluator's values read only the tape's limbs.**

An answer function *reads the tape* `T` (`TapeOn`) when every limb question `(cell, label)` — the
hash at `cellInput cell label` — is answered `T cell`, whatever the label: the table answers
(`tableAnswer`) and every overlaid oracle (`overlay`) do. On such answers every lane of the
evaluator delivers `laneValue` — the free fold of the tape's mask vectors at the switches off the
active one, the active one recovered from the published join — whatever the lane's labels and
whatever the fold gates answer (`evalLaneM_tape`): the fold answers only move the one-hot labels,
the labels of the limb questions, and a limb's answer does not see its label. Consequences:

* `openingQueriesM_tape`: `HW`'s opening delivers the point lanes' `laneValue`s — so the collector
  targets of the private side do not read the oracle's fixed-key answers, nor the pads, nor the
  hash off the limbs;
* `curvePrefixM_tape`: the prefix asks the hash at `bridgeInput (curveKey …)` (the curve lanes'
  `laneValue`s), and returns the answer there.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnOpening

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (openingQueriesM whitePadsM)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape cellInput)
open scoped ENNReal

noncomputable section

/-! ### 1. Answers that read a tape -/

/-- **Every limb question is answered by the tape's limb, whatever its label.** -/
def TapeOn (a : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) (T : Tape) : Prop :=
  ∀ (cell : Cell) (label : Block), a (.hash (cellInput cell label)) = T cell

theorem tapeOn_table (A : Table) : TapeOn (tableAnswer A) A.2.2.2 := tableAnswer_cell A

theorem tapeOn_overlay [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex] (T : Tape)
    (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    TapeOn (publicAnswer (OnLaw.overlay T O)) T := OnLaw.overlay_cell T O

variable {a : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer} {T : Tape}

/-- A switch's mask vector on answers that read a tape: the tape's, whatever the label. -/
theorem switchMaskM_tape (reads : TapeOn a T) (lane : Lane) (c : Fin chunkCount)
    (j : Fin (2 ^ chunkWidth c)) (label : Block) :
    (Programs.switchMaskM lane c j.val label).eval a =
      Vector.ofFn (masksOf VectorSite.lane T ⟨lane, c, j⟩) := by
  simp only [Programs.switchMaskM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    Programs.vector_get_ofFn]
  have limbs : ∀ limb : Fin (limbCount lane),
      (Programs.askHash (scaleInput lane c j.val limb.val label)).eval a = T ⟨⟨lane, c, j⟩, limb⟩ :=
    fun limb => reads ⟨⟨lane, c, j⟩, limb⟩ label
  simp only [limbs]
  rfl

/-- The mask vectors a chunk reads: the tape's, off the active switch (zeros at the active one). -/
def chunkMasks (lane : Lane) (c : Fin chunkCount) (alpha : Fin (2 ^ chunkWidth c)) (T : Tape) :
    Fin (2 ^ chunkWidth c) → Vector BaseField (laneCount lane) :=
  fun j => if j = alpha then Vector.ofFn fun _ => 0 else Vector.ofFn (masksOf VectorSite.lane T ⟨lane, c, j⟩)

theorem evalMasksM_tape (reads : TapeOn a T) (lane : Lane) (c : Fin chunkCount)
    (hot : HotLabels (chunkWidth c)) (alpha : Fin (2 ^ chunkWidth c)) :
    (Programs.evalMasksM lane c (chunkWidth c) hot alpha).eval a = chunkMasks lane c alpha T := by
  funext j
  simp only [Programs.evalMasksM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    Vector.get_ofFn, chunkMasks]
  by_cases active : j = alpha
  · rw [if_pos active, if_pos active]
    rfl
  · rw [if_neg active, if_neg active, switchMaskM_tape reads]

/-- **A lane's delivered values from the tape**: per chunk the free fold of the mask vectors off the
active switch, the active one recovered from the published join. -/
def laneValue (lane : Lane) (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (bits : BitVec coordinateBitCount) (T : Tape) : Fin (laneCount lane) → BaseField :=
  fun e => ∑ c : Fin chunkCount,
    Programs.evalScaleOf (chunkWidth c) (chunkMasks lane c (chunkOf bits c) T) (chunkOf bits c) (scale c) e

/-- **On answers that read a tape a lane delivers `laneValue`**, whatever its labels and fold joins. -/
theorem evalLaneM_tape (reads : TapeOn a T) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    (Programs.evalLaneM lane joins scale bits labels).eval a = laneValue lane scale bits T := by
  funext e
  simp only [Programs.evalLaneM, Programs.evalChunkM, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_vector, Vector.get_ofFn, evalMasksM_tape reads, laneValue]

/-! ### 2. The opening and the prefix -/

variable [FieldCertificate]

/-- The point lanes' delivered values. -/
def pointValues (P : Public) (bits : BitInput) (T : Tape) :
    (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField) :=
  (laneValue .pointX (fun chunk => Pipeline.readPointX (unpack (P.scale.get chunk)))
      (Pipeline.coordBits bits .x) T,
    laneValue .pointY (fun chunk => Pipeline.readPointY (unpack (P.scale.get chunk)))
      (Pipeline.coordBits bits .y) T)

/-- The curve lanes' bridge value. -/
def curveKey (P : Public) (bits : BitInput) (T : Tape) : BaseField :=
  CurveMembership.evaluate P.curve bits.toAffine
    (Pipeline.curveValues
      (laneValue .curveX (fun chunk => Pipeline.readCurveX (unpack (P.scale.get chunk)))
        (Pipeline.coordBits bits .x) T)
      (laneValue .curveY (fun chunk => Pipeline.readCurveY (unpack (P.scale.get chunk)))
        (Pipeline.coordBits bits .y) T))

/-- **`HW`'s opening delivers the point lanes' `laneValue`s** on answers that read a tape. -/
theorem openingQueriesM_tape (reads : TapeOn a T) (P : Public) (bits : BitInput) (mac : InputMac) :
    (openingQueriesM P bits mac).eval a = pointValues P bits T := by
  unfold openingQueriesM
  simp only [FreeQuery.eval_bind, FreeQuery.eval_pure, evalLaneM_tape reads]
  rfl

/-- **The prefix returns the hash answer at the bridge input of the curve lanes' value.** -/
theorem curvePrefixM_tape (reads : TapeOn a T) (P : Public) (bits : BitInput) (mac : InputMac) :
    (curvePrefixM P bits mac).eval a = a (.hash (bridgeInput (curveKey P bits T))) := by
  unfold curvePrefixM
  simp only [FreeQuery.eval_bind, evalLaneM_tape reads]
  rfl

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
