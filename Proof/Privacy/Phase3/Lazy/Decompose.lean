/-
**Phase 3, P4b — the honest evaluation, chunk 0 of `curveX` first and chunk 0 of `pointX` inside.**

* `evalLaneM_split`: a lane's evaluation is its chunk-0 fold, its chunk-0 masks, then `laneRest`
  (the other 55 chunks and the continuation), which reads the chunk-0 masks only through their
  value.
* `openingQueriesM_split`: the honest evaluation is the `curveX` chunk-0 fold and masks, then
  `curveRest` (the other `curveX` chunks, `curveY`, the bridge hash, the pads), then `pointPart`
  (the `pointX` lane, then `pointY`).
* `pointPart_split`: `pointPart` is the `pointX` chunk-0 fold and masks, then `pointRest`.
* Where the rests ask: `curveRest_plain` (plain queries away from `curveX` chunk 0 and from both
  point lanes: fold indices `CurveRestIndex`, hash inputs off the `curveX` chunk-0 cells) and
  `pointRest_labelled` (every designated query of the `pointX` chunk-0 masks and `pointRest` carries
  the designated switch's label).
-/

import Proof.Privacy.Phase3.Lazy.Masks

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### A lane with chunk 0 split off -/

/-- The chunks `1 … 55` of a lane, then the continuation on the lane value, given the chunk-0
masks. -/
def laneRest {β : Type} (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Vector BaseField (laneCount lane))
    (k : (Fin (laneCount lane) → BaseField) → FreeQuery Programs.Spec β) :
    FreeQuery Programs.Spec β :=
  FreeQuery.vector 55 (fun index : Fin 55 =>
      Programs.evalChunkM lane joins scale bits labels index.succ) >>= fun rest =>
    k fun element => ∑ c : Fin chunkCount,
      ((vcons (Programs.evalScaleOf (chunkWidth chunkZero) masks (chunkOf bits chunkZero)
        (scale chunkZero)) rest : Vector (Fin (laneCount lane) → BaseField) chunkCount)).get c
        element

/-- **A lane's evaluation is its chunk-0 fold and masks, then the rest.** -/
theorem evalLaneM_split {β : Type} (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block)
    (k : (Fin (laneCount lane) → BaseField) → FreeQuery Programs.Spec β) :
    Programs.evalLaneM lane joins scale bits labels >>= k =
      Programs.evalFoldM lane chunkZero (chunkValue bits chunkZero).toNat
          (labelAt (chunkLabels labels chunkZero)) (joinAt (hotSlice joins chunkZero))
          (chunkWidth chunkZero) >>= fun hot =>
        Programs.evalMasksM lane chunkZero (chunkWidth chunkZero) hot
            (chunkOf bits chunkZero) >>= fun masks =>
          laneRest lane joins scale bits labels masks k := by
  have split : FreeQuery.vector chunkCount (Programs.evalChunkM lane joins scale bits labels)
      = Programs.evalChunkM lane joins scale bits labels chunkZero >>= fun x =>
        FreeQuery.vector 55 (fun index : Fin 55 =>
          Programs.evalChunkM lane joins scale bits labels index.succ) >>= fun v =>
            (Pure.pure (vcons x v) :
              FreeQuery Programs.Spec (Vector (Fin (laneCount lane) → BaseField) chunkCount)) :=
    vector_succ_first 55 (Programs.evalChunkM lane joins scale bits labels)
  unfold Programs.evalLaneM
  rw [fq_bind_assoc, split, fq_bind_assoc]
  unfold Programs.evalChunkM
  simp only [fq_bind_assoc, fq_pure_bind]
  rfl

/-! ### The honest evaluation -/

variable [FieldCertificate]

/-- After `curveX`: the `curveY` lane, the bridge hash and the pads. -/
def curveTail (table : Public) (bits : BitInput) (mac : InputMac)
    (curveX : Fin curveElementCountX → BaseField) :
    Programs.M (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :=
  Programs.evalLaneM .curveY table.curveYHot
      (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y) >>= fun curveY =>
    Programs.askHash (bridgeInput (CurveMembership.evaluate table.curve bits.toAffine
        (Pipeline.curveValues curveX curveY))) >>= fun hashed =>
      whitePadsM ⟨hashed.1, hashed.2⟩

/-- After the pads: the `pointX` lane, then the `pointY` lane. -/
def pointPart (table : Public) (bits : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    Programs.M ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) :=
  Programs.evalLaneM .pointX table.pointXHot
      (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)
    >>= fun pointX =>
  Programs.evalLaneM .pointY table.pointYHot
      (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
    >>= fun pointY => Pure.pure (pointX, pointY)

/-- After the `curveX` chunk-0 masks: the other `curveX` chunks, `curveY`, the bridge hash, the
pads. -/
def curveRest (table : Public) (bits : BitInput) (mac : InputMac)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Vector BaseField curveElementCountX) :
    Programs.M (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :=
  laneRest .curveX table.curveXHot
    (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x) masks (curveTail table bits mac)

/-- **The honest evaluation, split**: the `curveX` chunk-0 fold and masks, then `curveRest`, then
`pointPart`. -/
theorem openingQueriesM_split (table : Public) (bits : BitInput) (mac : InputMac) :
    openingQueriesM table bits mac =
      Programs.evalFoldM .curveX chunkZero (chunkValue (Pipeline.coordBits bits .x) chunkZero).toNat
          (labelAt (chunkLabels (Pipeline.macLabels mac .x) chunkZero))
          (joinAt (hotSlice table.curveXHot chunkZero)) (chunkWidth chunkZero) >>= fun hot =>
        Programs.evalMasksM .curveX chunkZero (chunkWidth chunkZero) hot
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= fun masks =>
          curveRest table bits mac masks >>= pointPart table bits mac := by
  have shape : openingQueriesM table bits mac =
      Programs.evalLaneM .curveX table.curveXHot
        (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
        (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x) >>= fun curveX =>
          curveTail table bits mac curveX >>= pointPart table bits mac := by
    unfold openingQueriesM curveTail pointPart
    simp only [fq_bind_assoc]
  rw [shape, evalLaneM_split]
  unfold curveRest laneRest
  simp only [fq_bind_assoc]

/-- The rest of the `pointX` lane, then `pointY`. -/
def pointRest (table : Public) (bits : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Vector BaseField pointElementCountX) :
    Programs.M ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) :=
  laneRest .pointX table.pointXHot
    (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x) masks
    fun pointX =>
      Programs.evalLaneM .pointY table.pointYHot
          (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
          (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
        >>= fun pointY => Pure.pure (pointX, pointY)

/-- **`pointPart` is the `pointX` chunk-0 fold and masks, then `pointRest`.** -/
theorem pointPart_split (table : Public) (bits : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    pointPart table bits mac pads =
      Programs.evalFoldM .pointX chunkZero (chunkValue (Pipeline.coordBits bits .x) chunkZero).toNat
          (labelAt (chunkLabels (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x) chunkZero))
          (joinAt (hotSlice table.pointXHot chunkZero)) (chunkWidth chunkZero) >>= fun hot =>
        Programs.evalMasksM .pointX chunkZero (chunkWidth chunkZero) hot
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= fun masks =>
          pointRest table bits mac pads masks := by
  unfold pointPart pointRest
  rw [evalLaneM_split]

/-! ### Where the rests ask -/

/-- A fold index is at one (lane, chunk) only. -/
theorem indexAt_unique {lane lane' : Lane} {chunk chunk' : Fin chunkCount} {index : FixedIndex}
    (first : IndexAt lane chunk index) (second : IndexAt lane' chunk' index) :
    lane = lane' ∧ chunk = chunk' := by
  cases index with
  | hot l c _ _ _ => exact ⟨first.1.symm.trans second.1, first.2.symm.trans second.2⟩
  | gadget _ _ _ => exact first.elim

/-- A cell input is at one (lane, chunk) only. -/
theorem cellAt_unique {lane lane' : Lane} {chunk chunk' : Fin chunkCount} {input : BaseField}
    (first : CellAt lane chunk input) (second : CellAt lane' chunk' input) :
    lane = lane' ∧ chunk = chunk' := by
  obtain ⟨cell, label, rfl, rfl, rfl⟩ := first
  obtain ⟨cell', label', rfl, rfl, same⟩ := second
  have pair := cellInput_injective (a₁ := (cell', label')) (a₂ := (cell, label)) same
  simp only [Prod.mk.injEq] at pair
  rw [pair.1]
  exact ⟨rfl, rfl⟩

/-- A designated input is a cell input of chunk 0 of `pointX`. -/
theorem designated_cellAt {bits : BitInput} {input : BaseField}
    (designated : IsDesignated bits input) : CellAt .pointX chunkZero input := by
  obtain ⟨limb, label, rfl⟩ := (isDesignated_iff bits input).mp designated
  exact scaleInput_cellAt .pointX chunkZero (designatedSwitch bits) limb label

/-- The bridge input is no cell input. -/
theorem bridgeInput_not_cellAt (t : BaseField) (lane : Lane) (chunk : Fin chunkCount) :
    ¬ CellAt lane chunk (bridgeInput t) := by
  rintro ⟨cell, label, _, _, same⟩
  exact bridgeInput_ne_scaleInput t _ _ _ _ _ same.symm

/-- The fold indices the rest of `curveX`, `curveY` and the hash and pads may touch. -/
def CurveRestIndex (index : FixedIndex) : Prop :=
  (∃ c : Fin 55, IndexAt .curveX c.succ index) ∨ ∃ c, IndexAt .curveY c index

/-- The hash inputs the rest of `curveX`, `curveY`, the hash and the pads may ask: every input but
the `curveX` chunk-0 cells'. -/
def CurveRestInput (input : BaseField) : Prop := ¬ CellAt .curveX chunkZero input

theorem chunk_succ_ne_zero (c : Fin 55) : (c.succ : Fin chunkCount) ≠ chunkZero := by
  intro same
  have := congrArg Fin.val same
  simp [chunkZero] at this

theorem evalLaneM_allQ (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    AllQ (fun request => ∃ c, LaneAt lane c request)
      (Programs.evalLaneM lane joins scale bits labels) :=
  (AllQ.vector fun c => (evalChunkM_allQ lane joins scale bits labels c).mono
    fun _ inside => ⟨c, inside⟩).bind fun _ => .pure _

/-- The chunks `1 … 55` of a lane ask at their own chunks. -/
theorem laneRest_allQ {β : Type} (P : Request → Prop) (lane : Lane)
    (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Vector BaseField (laneCount lane))
    (k : (Fin (laneCount lane) → BaseField) → FreeQuery Programs.Spec β)
    (chunks : ∀ (c : Fin 55) (r : Request), LaneAt lane c.succ r → P r)
    (rest : ∀ value, AllQ P (k value)) :
    AllQ P (laneRest lane joins scale bits labels masks k) :=
  (AllQ.vector fun c => (evalChunkM_allQ lane joins scale bits labels c.succ).mono
    (chunks c)).bind fun _ => rest _

/-- A query of a (lane, chunk) other than chunk 0 of `curveX` and `pointX` is plain. -/
theorem plain_of_laneAt {bits : BitInput} {lane : Lane} {chunk : Fin chunkCount}
    (awayCurve : ¬ (lane = .curveX ∧ chunk = chunkZero))
    (awayPoint : ¬ (lane = .pointX ∧ chunk = chunkZero))
    (inside : ∀ index, IndexAt lane chunk index → CurveRestIndex index) (r : Request)
    (at' : LaneAt lane chunk r) : Plain bits CurveRestIndex CurveRestInput r := by
  cases r with
  | fixedForward index _ =>
      rcases at' with fixed | hashed
      · exact inside index fixed
      · exact hashed.elim
  | hash input =>
      rcases at' with fixed | hashed
      · exact fixed.elim
      · exact ⟨fun curve => awayCurve (cellAt_unique hashed curve),
          fun designated => awayPoint (cellAt_unique hashed (designated_cellAt designated))⟩
  | fixedInverse _ _ => rcases at' with h | h <;> exact h.elim
  | encForward _ _ => rcases at' with h | h <;> exact h.elim
  | encInverse _ _ => rcases at' with h | h <;> exact h.elim

/-- **`curveRest` asks plain queries: fold indices in `CurveRestIndex`, hash inputs off the
`curveX` chunk-0 cells, the pads.** -/
theorem curveRest_plain (bits : BitInput) (table : Public) (bits' : BitInput) (mac : InputMac)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Vector BaseField curveElementCountX) :
    AllQ (Plain bits CurveRestIndex CurveRestInput) (curveRest table bits' mac masks) := by
  refine laneRest_allQ _ _ _ _ _ _ _ _ (fun c r at' => plain_of_laneAt
    (fun both => chunk_succ_ne_zero c both.2) (by simp)
    (fun index inside => Or.inl ⟨c, inside⟩) r at') fun curveX => ?_
  have bridge : ∀ t : BaseField, AllQ (Plain bits CurveRestIndex CurveRestInput)
      (Programs.askHash (bridgeInput t)) := fun t =>
    .query (.hash (bridgeInput t)) FreeQuery.pure ⟨bridgeInput_not_cellAt t _ _,
      fun designated => bridgeInput_not_cellAt t _ _ (designated_cellAt designated)⟩
      fun _ => .pure _
  refine ((evalLaneM_allQ _ _ _ _ _).mono fun r at' => ?_).bind fun _ =>
    (bridge _).bind fun _ => (whitePadsM_allQ _).mono fun r enc => ?_
  · obtain ⟨c, at'⟩ := at'
    exact plain_of_laneAt (by simp) (by simp) (fun index inside => Or.inr ⟨c, inside⟩) r at'
  · cases r with
    | encForward _ _ => trivial
    | _ => exact enc.elim

/-- **Every designated query of the `pointX` chunk-0 masks and `pointRest` carries the designated
switch's label.** -/
theorem pointRest_labelled (bits : BitInput) (table : Public) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (hot : HotLabels (chunkWidth chunkZero)) :
    AllQ (Labelled bits (hot (designatedSwitch bits)))
      (Programs.evalMasksM .pointX chunkZero (chunkWidth chunkZero) hot
          (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>=
        pointRest table bits mac pads) := by
  refine ((evalMasksM_asks .pointX chunkZero hot _).mono fun r inside => ?_).bind
    fun masks => ?_
  · intro input same designated
    obtain ⟨switch, limb, asked⟩ := inside
    rw [same] at asked
    cases asked
    rw [designated_maskCell designated]
    exact scaleLabel_scaleInput _ _ _ _ _
  · refine laneRest_allQ _ _ _ _ _ _ _ _ (fun c r at' => ?_) fun pointX => ?_
    · intro input same designated
      subst same
      rcases at' with fixed | hashed
      · exact fixed.elim
      · exact absurd (cellAt_unique hashed (designated_cellAt designated)).2
          (chunk_succ_ne_zero c)
    · refine ((evalLaneM_allQ _ _ _ _ _).mono fun r at' => ?_).bind fun _ => .pure _
      intro input same designated
      subst same
      obtain ⟨c, at'⟩ := at'
      rcases at' with fixed | hashed
      · exact fixed.elim
      · exact absurd (cellAt_unique hashed (designated_cellAt designated)).1 (by decide)

end

end Kriterion.ArgoMAC.Phase3.Lazy
