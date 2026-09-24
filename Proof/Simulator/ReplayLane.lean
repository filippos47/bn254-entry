/-
**The replay, whole lanes.**

* `agree_chunkBody`: one chunk against `evalChunkM`, from the lane's cells (`LaneCells`);
* `agree_laneG`: a lane's chunk loop with a frame and an extra (record, memory) invariant;
* `agree_plainLane`: a plain lane (`curveX`, `curveY`, `pointY`) against `evalLaneM`;
* `agree_desLane`: lane `pointX` (`designatedLane`, chunk `0` designated) against `evalLaneM`,
  leaving `j*`, `E*`, `κ` and the complete record `fun _ => some E*` of the `452` designated
  inputs.
-/

import Proof.Simulator.ReplayChunk

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Addresses outside the replay's work cells -/

/-- An address outside the accumulators, the fold cells and `E*`, the temporaries and the
digit-extraction region. -/
def OffWork (address : Word) : Prop :=
  (∀ e, e < 733 → address ≠ word (accBase + e)) ∧
    (∀ j, j < 49 → address ≠ word (hotLabelBase + j)) ∧
    (∀ k, k < 16 → address ≠ word (tmpBase + k)) ∧ OffVector address

/-- Every address below `accBase` is outside the work cells. -/
theorem offWork_of_lt {value : Nat} (small : value < 2 ^ 46) : OffWork (word value) :=
  ⟨fun e bound => word_ne (by omega) (by unfold accBase; omega) (by unfold accBase; omega),
    fun j bound => word_ne (by omega) (by unfold hotLabelBase; omega)
      (by unfold hotLabelBase; omega),
    fun k bound => word_ne (by omega) (by unfold tmpBase; omega) (by unfold tmpBase; omega),
    fun index bound => word_ne (by omega) (by unfold vectorLimbBase; omega)
      (by unfold vectorLimbBase; omega)⟩

omit [FieldCertificate] in
theorem OffWork.chunkFrame {spec : Replay.LaneSpec} (ok : SpecOK spec) {address : Word}
    (off : OffWork address) : ChunkFrame spec address := by
  refine ⟨fun e bound => ?_, off.2.2.2, ⟨off.2.2.1 1 (by omega), fun index small =>
    off.2.1 index (by omega)⟩, off.2.2.1 0 (by omega)⟩
  have fits := ok.fits
  have cell := off.1 (spec.slot + e) (by omega)
  rwa [← Nat.add_assoc] at cell

omit [FieldCertificate] in
theorem specOK_curveX : SpecOK Replay.curveXSpec where
  fits := by decide
  labelsLow := by unfold Replay.curveXSpec labelBase; norm_num
  hotLow := by decide
  coordLow := by unfold Replay.curveXSpec reqX requestBase; norm_num

omit [FieldCertificate] in
theorem specOK_curveY : SpecOK Replay.curveYSpec where
  fits := by decide
  labelsLow := by unfold Replay.curveYSpec labelBase; norm_num
  hotLow := by decide
  coordLow := by unfold Replay.curveYSpec reqY requestBase; norm_num

omit [FieldCertificate] in
theorem specOK_pointX : SpecOK Replay.pointXSpec where
  fits := by decide
  labelsLow := by unfold Replay.pointXSpec whiteBase; norm_num
  hotLow := by decide
  coordLow := by unfold Replay.pointXSpec reqX requestBase; norm_num

omit [FieldCertificate] in
theorem specOK_pointY : SpecOK Replay.pointYSpec where
  fits := by decide
  labelsLow := by unfold Replay.pointYSpec whiteBase; norm_num
  hotLow := by decide
  coordLow := by unfold Replay.pointYSpec reqY requestBase; norm_num

omit [FieldCertificate] in
theorem OffWork.desFrame {address : Word} (off : OffWork address) : DesFrame address :=
  ⟨off.chunkFrame specOK_pointX, off.2.1 48 (by omega), off.2.2.1 6 (by omega),
    off.2.2.1 5 (by omega)⟩

/-- `E*`, `j*`, `κ` lie outside every chunk's cells of every lane. -/
theorem designated_chunkFrame {spec : Replay.LaneSpec} (ok : SpecOK spec) :
    ChunkFrame spec (word designatedLabel) ∧ ChunkFrame spec (word tmpJStar) ∧
      ChunkFrame spec (word tmpKappa) :=
  ⟨⟨(hotLabel_offAcc ok 48 (by omega)).1, (hotLabel_offAcc ok 48 (by omega)).2,
      ⟨hot_ne_tmp 48 1 (by omega) (by omega), fun index small =>
        hot_ne (show 48 < 49 by omega) (show index < 49 by omega) (by omega)⟩,
      hot_ne_tmp 48 0 (by omega) (by omega)⟩,
    ⟨(tmp_offAcc ok 6 (by omega)).1, (tmp_offAcc ok 6 (by omega)).2,
      ⟨tmp_ne (show 6 < 16 by omega) (show 1 < 16 by omega) (by omega), fun index small =>
        (hot_ne_tmp index 6 (by omega) (by omega)).symm⟩,
      tmp_ne (show 6 < 16 by omega) (show 0 < 16 by omega) (by omega)⟩,
    ⟨(tmp_offAcc ok 5 (by omega)).1, (tmp_offAcc ok 5 (by omega)).2,
      ⟨tmp_ne (show 5 < 16 by omega) (show 1 < 16 by omega) (by omega), fun index small =>
        (hot_ne_tmp index 5 (by omega) (by omega)).symm⟩,
      tmp_ne (show 5 < 16 by omega) (show 0 < 16 by omega) (by omega)⟩⟩

/-- An accumulator outside a lane's slots is outside that lane's chunk cells. -/
theorem acc_chunkFrame {spec : Replay.LaneSpec} (ok : SpecOK spec) (e : Nat) (small : e < 733)
    (outside : e < spec.slot ∨ spec.slot + laneCount spec.lane ≤ e) :
    ChunkFrame spec (word (accBase + e)) := by
  have fits := ok.fits
  refine ⟨fun e' bound => word_ne (by unfold accBase; omega) (by unfold accBase; omega)
      (by omega),
    fun index bound => word_ne (by unfold accBase; omega) (by unfold vectorLimbBase; omega)
      (by unfold accBase vectorLimbBase; omega),
    ⟨word_ne (by unfold accBase; omega) (by unfold tmpActive tmpBase; omega)
        (by unfold accBase tmpActive tmpBase; omega),
      fun index bound => word_ne (by unfold accBase; omega) (by unfold hotLabelBase; omega)
        (by unfold accBase hotLabelBase; omega)⟩,
    word_ne (by unfold accBase; omega) (by unfold tmpAlpha tmpBase; omega)
      (by unfold accBase tmpAlpha tmpBase; omega)⟩

/-! ### What a lane reads -/

omit [FieldCertificate] in
theorem hotAddress_small {spec : Replay.LaneSpec} (ok : SpecOK spec) (s : Fin foldStepCount) :
    hotBase + foldStepCount * spec.hotRow + s.val < 2 ^ 46 := by
  have hotLow := ok.hotLow
  have bound := s.isLt
  unfold foldStepCount at bound ⊢
  unfold hotBase
  omega

omit [FieldCertificate] in
theorem scaleAddress_small {spec : Replay.LaneSpec} (ok : SpecOK spec) (c : Fin chunkCount)
    (e : Fin (laneCount spec.lane)) :
    scaleCellBase + elementCount * c.val + spec.slot + e.val < 2 ^ 46 := by
  have fits := ok.fits
  have chunkBound := c.isLt
  have elementBound := e.isLt
  unfold chunkCount at chunkBound
  unfold scaleCellBase fieldBase curveCellCount rowCellCount elementCount
  omega

omit [FieldCertificate] in
/-- The lane's cells survive every run that leaves the addresses below `accBase` alone. -/
theorem LaneCells.transfer {spec : Replay.LaneSpec} (ok : SpecOK spec) {coord : Nat}
    {labels : Fin coordinateBitCount → Block} {joins : Vector Block foldStepCount}
    {scale : Fin chunkCount → Fin (laneCount spec.lane) → BaseField} {start memory : Memory}
    (cellsStart : LaneCells spec coord labels joins scale start)
    (low : ∀ value, value < 2 ^ 46 → memory.ram (word value) = start.ram (word value)) :
    LaneCells spec coord labels joins scale memory where
  coordCell := by rw [low _ ok.coordLow, cellsStart.coordCell]
  labelCells i := by
    have bound : i.val < 254 := i.isLt
    rw [low _ (by have := ok.labelsLow; omega), cellsStart.labelCells i]
  hotCells s := by rw [low _ (hotAddress_small ok s), cellsStart.hotCells s]
  scaleCells c e := by rw [low _ (scaleAddress_small ok c e), cellsStart.scaleCells c e]

/-! ### One chunk from the lane's cells -/

/-- **One chunk**, against `evalChunkM`, from the lane's cells. -/
theorem agree_chunkBody (bits : BitInput) (spec : Replay.LaneSpec) (ok : SpecOK spec)
    (designated : Bool) (coordBV : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount spec.lane) → BaseField) (chunk : Fin chunkCount)
    (memory : Memory) (record : DesignatedRecord) (accNow : Nat → BaseField)
    (lane : LaneCells spec coordBV.toNat labels joins scale memory)
    (cells : ∀ e, e < laneCount spec.lane → memory.ram (accCell spec e) = fieldWord (accNow e))
    (plainChunk : designated = false → spec.lane ≠ .pointX ∨ chunk ≠ chunkZero)
    (desChunk : designated = true → spec = Replay.pointXSpec ∧ chunk = chunkZero ∧
      (designatedSwitch bits).val = (chunkOf coordBV chunk).val ^^^ 1 ∧
      (activeSwitch bits).val = (chunkOf coordBV chunk).val) :
    Agree (ChunkPost bits spec designated accNow memory record)
      (rtree (Replay.chunkBody ordF0 spec designated chunk.val) memory)
      (interceptT bits (Programs.evalChunkM spec.lane joins scale coordBV labels chunk) record) := by
  unfold Programs.evalChunkM
  rw [show (chunkValue coordBV chunk).toNat = (chunkOf coordBV chunk).val from
    chunkValue_toNat coordBV chunk]
  refine agree_chunkCore bits spec ok designated chunk (chunkWidth chunk) rfl (chunkOf coordBV chunk)
    (labelAt (chunkLabels labels chunk)) (joinAt (hotSlice joins chunk)) (scale chunk) memory record
    accNow coordBV.toNat (lt_trans coordBV.isLt (by norm_num)) rfl lane.coordCell
    (fun step small => ?_) (by unfold joinAt; rw [if_pos rfl]) (fun step low high => ?_)
    (lane.scaleCells chunk) cells plainChunk desChunk
  · unfold labelAt
    rw [dif_pos small]
    unfold Replay.bitLabel
    rw [chunkFin_val, Nat.add_assoc spec.labels]
    exact lane.labelCells (chunkBitIndex chunk ⟨step, small⟩)
  · have inRange : step - 1 < chunkWidth chunk - 1 := by omega
    unfold joinAt
    rw [if_neg (by omega), dif_pos inRange]
    unfold hotSlice
    rw [Vector.get_ofFn]
    unfold Replay.hotJoin
    rw [chunkFin_val, Nat.add_assoc (hotBase + foldStepCount * spec.hotRow)]
    exact lane.hotCells (flatSlot chunk ⟨step - 1, inRange⟩)

/-! ### The general lane loop -/

/-- The invariant of a lane's chunk loop, with a frame and an extra invariant. -/
def LaneInv (spec : Replay.LaneSpec) (acc0 : Nat → BaseField) (start : Memory)
    (Frame : Word → Prop) (Extra : Nat → DesignatedRecord → Memory → Prop) (count : Nat)
    (state : Vector (Fin (laneCount spec.lane) → BaseField) count × DesignatedRecord)
    (memory : Memory) : Prop :=
  (∀ e : Fin (laneCount spec.lane), memory.ram (accCell spec e.val) = fieldWord (acc0 e.val +
      ∑ chunk : Fin count, state.1[chunk] e)) ∧
    (∀ address, Frame address → memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧ Extra count state.2 memory

/-- What a lane leaves. -/
def LanePost (spec : Replay.LaneSpec) (acc0 : Nat → BaseField) (start : Memory)
    (Frame : Word → Prop) (Final : DesignatedRecord → Memory → Prop)
    (result : (Fin (laneCount spec.lane) → BaseField) × DesignatedRecord) (after : Memory) : Prop :=
  (∀ e : Fin (laneCount spec.lane),
      after.ram (accCell spec e.val) = fieldWord (acc0 e.val + result.1 e)) ∧
    (∀ address, Frame address → after.ram address = start.ram address) ∧
    after.bits = start.bits ∧ Final result.2 after

/-- **A lane's chunk loop**, general frame and extra invariant. -/
theorem agree_laneG (bits : BitInput) (spec : Replay.LaneSpec) (bodies : Nat → Prog)
    (chunkProg : Fin chunkCount → FreeQuery Programs.Spec (Fin (laneCount spec.lane) → BaseField))
    (Frame : Word → Prop) (Extra : Nat → DesignatedRecord → Memory → Prop) (start : Memory)
    (record0 : DesignatedRecord) (acc0 : Nat → BaseField)
    (step : ∀ (chunk : Fin chunkCount) (memory : Memory) (record : DesignatedRecord)
      (accNow : Nat → BaseField), Extra chunk.val record memory →
      (∀ e, e < laneCount spec.lane → memory.ram (accCell spec e) = fieldWord (accNow e)) →
      (∀ address, Frame address → memory.ram address = start.ram address) →
      memory.bits = start.bits →
      Agree (LanePost spec accNow memory Frame (Extra (chunk.val + 1)))
        (rtree (bodies chunk.val) memory) (interceptT bits (chunkProg chunk) record))
    (extraStart : Extra 0 record0 start)
    (cells : ∀ e, e < laneCount spec.lane → start.ram (accCell spec e) = fieldWord (acc0 e)) :
    Agree (LanePost spec acc0 start Frame (Extra chunkCount))
      (rtree (Prog.rep chunkCount bodies) start)
      (interceptT bits (FreeQuery.bind (FreeQuery.vector chunkCount chunkProg) fun perChunk =>
        .pure fun e => ∑ chunk : Fin chunkCount, perChunk.get chunk e) record0) := by
  rw [interceptT_bind]
  have initial : LaneInv spec acc0 start Frame Extra 0 (#v[], record0) start := by
    refine ⟨fun e => ?_, fun _ _ => rfl, rfl, extraStart⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact cells e e.isLt
  have loop := agree_rep_vector bits bodies (LaneInv spec acc0 start Frame Extra) chunkCount
    chunkProg (fun chunk values record memory holds => by
      obtain ⟨accs, frame, bitsSame, extraHolds⟩ := holds
      have agree := step chunk memory record
        (fun e => if bound : e < laneCount spec.lane then acc0 e + ∑ earlier : Fin chunk.val,
          values[earlier] ⟨e, bound⟩ else 0) extraHolds
        (fun e bound => by rw [dif_pos bound]; exact accs ⟨e, bound⟩) frame bitsSame
      refine agree.mono fun result after post => ?_
      obtain ⟨accsAfter, frameAfter, bitsAfter, extraAfter⟩ := post
      refine ⟨fun e => ?_, fun address off => ?_, bitsAfter.trans bitsSame, extraAfter⟩
      · rw [accsAfter e]
        simp only [dif_pos e.isLt]
        rw [Fin.sum_univ_castSucc]
        try simp only [Fin.val_castSucc, Fin.val_last]
        rw [add_assoc]
        congr 3
        · refine Finset.sum_congr rfl fun earlier _ => ?_
          simp only [Fin.getElem_fin, Fin.val_castSucc, Vector.getElem_push_lt earlier.isLt]
        · simp only [Fin.getElem_fin, Fin.val_last, Vector.getElem_push_eq]
      · rw [frameAfter address off, frame address off]
      ) record0 start initial
  simp only [interceptT]
  exact Agree.map (Post' := LanePost spec acc0 start Frame (Extra chunkCount))
    (fun (state : Vector (Fin (laneCount spec.lane) → BaseField) chunkCount × DesignatedRecord) =>
      ((fun e => ∑ chunk : Fin chunkCount, state.1.get chunk e), state.2))
    (fun state after holds => ⟨fun e => by
      rw [holds.1 e]
      simp only [Vector.get_eq_getElem, Fin.getElem_fin], holds.2.1, holds.2.2.1, holds.2.2.2⟩) loop

/-! ### A plain lane -/

theorem rtree_lane (spec : Replay.LaneSpec) (memory : Memory) :
    rtree (Replay.lane ordF0 spec) memory =
      rtree (Prog.rep chunkCount fun chunk => Replay.chunkBody ordF0 spec false chunk) memory := by
  rw [show chunkCount = 55 + 1 from rfl, tree_rep_front]
  unfold Replay.lane
  rw [rtree_seq]
  rfl

/-- **A plain lane** (not lane `pointX`): the record unchanged. -/
theorem agree_plainLane (bits : BitInput) (spec : Replay.LaneSpec) (ok : SpecOK spec)
    (notX : spec.lane ≠ .pointX) (coordBV : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount spec.lane) → BaseField)
    (start : Memory) (record0 : DesignatedRecord) (acc0 : Nat → BaseField)
    (lane : LaneCells spec coordBV.toNat labels joins scale start)
    (cells : ∀ e, e < laneCount spec.lane → start.ram (accCell spec e) = fieldWord (acc0 e)) :
    Agree (LanePost spec acc0 start (ChunkFrame spec) fun record _ => record = record0)
      (rtree (Replay.lane ordF0 spec) start)
      (interceptT bits (Programs.evalLaneM spec.lane joins scale coordBV labels) record0) := by
  rw [rtree_lane]
  refine agree_laneG bits spec (fun chunk => Replay.chunkBody ordF0 spec false chunk)
    (Programs.evalChunkM spec.lane joins scale coordBV labels) (ChunkFrame spec)
    (fun _ record _ => record = record0) start record0 acc0
    (fun chunk memory record accNow extra accs frame bitsSame => ?_) rfl cells
  have laneNow := lane.transfer ok fun value small =>
    frame _ ((offWork_of_lt small).chunkFrame ok)
  refine (agree_chunkBody bits spec ok false coordBV labels joins scale chunk memory record accNow
    laneNow accs (fun _ => Or.inl notX) (fun absurdity => by cases absurdity)).mono
    fun result after post => ?_
  obtain ⟨accsAfter, frameAfter, bitsAfter, recordAfter, -⟩ := post
  exact ⟨accsAfter, fun address off => frameAfter address off (fun absurdity => by cases absurdity),
    bitsAfter, (recordAfter rfl).trans extra⟩

/-! ### The designated lane -/

/-- The chunk bodies of `designatedLane`, as one family. -/
def desBodies (chunk : Nat) : Prog :=
  if chunk = 0 then Replay.chunkBody ordF0 Replay.pointXSpec true 0
  else Replay.chunkBody ordF0 Replay.pointXSpec false chunk

theorem rtree_designatedLane (memory : Memory) :
    rtree (Replay.designatedLane ordF0 Replay.pointXSpec) memory =
      rtree (Prog.rep chunkCount desBodies) memory := by
  rw [show chunkCount = 55 + 1 from rfl, tree_rep_front]
  unfold Replay.designatedLane
  rw [rtree_seq]
  have first : desBodies 0 = Replay.chunkBody ordF0 Replay.pointXSpec true 0 := if_pos rfl
  have rest : (fun index => desBodies (index + 1)) =
      fun chunk => Replay.chunkBody ordF0 Replay.pointXSpec false (chunk + 1) := by
    funext index
    exact if_neg (Nat.succ_ne_zero index)
  rw [first, rest]
  rfl

/-- What the designated chunk leaves for the rest of the lane: `E*`, `j*`, `κ` and the complete
record. -/
def DesExtra (bits : BitInput) (count : Nat) (record : DesignatedRecord) (memory : Memory) : Prop :=
  1 ≤ count → ∃ star : Block, record = (fun _ => some star) ∧
    memory.ram (word designatedLabel) = blockWord star ∧
    memory.ram (word tmpJStar) = word (designatedSwitch bits).val ∧
    memory.ram (word tmpKappa) = fieldWord (kappa bits)

/-- **Lane `pointX`**, chunk `0` designated. -/
theorem agree_desLane (bits : BitInput) (labels : Fin coordinateBitCount → Block)
    (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount Replay.pointXSpec.lane) → BaseField)
    (start : Memory) (record0 : DesignatedRecord) (acc0 : Nat → BaseField)
    (lane : LaneCells Replay.pointXSpec (Pipeline.coordBits bits .x).toNat labels joins scale start)
    (cells : ∀ e, e < laneCount Replay.pointXSpec.lane →
      start.ram (accCell Replay.pointXSpec e) = fieldWord (acc0 e)) :
    Agree (LanePost Replay.pointXSpec acc0 start DesFrame (DesExtra bits chunkCount))
      (rtree (Replay.designatedLane ordF0 Replay.pointXSpec) start)
      (interceptT bits (Programs.evalLaneM .pointX joins scale (Pipeline.coordBits bits .x) labels)
        record0) := by
  have ok := specOK_pointX
  rw [rtree_designatedLane]
  refine agree_laneG bits Replay.pointXSpec desBodies
    (Programs.evalChunkM .pointX joins scale (Pipeline.coordBits bits .x) labels)
    DesFrame (DesExtra bits) start record0 acc0 ?_ (fun small => absurd small (by omega)) cells
  intro chunk memory record accNow extra accs frame bitsSame
  have laneNow := lane.transfer ok fun value small => frame _ (offWork_of_lt small).desFrame
  by_cases zero : chunk.val = 0
  · -- the designated chunk
    have chunkIs : chunk = chunkZero := Fin.ext zero
    subst chunkIs
    have body : desBodies chunkZero.val =
        Replay.chunkBody ordF0 Replay.pointXSpec true chunkZero.val := if_pos rfl
    rw [body]
    refine (agree_chunkBody bits Replay.pointXSpec ok true (Pipeline.coordBits bits .x) labels joins
      scale chunkZero memory record accNow laneNow accs (fun absurdity => by cases absurdity)
      (fun _ => ⟨rfl, rfl, rfl, rfl⟩)).mono fun result after post => ?_
    obtain ⟨accsAfter, frameAfter, bitsAfter, -, extraAfter⟩ := post
    exact ⟨accsAfter, fun address off => frameAfter address off.1 fun _ => off.2, bitsAfter,
      fun _ => extraAfter rfl⟩
  · -- a plain chunk of lane `pointX`
    have body : desBodies chunk.val = Replay.chunkBody ordF0 Replay.pointXSpec false chunk.val :=
      if_neg zero
    rw [body]
    refine (agree_chunkBody bits Replay.pointXSpec ok false (Pipeline.coordBits bits .x) labels joins
      scale chunk memory record accNow laneNow accs
      (fun _ => Or.inr fun same => zero (by rw [same]; rfl))
      (fun absurdity => by cases absurdity)).mono fun result after post => ?_
    obtain ⟨accsAfter, frameAfter, bitsAfter, recordAfter, -⟩ := post
    have chunkFrame : ∀ address, ChunkFrame Replay.pointXSpec address →
        after.ram address = memory.ram address :=
      fun address off => frameAfter address off (fun absurdity => by cases absurdity)
    refine ⟨accsAfter, fun address off => chunkFrame address off.1, bitsAfter, fun _ => ?_⟩
    obtain ⟨star, recorded, labelCell, jstarCell, kappaCell⟩ := extra (by omega)
    refine ⟨star, (recordAfter rfl).trans recorded, ?_, ?_, ?_⟩
    · rw [chunkFrame _ (designated_chunkFrame ok).1, labelCell]
    · rw [chunkFrame _ (designated_chunkFrame ok).2.1, jstarCell]
    · rw [chunkFrame _ (designated_chunkFrame ok).2.2, kappaCell]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
