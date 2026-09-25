/-
**The replay, whole** (`agree_replay`): `Replay.program` (the accumulator clear, lanes `curveX`
and `curveY`, the bridge and its hash at `bridgeInput t`, the `508` whitened labels, lane `pointX`
with its designated chunk, lane `pointY`) against P3's intercepted `openingQueriesM`, from any
memory satisfying `ReplayStart`. It leaves (`ReplayPost`) the two point lanes' (designated-free)
values in their accumulators, `j*`, `κ`, `E*` with the complete record `fun _ => some E*` of the
`362` designated inputs, and every cell outside the replay's work cells unchanged.
-/

import Proof.Simulator.ReplayStartCells

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Address facts -/

theorem acc_ne_tmp (e k : Nat) (small : e < 642) (kSmall : k < 16) :
    word (accBase + e) ≠ word (tmpBase + k) :=
  word_ne (by unfold accBase; omega) (by unfold tmpBase; omega) (by unfold accBase tmpBase; omega)

theorem acc_ne_white (e i : Nat) (small : e < 642) (iSmall : i < 508) :
    word (accBase + e) ≠ word (whiteBase + i) :=
  word_ne (by unfold accBase; omega) (by unfold whiteBase; omega) (by unfold accBase whiteBase; omega)

theorem tmpK1_ne_tmpK2 : word tmpK1 ≠ word tmpK2 :=
  tmp_ne (show 3 < 16 by omega) (show 4 < 16 by omega) (by omega)

omit [FieldCertificate] in
theorem OffReplay.tmpK1 {address : Word} (off : OffReplay address) : address ≠ word tmpK1 :=
  off.1.2.2.1 3 (by omega)

omit [FieldCertificate] in
theorem OffReplay.tmpK2 {address : Word} (off : OffReplay address) : address ≠ word tmpK2 :=
  off.1.2.2.1 4 (by omega)

/-! ### The replay's queries -/

omit [FieldCertificate] in
/-- **Each lane of the replay asks the honest evaluator's lane budget**: the design's per-lane
count `Design.laneQueries k` is `Programs.laneEvalBudget` of every lane with `k` limbs (T2's closed
form `laneEvalBudget_closed`). -/
theorem laneQueries_eq_laneEvalBudget (lane : Lane) :
    Design.laneQueries (limbCount lane) = Programs.laneEvalBudget lane := by
  rw [Design.laneQueries_eq, Programs.laneEvalBudget_closed]

/-! ### What the replay leaves -/

/-- **What the replay leaves.** -/
def ReplayPost (bits : BitInput) (start : Memory)
    (result : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      DesignatedRecord) (after : Memory) : Prop :=
  (∀ e : Fin pointElementCountX, after.ram (word (accBase + e.val)) = fieldWord (result.1.1 e)) ∧
    (∀ e : Fin pointElementCountY,
      after.ram (word (accBase + 367 + e.val)) = fieldWord (result.1.2 e)) ∧
    after.ram (word tmpJStar) = word (designatedSwitch bits).val ∧
    after.ram (word tmpKappa) = fieldWord (kappa bits) ∧
    (∃ star : Block, after.ram (word designatedLabel) = blockWord star ∧
      result.2 = fun _ => some star) ∧
    (∀ address, OffReplay address → after.ram address = start.ram address) ∧
    after.bits = start.bits

/-- **The replay.** -/
theorem agree_replay (source : Stage1Source) (input : AffineInput) (labels : LamportSignature)
    (memory : Memory) (start : ReplayStart source input labels memory) :
    Agree (ReplayPost (BitInput.ofAffine input) memory) (rtree (Replay.program ordF0 ordE0) memory)
      (interceptT (BitInput.ofAffine input)
        (openingQueriesM source.publicValue (BitInput.ofAffine input)
          (Lamport.restore input labels).inputMac) fun _ => none) := by
  -- the accumulator clear
  obtain ⟨m1, runInit, zeros, initFrame, initBits⟩ := rtree_initAcc memory
  unfold Replay.program
  rw [rtree_seq, runInit, bindOpt_pure]
  unfold openingQueriesM
  simp only [TreeLaws.monad_bind, TreeLaws.monad_pure, interceptT_bind]
  have frame1 : ∀ address, OffReplay address → m1.ram address = memory.ram address :=
    fun address off => initFrame address off.1.1
  -- lane `curveX`
  rw [rtree_seq]
  refine Agree.bindOpt (fun r1 m2 post1 => ?_) (agree_plainLane (BitInput.ofAffine input)
    Replay.curveXSpec specOK_curveX (by decide) _ _ _ _ m1 (fun _ => none) (fun _ => 0)
    (laneCells_curveX start frame1) (fun e bound => by
      have small : e < 3 := bound
      have cell := zeros (364 + e) (by omega)
      rw [← Nat.add_assoc] at cell
      exact cell))
  obtain ⟨accs2, frame2', bits2, record2⟩ := post1
  have frame2 : ∀ address, OffReplay address → m2.ram address = memory.ram address :=
    fun address off => (frame2' address (off.1.chunkFrame specOK_curveX)).trans
      (frame1 address off)
  have zeros2 : ∀ e, e < 642 → (e < 364 ∨ 367 ≤ e) → m2.ram (word (accBase + e)) = fieldWord 0 :=
    fun e small outside => (frame2' _ (acc_chunkFrame specOK_curveX e small outside)).trans
      (zeros e small)
  -- lane `curveY`
  rw [rtree_seq]
  refine Agree.bindOpt (fun r2 m3 post2 => ?_) (agree_plainLane (BitInput.ofAffine input)
    Replay.curveYSpec specOK_curveY (by decide) _ _ _ _ m2 r1.2 (fun _ => 0)
    (laneCells_curveY start frame2) (fun e bound => by
      have small : e < 2 := bound
      have cell := zeros2 (640 + e) (by omega) (by omega)
      rw [← Nat.add_assoc] at cell
      exact cell))
  obtain ⟨accs3, frame3', bits3, record3⟩ := post2
  have frame3 : ∀ address, OffReplay address → m3.ram address = memory.ram address :=
    fun address off => (frame3' address (off.1.chunkFrame specOK_curveY)).trans
      (frame2 address off)
  have zeros3 : ∀ e, e < 640 → (e < 364 ∨ 367 ≤ e) → m3.ram (word (accBase + e)) = fieldWord 0 :=
    fun e small outside => (frame3' _ (acc_chunkFrame specOK_curveY e (by omega)
      (Or.inl (show e < 640 by omega)))).trans (zeros2 e (by omega) outside)
  have curveXCells : ∀ e : Fin curveElementCountX,
      m3.ram (word (accBase + 364 + e.val)) = fieldWord (r1.1 e) := by
    intro e
    have small : e.val < 3 := e.isLt
    rw [Nat.add_assoc, frame3' _ (acc_chunkFrame specOK_curveY (364 + e.val) (by omega)
      (Or.inl (show 364 + e.val < 640 by omega))), ← Nat.add_assoc]
    have cell := accs2 e
    simp only [zero_add] at cell
    exact cell
  have curveYCells : ∀ e : Fin curveElementCountY,
      m3.ram (word (accBase + 640 + e.val)) = fieldWord (r2.1 e) := by
    intro e
    have cell := accs3 e
    simp only [zero_add] at cell
    exact cell
  -- the bridge and its hash
  rw [rtree_seq, bridge_value, interceptT_clean _ _ (clean_askHash _ _
    (not_isDesignated_bridgeInput _ _))]
  have bridgeAgree := (agree_bridge m3 input.x input.y source.curve (r1.1 ⟨0, by decide⟩) (r1.1 ⟨1, by decide⟩) (r1.1 ⟨2, by decide⟩)
    (r2.1 ⟨0, by decide⟩) (r2.1 ⟨1, by decide⟩)
    (by rw [frame3 _ (offReplay_of_lt reqX_small), start.reqXCell])
    (by rw [frame3 _ (offReplay_of_lt reqY_small), start.reqYCell])
    (by rw [frame3 (word fieldBase) (offReplay_of_lt (by unfold fieldBase; norm_num)), start.curve0])
    (curveXCells ⟨0, by decide⟩) (curveYCells ⟨0, by decide⟩) (curveXCells ⟨1, by decide⟩)
    (curveYCells ⟨1, by decide⟩) (curveXCells ⟨2, by decide⟩)).map
    (Post' := fun (value : (Block × Block) × DesignatedRecord) after =>
      BridgePost m3 value.1 after ∧ value.2 = r2.2)
    (fun keys => (keys, r2.2)) fun keys after post => ⟨post, rfl⟩
  refine Agree.bindOpt (fun r3 m4 post3 => ?_) bridgeAgree
  obtain ⟨⟨ram4, bits4⟩, record4⟩ := post3
  have frame4 : ∀ address, OffReplay address → m4.ram address = memory.ram address := by
    intro address off
    rw [ram4, Function.update_of_ne off.tmpK2, Function.update_of_ne off.tmpK1, frame3 address off]
  have k1Cell : m4.ram (word tmpK1) = blockWord r3.1.1 := by
    rw [ram4, Function.update_of_ne tmpK1_ne_tmpK2, Function.update_self]
  have k2Cell : m4.ram (word tmpK2) = blockWord r3.1.2 := by
    rw [ram4, Function.update_self]
  have zeros4 : ∀ e, e < 640 → (e < 364 ∨ 367 ≤ e) → m4.ram (word (accBase + e)) = fieldWord 0 := by
    intro e small outside
    rw [ram4, Function.update_of_ne (show word (accBase + e) ≠ word tmpK2 from
        acc_ne_tmp e 4 (by omega) (by omega)),
      Function.update_of_ne (show word (accBase + e) ≠ word tmpK1 from
        acc_ne_tmp e 3 (by omega) (by omega)), zeros3 e small outside]
  -- the whitening
  rw [rtree_seq]
  refine Agree.bindOpt (fun r4 m5 post4 => ?_) (agree_whiten (BitInput.ofAffine input) m4
    ⟨r3.1.1, r3.1.2⟩ (Lamport.restore input labels).inputMac r3.2 k1Cell k2Cell
    (fun i => by
      have small : i.val < 254 := i.isLt
      rw [frame4 _ (offReplay_of_lt (label_small i.val (by omega))),
        start.labelCells i.val (by omega)]
      exact congrArg blockWord (restore_x input labels i).symm)
    (fun i => by
      have small : i.val < 254 := i.isLt
      rw [frame4 (word (labelBase + 254 + i.val)) (offReplay_of_lt (by unfold labelBase; omega)),
        Nat.add_assoc, start.labelCells (254 + i.val) (by omega)]
      exact congrArg blockWord (restore_y input labels i).symm))
  obtain ⟨whitesX, whitesY, frame5', bits5, record5⟩ := post4
  have frame5 : ∀ address, OffReplay address → m5.ram address = memory.ram address :=
    fun address off => (frame5' address off.2).trans (frame4 address off)
  have zeros5 : ∀ e, e < 640 → (e < 364 ∨ 367 ≤ e) → m5.ram (word (accBase + e)) = fieldWord 0 :=
    fun e small outside => (frame5' _ fun i bound => acc_ne_white e i (by omega) bound).trans
      (zeros4 e small outside)
  -- lane `pointX`, chunk `0` designated
  rw [rtree_seq]
  refine Agree.bindOpt (fun r5 m6 post5 => ?_) (agree_desLane (BitInput.ofAffine input) _ _ _ m5
    r4.2 (fun _ => 0) (laneCells_pointX start _ frame5 whitesX) (fun e bound => by
      have small : e < 364 := bound
      have cell := zeros5 (0 + e) (by omega) (by omega)
      rw [← Nat.add_assoc] at cell
      exact cell))
  obtain ⟨accs6, frame6', bits6, extra6⟩ := post5
  obtain ⟨star, recorded, labelCell, jstarCell, kappaCell⟩ := extra6 (by decide)
  have frame6 : ∀ address, OffReplay address → m6.ram address = memory.ram address :=
    fun address off => (frame6' address off.1.desFrame).trans (frame5 address off)
  have whitesY6 : ∀ i : Fin coordinateBitCount, m6.ram (word (whiteBase + 254 + i.val)) =
      blockWord ((Programs.whitenMacOf r4.1 (Lamport.restore input labels).inputMac).y.get i) := by
    intro i
    have small : i.val < 254 := i.isLt
    rw [frame6' (word (whiteBase + 254 + i.val))
      (offWork_of_lt (by unfold whiteBase; omega)).desFrame, whitesY i]
  have zeros6 : ∀ e, e < laneCount Replay.pointYSpec.lane →
      m6.ram (accCell Replay.pointYSpec e) = fieldWord 0 := by
    intro e bound
    have small : e < 273 := bound
    show m6.ram (word (accBase + 367 + e)) = _
    rw [Nat.add_assoc, frame6' (word (accBase + (367 + e)))
      ⟨acc_chunkFrame specOK_pointX (367 + e) (by omega) (Or.inr (show 0 + 364 ≤ 367 + e by omega)),
        word_ne (by unfold accBase; omega) (by unfold designatedLabel hotLabelBase; omega)
          (by unfold accBase designatedLabel hotLabelBase; omega),
        acc_ne_tmp _ 6 (by omega) (by omega), acc_ne_tmp _ 5 (by omega) (by omega)⟩,
      zeros5 (367 + e) (by omega) (by omega)]
  -- lane `pointY`
  simp only [interceptT]
  refine Agree.map _ (fun r6 m7 post6 => ?_) (agree_plainLane (BitInput.ofAffine input)
    Replay.pointYSpec specOK_pointY (by decide) _ _ _ _ m6 r5.2 (fun _ => 0)
    (laneCells_pointY start _ frame6 whitesY6) zeros6)
  obtain ⟨accs7, frame7', bits7, record7⟩ := post6
  have three := designated_chunkFrame specOK_pointY
  refine ⟨fun e => ?_, fun e => ?_, ?_, ?_, ⟨star, ?_, ?_⟩, fun address off => ?_, ?_⟩
  · have small : e.val < 364 := e.isLt
    rw [frame7' _ (acc_chunkFrame specOK_pointY e.val (by omega) (Or.inl (show e.val < 367 by omega)))]
    have cell := accs6 e
    simp only [zero_add] at cell
    exact cell
  · have cell := accs7 e
    simp only [zero_add] at cell
    exact cell
  · rw [frame7' _ three.2.1, jstarCell]
  · rw [frame7' _ three.2.2, kappaCell]
  · rw [frame7' _ three.1, labelCell]
  · rw [record7]
    exact recorded
  · rw [frame7' address (off.1.chunkFrame specOK_pointY), frame6 address off]
  · rw [bits7, bits6, bits5, bits4, bits3, bits2, initBits]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
