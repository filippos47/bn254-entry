/-
**Phase 3, P1h — the evaluator-correctness containment.**

`designed_asks`: **every garbler entry at a designed index is asked by the adversary's own
evaluation** (the full evaluator `Programs.onCurveM` on the selected labels, on the tape) — on every
tape. Index by index (`designedRule`):

* a curve-lane fold gate off the active parent (any paid step) and every hash limb of a curve-lane
  switch off the active one: the evaluator's labels there are the garbler's
  (`Reach.asks_evalLane_hot`, `Reach.asks_evalLane_scale`), whatever the input;
* on the curve, the bridge hash at `bridgeInput t`: the evaluator's curve value is `t`
  (`Pipeline.curveValues_garble`, `CurveMembership.evaluateEncodedOnCurve`);
* on the curve, a point-lane gate or switch limb as above: the evaluator's pads are the garbler's,
  so its whitened labels are the garbler's (`Programs.whitenMacOf_real`, `EncPRF.whitenEncode`);
* on the curve, a gadget position where the input's bit equals the exceptional input's: the
  evaluator's transformed label is the garbler's (`Programs.transformMacOf_real`,
  `EncPRF.transformEncode`).

`designedEntries_eq`: hence the designed entries are the garbler's non-EncPRF entries that
`designedRule` keeps — **the reach disappears from the view**.
-/

import Proof.Privacy.Phase3.Hidden.Reach

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden

noncomputable section

/-! ### The lane lemmas with free arguments -/

theorem asks_lane (O : Oracle) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec PlanB.coordinateBits)
    (labels : Fin PlanB.coordinateBits → Block) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block)
    (joinsEq : joins = hotJoins O.1 lane delta bitKey) (labelsEq : labels = selectBits bitKey bits)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (asks : Asks (publicAnswer O)
      (Programs.evalLaneM lane (hotJoins O.1 lane delta bitKey) scale bits (selectBits bitKey
          bits)) q) :
    Asks (publicAnswer O) (Programs.evalLaneM lane joins scale bits labels) q := by
  subst joinsEq labelsEq
  exact asks

theorem asks_askHash_eq {ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer}
    (value key : BaseField) (same : value = key) : Asks ans (Programs.askHash value) (.hash key) := by
  subst same
  exact Asks.ask' _

/-- One label of a selected-label family. -/
def macAt (mac : InputMac) : Coord → Fin PlanB.coordinateBits → Block
  | .x, position => mac.x.get position
  | .y, position => mac.y.get position

/-- One label of an encoded coordinate. -/
theorem encodeCoordinate_get (key : CoordinateMacKey) (bits : BitVec coordinateBitCount)
    (index : Fin coordinateBitCount) :
    (encodeCoordinate key bits).get index = BitAdaptor.encode key[index.val] (bits.getLsb index) := by
  simp [encodeCoordinate, Vector.get_eq_getElem]

/-- The gadget of the evaluator asks every position of every digit, at the index of the input's
bit there, at its transformed label. -/
theorem asks_masks {ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer}
    (input : AffineInput) (mac : InputMac) (o : Fin digitCount)
    (κ : Coord) (position : Fin PlanB.coordinateBits) (label : Block)
    (labelEq : macAt mac κ position = label) :
    Asks ans (Programs.masksM input mac)
      (.fixedForward (.gadget o κ position ((inputBits input κ).getLsb position)) label) := by
  subst labelEq
  unfold Programs.masksM
  refine Asks.vector _ o (Asks.bind_left ?_)
  unfold Programs.gadgetMaskM
  cases κ
  · refine Asks.bind_left ?_
    unfold Programs.gadgetDigestM
    exact Asks.bind_left (Asks.vector _ position (Asks.hashM _ _))
  · refine Asks.bind_right (Asks.bind_left ?_)
    unfold Programs.gadgetDigestM
    exact Asks.bind_left (Asks.vector _ position (Asks.hashM _ _))

/-- `asks_masks` at a named bit. -/
theorem asks_masks_of {ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer}
    (input : AffineInput) (mac : InputMac) (o : Fin digitCount)
    (κ : Coord) (position : Fin PlanB.coordinateBits) (bit : Bool) (label : Block)
    (bitEq : (inputBits input κ).getLsb position = bit) (labelEq : macAt mac κ position = label) :
    Asks ans (Programs.masksM input mac) (.fixedForward (.gadget o κ position bit) label) := by
  subst bitEq
  exact asks_masks input mac o κ position label labelEq

/-! ### The tape -/

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- The published value is the pipeline's garbling on the tape. -/
theorem garble_table (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    (Scheme.scheme.garble parameter scalar tape).1 =
      Pipeline.garble (FieldMacToECMac.outputKeys construction scalar.value tape.1.offsets)
        tape.1.pointRandomness tape.1.exceptionPad tape.1.bridgeKey tape.1.curveMask tape.1.curveR1
        tape.1.curveR2 tape.2.1 tape.2.2.1 tape.2.2.2 tape.1.inputDelta tape.1.inputMacKey := by
  obtain ⟨coins, oracle⟩ := tape
  rw [← garble_eval parameter scalar coins oracle, Programs.eval_garbleM]

/-- The wire adapter restores the encoded labels. -/
theorem restore_encode (key : InputMacKey) (input : AffineInput) :
    Lamport.restore input (Scheme.scheme.encode key input) =
      ⟨BitInput.ofAffine input, key.encode (BitInput.ofAffine input)⟩ := by
  apply congrArg (Garbling.Labels.mk (BitInput.ofAffine input))
  apply InputMac.ext
  · apply Vector.ext
    intro index bound
    simp only [Lamport.restore, Scheme.scheme, Lamport.selectedLabels, Vector.getElem_ofFn]
    rw [dif_pos (show index < 254 from bound)]
    rfl
  · apply Vector.ext
    intro index bound
    simp only [Lamport.restore, Scheme.scheme, Lamport.selectedLabels, Vector.getElem_ofFn]
    rw [dif_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rfl

/-- **The reach is the transcript of the on-curve evaluator on the encoded labels.** -/
theorem reach_eq (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput) :
    reachTranscript (Scheme.scheme.garble parameter scalar tape).1 input
        (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input) tape =
      Hidden.transcriptOf (publicAnswer tape.2)
        (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
          (tape.1.inputMacKey.encode (BitInput.ofAffine input))) := by
  unfold reachTranscript
  rw [transcript_eq_transcriptOf, restore_encode]
  rfl

theorem coins_correlated (coins : Coins) : Pipeline.CorrelatedKey coins.inputMacKey coins.inputDelta := by
  intro κ position
  cases κ <;> simp [Pipeline.bitKeyOf, Coins.inputMacKey]

theorem laneKeys_correlated (tape : Coins × Oracle) (lane : Lane) (position : Fin PlanB.coordinateBits) :
    ((laneKeys tape).2 lane position).2 = ((laneKeys tape).2 lane position).1 ^^^ (laneKeys tape).1 lane := by
  cases lane
  · exact coins_correlated tape.1 .x position
  · exact coins_correlated tape.1 .y position
  · exact Pipeline.whitenedKey_correlated _ _ _ _ _ (coins_correlated tape.1) .x position
  · exact Pipeline.whitenedKey_correlated _ _ _ _ _ (coins_correlated tape.1) .y position

/-- **On the curve, the evaluator's curve value is the bridge key.** -/
theorem onCurve_bridge (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (valid : validate input = true) :
    CurveMembership.evaluate (Scheme.scheme.garble parameter scalar tape).1.curve
        (BitInput.ofAffine input).toAffine
        (Pipeline.curveValues
          (Pipeline.curveXValues tape.2.1 tape.2.2.2 (Scheme.scheme.garble parameter scalar tape).1
            (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input)))
          (Pipeline.curveYValues tape.2.1 tape.2.2.2 (Scheme.scheme.garble parameter scalar tape).1
            (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input)))) =
      tape.1.bridgeKey := by
  rw [garble_table, Pipeline.curveValues_garble _ _ _ _ _ _ _ _ _ _ _ _ (coins_correlated tape.1)
    (delivers tape.2.1 tape.2.2.2) input, BitInput.toAffineOfAffine]
  exact CurveMembership.evaluateEncodedOnCurve _ _ _ _ _ input ((validate_eq_true_iff input).mp valid)

/-! ### The designed entries are asked -/

/-- The input's bits on a lane's coordinate, as the evaluator reads them. -/
theorem coordBits_lane (input : AffineInput) (κ : Coord) :
    Pipeline.coordBits (BitInput.ofAffine input) κ = inputBits input κ := by
  cases κ <;> rfl

theorem macLabels_raw (key : InputMacKey) (input : AffineInput) (κ : Coord) :
    Pipeline.macLabels (key.encode (BitInput.ofAffine input)) κ =
      selectBits (Pipeline.bitKeyOf key κ) (inputBits input κ) := by
  rw [Pipeline.macLabels_encode, coordBits_lane]

/-- The evaluator's whitened labels, when its curve value is the bridge key. -/
theorem macLabels_white (tape : Coins × Oracle) (input : AffineInput) (κ : Coord) (value : BaseField)
    (same : value = tape.1.bridgeKey) :
    Pipeline.macLabels (Programs.whitenMacOf
        (Programs.realEvalPads tape.2.2.1 ⟨(tape.2.2.2 (bridgeInput value)).1,
          (tape.2.2.2 (bridgeInput value)).2⟩
          (BitInput.ofAffine input)) (tape.1.inputMacKey.encode (BitInput.ofAffine input))) κ =
      selectBits (Pipeline.bitKeyOf (Pipeline.whitenedKey tape.2.2.1 tape.2.2.2 tape.1.bridgeKey
        tape.1.inputMacKey) κ) (inputBits input κ) := by
  subst same
  rw [Programs.whitenMacOf_real, EncPRF.whitenEncode, ← coordBits_lane, Pipeline.macLabels_encode]
  rfl

theorem encode_get_congr_x (key : InputMacKey) (first second : BitInput) (i : Fin coordinateBitCount)
    (same : first.xBits.getLsb i = second.xBits.getLsb i) :
    (key.encode first).x.get i = (key.encode second).x.get i := by
  simp only [InputMacKey.encode, encodeCoordinate, Vector.get_ofFn, same]

theorem encode_get_congr_y (key : InputMacKey) (first second : BitInput) (i : Fin coordinateBitCount)
    (same : first.yBits.getLsb i = second.yBits.getLsb i) :
    (key.encode first).y.get i = (key.encode second).y.get i := by
  simp only [InputMacKey.encode, encodeCoordinate, Vector.get_ofFn, same]

/-- The evaluator's transformed label at a position where the input agrees with the exceptional
input is the garbler's gadget label. -/
theorem transformed_label (tape : Coins × Oracle) (input exceptional : AffineInput) (κ : Coord)
    (position : Fin PlanB.coordinateBits) (value : BaseField) (same : value = tape.1.bridgeKey)
    (agree : (inputBits input κ).getLsb position = (inputBits exceptional κ).getLsb position) :
    macAt (Programs.transformMacOf (Programs.realEvalPads tape.2.2.1
        ⟨(tape.2.2.2 (bridgeInput value)).1, (tape.2.2.2 (bridgeInput value)).2⟩
          (BitInput.ofAffine input))
        (tape.1.inputMacKey.encode (BitInput.ofAffine input))) κ position =
      macAt ((EncPRF.transformKey tape.2.2.1 (EncPRF.whiteningKeys tape.2.2.2 tape.1.bridgeKey)
        tape.1.inputMacKey).encodeAffine exceptional) κ position := by
  subst same
  rw [Programs.transformMacOf_real, EncPRF.transformEncode]
  cases κ
  · exact encode_get_congr_x _ _ _ position agree
  · exact encode_get_congr_y _ _ _ position agree

/-- The garbler's hot index, as the fold names it. -/
theorem hot_index_eq (ℓ : Lane) (k : Fin chunkCount) (fold : Fin chunkBits) (r : Fin (2 ^ chunkBits))
    (half : Bool) : FixedIndex.hot ℓ k fold r half = hotIndexNat ℓ k fold.val r.val half :=
  (hotIndexNat_eq ℓ k fold.val r.val half fold.isLt r.isLt).symm

/-- **The evaluator reaches every lane**: the curve lanes always, the point lanes on the curve. -/
theorem asks_onCurve (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (ℓ : Lane) (laneOk : (laneIsCurve ℓ || validate input) = true)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (asks : ∀ scale : Fin chunkCount → Fin (laneCount ℓ) → BaseField, Asks (publicAnswer tape.2)
      (Programs.evalLaneM ℓ (hotJoins tape.2.1 ℓ ((laneKeys tape).1 ℓ) ((laneKeys tape).2 ℓ)) scale
        (inputBits input ℓ.coord) (selectBits ((laneKeys tape).2 ℓ) (inputBits input ℓ.coord))) q) :
    Asks (publicAnswer tape.2) (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1
      (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))) q := by
  unfold Programs.onCurveM
  cases ℓ
  · refine Asks.bind_left (asks_lane tape.2 .curveX _ _ _ _ ((laneKeys tape).1 .curveX)
      ((laneKeys tape).2 .curveX) ?_ ?_ q (asks _))
    · rw [garble_table]
      rfl
    · exact Pipeline.macLabels_encode _ _ _
  · refine Asks.bind_right (Asks.bind_left (asks_lane tape.2 .curveY _ _ _ _
      ((laneKeys tape).1 .curveY) ((laneKeys tape).2 .curveY) ?_ ?_ q (asks _)))
    · rw [garble_table]
      rfl
    · exact Pipeline.macLabels_encode _ _ _
  · have valid : validate input = true := by simpa [laneIsCurve] using laneOk
    refine Asks.bind_right (Asks.bind_right (Asks.bind_right (Asks.bind_right (Asks.bind_left ?_))))
    rw [Programs.eval_evalPadsM, Programs.eval_askHash, Programs.eval_evalLaneM,
      Programs.eval_evalLaneM]
    refine asks_lane tape.2 .pointX _ _ _ _ ((laneKeys tape).1 .pointX) ((laneKeys tape).2 .pointX)
      ?_ ?_ q (asks _)
    · rw [garble_table]
      rfl
    · exact macLabels_white tape input .x _ (onCurve_bridge parameter scalar tape input valid)
  · have valid : validate input = true := by simpa [laneIsCurve] using laneOk
    refine Asks.bind_right (Asks.bind_right (Asks.bind_right (Asks.bind_right
      (Asks.bind_right (Asks.bind_left ?_)))))
    rw [Programs.eval_evalPadsM, Programs.eval_askHash, Programs.eval_evalLaneM,
      Programs.eval_evalLaneM]
    refine asks_lane tape.2 .pointY _ _ _ _ ((laneKeys tape).1 .pointY) ((laneKeys tape).2 .pointY)
      ?_ ?_ q (asks _)
    · rw [garble_table]
      rfl
    · exact macLabels_white tape input .y _ (onCurve_bridge parameter scalar tape input valid)

/-- **Containment at a designed fixed-key index.** -/
theorem designed_fixed (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (index : FixedIndex)
    (shape : GarblerAsk scalar tape.1 (.fixedForward index (garblerPointOf scalar tape index)))
    (designed : designedIndex scalar tape input index = true) :
    Asks (publicAnswer tape.2) (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1
      (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input)))
      (.fixedForward index (garblerPointOf scalar tape index)) := by
  cases index with
  | hot ℓ k fold r half =>
      obtain ⟨_, small, rSmall⟩ := shape
      simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq] at designed
      obtain ⟨off, laneOk⟩ := designed
      rw [hot_index_eq ℓ k fold r half,
        garblerPointOf_hot scalar tape ℓ k fold.val r.val half small rSmall]
      exact asks_onCurve parameter scalar tape input ℓ laneOk _ fun scale =>
        asks_evalLane_hot tape.2 ℓ _ _ (laneKeys_correlated tape ℓ) scale _ k fold.val small
          ⟨r.val, rSmall⟩ half off
  | gadget o κ position bit =>
      have isSome : (digitEndomorphismBase (digitKey scalar tape.1.offsets o).digit).isSome =
          true :=
        shape
      obtain ⟨phi, found⟩ := Option.isSome_iff_exists.mp isSome
      simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq] at designed
      obtain ⟨valid, agreeBit⟩ := designed
      have label : garblerPointOf scalar tape (.gadget o κ position bit) =
          macAt ((EncPRF.transformKey tape.2.2.1 (EncPRF.whiteningKeys tape.2.2.2 tape.1.bridgeKey)
            tape.1.inputMacKey).encodeAffine input) κ position := by
        show gadgetLabel scalar tape o κ position bit = _
        rw [← agreeBit]
        simp only [gadgetLabel, found]
        cases κ <;> simp only [macAt, InputMacKey.encodeAffine, InputMacKey.encode,
          BitInput.ofAffine, inputBits] <;>
          exact (encodeCoordinate_get _ _ position).symm
      rw [label]
      unfold Programs.onCurveM
      refine Asks.bind_right (Asks.bind_right (Asks.bind_right (Asks.bind_right
        (Asks.bind_right (Asks.bind_right (Asks.bind_left ?_))))))
      rw [Programs.eval_evalPadsM, Programs.eval_askHash, Programs.eval_evalLaneM,
        Programs.eval_evalLaneM]
      refine asks_masks_of _ _ o κ position bit _ ?_ ?_
      · rw [BitInput.toAffineOfAffine]
        exact agreeBit
      · exact transformed_label tape input input κ position _
          (onCurve_bridge parameter scalar tape input valid) rfl

/-- **Containment at a designed vector site**: every hash limb of a designed switch, at the
garbler's label. -/
theorem designed_scale (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (slot : LimbSite) (designed : designedSite input slot.1 = true) :
    Asks (publicAnswer tape.2) (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1
      (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input)))
      (.hash (labelInput slot (garblerLabelOf tape slot.1))) := by
  obtain ⟨⟨ℓ, k, j⟩, limb⟩ := slot
  simp only [designedSite, Bool.and_eq_true, decide_eq_true_eq] at designed
  obtain ⟨off, laneOk⟩ := designed
  exact asks_onCurve parameter scalar tape input ℓ laneOk _ fun scale =>
    asks_evalLane_scale tape.2 ℓ _ _ (laneKeys_correlated tape ℓ) scale _ k j limb off

/-- **The containment**: every garbler entry the designed rule keeps is asked by the adversary's
evaluation. -/
theorem designed_asks (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (entry : Entry FixedIndex EncPRF.PermutationIndex) (member : entry ∈ garblerTranscript scalar tape)
    (designed : designedRule scalar tape input entry = true) :
    Asks (publicAnswer tape.2) (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1
      (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))) entry.1 := by
  have good := garblerTranscript_good scalar tape entry member
  have shape := garblerTranscript_ask scalar tape entry member
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x =>
      have hx : x = garblerPointOf scalar tape index := good
      subst hx
      exact designed_fixed parameter scalar tape input index shape designed
  | fixedInverse _ _ => exact good.elim
  | encForward _ _ => simp [designedRule] at designed
  | encInverse _ _ => simp [designedRule] at designed
  | hash key =>
      have keep : designedHash input key = true := designed
      rcases (good : key = bridgeInput tape.1.bridgeKey ∨
          ∃ slot : LimbSite, key = labelInput slot (garblerLabelOf tape slot.1)) with
        bridge | ⟨slot, scale⟩
      · subst bridge
        rw [designedHash_bridgeInput] at keep
        unfold Programs.onCurveM
        refine Asks.bind_right (Asks.bind_right (Asks.bind_left ?_))
        rw [Programs.eval_evalLaneM, Programs.eval_evalLaneM]
        exact asks_askHash_eq _ _
          (congrArg bridgeInput (onCurve_bridge parameter scalar tape input keep))
      · subst scale
        rw [designedHash_labelInput] at keep
        exact designed_scale parameter scalar tape input slot keep

/-- **The designed entries are the garbler's entries the rule keeps**: the reach is not needed. -/
theorem designedEntries_eq (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) :
    designedEntries designedRule parameter scalar tape input =
      (garblerTranscript scalar tape).filter fun e => !e.IsEnc && designedRule scalar tape input e := by
  unfold designedEntries visibleEntries
  rw [List.filter_filter]
  refine List.filter_congr fun e member => ?_
  by_cases d : designedRule scalar tape input e = true
  · have asks := designed_asks parameter scalar tape input e member d
    rw [reach_eq]
    unfold Asks at asks
    simp [d, asks]
  · simp [d]

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
