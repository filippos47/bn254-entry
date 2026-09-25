/-
**Phase 3, P1f — the whole garbler on a shifted tape.**

`garbler_sim`: for every `TapeShift` that keeps every join (`TapeShift.Valid`), the garbler run on
`shiftTape T scalar tape` has transcript `shiftEntry` of the garbler's transcript on `tape`, every
entry of which has the garbler's shape (`Good`: a fixed-key query at index `i` asks at
`garblerPointOf i`, the hash at `bridgeInput t` or at a scale input under the garbler's label of its
switch), and publishes the same value.
-/

import Proof.Privacy.Phase3.Hidden.TapeShift

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)

noncomputable section

variable [FieldCertificate] [GroupCertificate]

/-- The relation of the two garbler runs. -/
def GarbleRel (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (e e' : Asked FixedIndex EncPRF.PermutationIndex) : Prop :=
  e' = shiftEntry T scalar tape.1 e ∧ Good scalar tape e

theorem shiftOracle_fixed (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (index : FixedIndex) (x : Block) :
    (shiftTape T scalar tape).2.1.permutation index (x ^^^ (indexShift T scalar tape.1 index).1) =
      tape.2.1.permutation index x ^^^ (indexShift T scalar tape.1 index).2 :=
  shiftPerm_shift _ _ _ x

/-- A fixed-key garbler entry at the garbler's point is related to its shift. -/
theorem garbleRel_fixed (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (index : FixedIndex) (x : Block) (good : x = garblerPointOf scalar tape index) :
    GarbleRel T scalar tape ⟨.fixedForward index x, tape.2.1.permutation index x⟩
      ⟨.fixedForward index (x ^^^ (indexShift T scalar tape.1 index).1),
        (shiftTape T scalar tape).2.1.permutation index (x ^^^ (indexShift T scalar tape.1 index).1)⟩ := by
  refine ⟨?_, good⟩
  rw [shiftOracle_fixed]
  rfl

/-- The shifted hash at a relabelled scale input is the old hash at the old one. -/
theorem shiftOracle_scale (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (slot : LimbSite) (label : Block) :
    (shiftTape T scalar tape).2.2.2 (labelInput slot (label ^^^ siteShift T slot.1)) =
      tape.2.2.2 (labelInput slot label) := by
  show shiftHash T tape.1.bridgeKey tape.2.2.2 _ = _
  unfold shiftHash
  rw [if_neg (fun same => bridgeInput_ne_scaleInput _ _ _ _ _ _ same.symm), relabel_labelInput,
    xor_cancel_right]

/-- A garbler scale entry at the garbler's label is related to its relabelled shift. -/
theorem garbleRel_scale (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (slot : LimbSite) (label : Block) (good : label = garblerLabelOf tape slot.1) :
    GarbleRel T scalar tape ⟨.hash (labelInput slot label), tape.2.2.2 (labelInput slot label)⟩
      ⟨.hash (labelInput slot (label ^^^ siteShift T slot.1)),
        (shiftTape T scalar tape).2.2.2 (labelInput slot (label ^^^ siteShift T slot.1))⟩ := by
  refine ⟨?_, Or.inr ⟨slot, by rw [good]⟩⟩
  rw [shiftOracle_scale]
  show _ = if labelInput slot label = bridgeInput tape.1.bridgeKey then _ else _
  rw [if_neg (fun same => bridgeInput_ne_scaleInput _ _ _ _ _ _ same.symm), relabel_labelInput]

/-! ### Index bookkeeping -/

theorem hotIndexNat_of_lt (lane : Lane) (c : Fin chunkCount) (n r : Nat) (half : Bool)
    (small : n < chunkWidth c) (entry : r < 2 ^ n) :
    ∃ (fold : Fin chunkBits) (e : Fin (2 ^ chunkBits)), fold.val = n ∧ e.val = r ∧
      hotIndexNat lane c n r half = .hot lane c fold e half := by
  have nSmall : n < chunkBits := lt_of_lt_of_le small (chunkWidth_le c)
  have rSmall : r < 2 ^ chunkBits :=
    lt_of_lt_of_le entry (Nat.pow_le_pow_right (by omega) nSmall.le)
  exact ⟨⟨n, nSmall⟩, ⟨r, rSmall⟩, rfl, rfl, hotIndexNat_eq lane c n r half nSmall rSmall⟩

theorem indexShift_hotIndexNat (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) (lane : Lane)
    (c : Fin chunkCount) (n r : Nat) (half : Bool) (small : n < chunkWidth c) (entry : r < 2 ^ n) :
    indexShift T scalar coins (hotIndexNat lane c n r half) = ((T.lane lane).fold c).hot n r half := by
  obtain ⟨fold, e, rfl, rfl, same⟩ := hotIndexNat_of_lt lane c n r half small entry
  rw [same]
  rfl

theorem garblerPointOf_hot (scalar : NonZeroScalar) (tape : Coins × Oracle) (lane : Lane)
    (c : Fin chunkCount) (n r : Nat) (half : Bool) (small : n < chunkWidth c) (entry : r < 2 ^ n) :
    garblerPointOf scalar tape (hotIndexNat lane c n r half) =
      (garbleFold tape.2.1 lane c ((laneKeys tape).1 lane)
        (labelAt fun p => (chunkKey ((laneKeys tape).2 lane) c p).1) n).1 ⟨r, entry⟩ := by
  obtain ⟨fold, e, rfl, rfl, same⟩ := hotIndexNat_of_lt lane c n r half small entry
  rw [same]
  show (garbleFold tape.2.1 lane c _ _ fold.val).1 _ = _
  exact congrArg _ (Fin.ext (Nat.mod_eq_of_lt entry))

/-! ### One lane of the garbler, on the whole shifted tape -/

theorem garbler_laneM (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) (lane : Lane) (delta delta' : Block)
    (bitKey bitKey' : Fin PlanB.coordinateBits → Block × Block)
    (deltaEq : delta = (laneKeys tape).1 lane) (bitKeyEq : bitKey = (laneKeys tape).2 lane)
    (deltaShift : delta' = delta ^^^ (T.lane lane).delta)
    (keys : ∀ position, (bitKey' position).1 = (bitKey position).1 ^^^ (T.lane lane).zero position) :
    Sim (publicAnswer tape.2) (publicAnswer (shiftTape T scalar tape).2) (GarbleRel T scalar tape)
      (fun tables tables' =>
        tables = Programs.laneTables tape.2.1 tape.2.2.2 lane delta bitKey ∧
        tables'.masks = tables.masks ∧ ∀ c, (tables'.hot c).2 = (tables.hot c).2)
      (Programs.laneM lane delta bitKey) (Programs.laneM lane delta' bitKey') := by
  subst deltaEq bitKeyEq deltaShift
  refine sim_laneM tape.2 (shiftTape T scalar tape).2 (T.lane lane) (valid lane) lane _ _ bitKey'
    keys ?_ ?_ ?_ ?_
  · intro c n r half x small entry
    have := shiftOracle_fixed T scalar tape (hotIndexNat lane c n r half) x
    rwa [indexShift_hotIndexNat T scalar tape.1 lane c n r half small entry] at this
  · intro c j limb
    exact shiftOracle_scale T scalar tape ⟨⟨lane, c, j⟩, limb⟩ _
  · intro c n r half small _
    have related := garbleRel_fixed T scalar tape (hotIndexNat lane c n r.val half) _
      (garblerPointOf_hot scalar tape lane c n r.val half small r.isLt).symm
    rwa [indexShift_hotIndexNat T scalar tape.1 lane c n r.val half small r.isLt] at related
  · intro c j limb
    exact garbleRel_scale T scalar tape ⟨⟨lane, c, j⟩, limb⟩ _ rfl

/-! ### The bridge hash and the pads -/

theorem garbler_askHash (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    Sim (publicAnswer tape.2) (publicAnswer (shiftTape T scalar tape).2) (GarbleRel T scalar tape)
      (fun hashed hashed' => hashed = tape.2.2.2 (bridgeInput tape.1.bridgeKey) ∧
        hashed' = (hashed.1, hashed.2 ^^^ T.key2))
      (Programs.askHash (bridgeInput tape.1.bridgeKey))
      (Programs.askHash (bridgeInput (shiftTape T scalar tape).1.bridgeKey)) := by
  unfold Programs.askHash
  refine Sim.ask (.hash (bridgeInput tape.1.bridgeKey)) (.hash (bridgeInput tape.1.bridgeKey))
    (fun (hashed hashed' : Block × Block) => hashed = tape.2.2.2 (bridgeInput tape.1.bridgeKey) ∧
      hashed' = (hashed.1, hashed.2 ^^^ T.key2)) ⟨?_, Or.inl rfl⟩ ⟨rfl, ?_⟩
  · show (⟨.hash (bridgeInput tape.1.bridgeKey),
        shiftHash T tape.1.bridgeKey tape.2.2.2 (bridgeInput tape.1.bridgeKey)⟩ :
        Asked FixedIndex EncPRF.PermutationIndex) =
      shiftEntry T scalar tape.1 ⟨.hash (bridgeInput tape.1.bridgeKey),
        tape.2.2.2 (bridgeInput tape.1.bridgeKey)⟩
    simp only [shiftEntry, shiftHash, if_true]
  · show shiftHash T tape.1.bridgeKey tape.2.2.2 (bridgeInput tape.1.bridgeKey) = _
    simp only [shiftHash, if_true]
    rfl

theorem garbler_padM (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount)
    (bit : Bool) :
    Sim (publicAnswer tape.2) (publicAnswer (shiftTape T scalar tape).2) (GarbleRel T scalar tape)
      (fun v v' => v = EncPRF.evenMansourPad tape.2.2.1 keys { coordinate, index, bit } ∧
        v' = v ^^^ T.key2)
      (Programs.padM keys coordinate index bit)
      (Programs.padM ⟨keys.first, keys.second ^^^ T.key2⟩ coordinate index bit) := by
  unfold Programs.padM Programs.askEnc
  refine Sim.bind (R := fun (v v' : Block) => v = tape.2.2.1.permutation (coordinate, index)
      (encodeBit bit ^^^ keys.first) ∧ v' = v)
    (Sim.ask (.encForward (coordinate, index) (encodeBit bit ^^^ keys.first))
      (.encForward (coordinate, index) (encodeBit bit ^^^ keys.first))
      (fun (v v' : Block) => v = tape.2.2.1.permutation (coordinate, index)
        (encodeBit bit ^^^ keys.first) ∧ v' = v) ⟨rfl, trivial⟩ ⟨rfl, rfl⟩)
    fun v v' related => Sim.pure' ?_
  obtain ⟨rfl, rfl⟩ := related
  refine ⟨rfl, ?_⟩
  show _ ^^^ (keys.second ^^^ T.key2) = _
  ac_rfl

/-- One position's two pads. -/
def padPair (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) :
    Programs.M (Block × Block) :=
  Programs.padM keys coordinate index false >>= fun zero =>
    Programs.padM keys coordinate index true >>= fun one => Pure.pure (zero, one)

/-- The relation of one position's two pads. -/
def PadPairRel (tape : Coins × Oracle) (T : TapeShift) (keys : WhiteningKeys)
    (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) (p p' : Block × Block) : Prop :=
  p.1 = EncPRF.evenMansourPad tape.2.2.1 keys { coordinate, index, bit := false } ∧
  p.2 = EncPRF.evenMansourPad tape.2.2.1 keys { coordinate, index, bit := true } ∧
  p'.1 = p.1 ^^^ T.key2 ∧ p'.2 = p.2 ^^^ T.key2

theorem garbler_padPair (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) :
    Sim (publicAnswer tape.2) (publicAnswer (shiftTape T scalar tape).2) (GarbleRel T scalar tape)
      (PadPairRel tape T keys coordinate index) (padPair keys coordinate index)
      (padPair ⟨keys.first, keys.second ^^^ T.key2⟩ coordinate index) :=
  Sim.bind (garbler_padM T scalar tape keys coordinate index false) fun _ _ hzero =>
    Sim.bind (garbler_padM T scalar tape keys coordinate index true) fun _ _ hone =>
      Sim.pure' ⟨hzero.1, hone.1, hzero.2, hone.2⟩

theorem garbler_padRow (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate) :
    Sim (publicAnswer tape.2) (publicAnswer (shiftTape T scalar tape).2) (GarbleRel T scalar tape)
      (fun v v' => ∀ index, PadPairRel tape T keys coordinate index (v.get index) (v'.get index))
      (FreeQuery.vector coordinateBitCount fun index => padPair keys coordinate index)
      (FreeQuery.vector coordinateBitCount fun index =>
        padPair ⟨keys.first, keys.second ^^^ T.key2⟩ coordinate index) :=
  Sim.vector coordinateBitCount _ _ fun index => garbler_padPair T scalar tape keys coordinate index

theorem garbler_padsM (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (keys : WhiteningKeys) :
    Sim (publicAnswer tape.2) (publicAnswer (shiftTape T scalar tape).2) (GarbleRel T scalar tape)
      (fun pads pads' => pads = Programs.realPads tape.2.2.1 keys ∧
        ∀ coordinate index bit, pads' coordinate index bit = pads coordinate index bit ^^^ T.key2)
      (Programs.padsM keys) (Programs.padsM ⟨keys.first, keys.second ^^^ T.key2⟩) := by
  unfold Programs.padsM
  refine Sim.bind (garbler_padRow T scalar tape keys .x) fun xs xs' hxs =>
    Sim.bind (garbler_padRow T scalar tape keys .y) fun ys ys' hys => Sim.pure' ⟨?_, ?_⟩
  · funext coordinate index bit
    cases coordinate <;> cases bit
    · exact (hxs index).1
    · exact (hxs index).2.1
    · exact (hys index).1
    · exact (hys index).2.1
  · intro coordinate index bit
    cases coordinate <;> cases bit
    · exact (hxs index).2.2.1
    · exact (hxs index).2.2.2
    · exact (hys index).2.2.1
    · exact (hys index).2.2.2

/-! ### The gadget -/

theorem garbler_gadgetPairsM (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (output : Fin digitCount) (coordinate : EncPRF.Coordinate) (key key' : CoordinateMacKey)
    (shift : Fin coordinateBitCount → Bool → Block)
    (labels : ∀ i bit, BitAdaptor.encode key'[i.val] bit = BitAdaptor.encode key[i.val] bit ^^^ shift i bit)
    (shifts : ∀ i bit, indexShift T scalar tape.1
      (.gadget output (Pipeline.gadgetCoord coordinate) i bit) = (shift i bit, shift i bit))
    (good : ∀ i bit, BitAdaptor.encode key[i.val] bit = garblerPointOf scalar tape
      (.gadget output (Pipeline.gadgetCoord coordinate) i bit)) :
    Sim (publicAnswer tape.2) (publicAnswer (shiftTape T scalar tape).2) (GarbleRel T scalar tape)
      (fun v v' => v' = v) (Programs.gadgetPairsM output coordinate key)
      (Programs.gadgetPairsM output coordinate key') := by
  have one : ∀ (i : Fin coordinateBitCount) (bit : Bool),
      Sim (publicAnswer tape.2) (publicAnswer (shiftTape T scalar tape).2) (GarbleRel T scalar tape)
        (fun v v' => v' = v)
        (Programs.hashM (.gadget output (Pipeline.gadgetCoord coordinate) i bit)
          (BitAdaptor.encode key[i.val] bit))
        (Programs.hashM (.gadget output (Pipeline.gadgetCoord coordinate) i bit)
          (BitAdaptor.encode key'[i.val] bit)) := by
    intro i bit
    rw [labels i bit]
    have oracle := shiftOracle_fixed T scalar tape
      (.gadget output (Pipeline.gadgetCoord coordinate) i bit) (BitAdaptor.encode key[i.val] bit)
    have entry := garbleRel_fixed T scalar tape
      (.gadget output (Pipeline.gadgetCoord coordinate) i bit) (BitAdaptor.encode key[i.val] bit)
      (good i bit)
    rw [shifts i bit] at oracle entry
    exact Sim.mono (sim_hashM tape.2 (shiftTape T scalar tape).2 _ _ _ _ oracle entry)
      fun v v' related => by rw [related.2, xor_cancel_right]
  unfold Programs.gadgetPairsM
  refine Sim.mono (Sim.vector coordinateBitCount (R := fun _ v v' => v' = v) _ _ fun i =>
    Sim.bind (one i false) fun zero zero' sameZero => Sim.bind (one i true) fun first first' sameFirst =>
      Sim.pure' (by rw [sameZero, sameFirst])) fun values values' related => ?_
  exact Vector.ext fun i small => by
    have := related ⟨i, small⟩
    simpa [Vector.get_eq_getElem] using this

/-- Both labels of a shifted, transformed key move by the gadget shift of their bit. -/
theorem transform_label_shift (T : TapeShift) (coins : Coins) (pads pads' : Programs.Pads)
    (padsShift : ∀ coordinate index bit, pads' coordinate index bit = pads coordinate index bit ^^^ T.key2)
    (index : Fin coordinateBitCount) (bit : Bool) :
    BitAdaptor.encode (Programs.transformKeyOf pads' (shiftCoins T coins).inputMacKey).x[index.val] bit =
      BitAdaptor.encode (Programs.transformKeyOf pads coins.inputMacKey).x[index.val] bit ^^^
        (T.key2 ^^^ T.zero .x index ^^^ (if bit then T.delta .x else 0)) ∧
    BitAdaptor.encode (Programs.transformKeyOf pads' (shiftCoins T coins).inputMacKey).y[index.val] bit =
      BitAdaptor.encode (Programs.transformKeyOf pads coins.inputMacKey).y[index.val] bit ^^^
        (T.key2 ^^^ T.zero .y index ^^^ (if bit then T.delta .y else 0)) := by
  simp only [Programs.transformKeyOf, Coins.inputMacKey, shiftCoins, Vector.getElem_ofFn,
    BitAdaptor.encode, encrypt, Cryptography.xor, padsShift]
  constructor
  · split <;> ac_rfl
  · split <;> ac_rfl

theorem garbler_garbleEntryM (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (pads pads' : Programs.Pads)
    (padsEq : pads = Programs.realPads tape.2.2.1
      ⟨(tape.2.2.2 (bridgeInput tape.1.bridgeKey)).1, (tape.2.2.2 (bridgeInput
          tape.1.bridgeKey)).2⟩)
    (padsShift : ∀ coordinate index bit, pads' coordinate index bit = pads coordinate index bit ^^^ T.key2)
    (output : Fin digitCount) (pad : Exception.Entry) :
    Sim (publicAnswer tape.2) (publicAnswer (shiftTape T scalar tape).2) (GarbleRel T scalar tape)
      (fun v v' => v' = v)
      (Programs.garbleEntryM output (digitKey scalar tape.1.offsets output)
        (Programs.transformKeyOf pads tape.1.inputMacKey) pad)
      (Programs.garbleEntryM output (digitKey scalar tape.1.offsets output)
        (Programs.transformKeyOf pads' (shiftCoins T tape.1).inputMacKey) pad) := by
  unfold Programs.garbleEntryM
  split
  · exact Sim.pure' rfl
  · rename_i phi found
    have labels := transform_label_shift T tape.1 pads pads' padsShift
    refine Sim.bind (garbler_gadgetPairsM T scalar tape output .x _ _ _ (fun i bit => (labels i bit).1)
        (fun i bit => by simp only [indexShift, gadgetShift, Pipeline.gadgetCoord])
        (fun i bit => by
          simp only [garblerPointOf, gadgetLabel, found, padsEq, Programs.transformKeyOf_realPads,
            EncPRF.whiteningKeys, Pipeline.gadgetCoord]))
      fun xPairs xPairs' sameX => Sim.bind
        (garbler_gadgetPairsM T scalar tape output .y _ _ _ (fun i bit => (labels i bit).2)
          (fun i bit => by simp only [indexShift, gadgetShift, Pipeline.gadgetCoord])
          (fun i bit => by
            simp only [garblerPointOf, gadgetLabel, found, padsEq, Programs.transformKeyOf_realPads,
              EncPRF.whiteningKeys, Pipeline.gadgetCoord]))
        fun yPairs yPairs' sameY => Sim.pure' ?_
    rw [sameX, sameY]

theorem garbler_gadgetM (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (pads pads' : Programs.Pads)
    (padsEq : pads = Programs.realPads tape.2.2.1
      ⟨(tape.2.2.2 (bridgeInput tape.1.bridgeKey)).1, (tape.2.2.2 (bridgeInput
          tape.1.bridgeKey)).2⟩)
    (padsShift : ∀ coordinate index bit, pads' coordinate index bit = pads coordinate index bit ^^^ T.key2) :
    Sim (publicAnswer tape.2) (publicAnswer (shiftTape T scalar tape).2) (GarbleRel T scalar tape)
      (fun v v' => v' = v)
      (Programs.gadgetM (FieldMacToECMac.outputKeys construction scalar.value tape.1.offsets)
        (Programs.transformKeyOf pads tape.1.inputMacKey) tape.1.exceptionPad)
      (Programs.gadgetM (FieldMacToECMac.outputKeys construction scalar.value tape.1.offsets)
        (Programs.transformKeyOf pads' (shiftCoins T tape.1).inputMacKey) tape.1.exceptionPad) := by
  unfold Programs.gadgetM
  refine Sim.mono (Sim.vector _ _ _ fun output =>
    garbler_garbleEntryM T scalar tape pads pads' padsEq padsShift output
      (tape.1.exceptionPad.get output)) fun v v' same => ?_
  exact Vector.ext fun i small => by
    have := same ⟨i, small⟩
    simpa [Vector.get_eq_getElem] using this

/-! ### The whole garbler -/

theorem assemble_congr (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (bridgeKey : BaseField) (curveMask : NonZeroBase)
    (cx cx' : Programs.LaneTables curveElementCountX) (cy cy' : Programs.LaneTables curveElementCountY)
    (px px' : Programs.LaneTables pointElementCountX) (py py' : Programs.LaneTables pointElementCountY)
    (gadget : Vector Exception.Entry FieldMacToECMac.outputMacCount)
    (mcx : cx'.masks = cx.masks) (jcx : ∀ c, (cx'.hot c).2 = (cx.hot c).2)
    (mcy : cy'.masks = cy.masks) (jcy : ∀ c, (cy'.hot c).2 = (cy.hot c).2)
    (mpx : px'.masks = px.masks) (jpx : ∀ c, (px'.hot c).2 = (px.hot c).2)
    (mpy : py'.masks = py.masks) (jpy : ∀ c, (py'.hot c).2 = (py.hot c).2) :
    Programs.assemble outputKeys pointRandomness bridgeKey curveMask cx' cy' px' py' gadget =
      Programs.assemble outputKeys pointRandomness bridgeKey curveMask cx cy px py gadget := by
  unfold Programs.assemble Programs.LaneTables.offsets Programs.LaneTables.hotJoins
    Programs.LaneTables.scaleJoins
  simp only [mcx, jcx, mcy, jcy, mpx, jpx, mpy, jpy]

theorem shift_curve_key (T : TapeShift) (coins : Coins) (κ : Coord) (position : Fin coordinateBitCount) :
    (Pipeline.bitKeyOf (shiftCoins T coins).inputMacKey κ position).1 =
      (Pipeline.bitKeyOf coins.inputMacKey κ position).1 ^^^ T.zero κ position := by
  cases κ <;> simp only [Pipeline.bitKeyOf, Coins.inputMacKey, shiftCoins, Vector.get_ofFn]

theorem shift_point_key (T : TapeShift) (coins : Coins) (pads pads' : Programs.Pads)
    (padsShift : ∀ coordinate index bit, pads' coordinate index bit = pads coordinate index bit ^^^ T.key2)
    (κ : Coord) (position : Fin coordinateBitCount) :
    (Pipeline.bitKeyOf (Programs.whitenKeyOf pads' (shiftCoins T coins).inputMacKey) κ position).1 =
      (Pipeline.bitKeyOf (Programs.whitenKeyOf pads coins.inputMacKey) κ position).1 ^^^
        (T.zero κ position ^^^ T.key2) := by
  cases κ <;>
  · simp only [Pipeline.bitKeyOf, Programs.whitenKeyOf, Coins.inputMacKey, shiftCoins, Vector.get_ofFn,
      Vector.getElem_ofFn, encrypt, Cryptography.xor, padsShift]
    ac_rfl

theorem lane_zero_curveX (T : TapeShift) (position : Fin PlanB.coordinateBits) :
    (T.lane .curveX).zero position = T.zero .x position := by
  simp [TapeShift.lane, laneIsPoint, Lane.coord]

theorem lane_zero_curveY (T : TapeShift) (position : Fin PlanB.coordinateBits) :
    (T.lane .curveY).zero position = T.zero .y position := by
  simp [TapeShift.lane, laneIsPoint, Lane.coord]

theorem lane_zero_pointX (T : TapeShift) (position : Fin PlanB.coordinateBits) :
    (T.lane .pointX).zero position = T.zero .x position ^^^ T.key2 := by
  simp [TapeShift.lane, laneIsPoint, Lane.coord]

theorem lane_zero_pointY (T : TapeShift) (position : Fin PlanB.coordinateBits) :
    (T.lane .pointY).zero position = T.zero .y position ^^^ T.key2 := by
  simp [TapeShift.lane, laneIsPoint, Lane.coord]

/-- **The whole garbler on the shifted tape.** -/
theorem garbler_sim (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    Sim (publicAnswer tape.2) (publicAnswer (shiftTape T scalar tape).2) (GarbleRel T scalar tape)
      (fun result result' => result'.1 = result.1)
      (Programs.garbleM scalar tape.1) (Programs.garbleM scalar (shiftTape T scalar tape).1) := by
  unfold Programs.garbleM
  refine Sim.bind (garbler_askHash T scalar tape) fun hashed hashed' hashedRel => ?_
  obtain ⟨rfl, rfl⟩ := hashedRel
  refine Sim.bind (garbler_padsM T scalar tape
    ⟨(tape.2.2.2 (bridgeInput tape.1.bridgeKey)).1, (tape.2.2.2 (bridgeInput tape.1.bridgeKey)).2⟩)
    fun pads pads' padsRel => ?_
  obtain ⟨rfl, padsShift⟩ := padsRel
  refine Sim.bind (garbler_laneM T valid scalar tape .curveX _ _ _ _ rfl rfl rfl
    fun position => ?_) fun cx cx' cxRel => ?_
  · exact (shift_curve_key T tape.1 _ position).trans (by rw [lane_zero_curveX])
  refine Sim.bind (garbler_laneM T valid scalar tape .curveY _ _ _ _ rfl rfl rfl
    fun position => ?_) fun cy cy' cyRel => ?_
  · exact (shift_curve_key T tape.1 _ position).trans (by rw [lane_zero_curveY])
  refine Sim.bind (garbler_laneM T valid scalar tape .pointX _ _ _ _ rfl rfl rfl
    fun position => ?_) fun px px' pxRel => ?_
  · exact (shift_point_key T tape.1 _ pads' padsShift _ position).trans
      (by rw [lane_zero_pointX])
  refine Sim.bind (garbler_laneM T valid scalar tape .pointY _ _ _ _ rfl rfl rfl
    fun position => ?_) fun py py' pyRel => ?_
  · exact (shift_point_key T tape.1 _ pads' padsShift _ position).trans
      (by rw [lane_zero_pointY])
  refine Sim.bind (garbler_gadgetM T scalar tape _ pads' rfl padsShift) fun gadget gadget' gadgetRel =>
    Sim.pure' ?_
  rw [gadgetRel]
  exact assemble_congr _ _ _ _ _ _ _ _ _ _ _ _ _ cxRel.2.1 cxRel.2.2 cyRel.2.1 cyRel.2.2
    pxRel.2.1 pxRel.2.2 pyRel.2.1 pyRel.2.2

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
