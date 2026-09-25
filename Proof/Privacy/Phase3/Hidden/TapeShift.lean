/-
**Phase 3, P1f — shifting the whole tape.**

A `TapeShift` fixes the shift of each coordinate's `Δ` and zero labels, of the second block of
`hash(bridgeInput t)` (the whitening key `k₂`), and per lane and chunk of the fold's step materials
and gate outputs. `shiftTape T scalar` applies it to a tape:

* the coins: `Δ` and the zero labels XOR the shift;
* the fixed-key permutations: `shiftPerm` at the index's shift (`indexShift`): the fold gates by
  `FoldShift.hot`, the gadget permutations conjugated by the shift of the label the garbler reads
  there (which depends on the digit's exceptional input, hence on the scalar);
* the hash: `k₂` at the bridge input `bridgeInput t` moves by `T.key2`, and every scale input is
  **relabelled** (`relabel`): the hash at `scaleInput ℓ c j i (L ⊕ s)` is the old hash at
  `scaleInput ℓ c j i L`, where `s = siteShift T (ℓ, c, j)` is the level shift of the switch, so
  every switch-mask vector is kept at the moved label; EncPRF is untouched.

`shiftEntry` is the matching map on transcript entries. `Good` is the shape of every garbler entry:
a fixed-key query at index `i` asks at `garblerPointOf i`, the hash is asked at `bridgeInput t` or
at a scale input under the garbler's own label of its switch (`garblerLabelOf`).
-/

import Proof.Privacy.Phase3.Hidden.Lane

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)

noncomputable section

/-- A point lane (system B), whose labels are whitened by `hash(bridgeInput t)`. -/
def laneIsPoint : Lane → Bool
  | .pointX | .pointY => true
  | _ => false

/-- The shift of the whole tape. -/
structure TapeShift where
  /-- The shift of each coordinate's `Δ`. -/
  delta : Coord → Block
  /-- The shift of each raw zero label. -/
  zero : Coord → Fin PlanB.coordinateBits → Block
  /-- The shift of `k₂ = hash(bridgeInput t).2`. -/
  key2 : Block
  /-- Per lane and chunk, the shift of each paid step material. -/
  m : Lane → Fin chunkCount → Nat → Nat → Block
  /-- Per lane and chunk, the shift of both outputs of each fold gate. -/
  o : Lane → Fin chunkCount → Nat → Nat → Block

namespace TapeShift

/-- The shift of one lane: system B's zero labels also move with `k₂`. -/
def lane (T : TapeShift) (ℓ : Lane) : LaneShift where
  delta := T.delta ℓ.coord
  zero position := T.zero ℓ.coord position ^^^ (if laneIsPoint ℓ then T.key2 else 0)
  m := T.m ℓ
  o := T.o ℓ

/-- Every lane keeps its joins. -/
def Valid (T : TapeShift) : Prop := ∀ ℓ, (T.lane ℓ).Valid

end TapeShift

/-! ### Relabelling the scale inputs -/

/-- The level shift of a vector site's one-hot label: its switch's level in its lane and chunk. -/
def siteShift (T : TapeShift) (site : VectorSite) : Block :=
  ((T.lane site.lane).fold site.chunk).level (chunkWidth site.chunk) site.switch.val

/-- **A scale input with its label**: limb `slot.2` of site `slot.1`, under the label `label`. -/
def labelInput (slot : LimbSite) (label : Block) : BaseField :=
  scaleInput slot.1.lane slot.1.chunk slot.1.switch.val slot.2.val label

/-- A scale input names its limb slot and its label (`scaleInput_injective`). -/
theorem labelInput_injective :
    Function.Injective fun pair : LimbSite × Block => labelInput pair.1 pair.2 := by
  rintro ⟨⟨⟨lane, chunk, switch⟩, limb⟩, label⟩ ⟨⟨⟨lane', chunk', switch'⟩, limb'⟩, label'⟩ same
  obtain ⟨laneEq, chunkEq, switchEq, limbEq, labelEq⟩ := scaleInput_injective
    (Pipeline.switch_lt_twoPowChunkBits chunk switch)
    (Pipeline.switch_lt_twoPowChunkBits chunk' switch')
    (lt_trans limb.isLt (limbCount_lt lane)) (lt_trans limb'.isLt (limbCount_lt lane')) same
  subst laneEq
  subst chunkEq
  obtain rfl : switch = switch' := Fin.ext switchEq
  obtain rfl : limb = limb' := Fin.ext limbEq
  exact Prod.ext rfl labelEq

theorem labelInput_inj {slot slot' : LimbSite} {label label' : Block}
    (same : labelInput slot label = labelInput slot' label') : slot = slot' ∧ label = label' :=
  Prod.mk.inj (labelInput_injective (a₁ := (slot, label)) (a₂ := (slot', label')) same)

/-- A scale input lies in the scale range. -/
theorem labelInput_val_lt (slot : LimbSite) (label : Block) :
    (labelInput slot label).val < scaleRange :=
  scaleInput_val_lt_scaleRange _ _ _ _ _

/-- **Relabel the scale inputs**: the label of every scale input of site `v` moves by `shift v`;
every other field element is fixed. -/
def relabel (shift : VectorSite → Block) : BaseField → BaseField :=
  Function.extend (fun pair : LimbSite × Block => labelInput pair.1 pair.2)
    (fun pair => labelInput pair.1 (pair.2 ^^^ shift pair.1.1)) id

theorem relabel_labelInput (shift : VectorSite → Block) (slot : LimbSite) (label : Block) :
    relabel shift (labelInput slot label) = labelInput slot (label ^^^ shift slot.1) :=
  labelInput_injective.extend_apply
    (fun pair : LimbSite × Block => labelInput pair.1 (pair.2 ^^^ shift pair.1.1)) id (slot, label)

theorem relabel_of_not (shift : VectorSite → Block) (value : BaseField)
    (none' : ∀ slot label, labelInput slot label ≠ value) : relabel shift value = value :=
  Function.extend_apply' _ _ value fun ⟨pair, same⟩ => none' pair.1 pair.2 same

theorem relabel_involutive (shift : VectorSite → Block) : Function.Involutive (relabel shift) := by
  intro value
  by_cases hit : ∃ slot label, labelInput slot label = value
  · obtain ⟨slot, label, rfl⟩ := hit
    rw [relabel_labelInput, relabel_labelInput, xor_cancel_right]
  · simp only [not_exists] at hit
    rw [relabel_of_not shift value hit, relabel_of_not shift value hit]

/-- Off the scale range nothing is relabelled (the bridge input in particular). -/
theorem relabel_of_not_lt (shift : VectorSite → Block) (value : BaseField)
    (high : ¬ value.val < scaleRange) : relabel shift value = value :=
  relabel_of_not shift value fun slot label same => high (same ▸ labelInput_val_lt slot label)

/-- The scale range is kept. -/
theorem relabel_val_lt (shift : VectorSite → Block) (value : BaseField)
    (low : value.val < scaleRange) : (relabel shift value).val < scaleRange := by
  by_cases hit : ∃ slot label, labelInput slot label = value
  · obtain ⟨slot, label, rfl⟩ := hit
    rw [relabel_labelInput]
    exact labelInput_val_lt _ _
  · simp only [not_exists] at hit
    rw [relabel_of_not shift value hit]
    exact low

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- The output key of digit `o`. -/
def digitKey (scalar : NonZeroScalar) (offsets : FieldMacToECMac.SuccessfulOffsets) (o : Fin digitCount) :
    FieldMacToECMac.OutputKey :=
  (FieldMacToECMac.outputKeys construction scalar.value offsets).get o

/-- One coordinate of an affine input. -/
def coordValue' : Coord → AffineInput → BaseField
  | .x, input => input.x
  | .y, input => input.y

/-- The bit of digit `o`'s exceptional input at `(κ, position)` (`false` for a digit without
exception, whose gadget asks nothing). -/
def exceptionalBit (scalar : NonZeroScalar) (offsets : FieldMacToECMac.SuccessfulOffsets)
    (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits) : Bool :=
  match digitEndomorphismBase (digitKey scalar offsets o).digit with
  | none => false
  | some phi => (coordinateBits (coordValue' κ
      (Exception.exceptionalInput phi (digitKey scalar offsets o).offset.coordinates))).getLsb position

/-- The bit of digit `o`'s sign-zero input (`Exception.tripleInput`, the input with `Q = 2K`) at
`(κ, position)` (`false` for a digit without exception). -/
def tripleBit (scalar : NonZeroScalar) (offsets : FieldMacToECMac.SuccessfulOffsets)
    (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits) : Bool :=
  match digitEndomorphismBase (digitKey scalar offsets o).digit with
  | none => false
  | some phi => (coordinateBits (coordValue' κ
      (Exception.tripleInput phi (digitKey scalar offsets o).offset.coordinates))).getLsb position

/-- The shift of the label the gadget reads at `(o, κ, position, bit)`: the index names the
label's bit. -/
def gadgetShift (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) (o : Fin digitCount)
    (κ : Coord) (position : Fin PlanB.coordinateBits) (bit : Bool) : Block :=
  T.key2 ^^^ T.zero κ position ^^^ (if bit then T.delta κ else 0)

/-- **The shift of every fixed-key permutation.** -/
def indexShift (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) : FixedIndex → Block × Block
  | .hot ℓ c fold entry half => ((T.lane ℓ).fold c).hot fold.val entry.val half
  | .gadget o κ position bit =>
      (gadgetShift T scalar coins o κ position bit, gadgetShift T scalar coins o κ position bit)

/-- The shifted coins. -/
def shiftCoins (T : TapeShift) (coins : Coins) : Coins :=
  { coins with
    inputZero := fun κ position => coins.inputZero κ position ^^^ T.zero κ position
    inputDelta := fun κ => coins.inputDelta κ ^^^ T.delta κ }

/-- **The shifted hash**: `k₂` at the bridge input, every scale input relabelled. -/
def shiftHash (T : TapeShift) (key : BaseField) (hash : EncPRF.HashOracle) : EncPRF.HashOracle :=
  fun value => if value = bridgeInput key then ((hash value).1, (hash value).2 ^^^ T.key2)
    else hash (relabel (siteShift T) value)

/-- The shifted oracle. -/
def shiftOracle (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) (oracle : Oracle) : Oracle :=
  (⟨fun index => shiftPerm (indexShift T scalar coins index).1 (indexShift T scalar coins index).2
      (oracle.1.permutation index)⟩, oracle.2.1, shiftHash T coins.bridgeKey oracle.2.2)

/-- **The shifted tape.** -/
def shiftTape (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle) : Coins × Oracle :=
  (shiftCoins T tape.1, shiftOracle T scalar tape.1 tape.2)

/-- The matching map on transcript entries. -/
def shiftEntry (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) :
    Asked FixedIndex EncPRF.PermutationIndex → Asked FixedIndex EncPRF.PermutationIndex
  | ⟨.fixedForward index input, answer⟩ =>
      ⟨.fixedForward index (input ^^^ (indexShift T scalar coins index).1),
        (show Block from answer) ^^^ (indexShift T scalar coins index).2⟩
  | ⟨.fixedInverse index output, answer⟩ =>
      ⟨.fixedInverse index (output ^^^ (indexShift T scalar coins index).2),
        (show Block from answer) ^^^ (indexShift T scalar coins index).1⟩
  | ⟨.encForward index input, answer⟩ => ⟨.encForward index input, answer⟩
  | ⟨.encInverse index output, answer⟩ => ⟨.encInverse index output, answer⟩
  | ⟨.hash value, answer⟩ =>
      if value = bridgeInput coins.bridgeKey then
        ⟨.hash value, ((show Block × Block from answer).1,
          (show Block × Block from answer).2 ^^^ T.key2)⟩
      else ⟨.hash (relabel (siteShift T) value), answer⟩

/-! ### The garbler's points -/

/-- Each lane's `Δ` and bit keys on a tape (`GameSwap.garblerKeys`). -/
def laneKeys (tape : Coins × Oracle) :
    (Lane → Block) × (Lane → Fin PlanB.coordinateBits → Block × Block) :=
  garblerKeys (tape.1, tape.2.1, tape.2.2.1) tape.2.2.2

/-- **The garbler's one-hot label at each vector site** (`MaskSwap.garblerLabel` at the tape's
keys). -/
def garblerLabelOf (tape : Coins × Oracle) (site : VectorSite) : Block :=
  garblerLabel tape.2.1 (laneKeys tape).1 (laneKeys tape).2 site

/-- The label the gadget of digit `o` reads at `(κ, position)`. -/
def gadgetLabel (scalar : NonZeroScalar) (tape : Coins × Oracle) (o : Fin digitCount) (κ : Coord)
    (position : Fin PlanB.coordinateBits) (bit : Bool) : Block :=
  match digitEndomorphismBase (digitKey scalar tape.1.offsets o).digit with
  | none => 0
  | some _ =>
      let key := EncPRF.transformKey tape.2.2.1 (EncPRF.whiteningKeys tape.2.2.2 tape.1.bridgeKey)
        tape.1.inputMacKey
      match κ with
      | .x => BitAdaptor.encode key.x[position.val] bit
      | .y => BitAdaptor.encode key.y[position.val] bit

/-- **The garbler's point at each fixed-key index.** -/
def garblerPointOf (scalar : NonZeroScalar) (tape : Coins × Oracle) : FixedIndex → Block
  | .hot ℓ c fold entry _ =>
      (garbleFold tape.2.1 ℓ c ((laneKeys tape).1 ℓ)
        (labelAt fun p => (chunkKey ((laneKeys tape).2 ℓ) c p).1) fold.val).1
        ⟨entry.val % 2 ^ fold.val, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  | .gadget o κ position bit => gadgetLabel scalar tape o κ position bit

/-- **The shape of a garbler entry.** -/
def Good (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    Asked FixedIndex EncPRF.PermutationIndex → Prop
  | ⟨.fixedForward index input, _⟩ => input = garblerPointOf scalar tape index
  | ⟨.encForward _ _, _⟩ => True
  | ⟨.hash value, _⟩ => value = bridgeInput tape.1.bridgeKey ∨
      ∃ slot : LimbSite, value = labelInput slot (garblerLabelOf tape slot.1)
  | _ => False

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
