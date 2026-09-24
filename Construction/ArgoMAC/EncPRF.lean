/-
This file defines the EncPRF label link.

The whitening keys are the hash of the bridge key `t` at `PlanB.bridgeInput t`, which lies in
`[2 ^ 150, p)`: outside the range `[0, 2 ^ 150)` of every `scale-hot` hash input, so the bridge
query and the switch mask queries are disjoint by construction.
-/

import Construction.ArgoMAC.Input
import Construction.PGS.BatchSampler

namespace Kriterion.ArgoMAC.EncPRF

open BN254 Cryptography

inductive Coordinate
  | x
  | y
deriving DecidableEq

instance : Fintype Coordinate := ⟨{.x, .y}, fun value => by cases value <;> simp⟩

structure Counter where
  coordinate : Coordinate
  index : Fin coordinateBitCount
  bit : Bool

abbrev PermutationIndex := Coordinate × Fin coordinateBitCount
abbrev HashOracle := BaseField → Block × Block

/-- The whitening keys of the bridge key `value`: one hash query at `PlanB.bridgeInput value`. -/
def whiteningKeys (oracle : HashOracle) (value : BaseField) : WhiteningKeys :=
  let keys := oracle (PlanB.bridgeInput value)
  { first := keys.1, second := keys.2 }

/-- This is the fixed-key AES pad. -/
def evenMansourPad (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (counter : Counter) : Block :=
  evenMansour (oracle.permutation (counter.coordinate, counter.index)) keys counter.bit

/-- This is `EncPRF(t, counter) xor label` from the paper. -/
def transformAt (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (counter : Counter) (label : Block) : Block :=
  encrypt (evenMansourPad oracle keys counter) label

theorem transformAtSelfInverse (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (counter : Counter) (label : Block) :
    transformAt oracle keys counter (transformAt oracle keys counter label) = label :=
  decryptEncrypt _ _

def transformCoordinateKey (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : Coordinate) (key : CoordinateMacKey) :
    CoordinateMacKey :=
  Vector.ofFn fun index =>
    let source := key[index.val]
    { falseLabel := transformAt oracle keys { coordinate, index, bit := false }
        source.falseLabel
      trueLabel := transformAt oracle keys { coordinate, index, bit := true }
        source.trueLabel }

/-- This operation transforms all label pairs. -/
def transformKey (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (key : InputMacKey) : InputMacKey := {
  x := transformCoordinateKey oracle keys .x key.x
  y := transformCoordinateKey oracle keys .y key.y
}

def transformCoordinateMac (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : Coordinate)
    (bits : BitVec coordinateBitCount) (mac : CoordinateMac) : CoordinateMac :=
  Vector.ofFn fun index =>
    let bit := bits.getLsb index
    let source := mac[index.val]
    transformAt oracle keys { coordinate, index, bit } source

/-- This operation transforms all selected labels. -/
def transformMac (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (input : BitInput) (mac : InputMac) : InputMac := {
  x := transformCoordinateMac oracle keys .x input.xBits mac.x
  y := transformCoordinateMac oracle keys .y input.yBits mac.y
}

theorem transformCoordinateEncode (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : Coordinate) (key : CoordinateMacKey)
    (bits : BitVec coordinateBitCount) :
    transformCoordinateMac oracle keys coordinate bits (encodeCoordinate key bits) =
      encodeCoordinate (transformCoordinateKey oracle keys coordinate key) bits := by
  apply Vector.ext
  intro index indexValid
  let finiteIndex : Fin coordinateBitCount := ⟨index, indexValid⟩
  change (transformCoordinateMac oracle keys coordinate bits
    (encodeCoordinate key bits))[index] =
      (encodeCoordinate (transformCoordinateKey oracle keys coordinate key) bits)[index]
  simp only [transformCoordinateMac, transformCoordinateKey, encodeCoordinate,
    Vector.getElem_ofFn]
  cases bits.getLsb finiteIndex <;> simp [BitAdaptor.encode]

theorem transformEncode (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (key : InputMacKey) (input : BitInput) :
    transformMac oracle keys input (key.encode input) =
      (transformKey oracle keys key).encode input := by
  apply InputMac.ext
  · exact transformCoordinateEncode oracle keys .x key.x input.xBits
  · exact transformCoordinateEncode oracle keys .y key.y input.yBits

theorem transformCoordinateMacSelfInverse
    (oracle : PermutationOracle PermutationIndex Block) (keys : WhiteningKeys)
    (coordinate : Coordinate) (bits : BitVec coordinateBitCount) (mac : CoordinateMac) :
    transformCoordinateMac oracle keys coordinate bits
        (transformCoordinateMac oracle keys coordinate bits mac) = mac := by
  apply Vector.ext
  intro index indexValid
  let finiteIndex : Fin coordinateBitCount := ⟨index, indexValid⟩
  change (transformCoordinateMac oracle keys coordinate bits
    (transformCoordinateMac oracle keys coordinate bits mac))[index] = mac[index]
  simp only [transformCoordinateMac, Vector.getElem_ofFn]
  exact transformAtSelfInverse oracle keys
    { coordinate, index := finiteIndex, bit := bits.getLsb finiteIndex } mac[index]

/-- Applying the selected-label transform twice restores the input labels. -/
theorem transformMacSelfInverse (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (input : BitInput) (mac : InputMac) :
    transformMac oracle keys input (transformMac oracle keys input mac) = mac := by
  apply InputMac.ext
  · exact transformCoordinateMacSelfInverse oracle keys .x input.xBits mac.x
  · exact transformCoordinateMacSelfInverse oracle keys .y input.yBits mac.y

/-! ### The correlation-preserving gate

The exception gadget's `transformAt` uses a *bit-dependent* pad (`evenMansour` selects the
whitening input by `counter.bit`), so the two labels of a position do not keep a common XOR
offset across the gate. Switch system B needs them to: its `bin-to-hot` fold is a free-XOR
fold, and it is sound only when every bit of a coordinate carries the *same* global offset.

`whitenAt` therefore applies one pad per (coordinate, position) to *both* labels of that
position. The pad is still `EncPRF(t, ·)` at the bridge key `t`, so without `t` every whitened
label is an unknown one-time pad of the real one; what survives is exactly the free-XOR
relation, which carries no information about the labels themselves. -/

/-- The correlation-preserving whitening pad of one label position. -/
def whitenPad (oracle : PermutationOracle PermutationIndex Block) (keys : WhiteningKeys)
    (coordinate : Coordinate) (index : Fin coordinateBitCount) : Block :=
  evenMansourPad oracle keys { coordinate, index, bit := false }

/-- The whitened label: one pad per position, applied to both labels of the pair. -/
def whitenAt (oracle : PermutationOracle PermutationIndex Block) (keys : WhiteningKeys)
    (coordinate : Coordinate) (index : Fin coordinateBitCount) (label : Block) : Block :=
  encrypt (whitenPad oracle keys coordinate index) label

theorem whitenAtSelfInverse (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : Coordinate) (index : Fin coordinateBitCount)
    (label : Block) :
    whitenAt oracle keys coordinate index (whitenAt oracle keys coordinate index label) = label :=
  decryptEncrypt _ _

/-- The whitening keeps the free-XOR offset of a label pair. -/
theorem whitenAt_xor (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : Coordinate) (index : Fin coordinateBitCount)
    (label delta : Block) :
    whitenAt oracle keys coordinate index (label ^^^ delta)
      = whitenAt oracle keys coordinate index label ^^^ delta := by
  show whitenPad oracle keys coordinate index ^^^ (label ^^^ delta)
    = (whitenPad oracle keys coordinate index ^^^ label) ^^^ delta
  rw [BitVec.xor_assoc]

def whitenCoordinateKey (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : Coordinate) (key : CoordinateMacKey) :
    CoordinateMacKey :=
  Vector.ofFn fun index =>
    let source := key[index.val]
    { falseLabel := whitenAt oracle keys coordinate index source.falseLabel
      trueLabel := whitenAt oracle keys coordinate index source.trueLabel }

/-- The whitened label pairs of both coordinates. -/
def whitenKey (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (key : InputMacKey) : InputMacKey := {
  x := whitenCoordinateKey oracle keys .x key.x
  y := whitenCoordinateKey oracle keys .y key.y
}

def whitenCoordinateMac (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : Coordinate) (mac : CoordinateMac) : CoordinateMac :=
  Vector.ofFn fun index => whitenAt oracle keys coordinate index mac[index.val]

/-- The whitened selected labels. Unlike `transformMac` this does not read the cleartext
bits: the pad of a position is the same for both labels, which is the whole point. -/
def whitenMac (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (mac : InputMac) : InputMac := {
  x := whitenCoordinateMac oracle keys .x mac.x
  y := whitenCoordinateMac oracle keys .y mac.y
}

theorem whitenCoordinateEncode (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : Coordinate) (key : CoordinateMacKey)
    (bits : BitVec coordinateBitCount) :
    whitenCoordinateMac oracle keys coordinate (encodeCoordinate key bits) =
      encodeCoordinate (whitenCoordinateKey oracle keys coordinate key) bits := by
  apply Vector.ext
  intro index indexValid
  change (whitenCoordinateMac oracle keys coordinate (encodeCoordinate key bits))[index] =
    (encodeCoordinate (whitenCoordinateKey oracle keys coordinate key) bits)[index]
  simp only [whitenCoordinateMac, whitenCoordinateKey, encodeCoordinate, Vector.getElem_ofFn]
  cases bits.getLsb (⟨index, indexValid⟩ : Fin coordinateBitCount) <;> simp [BitAdaptor.encode]

/-- Whitening the selected labels is selecting the whitened labels. -/
theorem whitenEncode (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (key : InputMacKey) (input : BitInput) :
    whitenMac oracle keys (key.encode input) = (whitenKey oracle keys key).encode input := by
  apply InputMac.ext
  · exact whitenCoordinateEncode oracle keys .x key.x input.xBits
  · exact whitenCoordinateEncode oracle keys .y key.y input.yBits

def transform (pad label : Block) : Block := encrypt pad label

def inverse (pad label : Block) : Block := encrypt pad label

theorem inverseTransform (pad label : Block) :
    inverse pad (transform pad label) = label :=
  decryptEncrypt pad label

end Kriterion.ArgoMAC.EncPRF
