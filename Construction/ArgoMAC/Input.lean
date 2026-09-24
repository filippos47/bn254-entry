/-
This file defines the 508-bit affine input and its selected labels.
-/

import Construction.ArgoMAC.BitAdaptor

namespace Kriterion.ArgoMAC

open BN254

abbrev CoordinateMacKey := Vector BitAdaptor.Key coordinateBitCount
abbrev CoordinateMac := Vector Cryptography.Block coordinateBitCount
abbrev CoordinateBits := BitVec coordinateBitCount

/-- The input stores `x_bits || y_bits`. -/
structure BitInput where
  xBits : CoordinateBits
  yBits : CoordinateBits
deriving DecidableEq

def BitInput.x (input : BitInput) : BaseField := input.xBits.toNat
def BitInput.y (input : BitInput) : BaseField := input.yBits.toNat

def BitInput.toAffine (input : BitInput) : AffineInput := {
  x := input.x
  y := input.y
}

/-- The key stores one label pair for each coordinate bit. -/
structure InputMacKey where
  x : CoordinateMacKey
  y : CoordinateMacKey

/-- The encoding contains one selected label for each coordinate bit. -/
@[ext] structure InputMac where
  x : CoordinateMac
  y : CoordinateMac
deriving DecidableEq

/-- This is the canonical 254-bit little-endian coordinate encoding. -/
def coordinateBits (value : BaseField) : BitVec coordinateBitCount :=
  BitVec.ofNat coordinateBitCount value.val

theorem coordinateBitsToNat (value : BaseField) :
    (coordinateBits value).toNat = value.val := by
  rw [coordinateBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_trans value.val_lt (by decide)

/-- This is the canonical encoding of two field coordinates. -/
def BitInput.ofAffine (input : AffineInput) : BitInput := {
  xBits := coordinateBits input.x
  yBits := coordinateBits input.y
}

def encodeCoordinate (key : CoordinateMacKey)
    (bits : BitVec coordinateBitCount) : CoordinateMac :=
  Vector.ofFn fun index => BitAdaptor.encode key[index.val] (bits.getLsb index)

/-- This is `InputMacKey::encode`. -/
def InputMacKey.encode (key : InputMacKey) (input : BitInput) : InputMac := {
  x := encodeCoordinate key.x input.xBits
  y := encodeCoordinate key.y input.yBits
}

def InputMacKey.encodeAffine (key : InputMacKey) (input : AffineInput) : InputMac :=
  key.encode (BitInput.ofAffine input)

theorem InputMacKey.encodeOfAffine (key : InputMacKey) (input : AffineInput) :
    key.encode (BitInput.ofAffine input) = key.encodeAffine input := rfl

theorem BitInput.toAffineOfAffine (input : AffineInput) :
    (BitInput.ofAffine input).toAffine = input := by
  cases input with
  | mk x y =>
      simp [BitInput.ofAffine, BitInput.toAffine, BitInput.x, BitInput.y,
        coordinateBitsToNat]

end Kriterion.ArgoMAC
