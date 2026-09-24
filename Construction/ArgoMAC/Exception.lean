/-
This file defines the exception gadget that recovers the digit at the Jacobian doubling case.
-/

import Construction.ArgoMAC.Base7
import Construction.ArgoMAC.EncPRF

namespace Kriterion.ArgoMAC.Exception

open BN254 Cryptography

/-- `digitCode` assigns each digit its one-byte code. -/
def digitCode : Digit → BitVec 8
  | .zero => 0
  | .one => 1
  | .negOne => 2
  | .omega => 3
  | .negOmega => 4
  | .omegaSquared => 5
  | .negOmegaSquared => 6

/-- `digitOfCode` decodes a one-byte code, mapping every unused code to `zero`. -/
def digitOfCode (code : BitVec 8) : Digit :=
  match code.toNat with
  | 1 => .one
  | 2 => .negOne
  | 3 => .omega
  | 4 => .negOmega
  | 5 => .omegaSquared
  | 6 => .negOmegaSquared
  | _ => .zero

/-- Decoding inverts `digitCode`. -/
theorem digitOfCode_digitCode (digit : Digit) : digitOfCode (digitCode digit) = digit := by
  cases digit <;> rfl

/-- The rank of `x` inside its orbit `{x, μx, μ²x}` under the cube root of unity. -/
def orbitRank (x : BaseField) : Fin 3 :=
  let first := endomorphismBase * x
  let second := endomorphismBase ^ 2 * x
  ⟨(if first.val < x.val then 1 else 0) + (if second.val < x.val then 1 else 0), by
    split_ifs <;> omega⟩

/-- The rank of `y` inside `{y, -y}`. -/
def signRank (y : BaseField) : Fin 2 :=
  if (-y).val < y.val then 1 else 0

/-- `exceptionIndex` is the gadget slot of an input, combining both ranks. -/
def exceptionIndex (input : AffineInput) : Fin 6 :=
  ⟨(orbitRank input.x).val * 2 + (signRank input.y).val, by
    have first := (orbitRank input.x).isLt
    have second := (signRank input.y).isLt
    omega⟩

/-- `Entry` is the six-byte exception gadget table. -/
abbrev Entry := Vector (BitVec 8) 6

/-- `lowByte` truncates a block to its low byte. -/
def lowByte (block : Block) : BitVec 8 := BitVec.ofNat 8 block.toNat

/-- The input whose digit transform lands exactly on the offset. -/
def exceptionalInput (phi : BaseField) (offset : AffineInput) : AffineInput :=
  { x := phi ^ 2 * offset.x, y := phi ^ 3 * offset.y }

/-- The digit transform of `exceptionalInput` recovers the offset for a sixth root of unity. -/
theorem exceptionalInput_transform (phi : BaseField) (phiSix : phi ^ 6 = 1)
    (offset : AffineInput) :
    ({ x := phi ^ 4 * (exceptionalInput phi offset).x,
       y := phi ^ 3 * (exceptionalInput phi offset).y } : AffineInput) = offset := by
  cases offset with
  | mk kx ky =>
      simp only [exceptionalInput, AffineInput.mk.injEq]
      constructor
      · calc phi ^ 4 * (phi ^ 2 * kx) = phi ^ 6 * kx := by ring
          _ = kx := by rw [phiSix, one_mul]
      · calc phi ^ 3 * (phi ^ 3 * ky) = phi ^ 6 * ky := by ring
          _ = ky := by rw [phiSix, one_mul]

/-- `writeEntry` stores a masked byte at one gadget slot. -/
def writeEntry (pad : Entry) (index : Fin 6) (value : BitVec 8) : Entry :=
  pad.set index value

/-- `unlock` reads the slot selected by the input and removes the gadget mask. -/
def unlock (mask : BitVec 8) (entry : Entry) (input : AffineInput) : Digit :=
  digitOfCode (entry.get (exceptionIndex input) ^^^ mask)

/-- Unlocking the slot written for an input recovers the digit stored there. -/
theorem unlock_writeEntry (mask : BitVec 8) (pad : Entry) (input : AffineInput)
    (digit : Digit) :
    unlock mask (writeEntry pad (exceptionIndex input) (mask ^^^ digitCode digit)) input =
      digit := by
  simp only [unlock, writeEntry, Vector.get_eq_getElem, Vector.getElem_set_self]
  rw [BitVec.xor_comm mask (digitCode digit), BitVec.xor_assoc,
    BitVec.xor_self, BitVec.xor_zero, digitOfCode_digitCode]

end Kriterion.ArgoMAC.Exception
