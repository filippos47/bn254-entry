/-
This file defines the Plan B public value: everything the garbler publishes.

The plan source is `2026-09-17-planB.md`, section D.5. Every field has a
fixed width and there are no `Option` tags anywhere, so *every* inhabitant of `Public` encodes
to exactly `ciphertextBytesConstant` bytes; the byte-count theorem therefore does not mention
`garble` at all.

| Field       | Encoding                                 | Bytes   |
|-------------|------------------------------------------|---------|
| `curve`, `rows` | one base-`p` word of `1 + 91 * 10 = 911` field elements | 28,879 |
| `exception` | `Vector (Vector (BitVec 3) 12) 91`, one word | 410     |
| `curveXHot` | `Vector Block 202`                        | 3,232   |
| `curveYHot` | `Vector Block 202`                        | 3,232   |
| `pointXHot` | `Vector Block 202`                        | 3,232   |
| `pointYHot` | `Vector Block 202`                        | 3,232   |
| `scale`     | `Vector (BitVec 162816) 52`, base-`p` words | 1,058,304 |
| **total**   |                                           | **1,100,521** |
-/

import Construction.ArgoMAC.Exception
import Construction.PGS.Packing

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-- The ten published constants of one digit's three rows.

The sign row publishes four coefficients (it has no `x` and no `x y` monomial), so a digit
publishes `4 + 4 + 2 = 10` field elements. -/
structure RowGamma where
  /-- `X` row constant `c0`. -/
  xC0 : BaseField
  /-- `X` row constant `c1`. -/
  xC1 : BaseField
  /-- `X` row constant `c2`. -/
  xC2 : BaseField
  /-- `X` row constant `c4`. -/
  xC4 : BaseField
  /-- `Y` row constant `c0`. -/
  yC0 : BaseField
  /-- `Y` row constant `c2`. -/
  yC2 : BaseField
  /-- `Y` row constant `c4`. -/
  yC4 : BaseField
  /-- `Y` row constant `c5`. -/
  yC5 : BaseField
  /-- `Z` row constant `c0`. -/
  zC0 : BaseField
  /-- `Z` row constant `c1`. -/
  zC1 : BaseField

/-- The published constants of one digit, in wire order (`xC0, xC1, xC2, xC4, yC0, yC2, yC4,
yC5, zC0, zC1` at `0 .. 9`). -/
def RowGamma.cell (row : RowGamma) : Nat → BaseField
  | 0 => row.xC0
  | 1 => row.xC1
  | 2 => row.xC2
  | 3 => row.xC4
  | 4 => row.yC0
  | 5 => row.yC2
  | 6 => row.yC4
  | 7 => row.yC5
  | 8 => row.zC0
  | _ => row.zC1

/-- A digit's constants are its ten cells. -/
theorem RowGamma.eta_cell (row : RowGamma) :
    (⟨row.cell 0, row.cell 1, row.cell 2, row.cell 3, row.cell 4, row.cell 5, row.cell 6,
      row.cell 7, row.cell 8, row.cell 9⟩ : RowGamma) = row := by
  cases row; rfl

/-- The complete public value of a Plan B garbling.

Every field is fixed-width: there are no `Option` tags, so every inhabitant encodes to exactly
`ciphertextBytesConstant` bytes. -/
structure Public where
  /-- The curve-membership check: one published constant. -/
  curve : BaseField
  /-- The ten published row constants of each digit. -/
  rows : Vector RowGamma digitCount
  /-- The exception gadget, twelve three-bit slots per digit. -/
  exception : Vector Exception.Entry digitCount
  /-- System A's `bin-to-hot` fold joins on the x coordinate's raw Lamport labels. -/
  curveXHot : Vector Block foldStepCount
  /-- System A's `bin-to-hot` fold joins on the y coordinate's raw Lamport labels. -/
  curveYHot : Vector Block foldStepCount
  /-- System B's `bin-to-hot` fold joins on the x coordinate's EncPRF-whitened labels. -/
  pointXHot : Vector Block foldStepCount
  /-- System B's `bin-to-hot` fold joins on the y coordinate's EncPRF-whitened labels. -/
  pointYHot : Vector Block foldStepCount
  /-- The `scale-hot` join of each chunk, all four lanes interleaved into one word. -/
  scale : Vector (BitVec chunkJoinBits) chunkCount

/-- The Plan B ciphertext size in bytes. -/
def ciphertextBytesConstant : Nat := 1100521

end Kriterion.ArgoMAC.PlanB
