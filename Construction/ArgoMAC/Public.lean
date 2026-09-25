/-
This file defines the Plan B public value: everything the garbler publishes.

The plan source is `2026-09-17-planB.md`, section D.5. Every field has a
fixed width and there are no `Option` tags anywhere, so *every* inhabitant of `Public` encodes
to exactly `ciphertextBytesConstant` bytes; the byte-count theorem therefore does not mention
`garble` at all.

| Field       | Encoding                                 | Bytes   |
|-------------|------------------------------------------|---------|
| `curve`     | `3 * Wire.field`                          | 96      |
| `rows`      | `Vector RowGamma 91`, 3 field elements    | 8,736   |
| `exception` | `Vector (Vector (BitVec 8) 12) 91`        | 1,092   |
| `curveXHot` | `Vector Block 202`                        | 3,232   |
| `curveYHot` | `Vector Block 202`                        | 3,232   |
| `pointXHot` | `Vector Block 202`                        | 3,232   |
| `pointYHot` | `Vector Block 202`                        | 3,232   |
| `scale`     | `Vector (BitVec 163072) 52`               | 1,059,968 |
| **total**   |                                           | **1,082,820** |
-/

import Construction.ArgoMAC.Exception
import Construction.PGS.Packing

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-- The three published constants of one digit's three rows, one per row.

The slopes of the seven elements a digit consumes carry the true row coefficients
(`Biquadratic.slopes`), so each row publishes only the constant that absorbs its collector's
offset: `X` and `Z` their constant monomial, the sign row (in the `Y` slot) its `x²`
coefficient. -/
structure RowGamma where
  /-- The `X` row constant. -/
  gX : BaseField
  /-- The sign row's `x²` coefficient. -/
  gY : BaseField
  /-- The `Z` row constant. -/
  gZ : BaseField

/-- The complete public value of a Plan B garbling.

Every field is fixed-width: there are no `Option` tags, so every inhabitant encodes to exactly
`ciphertextBytesConstant` bytes. -/
structure Public where
  /-- The curve-membership check: three published constants. -/
  curve : BaseField × BaseField × BaseField
  /-- The three published row constants of each digit. -/
  rows : Vector RowGamma digitCount
  /-- The exception gadget, twelve bytes per digit. -/
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
def ciphertextBytesConstant : Nat := 1082820

end Kriterion.ArgoMAC.PlanB
