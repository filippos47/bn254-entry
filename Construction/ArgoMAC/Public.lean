/-
This file defines the Plan B public value: everything the garbler publishes.

The plan source is `2026-09-17-planB.md`, section D.5. Every field has a
fixed width and there are no `Option` tags anywhere, so *every* inhabitant of `Public` encodes
to exactly `ciphertextBytesConstant` bytes; the byte-count theorem therefore does not mention
`garble` at all.

| Field       | Encoding                                 | Bytes   |
|-------------|------------------------------------------|---------|
| `curve`     | `3 * Wire.field`                          | 96      |
| `rows`      | `Vector RowGamma 91`, 11 field elements   | 32,032  |
| `exception` | `Vector (Vector (BitVec 8) 6) 91`         | 546     |
| `curveXHot` | `Vector Block 198`                        | 3,168   |
| `curveYHot` | `Vector Block 198`                        | 3,168   |
| `pointXHot` | `Vector Block 198`                        | 3,168   |
| `pointYHot` | `Vector Block 198`                        | 3,168   |
| `scale`     | `Vector (BitVec 186184) 56`               | 1,303,288 |
| **total**   |                                           | **1,348,634** |
-/

import Construction.ArgoMAC.Exception
import Construction.PGS.Packing

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-- The eleven published constants of one digit's three Jacobian rows.

The `Y` row publishes five coefficients, not six (`c1` is always absent in the baseline's
`Biquadratic.garbleY`), so a digit publishes `4 + 5 + 2 = 11` field elements. -/
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
  /-- `Y` row constant `c3`. -/
  yC3 : BaseField
  /-- `Y` row constant `c4`. -/
  yC4 : BaseField
  /-- `Y` row constant `c5`. -/
  yC5 : BaseField
  /-- `Z` row constant `c0`. -/
  zC0 : BaseField
  /-- `Z` row constant `c1`. -/
  zC1 : BaseField

/-- The complete public value of a Plan B garbling.

Every field is fixed-width: there are no `Option` tags, so every inhabitant encodes to exactly
`ciphertextBytesConstant` bytes. -/
structure Public where
  /-- The curve-membership check: three published constants. -/
  curve : BaseField × BaseField × BaseField
  /-- The eleven published row constants of each digit. -/
  rows : Vector RowGamma digitCount
  /-- The doubling-exception gadget, six bytes per digit. -/
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
def ciphertextBytesConstant : Nat := 1348634

end Kriterion.ArgoMAC.PlanB
