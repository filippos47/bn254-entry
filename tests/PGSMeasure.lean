/-
Plan B measure dry run (Task 12). Not shipped: this file is outside the verifier's copy set.

The measurement is taken on the encoder itself, applied to a fully populated inhabitant of
`Public` whose 56 chunk words are produced by the real `pack`. `Kriterion.Benchmark
.ciphertextBytes` reads `Solution.ciphertextBytes`, whose obligation
`Solution.ciphertextSize` is exactly `Wire.encoding_length`.
-/

import Construction.PGS.Encoding

open Kriterion Kriterion.ArgoMAC Kriterion.ArgoMAC.PlanB

/-- Eleven distinct published constants. -/
def sampleGamma (digit : Nat) : RowGamma :=
  { xC0 := (digit + 1 : Nat), xC1 := (digit + 2 : Nat), xC2 := (digit + 3 : Nat),
    xC4 := (digit + 4 : Nat), yC0 := (digit + 5 : Nat), yC2 := (digit + 6 : Nat),
    yC3 := (digit + 7 : Nat), yC4 := (digit + 8 : Nat), yC5 := (digit + 9 : Nat),
    zC0 := (digit + 10 : Nat), zC1 := (digit + 11 : Nat) }

/-- Six gadget bytes. -/
def sampleEntry (digit : Nat) : Exception.Entry :=
  Vector.ofFn fun position : Fin 6 => BitVec.ofNat 8 (digit + position.val)

/-- One chunk's join word, packed by the real `pack` from 733 distinct field values. -/
def sampleWord (chunk : Nat) : BitVec chunkJoinBits :=
  pack fun element => ((element.val * 7 + chunk * 13 + 1 : Nat) : BN254.BaseField)

/-- A fully populated public value. -/
def samplePublic : Public :=
  { curve := ((11 : Nat), (22 : Nat), (33 : Nat))
    rows := Vector.ofFn fun digit : Fin digitCount => sampleGamma digit.val
    exception := Vector.ofFn fun digit : Fin digitCount => sampleEntry digit.val
    curveXHot := Vector.ofFn fun step : Fin foldStepCount =>
      BitVec.ofNat 128 (step.val * 1234567 + 1)
    curveYHot := Vector.ofFn fun step : Fin foldStepCount =>
      BitVec.ofNat 128 (step.val * 7654321 + 2)
    pointXHot := Vector.ofFn fun step : Fin foldStepCount =>
      BitVec.ofNat 128 (step.val * 2345671 + 3)
    pointYHot := Vector.ofFn fun step : Fin foldStepCount =>
      BitVec.ofNat 128 (step.val * 6543217 + 4)
    scale := Vector.ofFn fun chunk : Fin chunkCount => sampleWord chunk.val }

-- Prints `1348634`.
#eval (Wire.encoding.encode samplePublic).length
