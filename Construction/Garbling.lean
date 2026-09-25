/-
This file defines the ArgoMAC garbling scheme.
-/

import Construction.ArgoMAC
import GarbledCircuit

namespace Kriterion.ArgoMAC.Garbling

open BN254 Cryptography

/-- This structure contains every explicit garbling input.

The input labels are stored in free-XOR form: one zero label per bit and one global offset per
coordinate. That is what the chunked switch systems need (`Pipeline.CorrelatedKey`), and it
keeps the tape a plain product of finite types -- the correlation is a *definition*, not a
constraint on the tape. `inputMacKey` is derived below, so every downstream reader of
`randomness.inputMacKey` is unchanged. -/
structure Randomness where
  offsets : FieldMacToECMac.SuccessfulOffsets
  offsetsClamped : ∀ [FieldCertificate] [GroupCertificate], offsets.IsClamped
  pointRandomness : FieldMacToECMac.Randomness
  exceptionPad : FieldMacToECMac.ExceptionPad
  bridgeKey : BaseField
  curveMask : NonZeroBase
  curveR1 : BaseField
  curveR2 : BaseField
  fixedKeyOracle : PermutationOracle PlanB.FixedIndex Block
  inputZero : PlanB.Coord → Fin coordinateBitCount → Block
  inputDelta : PlanB.Coord → Block
  encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block
  hashOracle : EncPRF.HashOracle

/-- The 508 Lamport label pairs of one tape: `(Z_j, Z_j xor Delta)`. -/
def Randomness.inputMacKey (randomness : Randomness) : InputMacKey := {
  x := Vector.ofFn fun position =>
    { falseLabel := randomness.inputZero .x position
      trueLabel := randomness.inputZero .x position ^^^ randomness.inputDelta .x }
  y := Vector.ofFn fun position =>
    { falseLabel := randomness.inputZero .y position
      trueLabel := randomness.inputZero .y position ^^^ randomness.inputDelta .y } }

/-- The derived label pairs satisfy the free-XOR relation, by construction. -/
theorem Randomness.correlated (randomness : Randomness) :
    Pipeline.CorrelatedKey randomness.inputMacKey randomness.inputDelta := by
  intro coord position
  cases coord <;>
    · simp only [Pipeline.bitKeyOf, Randomness.inputMacKey, Vector.get_eq_getElem,
        Vector.getElem_ofFn]

structure EncodingKey where
  scalar : NonZeroScalar
  randomness : Randomness

structure Labels where
  input : BitInput
  inputMac : InputMac

abbrev PublicCircuit := PlanB.Public

abbrev EvaluationOracle := PublicOracle PlanB.FixedIndex EncPRF.PermutationIndex
abbrev OracleQuery := PublicQuery PlanB.FixedIndex EncPRF.PermutationIndex
abbrev OracleAnswer := @PublicQuery.Answer PlanB.FixedIndex EncPRF.PermutationIndex
abbrev oracleSpec := publicOracleSpec PlanB.FixedIndex EncPRF.PermutationIndex

/-- The handler exposes every oracle that evaluation reads. -/
def oracleHandler : OracleHandler oracleSpec Randomness :=
  publicHandler fun randomness =>
    (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)

structure Topology where
  coordinateBits : Nat
  outputDigits : Nat

def garble (construction : Construction) (scalar : NonZeroScalar)
    (randomness : Randomness) : PublicCircuit × EncodingKey :=
  (Pipeline.garble
      (FieldMacToECMac.outputKeys construction scalar.value randomness.offsets)
      randomness.pointRandomness randomness.exceptionPad randomness.bridgeKey
      randomness.curveMask randomness.curveR1 randomness.curveR2
      randomness.fixedKeyOracle randomness.encPRFOracle randomness.hashOracle
      randomness.inputDelta randomness.inputMacKey,
    { scalar, randomness })

def encode (key : EncodingKey) (input : BitInput) : Labels := {
  input
  inputMac := key.randomness.inputMacKey.encode input
}

/-- `fieldPower value exponent` is `value ^ exponent` by the challenge library's square-and-multiply
`modularPower`, for exponents below `2 ^ 254`. -/
def fieldPower (value : BaseField) (exponent : Nat) : BaseField :=
  (modularPower baseFieldModulus 254 value.val exponent 1 : Nat)

/-- The exponent of the quadratic character, `(p - 1) / 2`. -/
def characterExponent : Nat := (baseFieldModulus - 1) / 2

/-- The exponent of the square root of a square, `(p + 1) / 4`: `p ≡ 3 (mod 4)`. -/
def rootExponent : Nat := (baseFieldModulus + 1) / 4

/-- The group scalar `3 / 2`, as `3 * (r + 1) / 2`. -/
def threeHalves : ScalarField := 3 * ((scalarFieldModulus + 1) / 2 : Nat)

/-- A homogeneous row decodes through its `X` and `Z` rows and the sign row, or through the
gadget. `x = X / Z²`; `y` is the square root of `x³ + 3` whose character is the sign row's
(`S = τ² L² y`). The gadget covers the two inputs where this fails: `Z = 0 = X` (`Q = K`, the
result is `2 Q`) and `S = 0 ≠ Z` (`Q = 2K`, the result is `(3/2) Q`); `Z = 0 ≠ X` is `Q = -K`. -/
def decodeHomogeneous [FieldCertificate] [GroupCertificate]
    (value : FieldMacToECMac.HomogeneousValue) (exceptionDigit tripleDigit : Digit)
    (inputPoint : Point) : Option Point :=
  if value.z = 0 then
    if value.x = 0 then
      some ((2 : ScalarField) • digitEndomorphism exceptionDigit inputPoint)
    else some 0
  else if value.y = 0 then
    some (threeHalves • digitEndomorphism tripleDigit inputPoint)
  else
    let x := value.x / value.z ^ 2
    let y := fieldPower value.y characterExponent * fieldPower (x ^ 3 + 3) rootExponent
    decodePoint { x := x, y := y }

def decodePointMacs [FieldCertificate] [GroupCertificate]
    (values : Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount)
    (digits tripleDigits : Vector Digit FieldMacToECMac.outputMacCount) (inputPoint : Point) :
    Option (List Point) :=
  (List.zip values.toList (List.zip digits.toList tripleDigits.toList)).mapM fun pair =>
    decodeHomogeneous pair.1 pair.2.1 pair.2.2 inputPoint

def decodeResult [FieldCertificate] [GroupCertificate]
    (result : FieldMacToECMac.Result) : Option Point :=
  match decodePoint result.point with
  | none => none
  | some inputPoint =>
      (decodePointMacs result.pointMacs result.exceptionDigits result.tripleDigits
        inputPoint).map (pointHorner radix)

def evaluate [FieldCertificate] [GroupCertificate] (oracle : EvaluationOracle)
    (table : PublicCircuit) (labels : Labels) : Option Point :=
  (Pipeline.evaluate oracle.1 oracle.2.1 oracle.2.2
    table labels.input labels.inputMac).bind decodeResult

/-- Correct labels evaluate all table rows.

`delivers` is the chunked switch systems' delivery fact, `evalCoord_garbleCoord` of
`Proof/Correctness/PGS/AffineFp.lean`; `Construction` may not import `Proof`, so it travels as
a hypothesis and Task 20 discharges it. -/
theorem evaluateEncodeRows [FieldCertificate] (construction : Construction)
    (key : EncodingKey)
    (delivers : Pipeline.Delivers key.randomness.fixedKeyOracle key.randomness.hashOracle)
    (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    Pipeline.evaluate key.randomness.fixedKeyOracle key.randomness.encPRFOracle
        key.randomness.hashOracle (garble construction key.scalar key.randomness).1
        (BitInput.ofAffine input) (encode key (BitInput.ofAffine input)).inputMac =
      some (FieldMacToECMac.expectedResult
        (FieldMacToECMac.outputKeys construction key.scalar.value key.randomness.offsets)
        (FieldMacToECMac.rowsForOutputKeys
          (FieldMacToECMac.outputKeys construction key.scalar.value key.randomness.offsets)
          key.randomness.pointRandomness)
        key.randomness.pointRandomness
        (Pipeline.digitK key.randomness.fixedKeyOracle key.randomness.hashOracle
          key.randomness.inputDelta
          (Pipeline.whitenedKey key.randomness.encPRFOracle key.randomness.hashOracle
            key.randomness.bridgeKey key.randomness.inputMacKey))
        (EncPRF.transformKey key.randomness.encPRFOracle
          (EncPRF.whiteningKeys key.randomness.hashOracle key.randomness.bridgeKey)
          key.randomness.inputMacKey)
        (Pipeline.gadgetPermutations key.randomness.fixedKeyOracle)
        key.randomness.exceptionPad input) :=
  Pipeline.evaluateEncoded
    (FieldMacToECMac.outputKeys construction key.scalar.value key.randomness.offsets)
    key.randomness.pointRandomness key.randomness.exceptionPad
    key.randomness.bridgeKey key.randomness.curveMask
    key.randomness.curveR1 key.randomness.curveR2 key.randomness.fixedKeyOracle
    key.randomness.encPRFOracle key.randomness.hashOracle key.randomness.inputDelta
    key.randomness.inputMacKey key.randomness.correlated delivers input point decoded

def garbledCircuit [FieldCertificate] [GroupCertificate] (construction : Construction) :
    GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness PublicCircuit
      EncodingKey Labels EvaluationOracle := {
  function := fun scalar input => checkedScalarMultiplication scalar.value input
  garble := fun _ scalar randomness => garble construction scalar randomness
  encode := fun key input => encode key (BitInput.ofAffine input)
  evaluate := fun oracle table _ labels => some (evaluate oracle table labels)
}

def topology (_scalar : NonZeroScalar) : Topology := {
  coordinateBits := 508
  outputDigits := 91
}

end Kriterion.ArgoMAC.Garbling

namespace Kriterion.ArgoMAC.Lamport
open BN254 Cryptography

def keyPairs (key : InputMacKey) : GarbledCircuit.LamportSecretKey :=
  Vector.ofFn fun index =>
    if low : index.val < 254 then
      let item := key.x.get ⟨index.val, low⟩
      (item.falseLabel, item.trueLabel)
    else
      let item := key.y.get ⟨index.val - 254, by
        change index.val - 254 < 254
        omega⟩
      (item.falseLabel, item.trueLabel)

def selectedLabels (mac : InputMac) : GarbledCircuit.LamportSignature :=
  Vector.ofFn fun index =>
    if low : index.val < 254 then
      mac.x.get ⟨index.val, low⟩
    else
      mac.y.get ⟨index.val - 254, by
        change index.val - 254 < 254
        omega⟩

/-- The evaluator reconstructs its internal labels from its input and 508 blocks. -/
def restore (input : AffineInput) (labels : GarbledCircuit.LamportSignature) : Garbling.Labels := {
  input := BitInput.ofAffine input
  inputMac := {
    x := Vector.ofFn fun index => labels[index.val]'(by have : index.val < 254 := index.isLt; omega)
    y := Vector.ofFn fun index => labels[254 + index.val]'(by have : index.val < 254 := index.isLt; omega)
  }
}

/-- This adapter removes the repeated input from the transmitted labels. -/
def wireCircuit [FieldCertificate] [GroupCertificate] :=
  (Garbling.garbledCircuit construction).mapLabels (fun labels => selectedLabels labels.inputMac) restore

end Kriterion.ArgoMAC.Lamport
