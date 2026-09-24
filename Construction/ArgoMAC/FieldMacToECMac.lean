/-
This file defines the observable `C_23` table operation: the 91 output MACs, their three
Jacobian rows and the doubling-exception gadget.

Plan B changes the delivery of the row elements and nothing else. `Table` is now the published
`RowGamma` vector and the gadget entries; the five per-adaptor window families are gone, and
`garble`/`evaluate` take the per-digit element families the projectivized garbling scheme
produces. The exception gadget is v2, unchanged: it hashes the 508 post-EncPRF selected Lamport
labels, one `daviesMeyer` call per label, XOR-folded, low byte taken. It does *not* hash
one-hot or switch labels -- those are a deterministic function of the Lamport labels, so
hashing them would add no unpredictability and would break the one-construction-query-per-index
invariant. Only the index the permutations come from is re-dimensioned, to
`FixedIndex.gadget digit coord position`, with no tweak.
The plan source is `2026-09-17-planB.md`, sections D.4 and Task 18.
-/

import Construction.ArgoMAC.Biquadratic
import Construction.ArgoMAC.Coordinates
import Construction.ArgoMAC.Exception
import Construction.ArgoMAC.Public
import Construction.ArgoMAC.RandomizedEncoding

namespace Kriterion.ArgoMAC.FieldMacToECMac

open BN254 Kriterion.ArgoMAC.PlanB

abbrev outputMacCount : Nat := 91

/-- The evaluator computes one homogeneous row before batch inversion. -/
structure HomogeneousValue where
  /-- The Jacobian `X` coordinate. -/
  x : BaseField
  /-- The Jacobian `Y` coordinate. -/
  y : BaseField
  /-- The Jacobian `Z` coordinate. -/
  z : BaseField
deriving DecidableEq

/-- `ExceptionPad` is the fresh pad the garbler draws for the exception gadget. -/
abbrev ExceptionPad := Vector Exception.Entry outputMacCount

/-- The published table: the eleven row constants of each digit, and the gadget entries. -/
abbrev Table := Vector RowGamma outputMacCount × Vector Exception.Entry outputMacCount

/-- One element family per digit: the garbler reads the element offsets through it, the
evaluator the delivered values. -/
abbrev DigitValues := Fin outputMacCount → Biquadratic.Values

structure RowRandomness where
  /-- The row randomizer `rho`. -/
  rho : NonZeroBase
  /-- The `X` row randomizers. -/
  x : Biquadratic.XRandomness
  /-- The `Y` row randomizers. -/
  y : Biquadratic.YRandomness
  /-- The `Z` row randomizer. -/
  z : Biquadratic.ZRandomness

abbrev Randomness := Vector RowRandomness outputMacCount
abbrev Rows := Vector Coordinates.Rows outputMacCount

/-- This is a non-identity affine output offset. -/
structure AffineOffset where
  coordinates : AffineInput
  onCurve : OnCurve coordinates

def AffineOffset.point [FieldCertificate] (offset : AffineOffset) : Point :=
  (decodePoint offset.coordinates).get (by
    have defined : decodePoint offset.coordinates ≠ none :=
      (decodePoint_defined offset.coordinates).mpr offset.onCurve
    cases decoded : decodePoint offset.coordinates with
    | none => exact (defined decoded).elim
    | some point => rfl)

def freeOffsetPoints [FieldCertificate] (free : Vector AffineOffset 90) : List Point :=
  free.toList.map fun offset => AffineOffset.point offset

def clampedFirst [FieldCertificate] [GroupCertificate]
    (free : Vector AffineOffset 90) : Point :=
  -(radix • pointHorner radix (freeOffsetPoints free))

/-- This contains the affine offsets from one successful garbling run. -/
structure SuccessfulOffsets where
  first : AffineOffset
  free : Vector AffineOffset 90

def SuccessfulOffsets.IsClamped [FieldCertificate] [GroupCertificate]
    (offsets : SuccessfulOffsets) : Prop :=
  AffineOffset.point offsets.first = clampedFirst offsets.free

def SuccessfulOffsets.values (offsets : SuccessfulOffsets) :
    Vector AffineOffset outputMacCount :=
  ⟨(offsets.first :: offsets.free.toList).toArray, by simp [outputMacCount]⟩

/-- This is one successful `EndoMacKey`. -/
structure OutputKey where
  digit : Digit
  offset : AffineOffset

abbrev OutputKeys := Vector OutputKey outputMacCount

def outputKeys (construction : Construction) (scalar : ScalarField)
    (offsets : SuccessfulOffsets) : OutputKeys :=
  let digits : Vector Digit outputMacCount :=
    ⟨(construction.digits scalar).toArray,
      by simpa [outputMacCount] using construction.digitCount scalar⟩
  let offsetValues := offsets.values
  Vector.ofFn fun index => {
    digit := digits.get index
    offset := offsetValues.get index
  }

def rowsForOutputKeys (keys : OutputKeys) (randomness : Randomness) : Rows :=
  Vector.ofFn fun index =>
    Coordinates.rows (keys.get index).offset.coordinates
      (digitEndomorphismBase (keys.get index).digit)
      (randomness.get index).rho.value

/-- The Jacobian rows only use the monomials their biquadratic table carries. -/
def SparseRow (rows : Coordinates.Rows) : Prop :=
  rows.x.xy = 0 ∧ rows.x.ySquared = 0 ∧ rows.y.x = 0 ∧ rows.z.y = 0 ∧
    rows.z.xy = 0 ∧ rows.z.xSquared = 0 ∧ rows.z.ySquared = 0

theorem coordinatesRowsSparse (offset : AffineInput)
    (endomorphismBase : Option BaseField) (randomizer : BaseField) :
    SparseRow (Coordinates.rows offset endomorphismBase randomizer) := by
  cases endomorphismBase <;> simp [SparseRow, Coordinates.rows, Coordinates.scale,
    Coordinates.xCoefficients, Coordinates.yCoefficients, Coordinates.zCoefficients]

theorem rowsForOutputKeysSparse (keys : OutputKeys) (randomness : Randomness) :
    ∀ index, SparseRow ((rowsForOutputKeys keys randomness).get index) := by
  intro index
  simp [rowsForOutputKeys, coordinatesRowsSparse]

/-- The eleven published constants of one digit's three rows. -/
def garbleRow (rows : Coordinates.Rows) (randomness : RowRandomness)
    (K : Biquadratic.Values) : RowGamma :=
  let x := Biquadratic.garbleX rows.x.constant rows.x.x rows.x.y rows.x.xSquared randomness.x K
  let y := Biquadratic.garbleY rows.y.constant rows.y.y rows.y.xy rows.y.xSquared
    rows.y.ySquared randomness.y K
  let z := Biquadratic.garbleZ rows.z.constant rows.z.x randomness.z K
  { xC0 := x.c0, xC1 := x.c1, xC2 := x.c2, xC4 := x.c4
    yC0 := y.c0, yC2 := y.c2, yC3 := y.c3, yC4 := y.c4, yC5 := y.c5
    zC0 := z.c0, zC1 := z.c1 }

/-- The `X` row constants of one digit's published gamma. -/
def xGammaOf (gamma : RowGamma) : Biquadratic.XGamma :=
  { c0 := gamma.xC0, c1 := gamma.xC1, c2 := gamma.xC2, c4 := gamma.xC4 }

/-- The `Y` row constants of one digit's published gamma. -/
def yGammaOf (gamma : RowGamma) : Biquadratic.YGamma :=
  { c0 := gamma.yC0, c2 := gamma.yC2, c3 := gamma.yC3, c4 := gamma.yC4, c5 := gamma.yC5 }

/-- The `Z` row constants of one digit's published gamma. -/
def zGammaOf (gamma : RowGamma) : Biquadratic.ZGamma :=
  { c0 := gamma.zC0, c1 := gamma.zC1 }

/-- One digit's homogeneous row value. -/
def evaluateGamma (gamma : RowGamma) (input : AffineInput) (values : Biquadratic.Values) :
    HomogeneousValue := {
  x := Biquadratic.evaluateX (xGammaOf gamma) input values
  y := Biquadratic.evaluateY (yGammaOf gamma) input values
  z := Biquadratic.evaluateZ (zGammaOf gamma) input values }

/-- The gadget mask reads one dedicated fixed-key permutation family per output digit.
Each output digit and coordinate gets `coordinateBitCount` permutations, one per label. -/
abbrev GadgetPermutations :=
  Fin outputMacCount → EncPRF.Coordinate → Fin coordinateBitCount →
    Equiv Cryptography.Block Cryptography.Block

/-- `gadgetDigest` compresses the selected labels of one coordinate MAC. -/
def gadgetDigest (perms : Fin coordinateBitCount → Equiv Cryptography.Block Cryptography.Block)
    (mac : CoordinateMac) : Cryptography.Block :=
  Fin.foldl coordinateBitCount
    (fun acc index => acc ^^^ Cryptography.daviesMeyer (perms index) (mac.get index)) 0

/-- `gadgetMask` is the one-time pad byte of one exception gadget slot.
It is a digest of the evaluator's own labels, so it is not affine in the input. -/
def gadgetMask (perms : GadgetPermutations) (output : Fin outputMacCount)
    (mac : InputMac) : BitVec 8 :=
  Exception.lowByte (gadgetDigest (perms output .x) mac.x ^^^ gadgetDigest (perms output .y) mac.y)

/-- `garbleEntry` writes the digit of one output key into its exceptional gadget slot. -/
def garbleEntry (perms : GadgetPermutations) (output : Fin outputMacCount) (key : OutputKey)
    (inputKey : InputMacKey) (pad : Exception.Entry) : Exception.Entry :=
  match digitEndomorphismBase key.digit with
  | none => pad
  | some phi =>
      let exceptional := Exception.exceptionalInput phi key.offset.coordinates
      Exception.writeEntry pad (Exception.exceptionIndex exceptional)
        (gadgetMask perms output (inputKey.encodeAffine exceptional) ^^^
          Exception.digitCode key.digit)

/-- `garble` publishes the eleven constants of each digit and the gadget entries.
`K` carries the element offsets the projectivized garbling scheme computed from the tape. -/
def garble (keys : OutputKeys) (rows : Rows) (randomness : Randomness) (K : DigitValues)
    (inputKey : InputMacKey) (perms : GadgetPermutations) (pad : ExceptionPad) : Table :=
  (Vector.ofFn fun index => garbleRow (rows.get index) (randomness.get index) (K index),
    Vector.ofFn fun index =>
      garbleEntry perms index (keys.get index) inputKey (pad.get index))

def evaluateHomogeneous (table : Table) (values : DigitValues)
    (input : AffineInput) : Vector HomogeneousValue outputMacCount :=
  Vector.ofFn fun index => evaluateGamma (table.1.get index) input (values index)

/-- The result keeps 91 homogeneous MAC values for checked decode. -/
structure Result where
  /-- The evaluator's cleartext input point. -/
  point : AffineInput
  /-- The 91 homogeneous row values. -/
  pointMacs : Vector HomogeneousValue outputMacCount
  /-- The 91 digits the exception gadget unlocks. -/
  exceptionDigits : Vector Digit outputMacCount

def evaluate (table : Table) (values : DigitValues) (perms : GadgetPermutations)
    (input : AffineInput) (inputMac : InputMac) : Result := {
  point := input
  pointMacs := evaluateHomogeneous table values input
  exceptionDigits := Vector.ofFn fun index =>
    Exception.unlock (gadgetMask perms index inputMac) (table.2.get index) input
}

def evaluateRow (rows : Coordinates.Rows) (input : AffineInput) : HomogeneousValue := {
  x := Coordinates.evaluate rows.x input
  y := Coordinates.evaluate rows.y input
  z := Coordinates.evaluate rows.z input
}

def evaluateRows (rows : Rows) (input : AffineInput) :
    Vector HomogeneousValue outputMacCount :=
  Vector.ofFn fun index => evaluateRow (rows.get index) input

theorem evaluateRowsNone (offset input : AffineInput) (randomizer : BaseField) :
    evaluateRow (Coordinates.rows offset none randomizer) input = {
      x := randomizer ^ 2 * offset.x
      y := randomizer ^ 3 * offset.y
      z := randomizer } := by
  cases offset with
  | mk offsetX offsetY =>
      simp [evaluateRow, Coordinates.rows, Coordinates.scale, Coordinates.evaluate]
      refine ⟨by ring, by ring⟩

def transformedInput (phi : BaseField) (input : AffineInput) : AffineInput := {
  x := phi ^ 4 * input.x
  y := phi ^ 3 * input.y
}

/-- A nonzero-digit row evaluates the coefficient tables at the transformed input. -/
theorem evaluateRowsSome (offset input : AffineInput) (phi randomizer : BaseField) :
    evaluateRow (Coordinates.rows offset (some phi) randomizer) input = {
      x := randomizer ^ 2 *
        Coordinates.evaluate (Coordinates.xCoefficients offset) (transformedInput phi input)
      y := randomizer ^ 3 *
        Coordinates.evaluate (Coordinates.yCoefficients offset) (transformedInput phi input)
      z := randomizer *
        Coordinates.evaluate (Coordinates.zCoefficients offset)
          (transformedInput phi input) } := by
  obtain ⟨xRow, yRow, zRow⟩ := Coordinates.evaluateRowsSome offset input phi randomizer
  simp only [evaluateRow]
  rw [xRow, yRow, zRow]
  rfl

def expectedResult (keys : OutputKeys) (rows : Rows) (randomness : Randomness)
    (K : DigitValues) (inputKey : InputMacKey) (perms : GadgetPermutations)
    (pad : ExceptionPad) (input : AffineInput) : Result := {
  point := input
  pointMacs := evaluateRows rows input
  exceptionDigits := Vector.ofFn fun index =>
    Exception.unlock (gadgetMask perms index (inputKey.encodeAffine input))
      ((garble keys rows randomness K inputKey perms pad).2.get index) input
}

/-- The delivered element family of one digit: `a_e * coord + K e` for every element slot. -/
def delivered (randomness : Randomness) (K : DigitValues) (input : AffineInput) : DigitValues :=
  fun index =>
    Biquadratic.delivered (randomness.get index).x (randomness.get index).y
      (randomness.get index).z (K index) input

/-- On the curve, the delivered values evaluate every digit's three rows to the rows' own
values (the `Y` row is exact only there: `Biquadratic.evaluateEncodedY`). -/
theorem evaluateHomogeneousEncoded (keys : OutputKeys) (rows : Rows)
    (randomness : Randomness) (K : DigitValues) (inputKey : InputMacKey)
    (perms : GadgetPermutations) (pad : ExceptionPad) (input : AffineInput)
    (onCurve : OnCurve input) :
    (∀ index, SparseRow (rows.get index)) →
    evaluateHomogeneous (garble keys rows randomness K inputKey perms pad)
        (delivered randomness K input) input =
      evaluateRows rows input := by
  intro sparse
  apply Vector.ext
  intro index inRange
  have rowSparse := sparse ⟨index, inRange⟩
  rcases rowSparse with ⟨xXY, xY2, yX, zY, zXY, zX2, zY2⟩
  simp only [evaluateHomogeneous, garble, garbleRow, evaluateGamma, xGammaOf,
    yGammaOf, zGammaOf, delivered, Vector.getElem_ofFn, Vector.get_ofFn]
  rw [Biquadratic.evaluateEncodedX, Biquadratic.evaluateEncodedY (onCurve := onCurve),
    Biquadratic.evaluateEncodedZ]
  simp [evaluateRows, evaluateRow, Coordinates.evaluate, xXY, xY2, yX, zY, zXY, zX2, zY2]
  ring_nf

/-- On the curve, the evaluator's result is the expected one. -/
theorem evaluateEncoded (keys : OutputKeys) (rows : Rows) (randomness : Randomness)
    (K : DigitValues) (inputKey : InputMacKey) (perms : GadgetPermutations)
    (pad : ExceptionPad) (input : AffineInput) (onCurve : OnCurve input) :
    (∀ index, SparseRow (rows.get index)) →
    evaluate (garble keys rows randomness K inputKey perms pad)
        (delivered randomness K input) perms input (inputKey.encodeAffine input) =
      expectedResult keys rows randomness K inputKey perms pad input := by
  intro sparse
  simp only [evaluate, expectedResult,
    evaluateHomogeneousEncoded keys rows randomness K inputKey perms pad input onCurve sparse]

/-- The gadget slot written for one output key unlocks that key's digit. -/
theorem unlockExceptional (keys : OutputKeys) (rows : Rows) (randomness : Randomness)
    (K : DigitValues) (inputKey : InputMacKey) (perms : GadgetPermutations)
    (pad : ExceptionPad) (index : Fin outputMacCount) (phi : BaseField)
    (selected : digitEndomorphismBase (keys.get index).digit = some phi) :
    (expectedResult keys rows randomness K inputKey perms pad
        (Exception.exceptionalInput phi (keys.get index).offset.coordinates)).exceptionDigits.get
      index = (keys.get index).digit := by
  simp only [expectedResult, garble, Vector.get_ofFn, garbleEntry, selected]
  exact Exception.unlock_writeEntry _ _ _ _

end Kriterion.ArgoMAC.FieldMacToECMac
