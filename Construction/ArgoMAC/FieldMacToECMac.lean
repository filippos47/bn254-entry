/-
This file defines the observable `C_23` table operation: the 91 output MACs, their three rows
(Jacobian `X` and `Z`, and the sign row in the `Y` slot) and the exception gadget.

Plan B changes the delivery of the row elements and nothing else. `Table` is now the published
`RowGamma` vector (three constants per digit) and the gadget entries; the five per-adaptor window families are gone, and
`garble`/`evaluate` take the per-digit element families the projectivized garbling scheme
produces. The exception gadget hashes the 508 post-EncPRF selected Lamport labels, one
`daviesMeyer` call per label, XOR-folded, low byte taken. It does *not* hash one-hot or switch
labels -- those are a deterministic function of the Lamport labels, so hashing them would add no
unpredictability and would break the one-construction-query-per-index invariant. The
permutations come from `FixedIndex.gadget digit coord position bit`: the bit is the label's, so
the garbler, which digests the labels of the digit's two exceptional inputs (`Q = K` and
`Q = 2K`), asks every index at one point only. Both exceptional slots of a digit are unlocked by
the same digest, so the evaluator asks 508 questions per digit, as before.
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
  /-- The sign row `S = τ² L² y_R`: its quadratic character is the character of `y_R`. -/
  y : BaseField
  /-- The Jacobian `Z` coordinate. -/
  z : BaseField
deriving DecidableEq

/-- `ExceptionPad` is the fresh pad the garbler draws for the exception gadget. -/
abbrev ExceptionPad := Vector Exception.Entry outputMacCount

/-- The published table: the three row constants of each digit, and the gadget entries. -/
abbrev Table := Vector RowGamma outputMacCount × Vector Exception.Entry outputMacCount

/-- One element family per digit: the garbler reads the element offsets through it, the
evaluator the delivered values. -/
abbrev DigitValues := Fin outputMacCount → Biquadratic.Values

/-- One digit's row randomness: the lift scales `rho` and `tau` alone. The slopes carry the true
row coefficients, so the rows need no randomisers of their own. -/
structure RowRandomness where
  /-- The row randomizer `rho` of the Jacobian `X` and `Z` rows. -/
  rho : NonZeroBase
  /-- The sign row randomizer `tau`, independent of `rho`: the sign row is `tau²` times its
  polynomial. -/
  tau : NonZeroBase

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
      (randomness.get index).rho.value (randomness.get index).tau.value

/-- The Jacobian rows only use the monomials their biquadratic table carries. -/
def SparseRow (rows : Coordinates.Rows) : Prop :=
  rows.x.xy = 0 ∧ rows.x.ySquared = 0 ∧ rows.y.x = 0 ∧ rows.y.xy = 0 ∧ rows.z.y = 0 ∧
    rows.z.xy = 0 ∧ rows.z.xSquared = 0 ∧ rows.z.ySquared = 0

theorem coordinatesRowsSparse (offset : AffineInput)
    (endomorphismBase : Option BaseField) (randomizer signRandomizer : BaseField) :
    SparseRow (Coordinates.rows offset endomorphismBase randomizer signRandomizer) := by
  cases endomorphismBase <;> simp [SparseRow, Coordinates.rows, Coordinates.scale,
    Coordinates.xCoefficients, Coordinates.signCoefficients, Coordinates.zCoefficients]

theorem rowsForOutputKeysSparse (keys : OutputKeys) (randomness : Randomness) :
    ∀ index, SparseRow ((rowsForOutputKeys keys randomness).get index) := by
  intro index
  simp [rowsForOutputKeys, coordinatesRowsSparse]

/-- The three published constants of one digit's three rows. -/
def garbleRow (rows : Coordinates.Rows) (K : Biquadratic.Values) : RowGamma :=
  Biquadratic.garble rows K

/-- One digit's homogeneous row value. -/
def evaluateGamma (gamma : RowGamma) (input : AffineInput) (values : Biquadratic.Values) :
    HomogeneousValue := {
  x := Biquadratic.evaluateX gamma input values
  y := Biquadratic.evaluateY gamma input values
  z := Biquadratic.evaluateZ gamma values }

/-- The gadget mask reads one dedicated fixed-key permutation family per output digit.
Each output digit and coordinate gets two permutations per label position, one per label bit. -/
abbrev GadgetPermutations :=
  Fin outputMacCount → EncPRF.Coordinate → Fin coordinateBitCount → Bool →
    Equiv Cryptography.Block Cryptography.Block

/-- `gadgetDigest` compresses the selected labels of one coordinate MAC, each label through the
permutation of its position and bit. -/
def gadgetDigest
    (perms : Fin coordinateBitCount → Bool → Equiv Cryptography.Block Cryptography.Block)
    (bits : CoordinateBits) (mac : CoordinateMac) : Cryptography.Block :=
  Fin.foldl coordinateBitCount
    (fun acc index =>
      acc ^^^ Cryptography.daviesMeyer (perms index (bits.getLsb index)) (mac.get index)) 0

/-- `gadgetMask` is the one-time pad byte of the exception gadget slots of one digit at one
input. It is a digest of the labels of that input, so it is not affine in the input. -/
def gadgetMask (perms : GadgetPermutations) (output : Fin outputMacCount)
    (input : AffineInput) (mac : InputMac) : BitVec 8 :=
  Exception.lowByte (gadgetDigest (perms output .x) (coordinateBits input.x) mac.x ^^^
    gadgetDigest (perms output .y) (coordinateBits input.y) mac.y)

/-- One exceptional slot of an entry: the digit, masked by the digest of the input's labels. -/
def writeCase (perms : GadgetPermutations) (output : Fin outputMacCount) (key : OutputKey)
    (inputKey : InputMacKey) (triple : Bool) (exceptional : AffineInput) (entry : Exception.Entry) :
    Exception.Entry :=
  Exception.writeEntry entry (Exception.slotOf triple exceptional)
    (gadgetMask perms output exceptional (inputKey.encodeAffine exceptional) ^^^
      Exception.digitCode key.digit)

/-- `garbleEntry` writes the digit of one output key into its two exceptional gadget slots: the
doubling input `Q = K` and the sign row's zero `Q = 2K`. -/
def garbleEntry (perms : GadgetPermutations) (output : Fin outputMacCount) (key : OutputKey)
    (inputKey : InputMacKey) (pad : Exception.Entry) : Exception.Entry :=
  match digitEndomorphismBase key.digit with
  | none => pad
  | some phi =>
      writeCase perms output key inputKey true
        (Exception.tripleInput phi key.offset.coordinates)
        (writeCase perms output key inputKey false
          (Exception.exceptionalInput phi key.offset.coordinates) pad)

/-- `garble` publishes the three constants of each digit and the gadget entries.
`K` carries the element offsets the projectivized garbling scheme computed from the tape. -/
def garble (keys : OutputKeys) (rows : Rows) (K : DigitValues)
    (inputKey : InputMacKey) (perms : GadgetPermutations) (pad : ExceptionPad) : Table :=
  (Vector.ofFn fun index => garbleRow (rows.get index) (K index),
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
  /-- The 91 digits the exception gadget unlocks at the doubling input. -/
  exceptionDigits : Vector Digit outputMacCount
  /-- The 91 digits the exception gadget unlocks at the sign row's zero. -/
  tripleDigits : Vector Digit outputMacCount

def evaluate (table : Table) (values : DigitValues) (perms : GadgetPermutations)
    (input : AffineInput) (inputMac : InputMac) : Result := {
  point := input
  pointMacs := evaluateHomogeneous table values input
  exceptionDigits := Vector.ofFn fun index =>
    Exception.unlock (gadgetMask perms index input inputMac) (table.2.get index) false input
  tripleDigits := Vector.ofFn fun index =>
    Exception.unlock (gadgetMask perms index input inputMac) (table.2.get index) true input
}

def evaluateRow (rows : Coordinates.Rows) (input : AffineInput) : HomogeneousValue := {
  x := Coordinates.evaluate rows.x input
  y := Coordinates.evaluate rows.y input
  z := Coordinates.evaluate rows.z input
}

def evaluateRows (rows : Rows) (input : AffineInput) :
    Vector HomogeneousValue outputMacCount :=
  Vector.ofFn fun index => evaluateRow (rows.get index) input

theorem evaluateRowsNone (offset input : AffineInput) (randomizer signRandomizer : BaseField) :
    evaluateRow (Coordinates.rows offset none randomizer signRandomizer) input = {
      x := randomizer ^ 2 * offset.x
      y := signRandomizer ^ 2 * offset.y
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
theorem evaluateRowsSome (offset input : AffineInput) (phi randomizer signRandomizer : BaseField) :
    evaluateRow (Coordinates.rows offset (some phi) randomizer signRandomizer) input = {
      x := randomizer ^ 2 *
        Coordinates.evaluate (Coordinates.xCoefficients offset) (transformedInput phi input)
      y := signRandomizer ^ 2 *
        Coordinates.evaluate (Coordinates.signCoefficients offset) (transformedInput phi input)
      z := randomizer *
        Coordinates.evaluate (Coordinates.zCoefficients offset)
          (transformedInput phi input) } := by
  obtain ⟨xRow, yRow, zRow⟩ :=
    Coordinates.evaluateRowsSome offset input phi randomizer signRandomizer
  simp only [evaluateRow]
  rw [xRow, yRow, zRow]
  rfl

def expectedResult (keys : OutputKeys) (rows : Rows)
    (K : DigitValues) (inputKey : InputMacKey) (perms : GadgetPermutations)
    (pad : ExceptionPad) (input : AffineInput) : Result := {
  point := input
  pointMacs := evaluateRows rows input
  exceptionDigits := Vector.ofFn fun index =>
    Exception.unlock (gadgetMask perms index input (inputKey.encodeAffine input))
      ((garble keys rows K inputKey perms pad).2.get index) false input
  tripleDigits := Vector.ofFn fun index =>
    Exception.unlock (gadgetMask perms index input (inputKey.encodeAffine input))
      ((garble keys rows K inputKey perms pad).2.get index) true input
}

/-- The delivered element family of one digit: `a_e * coord + K e` for every element slot. -/
def delivered (rows : Rows) (K : DigitValues) (input : AffineInput) : DigitValues :=
  fun index => Biquadratic.delivered (rows.get index) (K index) input

/-- On the curve, the delivered values evaluate every digit's three rows to the rows' own
values (the `Y` row is exact only there: `Biquadratic.evaluateEncodedY`). -/
theorem evaluateHomogeneousEncoded (keys : OutputKeys) (rows : Rows)
    (K : DigitValues) (inputKey : InputMacKey)
    (perms : GadgetPermutations) (pad : ExceptionPad) (input : AffineInput)
    (onCurve : OnCurve input) :
    (∀ index, SparseRow (rows.get index)) →
    evaluateHomogeneous (garble keys rows K inputKey perms pad)
        (delivered rows K input) input =
      evaluateRows rows input := by
  intro sparse
  apply Vector.ext
  intro index inRange
  have rowSparse := sparse ⟨index, inRange⟩
  rcases rowSparse with ⟨xXY, xY2, yX, yXY, zY, zXY, zX2, zY2⟩
  simp only [evaluateHomogeneous, garble, garbleRow, evaluateGamma, delivered,
    Vector.getElem_ofFn, Vector.get_ofFn]
  rw [Biquadratic.evaluateEncodedX, Biquadratic.evaluateEncodedY (onCurve := onCurve),
    Biquadratic.evaluateEncodedZ]
  simp [evaluateRows, evaluateRow, Coordinates.evaluate, xXY, xY2, yX, yXY, zY, zXY, zX2, zY2]

/-- On the curve, the evaluator's result is the expected one. -/
theorem evaluateEncoded (keys : OutputKeys) (rows : Rows)
    (K : DigitValues) (inputKey : InputMacKey) (perms : GadgetPermutations)
    (pad : ExceptionPad) (input : AffineInput) (onCurve : OnCurve input) :
    (∀ index, SparseRow (rows.get index)) →
    evaluate (garble keys rows K inputKey perms pad)
        (delivered rows K input) perms input (inputKey.encodeAffine input) =
      expectedResult keys rows K inputKey perms pad input := by
  intro sparse
  simp only [evaluate, expectedResult,
    evaluateHomogeneousEncoded keys rows K inputKey perms pad input onCurve sparse]

/-- The doubling slot written for one output key unlocks that key's digit. -/
theorem unlockExceptional (keys : OutputKeys) (rows : Rows)
    (K : DigitValues) (inputKey : InputMacKey) (perms : GadgetPermutations)
    (pad : ExceptionPad) (index : Fin outputMacCount) (phi : BaseField)
    (selected : digitEndomorphismBase (keys.get index).digit = some phi) :
    (expectedResult keys rows K inputKey perms pad
        (Exception.exceptionalInput phi (keys.get index).offset.coordinates)).exceptionDigits.get
      index = (keys.get index).digit := by
  simp only [expectedResult, garble, Vector.get_ofFn, garbleEntry, selected, writeCase]
  rw [Exception.unlock_writeEntry_ne _ _ _ _ _ _ (Exception.slotOf_ne _ _).symm]
  exact Exception.unlock_writeEntry _ _ _ _ _

/-- The sign row's zero slot written for one output key unlocks that key's digit. -/
theorem unlockTriple (keys : OutputKeys) (rows : Rows)
    (K : DigitValues) (inputKey : InputMacKey) (perms : GadgetPermutations)
    (pad : ExceptionPad) (index : Fin outputMacCount) (phi : BaseField)
    (selected : digitEndomorphismBase (keys.get index).digit = some phi) :
    (expectedResult keys rows K inputKey perms pad
        (Exception.tripleInput phi (keys.get index).offset.coordinates)).tripleDigits.get
      index = (keys.get index).digit := by
  simp only [expectedResult, garble, Vector.get_ofFn, garbleEntry, selected, writeCase]
  exact Exception.unlock_writeEntry _ _ _ _ _

end Kriterion.ArgoMAC.FieldMacToECMac
