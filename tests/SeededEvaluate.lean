/-
Seeded end-to-end run of the Plan B garbler and evaluator. Not shipped: the verifier copies only
`Construction*`, `Proof*` and `Submission`.

The pure definitions `Pipeline.garble` and `Pipeline.evaluate` are specifications: they recompute
a switch mask vector (up to `452` hash limbs and `455` base-`p` digits) for every element that
reads it, so running them directly is out of reach. This file runs memoised copies,
`garbleFast` and `evaluateFast`, that let-bind every table once, and proves each equal to the
specification (`garbleFast_eq`, `evaluateFast_eq`). The `#eval`s therefore run the construction
itself, on the benchmark tape `Seed.randomness`.

The two BN254 certificates are `Prop`-valued premises that the challenge library keeps as class
hypotheses (it does not prove that `p` is prime). Evaluation needs their instances but never
inspects them, so this file postulates them for its `#eval`s; nothing outside this test file
depends on them, and `#print axioms` of every shipped theorem is unaffected. These two file-local
`axiom` certificates (`fieldCertificate`, `groupCertificate`, below) are deliberate and test-only:
the verifier builds only `Construction`, `Proof` and `Submission`, and its computability lint is
scoped to `Construction/`.

Run with `lake env lean tests/SeededEvaluate.lean`.
-/

import Construction.Garbling
import Construction.ArgoMAC.Seed
import Construction.PGS.Encoding

set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.SeededTest

open BN254 Cryptography
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Pipeline (bitKeyOf whitenedKey)

/-! ### Base-`p` digits, once per vector -/

/-- The successive quotients `value / p ^ e` for `e < count`. -/
def quotients (value : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 => value :: quotients (value / baseFieldModulus) count

theorem quotients_length (value count : Nat) : (quotients value count).length = count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => simp [quotients, ih]

theorem quotients_getElem (value count e : Nat) (h : e < (quotients value count).length) :
    (quotients value count)[e] = value / baseFieldModulus ^ e := by
  induction count generalizing value e with
  | zero => simp [quotients] at h
  | succ count ih =>
    cases e with
    | zero => simp [quotients]
    | succ e =>
      simp only [quotients, List.getElem_cons_succ]
      rw [ih, Nat.div_div_eq_div_mul, pow_succ']

/-- `sampleLane`, with the limb number and its quotients computed once for the whole vector. -/
def sampleLaneVec (n k : Nat) (h : Fin k → Block × Block) : Vector BaseField n :=
  ⟨(List.map (fun q : Nat => (q : BaseField)) (quotients (limbsToNat k h) n)).toArray,
    by simp [quotients_length]⟩

theorem sampleLaneVec_get (n k : Nat) (h : Fin k → Block × Block) (e : Fin n) :
    (sampleLaneVec n k h).get e = sampleLane n k h e := by
  simp only [sampleLaneVec, Vector.get, List.getElem_toArray, List.getElem_map,
    quotients_getElem, sampleLane]
  rfl

/-! ### Garbler tables of one lane -/

/-- A switch of chunk `c`, inside the `2 ^ chunkBits`-wide switch radix. -/
def widen (c : Fin chunkCount) (j : Fin (2 ^ chunkWidth c)) : Fin (2 ^ chunkBits) :=
  ⟨j.val, Pipeline.switch_lt_twoPowChunkBits c j⟩

/-- The garbler's one-hot labels of every chunk, padded to `2 ^ chunkBits` entries. -/
def hotTable (oracle : PermutationOracle FixedIndex Block) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) :
    Vector (Vector Block (2 ^ chunkBits)) chunkCount :=
  Vector.ofFn fun c =>
    let hot := (garbleChunk oracle lane delta bitKey c).1
    Vector.ofFn fun j => if h : j.val < 2 ^ chunkWidth c then hot ⟨j.val, h⟩ else 0

theorem hotTable_get (oracle : PermutationOracle FixedIndex Block) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) (c : Fin chunkCount)
    (j : Fin (2 ^ chunkWidth c)) :
    ((hotTable oracle lane delta bitKey).get c).get (widen c j)
      = (garbleChunk oracle lane delta bitKey c).1 j := by
  simp [hotTable, widen, j.isLt]

/-- Every switch mask vector of one lane, padded with zero vectors outside a chunk's range. -/
def maskTable (hashOracle : EncPRF.HashOracle) (lane : Lane)
    (hot : Vector (Vector Block (2 ^ chunkBits)) chunkCount) :
    Vector (Vector (Vector BaseField (laneCount lane)) (2 ^ chunkBits)) chunkCount :=
  Vector.ofFn fun c => Vector.ofFn fun j =>
    if j.val < 2 ^ chunkWidth c then
      sampleLaneVec (laneCount lane) (limbCount lane) fun i =>
        hashOracle (scaleInput lane c j.val i ((hot.get c).get j))
    else Vector.replicate _ 0

theorem maskTable_get (hashOracle : EncPRF.HashOracle) (lane : Lane)
    (hot : Vector (Vector Block (2 ^ chunkBits)) chunkCount) (c : Fin chunkCount)
    (j : Fin (2 ^ chunkWidth c)) (e : Fin (laneCount lane)) :
    (((maskTable hashOracle lane hot).get c).get (widen c j)).get e
      = switchMask hashOracle lane c j.val ((hot.get c).get (widen c j)) e := by
  simp only [maskTable, Vector.get_ofFn]
  rw [if_pos (show (widen c j).val < 2 ^ chunkWidth c from j.isLt), sampleLaneVec_get]
  rfl

/-- The lane's element offsets `O[e]`, read from its mask table. -/
def offsetsVec (lane : Lane)
    (masks : Vector (Vector (Vector BaseField (laneCount lane)) (2 ^ chunkBits)) chunkCount) :
    Vector BaseField (laneCount lane) :=
  Vector.ofFn fun e => ∑ c : Fin chunkCount, ∑ j : Fin (2 ^ chunkWidth c),
    iota _ j * (((masks.get c).get (widen c j)).get e)

theorem offsetsVec_get (oracle : PermutationOracle FixedIndex Block)
    (hashOracle : EncPRF.HashOracle) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) (e : Fin (laneCount lane)) :
    (offsetsVec lane (maskTable hashOracle lane (hotTable oracle lane delta bitKey))).get e
      = offsets oracle hashOracle lane delta bitKey e := by
  simp only [offsetsVec, Vector.get_ofFn, offsets, outputMask, maskTable_get, hotTable_get]

/-- The lane's published `scale-hot` joins, read from its mask table. -/
def joinsVec (lane : Lane)
    (masks : Vector (Vector (Vector BaseField (laneCount lane)) (2 ^ chunkBits)) chunkCount)
    (slopes : Vector BaseField (laneCount lane)) :
    Vector (Vector BaseField (laneCount lane)) chunkCount :=
  Vector.ofFn fun c => Vector.ofFn fun e =>
    (∑ j : Fin (2 ^ chunkWidth c), ((masks.get c).get (widen c j)).get e)
      + slopes.get e * (2 : BaseField) ^ chunkOffset c

theorem joinsVec_get (oracle : PermutationOracle FixedIndex Block)
    (hashOracle : EncPRF.HashOracle) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block)
    (slopes : Fin (laneCount lane) → BaseField) (c : Fin chunkCount) (e : Fin (laneCount lane)) :
    ((joinsVec lane (maskTable hashOracle lane (hotTable oracle lane delta bitKey))
        (Vector.ofFn slopes)).get c).get e
      = scaleJoins oracle hashOracle lane delta bitKey slopes c e := by
  simp only [joinsVec, Vector.get_ofFn, scaleJoins, garbleScale, maskTotal, chunkScalar,
    maskTable_get, hotTable_get]

/-! ### The memoised garbler -/

/-- `Pipeline.garble`, with every lane's one-hot labels, masks, offsets, slopes and joins
computed once. -/
def garbleFast (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness)
    (exceptionPad : FieldMacToECMac.ExceptionPad)
    (bridgeKey : BaseField) (curveMask : NonZeroBase)
    (fixedKeyOracle : PermutationOracle FixedIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (delta : Coord → Block) (inputKey : InputMacKey) :
    Public :=
  let whitened := whitenedKey encPRFOracle hashOracle bridgeKey inputKey
  let maskCX := maskTable hashOracle .curveX
    (hotTable fixedKeyOracle .curveX (delta .x) (bitKeyOf inputKey .x))
  let maskCY := maskTable hashOracle .curveY
    (hotTable fixedKeyOracle .curveY (delta .y) (bitKeyOf inputKey .y))
  let maskPX := maskTable hashOracle .pointX
    (hotTable fixedKeyOracle .pointX (delta .x) (bitKeyOf whitened .x))
  let maskPY := maskTable hashOracle .pointY
    (hotTable fixedKeyOracle .pointY (delta .y) (bitKeyOf whitened .y))
  let offCX := offsetsVec .curveX maskCX
  let offCY := offsetsVec .curveY maskCY
  let offPX := offsetsVec .pointX maskPX
  let offPY := offsetsVec .pointY maskPY
  let curveK : CurveMembership.Values :=
    Pipeline.curveValues (fun e => offCX.get e) (fun e => offCY.get e)
  let digitK : FieldMacToECMac.DigitValues := fun digit =>
    Pipeline.digitValues (fun e => offPX.get e) (fun e => offPY.get e) digit
  let curveSlopes := CurveMembership.slopes curveMask.value curveK
  let pointSlopes : Fin digitCount → Biquadratic.Values := fun digit =>
    Biquadratic.slopes (pointRandomness.get digit).x (pointRandomness.get digit).y
      (pointRandomness.get digit).z (digitK digit)
  let joinCX := joinsVec .curveX maskCX (Vector.ofFn (Pipeline.curveXAssemble curveSlopes))
  let joinCY := joinsVec .curveY maskCY (Vector.ofFn (Pipeline.curveYAssemble curveSlopes))
  let joinPX := joinsVec .pointX maskPX (Vector.ofFn (Pipeline.pointXAssemble pointSlopes))
  let joinPY := joinsVec .pointY maskPY (Vector.ofFn (Pipeline.pointYAssemble pointSlopes))
  let table := FieldMacToECMac.garble outputKeys
    (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness) pointRandomness digitK
    (EncPRF.transformKey encPRFOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey)
    (Pipeline.gadgetPermutations fixedKeyOracle) exceptionPad
  { curve := CurveMembership.garble bridgeKey curveMask.value curveK
    rows := table.1
    exception := table.2
    curveXHot := hotJoins fixedKeyOracle .curveX (delta .x) (bitKeyOf inputKey .x)
    curveYHot := hotJoins fixedKeyOracle .curveY (delta .y) (bitKeyOf inputKey .y)
    pointXHot := hotJoins fixedKeyOracle .pointX (delta .x) (bitKeyOf whitened .x)
    pointYHot := hotJoins fixedKeyOracle .pointY (delta .y) (bitKeyOf whitened .y)
    scale := Vector.ofFn fun chunk => pack (Pipeline.assembleWord
      (fun e => (joinPX.get chunk).get e) (fun e => (joinCX.get chunk).get e)
      (fun e => (joinPY.get chunk).get e) (fun e => (joinCY.get chunk).get e)) }

/-- **The memoised garbler is the garbler.** -/
theorem garbleFast_eq (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness)
    (exceptionPad : FieldMacToECMac.ExceptionPad)
    (bridgeKey : BaseField) (curveMask : NonZeroBase)
    (fixedKeyOracle : PermutationOracle FixedIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (delta : Coord → Block) (inputKey : InputMacKey) :
    garbleFast outputKeys pointRandomness exceptionPad bridgeKey curveMask
        fixedKeyOracle encPRFOracle hashOracle delta inputKey
      = Pipeline.garble outputKeys pointRandomness exceptionPad bridgeKey curveMask fixedKeyOracle encPRFOracle hashOracle delta inputKey := by
  have curveK : Pipeline.curveValues
      (fun e => (offsetsVec .curveX (maskTable hashOracle .curveX
        (hotTable fixedKeyOracle .curveX (delta .x) (bitKeyOf inputKey .x)))).get e)
      (fun e => (offsetsVec .curveY (maskTable hashOracle .curveY
        (hotTable fixedKeyOracle .curveY (delta .y) (bitKeyOf inputKey .y)))).get e)
      = Pipeline.curveK fixedKeyOracle hashOracle delta inputKey := by
    simp only [offsetsVec_get]
    rfl
  have digitK : (fun digit : Fin FieldMacToECMac.outputMacCount => Pipeline.digitValues
      (fun e => (offsetsVec .pointX (maskTable hashOracle .pointX
        (hotTable fixedKeyOracle .pointX (delta .x)
          (bitKeyOf (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) .x)))).get e)
      (fun e => (offsetsVec .pointY (maskTable hashOracle .pointY
        (hotTable fixedKeyOracle .pointY (delta .y)
          (bitKeyOf (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) .y)))).get e) digit)
      = Pipeline.digitK fixedKeyOracle hashOracle delta
          (whitenedKey encPRFOracle hashOracle bridgeKey inputKey) := by
    simp only [offsetsVec_get]
    rfl
  have word : ∀ (a a' : Fin pointElementCountX → BaseField)
      (b b' : Fin curveElementCountX → BaseField) (c c' : Fin pointElementCountY → BaseField)
      (d d' : Fin curveElementCountY → BaseField), a = a' → b = b' → c = c' → d = d' →
      pack (Pipeline.assembleWord a b c d) = pack (Pipeline.assembleWord a' b' c' d') := by
    rintro _ _ _ _ _ _ _ _ rfl rfl rfl rfl
    rfl
  simp only [garbleFast, Pipeline.garble]
  rw [curveK, digitK]
  refine congrArg (Public.mk _ _ _ _ _ _ _) (congrArg Vector.ofFn (funext fun chunk => ?_))
  refine word _ _ _ _ _ _ _ _ (funext fun e => ?_) (funext fun e => ?_) (funext fun e => ?_)
    (funext fun e => ?_)
  · rw [joinsVec_get]
    simp only [offsetsVec_get]
    rfl
  · rw [joinsVec_get]
    simp only [Pipeline.curveXGarbled, garbleCoord, Pipeline.curveSlopes]
  · rw [joinsVec_get]
    simp only [offsetsVec_get]
    rfl
  · rw [joinsVec_get]
    simp only [Pipeline.curveYGarbled, garbleCoord, Pipeline.curveSlopes]

/-! ### The memoised evaluator -/

/-- The evaluator's one-hot labels of every chunk, padded to `2 ^ chunkBits` entries. -/
def heldTable (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (joins : Vector Block foldStepCount) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) : Vector (Vector Block (2 ^ chunkBits)) chunkCount :=
  Vector.ofFn fun c =>
    let hot := evalHot oracle lane c (chunkWidth c) (hotSlice joins c) (chunkLabels labels c)
      (chunkValue bits c)
    Vector.ofFn fun j => if h : j.val < 2 ^ chunkWidth c then hot ⟨j.val, h⟩ else 0

/-- The evaluator's mask vectors of the closed switches; the active switch's slot is zero. -/
def closedMasks (hashOracle : EncPRF.HashOracle) (lane : Lane) (bits : BitVec coordinateBitCount)
    (held : Vector (Vector Block (2 ^ chunkBits)) chunkCount) :
    Vector (Vector (Vector BaseField (laneCount lane)) (2 ^ chunkBits)) chunkCount :=
  Vector.ofFn fun c => Vector.ofFn fun j =>
    if j.val < 2 ^ chunkWidth c ∧ j.val ≠ (chunkOf bits c).val then
      sampleLaneVec (laneCount lane) (limbCount lane) fun i =>
        hashOracle (scaleInput lane c j.val i ((held.get c).get j))
    else Vector.replicate _ 0

theorem closedMasks_get (oracle : PermutationOracle FixedIndex Block)
    (hashOracle : EncPRF.HashOracle) (lane : Lane) (joins : Vector Block foldStepCount)
    (bits : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block)
    (c : Fin chunkCount) (j : Fin (2 ^ chunkWidth c)) (closed : j ≠ chunkOf bits c)
    (e : Fin (laneCount lane)) :
    (((closedMasks hashOracle lane bits (heldTable oracle lane joins bits labels)).get c).get
        (widen c j)).get e
      = switchMask hashOracle lane c j.val
          (evalHot oracle lane c (chunkWidth c) (hotSlice joins c) (chunkLabels labels c)
            (chunkValue bits c) j) e := by
  simp only [closedMasks, Vector.get_ofFn]
  rw [if_pos ⟨(show (widen c j).val < 2 ^ chunkWidth c from j.isLt),
    fun same => closed (Fin.ext same)⟩, sampleLaneVec_get]
  simp only [heldTable, Vector.get_ofFn, widen]
  rw [dif_pos j.isLt]
  rfl

/-- `evalCoord`, with the held one-hot labels and the closed switches' mask vectors computed
once. The active switch's vector is never computed: its label is recovered from the join. -/
def evalLaneVec (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (bits : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block) :
    Vector BaseField (laneCount lane) :=
  let masks := closedMasks hashOracle lane bits (heldTable oracle lane joins bits labels)
  Vector.ofFn fun e => ∑ c : Fin chunkCount, ∑ j : Fin (2 ^ chunkWidth c), iota _ j *
    (if j = chunkOf bits c then
        scale c e - ∑ other ∈ Finset.univ.erase (chunkOf bits c),
          ((masks.get c).get (widen c other)).get e
      else ((masks.get c).get (widen c j)).get e)

theorem evalLaneVec_get (oracle : PermutationOracle FixedIndex Block)
    (hashOracle : EncPRF.HashOracle) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (bits : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block)
    (e : Fin (laneCount lane)) :
    (evalLaneVec oracle hashOracle lane joins scale bits labels).get e
      = evalCoord oracle hashOracle lane joins scale bits labels e := by
  simp only [evalLaneVec, Vector.get_ofFn, evalCoord, evalScale]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases active : j = chunkOf bits c
  · rw [if_pos active, if_pos active,
      Finset.sum_congr rfl fun other member =>
        closedMasks_get oracle hashOracle lane joins bits labels c other
          (Finset.ne_of_mem_erase member) e]
  · rw [if_neg active, if_neg active,
      closedMasks_get oracle hashOracle lane joins bits labels c j active e]

/-- `Pipeline.evaluate`, with every lane's values computed once. -/
def evaluateFast [FieldCertificate] (fixedKeyOracle : PermutationOracle FixedIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (table : Public)
    (input : BitInput) (inputMac : InputMac) : Option FieldMacToECMac.Result :=
  let affineInput := input.toAffine
  match decodePoint affineInput with
  | none => none
  | some _ =>
      let cx := evalLaneVec fixedKeyOracle hashOracle .curveX table.curveXHot
        (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
        (Pipeline.coordBits input .x) (Pipeline.macLabels inputMac .x)
      let cy := evalLaneVec fixedKeyOracle hashOracle .curveY table.curveYHot
        (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
        (Pipeline.coordBits input .y) (Pipeline.macLabels inputMac .y)
      let bridgeKey := CurveMembership.evaluate table.curve affineInput
        (Pipeline.curveValues (fun e => cx.get e) (fun e => cy.get e))
      let keys := EncPRF.whiteningKeys hashOracle bridgeKey
      let whitenedMac := EncPRF.whitenMac encPRFOracle keys inputMac
      let pointInputMac := EncPRF.transformMac encPRFOracle keys input inputMac
      let px := evalLaneVec fixedKeyOracle hashOracle .pointX table.pointXHot
        (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
        (Pipeline.coordBits input .x) (Pipeline.macLabels whitenedMac .x)
      let py := evalLaneVec fixedKeyOracle hashOracle .pointY table.pointYHot
        (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
        (Pipeline.coordBits input .y) (Pipeline.macLabels whitenedMac .y)
      some (FieldMacToECMac.evaluate (Pipeline.pointTable table)
        (Pipeline.digitValues (fun e => px.get e) (fun e => py.get e))
        (Pipeline.gadgetPermutations fixedKeyOracle) affineInput pointInputMac)

/-- **The memoised evaluator is the evaluator.** -/
theorem evaluateFast_eq [FieldCertificate] (fixedKeyOracle : PermutationOracle FixedIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (table : Public)
    (input : BitInput) (inputMac : InputMac) :
    evaluateFast fixedKeyOracle encPRFOracle hashOracle table input inputMac
      = Pipeline.evaluate fixedKeyOracle encPRFOracle hashOracle table input inputMac := by
  simp only [evaluateFast, Pipeline.evaluate, evalLaneVec_get, Pipeline.curveXValues,
    Pipeline.curveYValues, Pipeline.pointXValues, Pipeline.pointYValues]
  rfl

/-! ### The seeded run -/

/-- The garbled table of the seeded tape, by the memoised garbler. -/
def seededTable (seed : BitVec 256) (scalar : NonZeroScalar) : Public :=
  let tape := Seed.randomness seed
  garbleFast (FieldMacToECMac.outputKeys construction scalar.value tape.offsets)
    tape.pointRandomness tape.exceptionPad tape.bridgeKey tape.curveMask
    tape.fixedKeyOracle tape.encPRFOracle tape.hashOracle tape.inputDelta tape.inputMacKey

/-- `seededTable` is the garbler's table on the seeded tape. -/
theorem seededTable_eq (seed : BitVec 256) (scalar : NonZeroScalar) :
    seededTable seed scalar = (Garbling.garble construction scalar (Seed.randomness seed)).1 := by
  simp only [seededTable, garbleFast_eq]
  rfl

/-- The circuit's answer on one input, by the memoised evaluator on a given table. -/
def seededEvaluate [FieldCertificate] [GroupCertificate] (seed : BitVec 256)
    (scalar : NonZeroScalar) (table : Public) (input : AffineInput) : Option (Option Point) :=
  let tape := Seed.randomness seed
  let labels := Garbling.encode ⟨scalar, tape⟩ (BitInput.ofAffine input)
  some ((evaluateFast tape.fixedKeyOracle tape.encPRFOracle tape.hashOracle table labels.input
    labels.inputMac).bind Garbling.decodeResult)

/-- **The seeded run is the circuit.** On the seeded table, `seededEvaluate` is
`(garbledCircuit construction).evaluate` of the garbler's own table and labels. -/
theorem seededEvaluate_eq [FieldCertificate] [GroupCertificate] (seed : BitVec 256)
    (scalar : NonZeroScalar) (input : AffineInput) :
    seededEvaluate seed scalar (seededTable seed scalar) input
      = (Garbling.garbledCircuit construction).evaluate
          ((Seed.randomness seed).fixedKeyOracle, (Seed.randomness seed).encPRFOracle,
            (Seed.randomness seed).hashOracle)
          ((Garbling.garbledCircuit construction).garble 0 scalar (Seed.randomness seed)).1 input
          ((Garbling.garbledCircuit construction).encode
            ((Garbling.garbledCircuit construction).garble 0 scalar (Seed.randomness seed)).2
            input) := by
  simp only [seededEvaluate, seededTable_eq, evaluateFast_eq]
  rfl

/-! ### The `#eval`s

The certificates are postulated here, for evaluation only; see the header. -/

/-- The library's retained primality premise (evaluation only). -/
axiom fieldCertificate : FieldCertificate

/-- The library's retained group-law premise (evaluation only). -/
axiom groupCertificate : @GroupCertificate fieldCertificate

attribute [local instance] fieldCertificate groupCertificate

/-- The affine coordinates of a result, `none` for the point at infinity. -/
def coordinates : Option (Option Point) → Option (Option (Option (BaseField × BaseField)))
  | none => none
  | some none => some none
  | some (some .zero) => some (some none)
  | some (some (.some (x := x) (y := y) _)) => some (some (some (x, y)))

/-- The expected answer: `some (some (k • P))` on the curve, by the certificate-free
double-and-add `Seed.smulFuel` (`Seed.smulFuel_represents`), and `some none` off it. -/
def expected (scalar : NonZeroScalar) (input : AffineInput) :
    Option (Option (Option (BaseField × BaseField))) :=
  if validate input then some (some (Seed.smulFuel (some (input.x, input.y)) 254 scalar.value.val))
  else some none

/-- A short rendering of a result. -/
def render : Option (Option (Option (BaseField × BaseField))) → String
  | none => "none"
  | some none => "some none"
  | some (some none) => "some (some 0)"
  | some (some (some (x, y))) => s!"some (some (x = {x.val}, y = {y.val}))"

/-- The benchmark seed. -/
def seed : BitVec 256 := 0x5eed

/-- The scalar `k`. -/
def scalar : NonZeroScalar :=
  ⟨0x1d4a3c7e9b25f6081e3a7c5d2b9f4e6a8c0d1f3b5a7e9c2d4f6b8a0c1e3d5f7, by decide⟩

/-- The generator `(1, 2)`. -/
def generatorInput : AffineInput := ⟨1, 2⟩

/-- A second point on the curve, `5 • (1, 2)`. -/
def secondInput : AffineInput :=
  match Seed.smulFuel (some (1, 2)) 254 5 with
  | some (x, y) => ⟨x, y⟩
  | none => ⟨1, 2⟩

/-- A point off the curve: `3 ^ 2 ≠ 1 ^ 3 + 3`. -/
def offCurveInput : AffineInput := ⟨1, 3⟩

/-- The benchmark hash separates the limbs: three scale inputs at one label that differ only in
their tag (limb `0` vs limb `451` of a `pointX` switch, and a `curveX` limb) get three distinct
answers, so a limb-order or limb-index mismatch between garbler and evaluator would show. -/
def limbsDistinct : Bool :=
  let hash := (Seed.randomness seed).hashOracle
  let label : Block := 0x0123456789abcdef0fedcba987654321
  let first := hash (scaleInput .pointX ⟨0, by decide⟩ 1 0 label)
  let last := hash (scaleInput .pointX ⟨0, by decide⟩ 1 451 label)
  let other := hash (scaleInput .curveX ⟨5, by decide⟩ 3 2 label)
  first != last && first != other && last != other

#eval limbsDistinct

/-- Garble once on the seeded tape, then evaluate the three inputs. -/
def run : IO Unit := do
  let t0 ← IO.monoMsNow
  let table := seededTable seed scalar
  IO.println s!"garbled: {(PlanB.Wire.encoding.encode table).length} bytes"
  let t1 ← IO.monoMsNow
  IO.println s!"  [garble: {t1 - t0} ms]"
  for (label, input) in [("generator", generatorInput), ("5 * generator", secondInput),
      ("off curve", offCurveInput)] do
    let t2 ← IO.monoMsNow
    let got := coordinates (seededEvaluate seed scalar table input)
    IO.println s!"{label}: on curve = {validate input}; result = {render got}"
    let shape := if validate input then "some (some (k • P))" else "some none"
    IO.println s!"  equals the expected {shape}: {decide (got = expected scalar input)}"
    let t3 ← IO.monoMsNow
    IO.println s!"  [evaluate: {t3 - t2} ms]"

#eval run

end Kriterion.ArgoMAC.SeededTest
