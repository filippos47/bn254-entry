/-
This file derives one reproducible garbling tape from a 256-bit seed.
`Scheme.witness` takes its coins from this tape, and the unshipped `tests/SeededEvaluate.lean`
runs the garbler and the evaluator on it. The security game samples the complete tape
uniformly instead.
The entry cannot use the Mathlib group law here. That law needs the BN254 field
certificate, and the entry does not hold it. This file computes the clamped offset with
plain `ZMod` ring operations and proves the result equal to the Mathlib group law.
-/

import Construction.Garbling
import Mathlib.FieldTheory.Finite.Basic

set_option maxRecDepth 10000

namespace Kriterion.ArgoMAC.Seed

open BN254 Cryptography

/-! ## Field arithmetic without the certificate -/

/-- Binary exponentiation with explicit fuel. -/
def powFuel (base : BaseField) : Nat → Nat → BaseField
  | 0, _ => 1
  | fuel + 1, exponent =>
      if exponent = 0 then 1 else
      let half := powFuel base fuel (exponent / 2)
      if exponent % 2 = 1 then half * half * base else half * half

theorem powFuel_eq (base : BaseField) (fuel exponent : Nat) (bound : exponent < 2 ^ fuel) :
    powFuel base fuel exponent = base ^ exponent := by
  induction fuel generalizing exponent with
  | zero =>
      have zero : exponent = 0 := by simpa using bound
      subst zero
      simp [powFuel]
  | succ fuel inductionHypothesis =>
      have halfBound : exponent / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at bound
        omega
      simp only [powFuel]
      split_ifs with zero odd
      · subst zero
        simp
      · rw [inductionHypothesis (exponent / 2) halfBound, ← pow_add, ← pow_succ]
        congr 1
        omega
      · rw [inductionHypothesis (exponent / 2) halfBound, ← pow_add]
        congr 1
        omega

/-- The Fermat inverse. It equals the field inverse under the certificate. -/
def inv (value : BaseField) : BaseField :=
  powFuel value 254 (baseFieldModulus - 2)

theorem inv_eq [FieldCertificate] (value : BaseField) : inv value = value⁻¹ := by
  rw [inv, powFuel_eq _ _ _ (by decide)]
  by_cases zero : value = 0
  · subst zero
    rw [zero_pow (by decide), inv_zero]
  · apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show baseFieldModulus - 2 + 1 = baseFieldModulus - 1 by decide]
    exact ZMod.pow_card_sub_one_eq_one zero

/-! ## The affine group law without the certificate -/

/-- One affine point, or `none` for the point at infinity. -/
abbrev Coordinates := Option (BaseField × BaseField)

/-- This is `WeierstrassCurve.Affine.slope` for `y² = x³ + 3` with the Fermat inverse. -/
def slope (x₁ x₂ y₁ y₂ : BaseField) : BaseField :=
  if x₁ = x₂ then
    if y₁ = -y₂ then 0 else (3 * (x₁ * x₁)) * inv (y₁ - -y₁)
  else (y₁ - y₂) * inv (x₁ - x₂)

def add : Coordinates → Coordinates → Coordinates
  | none, second => second
  | first, none => first
  | some (x₁, y₁), some (x₂, y₂) =>
      if x₁ = x₂ ∧ y₁ = -y₂ then none else
      let line := slope x₁ x₂ y₁ y₂
      let x₃ := line * line - x₁ - x₂
      some (x₃, -(line * (x₃ - x₁) + y₁))

/-- Double-and-add with explicit fuel. -/
def smulFuel (point : Coordinates) : Nat → Nat → Coordinates
  | 0, _ => none
  | fuel + 1, scalar =>
      if scalar = 0 then none else
      let half := smulFuel point fuel (scalar / 2)
      let double := add half half
      if scalar % 2 = 1 then add double point else double

/-- `Represents coordinates point` says the coordinates name the Mathlib point. -/
def Represents [FieldCertificate] : Coordinates → Point → Prop
  | none, .zero => True
  | some (x, y), .some (x := x') (y := y') _ => x = x' ∧ y = y'
  | _, _ => False

theorem represents_ne_zero [FieldCertificate] {x y : BaseField} {point : Point}
    (represents : Represents (some (x, y)) point) : point ≠ 0 := by
  rcases point with _ | @⟨x', y', valid⟩
  · exact represents.elim
  · exact fun equal => by cases equal

theorem represents_unique [FieldCertificate] {coordinates : Coordinates} {first second : Point}
    (left : Represents coordinates first) (right : Represents coordinates second) :
    first = second := by
  rcases coordinates with _ | ⟨x, y⟩
  · rcases first with _ | _
    · rcases second with _ | _
      · rfl
      · exact right.elim
    · exact left.elim
  · rcases first with _ | @⟨x₁, y₁, valid₁⟩
    · exact left.elim
    · rcases second with _ | @⟨x₂, y₂, valid₂⟩
      · exact right.elim
      · obtain ⟨rfl, rfl⟩ := left
        obtain ⟨rfl, rfl⟩ := right
        rfl

theorem slope_eq [FieldCertificate] (x₁ x₂ y₁ y₂ : BaseField) :
    slope x₁ x₂ y₁ y₂ = curve.toAffine.slope x₁ x₂ y₁ y₂ := by
  simp only [slope, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY, curve,
    inv_eq, div_eq_mul_inv, zero_mul, mul_zero, sub_zero, add_zero, pow_two]

theorem add_represents [FieldCertificate] {first second : Coordinates} {left right : Point}
    (leftRepresents : Represents first left) (rightRepresents : Represents second right) :
    Represents (add first second) (left + right) := by
  rcases first with _ | ⟨x₁, y₁⟩
  · rcases left with _ | _
    · have reduce : add none second = second := by cases second <;> rfl
      rw [reduce]
      show Represents second (0 + right)
      rw [zero_add]
      exact rightRepresents
    · exact leftRepresents.elim
  · rcases left with _ | @⟨x₁', y₁', valid₁⟩
    · exact leftRepresents.elim
    obtain ⟨rfl, rfl⟩ := leftRepresents
    rcases second with _ | ⟨x₂, y₂⟩
    · rcases right with _ | _
      · show Represents (some (x₁, y₁)) (WeierstrassCurve.Affine.Point.some _ _ valid₁ + 0)
        rw [add_zero]
        exact ⟨rfl, rfl⟩
      · exact rightRepresents.elim
    · rcases right with _ | @⟨x₂', y₂', valid₂⟩
      · exact rightRepresents.elim
      obtain ⟨rfl, rfl⟩ := rightRepresents
      have negY : curve.toAffine.negY x₂ y₂ = -y₂ := by
        simp [WeierstrassCurve.Affine.negY, curve]
      by_cases opposite : x₁ = x₂ ∧ y₁ = -y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq opposite.1 (by rw [negY]; exact opposite.2)]
        simp only [add, opposite, and_self, if_true]
        exact trivial
      · have opposite' : ¬(x₁ = x₂ ∧ y₁ = curve.toAffine.negY x₂ y₂) := by rwa [negY]
        rw [WeierstrassCurve.Affine.Point.add_some opposite']
        simp only [add, opposite, if_false, Represents]
        simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
          WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, curve, slope_eq, pow_two]

theorem smulFuel_represents [FieldCertificate] {coordinates : Coordinates} {point : Point}
    (represents : Represents coordinates point) (fuel scalar : Nat)
    (bound : scalar < 2 ^ fuel) :
    Represents (smulFuel coordinates fuel scalar) (scalar • point) := by
  induction fuel generalizing scalar with
  | zero =>
      have zero : scalar = 0 := by simpa using bound
      subst zero
      simp [smulFuel, Represents]
  | succ fuel inductionHypothesis =>
      have halfBound : scalar / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at bound
        omega
      have half := inductionHypothesis (scalar / 2) halfBound
      have double := add_represents half half
      simp only [smulFuel]
      split_ifs with zero odd
      · subst zero
        simp [Represents]
      · have split : scalar • point = (scalar / 2) • point + (scalar / 2) • point + point := by
          conv_lhs => rw [show scalar = scalar / 2 + scalar / 2 + 1 by omega]
          rw [add_nsmul, add_nsmul, one_nsmul]
        rw [split]
        exact add_represents double represents
      · have split : scalar • point = (scalar / 2) • point + (scalar / 2) • point := by
          conv_lhs => rw [show scalar = scalar / 2 + scalar / 2 by omega]
          rw [add_nsmul]
        rw [split]
        exact double

/-! ## Scalar facts -/

theorem zmod_smul_eq [FieldCertificate] [GroupCertificate] (scalar : ScalarField) (point : Point) :
    scalar • point = scalar.val • point := rfl

theorem smul_ne_zero_of_coprime [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (point : Point) (nonzero : point ≠ 0)
    (coprime : Nat.gcd scalar.val scalarFieldModulus = 1) : scalar • point ≠ 0 := by
  intro zero
  have order : scalarFieldModulus • point = 0 := GroupCertificate.groupOrder point
  have valSmul : scalar.val • point = 0 := zero
  have bezout := Nat.gcd_eq_gcd_ab scalar.val scalarFieldModulus
  rw [coprime, Nat.cast_one] at bezout
  apply nonzero
  calc point = (1 : ℤ) • point := (one_zsmul point).symm
    _ = (scalar.val * Nat.gcdA scalar.val scalarFieldModulus +
          scalarFieldModulus * Nat.gcdB scalar.val scalarFieldModulus : ℤ) • point := by
        rw [bezout]
    _ = 0 := by
        rw [add_zsmul, mul_comm (scalar.val : ℤ), mul_comm (scalarFieldModulus : ℤ), mul_zsmul,
          mul_zsmul, natCast_zsmul, natCast_zsmul, valSmul, order, zsmul_zero, zsmul_zero, add_zero]

/-! ## The clamped offsets -/

def generatorOffset : FieldMacToECMac.AffineOffset := ⟨{ x := 1, y := 2 }, generatorOnCurve⟩

/-- Every free offset is the generator. -/
def freeOffsets : Vector FieldMacToECMac.AffineOffset 90 := Vector.replicate 90 generatorOffset

def geometric : Nat → ScalarField
  | 0 => 0
  | count + 1 => 1 + radix * geometric count

/-- The clamped first offset is this multiple of the generator. -/
@[irreducible] def clampScalar : ScalarField := -(radix * geometric 90)

def generatorCoordinates : Coordinates := some (1, 2)

@[irreducible] def clampedCoordinates : Coordinates :=
  smulFuel generatorCoordinates 254 clampScalar.val

def offsetOf : Coordinates → FieldMacToECMac.AffineOffset
  | some (x, y) =>
      if valid : validate { x, y } = true then ⟨{ x, y }, (validate_eq_true_iff _).mp valid⟩
      else generatorOffset
  | none => generatorOffset

def offsets : FieldMacToECMac.SuccessfulOffsets :=
  { first := offsetOf clampedCoordinates, free := freeOffsets }

theorem clampScalar_coprime : Nat.gcd clampScalar.val scalarFieldModulus = 1 := by
  decide +kernel

theorem clampScalar_val_lt : clampScalar.val < 2 ^ 254 :=
  lt_trans (ZMod.val_lt _) (by decide)

theorem offset_represents [FieldCertificate] (offset : FieldMacToECMac.AffineOffset) :
    Represents (some (offset.coordinates.x, offset.coordinates.y)) offset.point := by
  have valid : validate offset.coordinates = true := (validate_eq_true_iff _).mpr offset.onCurve
  have decoded : decodePoint offset.coordinates = some (WeierstrassCurve.Affine.Point.some offset.coordinates.x offset.coordinates.y
      ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mp
        ((equation_iff_onCurve _).mpr offset.onCurve))) := by
    simp [decodePoint, valid]
  unfold FieldMacToECMac.AffineOffset.point
  rw [Option.get_of_mem _ (Option.mem_def.mpr decoded)]
  exact ⟨rfl, rfl⟩

theorem pointHorner_replicate [FieldCertificate] [GroupCertificate] (point : Point) (count : Nat) :
    pointHorner radix (List.replicate count point) = geometric count • point := by
  induction count with
  | zero =>
      simp only [List.replicate_zero, pointHorner, geometric]
      exact (zero_smul ScalarField point).symm
  | succ count inductionHypothesis =>
      simp only [List.replicate_succ, pointHorner, geometric, inductionHypothesis, add_smul,
        one_smul, mul_smul]

theorem freeOffsetPoints_freeOffsets [FieldCertificate] :
    FieldMacToECMac.freeOffsetPoints freeOffsets = List.replicate 90 generatorOffset.point := by
  simp [FieldMacToECMac.freeOffsetPoints, freeOffsets]

theorem clampedFirst_freeOffsets [FieldCertificate] [GroupCertificate] :
    FieldMacToECMac.clampedFirst freeOffsets = clampScalar • generatorOffset.point := by
  rw [FieldMacToECMac.clampedFirst, freeOffsetPoints_freeOffsets, pointHorner_replicate,
    smul_smul, ← neg_smul, clampScalar]

theorem offsets_clamped [FieldCertificate] [GroupCertificate] : offsets.IsClamped := by
  have generator := offset_represents generatorOffset
  have represents : Represents clampedCoordinates (clampScalar.val • generatorOffset.point) := by
    rw [clampedCoordinates]
    exact smulFuel_represents generator 254 clampScalar.val clampScalar_val_lt
  have nonzero : clampScalar • generatorOffset.point ≠ 0 :=
    smul_ne_zero_of_coprime _ _ (represents_ne_zero generator) clampScalar_coprime
  rw [zmod_smul_eq] at nonzero
  show (offsetOf clampedCoordinates).point = FieldMacToECMac.clampedFirst freeOffsets
  rw [clampedFirst_freeOffsets, zmod_smul_eq]
  rcases target : clampScalar.val • generatorOffset.point with _ | @⟨x, y, valid⟩
  · exact (nonzero target).elim
  · rw [target] at represents
    rcases coordinates : clampedCoordinates with _ | ⟨x', y'⟩
    · rw [coordinates] at represents
      exact represents.elim
    · rw [coordinates] at represents
      obtain ⟨rfl, rfl⟩ := represents
      have onCurve : OnCurve { x := x', y := y' } := (equation_iff_onCurve _).mp
        ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mpr valid)
      have validTrue := (validate_eq_true_iff _).mpr onCurve
      show (offsetOf (some (x', y'))).point = _
      simp only [offsetOf, validTrue, dite_true]
      exact represents_unique (offset_represents _) ⟨rfl, rfl⟩

/-! ## Derived blocks, keys, and permutations -/

def block (seed : BitVec 256) (index : Nat) : Block :=
  BitVec.ofNat 128 ((seed.toNat + index + 1) * (2 * index + 0x9E3779B97F4A7C15))

def field (seed : BitVec 256) (index : Nat) : BaseField :=
  ((block seed (2 * index)).toNat + 2 ^ 128 * (block seed (2 * index + 1)).toNat : Nat)

/-- The benchmark hash's input word: a field element folded into `127` bits. The low `127` bits
are kept, and the high `127` bits enter through a derived block, so every bit of the input --
in particular every scale-tag bit above bit `128` -- moves the word. -/
def hashWord (seed : BitVec 256) (value : BaseField) : Nat :=
  (value.val % 2 ^ 127) ^^^ ((block seed (300_000 + value.val / 2 ^ 127)).toNat % 2 ^ 127)

def nonZeroBase (value : BaseField) : NonZeroBase :=
  if zero : value = 0 then ⟨1, by decide⟩ else ⟨value, zero⟩

/-- Addition by a derived key is one public permutation. -/
def shift (key : Block) : Equiv Block Block := {
  toFun := fun value => value + key
  invFun := fun value => value - key
  left_inv := fun value => BitVec.add_sub_cancel value key
  right_inv := fun value => BitVec.sub_add_cancel value key
}

/-! ### An injective code for the Plan B fixed-key index

`hot` occupies `0 .. 4 * 52 * 5 * 2 ^ 5 * 2 - 1` and `gadget` the next `91 * 2 * 254 * 2`. Every
constructor's code is the mixed-radix value of its arguments, so the map is injective on the
whole index type. The `hot` family runs over the four *lanes* -- two switch systems on each of
the two coordinates. The `scale-hot` switch masks are hash queries (`PlanB.scaleInput`), not
fixed-key gates, so they need no code here: `hashOracle` below answers every field input. -/

/-- The coordinate's code. -/
def coordCode : PlanB.Coord → Nat
  | .x => 0
  | .y => 1

/-- The block index of a `hot` gate. The repaired fold step names two permutations per gate,
so the code carries the `half` bit too. The lane's code is the scale tag's `PlanB.laneCode`. -/
def hotCode (lane : PlanB.Lane) (chunk fold entry : Nat) (half : Bool) : Nat :=
  ((((PlanB.laneCode lane * PlanB.chunkCount + chunk) * PlanB.chunkBits + fold)
    * 2 ^ PlanB.chunkBits + entry) * 2) + (if half then 1 else 0)

/-- The number of `hot` indices. -/
def hotCount : Nat := 4 * PlanB.chunkCount * PlanB.chunkBits * 2 ^ PlanB.chunkBits * 2

/-- The block index of a `gadget` permutation. -/
def gadgetCode (digit : Nat) (coord : PlanB.Coord) (position : Nat) (bit : Bool) : Nat :=
  hotCount + ((digit * 2 + coordCode coord) * PlanB.coordinateBits + position) * 2 +
    (if bit then 1 else 0)

/-- An injective code for the Plan B fixed-key index. -/
def fixedKeyCode : PlanB.FixedIndex → Nat
  | .hot lane chunk fold entry half => hotCode lane chunk.val fold.val entry.val half
  | .gadget digit coord position bit => gadgetCode digit.val coord position.val bit

/-- The `EncPRF` permutation index code. -/
def encPRFCode (index : EncPRF.PermutationIndex) : Nat :=
  (match index.1 with | .x => 0 | .y => 1) * coordinateBitCount + index.2.val

/-- The base block index of one coordinate's zero labels. -/
def zeroLabelBase : PlanB.Coord → Nat
  | .x => 0
  | .y => 300

def rowRandomness (seed : BitVec 256) (row : Nat) : FieldMacToECMac.RowRandomness :=
  let base := 60_000 + row * 16
  { rho := nonZeroBase (field seed base)
    tau := nonZeroBase (field seed (base + 9))
    x := {
      r1 := field seed (base + 1)
      r2 := field seed (base + 2)
      r4 := field seed (base + 3) }
    y := {
      r2 := field seed (base + 4)
      r4 := field seed (base + 6)
      r5 := field seed (base + 7) }
    z := {
      r1 := field seed (base + 8) } }

/-- This is the complete benchmark tape for one seed. -/
def randomness (seed : BitVec 256) : Garbling.Randomness := {
  offsets
  offsetsClamped := by
    intro _ _
    exact offsets_clamped
  pointRandomness := Vector.ofFn fun row => rowRandomness seed row.val
  exceptionPad := Vector.ofFn fun row =>
    Vector.ofFn fun slot => Exception.lowByte (block seed (200_000 + row.val * 12 + slot.val))
  bridgeKey := field seed 1
  curveMask := nonZeroBase (field seed 2)
  curveR1 := field seed 3
  curveR2 := field seed 4
  fixedKeyOracle := ⟨fun index => shift (block seed (2_000_000 + fixedKeyCode index))⟩
  inputZero := fun coord position => block seed (zeroLabelBase coord + position.val)
  inputDelta := fun coord => block seed (600 + coordCode coord)
  encPRFOracle := ⟨fun index => shift (block seed (40_000 + encPRFCode index))⟩
  hashOracle := fun value =>
    (block seed (100_000 + 2 * hashWord seed value),
      block seed (100_000 + 2 * hashWord seed value + 1))
}

end Kriterion.ArgoMAC.Seed
