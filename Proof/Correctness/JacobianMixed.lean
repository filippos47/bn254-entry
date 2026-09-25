/-
This file proves perfect correctness for the Jacobian mixed-addition rows.
The rows come from `gc_argomac_new.tex`, equations `c2_coeffs_X`, `c2_coeffs_Y`, `c2_coeffs_Z`.
The exceptional cases of the mixed addition are resolved by the exception gadget.
-/

import Mathlib.Tactic.LinearCombination
import Proof.Correctness.PGS.Row
import Security.Correctness

namespace Kriterion.ArgoMAC.JacobianMixed

open BN254

private theorem twoNe : (2 : BaseField) ≠ 0 := by decide

private theorem fourNe : (4 : BaseField) ≠ 0 := by decide

/-- No affine curve point has a vanishing `y` coordinate. -/
theorem noAffineYZero [FieldCertificate] [GroupCertificate]
    (input : AffineInput) (inputOnCurve : OnCurve input) : input.y ≠ 0 := by
  intro yZero
  let valid : curve.toAffine.Nonsingular input.x input.y :=
    (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mp
      ((equation_iff_onCurve input).mpr inputOnCurve)
  let point : Point := .some _ _ valid
  have ySelfNeg : input.y = curve.toAffine.negY input.x input.y := by
    simp [WeierstrassCurve.Affine.negY, curve, yZero]
  have twoPoint : 2 • point = 0 := by
    simpa [two_nsmul] using WeierstrassCurve.Affine.Point.add_self_of_Y_eq ySelfNeg
  have groupOrder := GroupCertificate.groupOrder point
  have modulusOdd : scalarFieldModulus = 2 * (scalarFieldModulus / 2) + 1 := by
    decide
  rw [modulusOdd, add_nsmul, mul_nsmul, twoPoint, nsmul_zero, zero_add, one_nsmul]
    at groupOrder
  exact WeierstrassCurve.Affine.Point.some_ne_zero valid groupOrder

/-- `affinePoint` is the Mathlib point of an on-curve coordinate pair. -/
def affinePoint [FieldCertificate] (input : AffineInput) (inputOnCurve : OnCurve input) : Point :=
  .some input.x input.y <| (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mp
    ((equation_iff_onCurve input).mpr inputOnCurve)

theorem decodePoint_eq_affinePoint [FieldCertificate]
    (input : AffineInput) (inputOnCurve : OnCurve input) :
    decodePoint input = some (affinePoint input inputOnCurve) := by
  simp [decodePoint, (validate_eq_true_iff input).mpr inputOnCurve, affinePoint]

theorem affineOffsetPoint_eq [FieldCertificate]
    (offset : FieldMacToECMac.AffineOffset) :
    FieldMacToECMac.AffineOffset.point offset =
      affinePoint offset.coordinates offset.onCurve := by
  simp [FieldMacToECMac.AffineOffset.point, decodePoint,
    (validate_eq_true_iff offset.coordinates).mpr offset.onCurve, affinePoint]

theorem affinePoint_eq_of_decode [FieldCertificate]
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point)
    (inputOnCurve : OnCurve input) :
    affinePoint input inputOnCurve = point := by
  have canonical := decodePoint_eq_affinePoint input inputOnCurve
  exact Option.some.inj (canonical.symm.trans decoded)

theorem transformedInputPoint_eq_digitEndomorphism
    [FieldCertificate] (digit : Digit) (phi : BaseField)
    (selected : digitEndomorphismBase digit = some phi)
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point)
    (transformedOnCurve : OnCurve (FieldMacToECMac.transformedInput phi input)) :
    affinePoint (FieldMacToECMac.transformedInput phi input) transformedOnCurve =
      digitEndomorphism digit point := by
  have inputOnCurve : OnCurve input :=
    (decodePoint_defined input).mp (by simp [decoded])
  have pointEq := affinePoint_eq_of_decode input point decoded inputOnCurve
  have generatorSquared : endomorphismGenerator ^ 2 = BN254.endomorphismBase := by
    calc
      endomorphismGenerator ^ 2 =
          BN254.endomorphismBase ^ 3 * BN254.endomorphismBase := by
        simp only [endomorphismGenerator]
        ring
      _ = BN254.endomorphismBase := by rw [BN254.endomorphismBaseCube]; simp
  have generatorCube : endomorphismGenerator ^ 3 = (-1 : BaseField) := by
    calc
      endomorphismGenerator ^ 3 = -(BN254.endomorphismBase ^ 3) ^ 2 := by
        simp only [endomorphismGenerator]
        ring
      _ = -1 := by rw [BN254.endomorphismBaseCube]; simp
  have generatorFourth :
      endomorphismGenerator ^ 4 = BN254.endomorphismBase ^ 2 := by
    calc
      endomorphismGenerator ^ 4 =
          endomorphismGenerator ^ 3 * endomorphismGenerator := by ring
      _ = BN254.endomorphismBase ^ 2 := by
        rw [generatorCube]
        simp [endomorphismGenerator]
  have generatorSixth : endomorphismGenerator ^ 6 = (1 : BaseField) := by
    calc
      endomorphismGenerator ^ 6 = (endomorphismGenerator ^ 3) ^ 2 := by ring
      _ = 1 := by rw [generatorCube]; ring
  subst point
  cases digit with
  | zero => simp [digitEndomorphismBase] at selected
  | one =>
      simp [digitEndomorphismBase] at selected
      subst phi
      simp [FieldMacToECMac.transformedInput, affinePoint, digitEndomorphism]
  | negOne =>
      simp [digitEndomorphismBase] at selected
      subst phi
      simp [FieldMacToECMac.transformedInput, affinePoint, digitEndomorphism, curve,
        show (endomorphismGenerator ^ 3) ^ 4 = (1 : BaseField) by
          rw [generatorCube]
          ring,
        show (endomorphismGenerator ^ 3) ^ 3 = (-1 : BaseField) by
          rw [generatorCube]
          ring]
      change _ = WeierstrassCurve.Affine.Point.neg _
      simp [WeierstrassCurve.Affine.Point.neg, WeierstrassCurve.Affine.negY, curve, pow_two, mul_assoc]
  | omega =>
      simp [digitEndomorphismBase] at selected
      subst phi
      simp [FieldMacToECMac.transformedInput, affinePoint, digitEndomorphism,
        BN254.endomorphism,
        show (endomorphismGenerator ^ 2) ^ 4 =
          (BN254.endomorphismBase : BaseField) by
            calc
              (endomorphismGenerator ^ 2) ^ 4 =
                  endomorphismGenerator ^ 6 * endomorphismGenerator ^ 2 := by ring
              _ = BN254.endomorphismBase := by rw [generatorSixth, generatorSquared]; simp,
        show (endomorphismGenerator ^ 2) ^ 3 = (1 : BaseField) by
          rw [show (endomorphismGenerator ^ 2) ^ 3 =
            endomorphismGenerator ^ 6 by ring, generatorSixth]]
  | negOmega =>
      simp [digitEndomorphismBase] at selected
      subst phi
      simp [FieldMacToECMac.transformedInput, affinePoint, digitEndomorphism,
        BN254.endomorphism, curve,
        show (endomorphismGenerator ^ 5) ^ 4 =
          (BN254.endomorphismBase : BaseField) by
            calc
              (endomorphismGenerator ^ 5) ^ 4 =
                  (endomorphismGenerator ^ 6) ^ 3 *
                    endomorphismGenerator ^ 2 := by ring
              _ = BN254.endomorphismBase := by rw [generatorSixth, generatorSquared]; simp,
        show (endomorphismGenerator ^ 5) ^ 3 = (-1 : BaseField) by
          calc
            (endomorphismGenerator ^ 5) ^ 3 =
                (endomorphismGenerator ^ 6) ^ 2 * endomorphismGenerator ^ 3 := by ring
            _ = -1 := by rw [generatorSixth, generatorCube]; simp]
      change _ = WeierstrassCurve.Affine.Point.neg _
      simp [WeierstrassCurve.Affine.Point.neg, WeierstrassCurve.Affine.negY, curve, pow_two, mul_assoc]
  | omegaSquared =>
      simp [digitEndomorphismBase] at selected
      subst phi
      simp [FieldMacToECMac.transformedInput, affinePoint, digitEndomorphism,
        BN254.endomorphism,
        show (endomorphismGenerator ^ 4) ^ 4 =
          (BN254.endomorphismBase ^ 2 : BaseField) by
            calc
              (endomorphismGenerator ^ 4) ^ 4 =
                  (endomorphismGenerator ^ 6) ^ 2 *
                    endomorphismGenerator ^ 4 := by ring
              _ = BN254.endomorphismBase ^ 2 := by
                rw [generatorSixth, generatorFourth]
                simp,
        show (endomorphismGenerator ^ 4) ^ 3 = (1 : BaseField) by
          rw [show (endomorphismGenerator ^ 4) ^ 3 =
            (endomorphismGenerator ^ 6) ^ 2 by ring, generatorSixth]
          simp] <;> ring
  | negOmegaSquared =>
      simp [digitEndomorphismBase] at selected
      subst phi
      simp [FieldMacToECMac.transformedInput, affinePoint, digitEndomorphism,
        BN254.endomorphism, curve,
        show endomorphismGenerator ^ 4 =
          (BN254.endomorphismBase ^ 2 : BaseField) from generatorFourth,
        show endomorphismGenerator ^ 3 = (-1 : BaseField) from generatorCube]
      change _ = WeierstrassCurve.Affine.Point.neg _
      simp [WeierstrassCurve.Affine.Point.neg, WeierstrassCurve.Affine.negY, curve, pow_two, mul_assoc]

/-! ### The sign row's decoder -/

theorem characterExponent_add_root :
    Garbling.characterExponent + 2 * Garbling.rootExponent = baseFieldModulus := by
  unfold Garbling.characterExponent Garbling.rootExponent baseFieldModulus
  norm_num

theorem two_characterExponent : 2 * Garbling.characterExponent = baseFieldModulus - 1 := by
  unfold Garbling.characterExponent baseFieldModulus
  norm_num

theorem characterExponent_lt : Garbling.characterExponent < 2 ^ 254 := by
  unfold Garbling.characterExponent baseFieldModulus
  norm_num

theorem rootExponent_lt : Garbling.rootExponent < 2 ^ 254 := by
  unfold Garbling.rootExponent baseFieldModulus
  norm_num

/-- The library's square-and-multiply is the field power. -/
theorem fieldPower_eq (value : BaseField) (exponent : Nat) (small : exponent < 2 ^ 254) :
    Garbling.fieldPower value exponent = value ^ exponent := by
  unfold Garbling.fieldPower
  rw [modularPower_correct _ _ _ _ _ small]
  simp

/-- **The sign root.** For `h ≠ 0`, `(h² y)^((p-1)/2) (y²)^((p+1)/4) = y`: the square `h²` has
character one, and `y^((p-1)/2) y^((p+1)/2) = y^p = y` by Fermat. -/
theorem signRoot [FieldCertificate] (h y : BaseField) (hNe : h ≠ 0) :
    Garbling.fieldPower (h ^ 2 * y) Garbling.characterExponent *
      Garbling.fieldPower (y ^ 2) Garbling.rootExponent = y := by
  rw [fieldPower_eq _ _ characterExponent_lt, fieldPower_eq _ _ rootExponent_lt]
  have total := characterExponent_add_root
  have twice := two_characterExponent
  generalize Garbling.characterExponent = c at total twice
  generalize Garbling.rootExponent = r at total
  calc (h ^ 2 * y) ^ c * (y ^ 2) ^ r = h ^ (2 * c) * y ^ (c + 2 * r) := by ring
    _ = h ^ (baseFieldModulus - 1) * y ^ baseFieldModulus := by rw [twice, total]
    _ = y := by rw [ZMod.pow_card_sub_one_eq_one hNe, ZMod.pow_card, one_mul]

/-- `3 / 2` times `2` is `3` in the scalar field. -/
theorem threeHalves_mul_two : Garbling.threeHalves * 2 = 3 := by
  unfold Garbling.threeHalves
  have half : (((scalarFieldModulus + 1) / 2 : Nat) : ScalarField) * 2 = 1 := by
    have nat : (scalarFieldModulus + 1) / 2 * 2 = scalarFieldModulus + 1 := by
      unfold scalarFieldModulus
      norm_num
    rw [show (2 : ScalarField) = ((2 : Nat) : ScalarField) by norm_cast, ← Nat.cast_mul, nat]
    simp
  rw [mul_assoc, half, mul_one]

/-- The affine sum of two on-curve points with distinct `x` is on the curve. -/
theorem sumOnCurve_of_X_ne [FieldCertificate] (offset input : AffineInput) (offsetOnCurve : OnCurve offset)
    (inputOnCurve : OnCurve input) (xNe : input.x ≠ offset.x) :
    OnCurve
      { x := curve.toAffine.addX input.x offset.x
          (curve.toAffine.slope input.x offset.x input.y offset.y)
        y := curve.toAffine.addY input.x offset.x input.y
          (curve.toAffine.slope input.x offset.x input.y offset.y) } :=
  (equation_iff_onCurve _).mp
    (WeierstrassCurve.Affine.equation_add ((equation_iff_onCurve input).mpr inputOnCurve)
      ((equation_iff_onCurve offset).mpr offsetOnCurve) fun exceptional => xNe exceptional.1)

/-- The Jacobian `X` row over `Z²` is the sum's `x`. -/
theorem xRow_div [FieldCertificate] (offset input : AffineInput) (offsetOnCurve : OnCurve offset)
    (inputOnCurve : OnCurve input) (xNe : input.x ≠ offset.x) :
    Coordinates.evaluate (Coordinates.xCoefficients offset) input / (input.x - offset.x) ^ 2 =
      curve.toAffine.addX input.x offset.x
        (curve.toAffine.slope input.x offset.x input.y offset.y) := by
  have dNe : input.x - offset.x ≠ 0 := sub_ne_zero.mpr xNe
  rw [Coordinates.evaluateX offset input offsetOnCurve inputOnCurve,
    WeierstrassCurve.Affine.slope_of_X_ne xNe]
  simp only [WeierstrassCurve.Affine.addX, curve, Coordinates.jacobianX,
    zero_mul, add_zero, sub_zero]
  field_simp
  ring

/-- The Jacobian `Y` formula over `Z³` is the sum's `y`. -/
theorem jacobianY_div [FieldCertificate] (offset input : AffineInput) (xNe : input.x ≠ offset.x) :
    Coordinates.jacobianY offset input / (input.x - offset.x) ^ 3 =
      curve.toAffine.addY input.x offset.x input.y
        (curve.toAffine.slope input.x offset.x input.y offset.y) := by
  have dNe : input.x - offset.x ≠ 0 := sub_ne_zero.mpr xNe
  rw [WeierstrassCurve.Affine.slope_of_X_ne xNe]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, curve,
    Coordinates.jacobianY, Coordinates.jacobianX, zero_mul, add_zero, sub_zero]
  field_simp
  ring

/-- **The sign row's value**: `S₀ = L² y_R` off `x = kx`. -/
theorem signValue [FieldCertificate] (offset input : AffineInput) (offsetOnCurve : OnCurve offset)
    (inputOnCurve : OnCurve input) (xNe : input.x ≠ offset.x) :
    Coordinates.evaluate (Coordinates.signCoefficients offset) input =
      Coordinates.tangentLine offset input ^ 2 *
        curve.toAffine.addY input.x offset.x input.y
          (curve.toAffine.slope input.x offset.x input.y offset.y) := by
  have dNe : input.x - offset.x ≠ 0 := sub_ne_zero.mpr xNe
  have identity := Coordinates.evaluateSign offset input offsetOnCurve inputOnCurve
  rw [← jacobianY_div offset input xNe]
  simp only [Coordinates.jacobianZ] at identity
  field_simp
  linear_combination identity

/-- The affine double of an on-curve offset is the group double. -/
theorem affinePoint_double [FieldCertificate] [GroupCertificate] (offset : AffineInput)
    (offsetOnCurve : OnCurve offset) (doubleOnCurve : OnCurve (Exception.doubleOffset offset)) :
    affinePoint (Exception.doubleOffset offset) doubleOnCurve =
      affinePoint offset offsetOnCurve + affinePoint offset offsetOnCurve := by
  have yNe : offset.y ≠ 0 := noAffineYZero offset offsetOnCurve
  have two : (2 : BaseField) ≠ 0 := twoNe
  have four : (4 : BaseField) ≠ 0 := fourNe
  have hy : offset.y ≠ curve.toAffine.negY offset.x offset.y := by
    simp only [WeierstrassCurve.Affine.negY, curve, zero_mul, sub_zero]
    intro same
    have twice : 2 * offset.y = 0 := by linear_combination same
    exact yNe ((mul_eq_zero.mp twice).resolve_left two)
  have slopeEq : curve.toAffine.slope offset.x offset.x offset.y offset.y =
      3 * offset.x ^ 2 * (2 * offset.y)⁻¹ := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    simp only [WeierstrassCurve.Affine.negY, curve]
    rw [div_eq_mul_inv]
    congr 1
    · ring
    · congr 1
      ring
  simp only [affinePoint]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  congr 1
  · rw [slopeEq]
    simp only [Exception.doubleOffset, WeierstrassCurve.Affine.addX, curve]
    ring
  · rw [slopeEq]
    simp only [Exception.doubleOffset, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.negY, curve]
    ring

/-- The double of an on-curve offset is on the curve (the tangent point of the group law). -/
theorem doubleOffset_onCurve [FieldCertificate] [GroupCertificate] (offset : AffineInput)
    (offsetOnCurve : OnCurve offset) : OnCurve (Exception.doubleOffset offset) := by
  have yNe : offset.y ≠ 0 := noAffineYZero offset offsetOnCurve
  have two : (2 : BaseField) ≠ 0 := twoNe
  have hy : offset.y ≠ curve.toAffine.negY offset.x offset.y := by
    simp only [WeierstrassCurve.Affine.negY, curve, zero_mul, sub_zero]
    intro same
    have twice : 2 * offset.y = 0 := by linear_combination same
    exact yNe ((mul_eq_zero.mp twice).resolve_left two)
  have slopeEq : curve.toAffine.slope offset.x offset.x offset.y offset.y =
      3 * offset.x ^ 2 * (2 * offset.y)⁻¹ := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    simp only [WeierstrassCurve.Affine.negY, curve]
    rw [div_eq_mul_inv]
    congr 1
    · ring
    · congr 1
      ring
  have valid : curve.toAffine.Nonsingular offset.x offset.y :=
    (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mp
      ((equation_iff_onCurve offset).mpr offsetOnCurve)
  have sum := WeierstrassCurve.Affine.nonsingular_add valid valid (fun same => hy same.2)
  have xEq : curve.toAffine.addX offset.x offset.x
      (curve.toAffine.slope offset.x offset.x offset.y offset.y) = (Exception.doubleOffset offset).x := by
    rw [slopeEq]
    simp only [Exception.doubleOffset, WeierstrassCurve.Affine.addX, curve]
    ring
  have yEq : curve.toAffine.addY offset.x offset.x offset.y
      (curve.toAffine.slope offset.x offset.x offset.y offset.y) = (Exception.doubleOffset offset).y := by
    rw [slopeEq]
    simp only [Exception.doubleOffset, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.negY, curve]
    ring
  rw [xEq, yEq] at sum
  exact (equation_iff_onCurve _).mp sum.1

/-- **Doubling is injective on the curve**: the group has odd order. -/
theorem doubleOffset_injective [FieldCertificate] [GroupCertificate] (first second : AffineInput)
    (firstOnCurve : OnCurve first) (secondOnCurve : OnCurve second)
    (same : Exception.doubleOffset first = Exception.doubleOffset second) : first = second := by
  have firstDouble := affinePoint_double first firstOnCurve (doubleOffset_onCurve first firstOnCurve)
  have secondDouble := affinePoint_double second secondOnCurve
    (doubleOffset_onCurve second secondOnCurve)
  have doubles : affinePoint (Exception.doubleOffset first) (doubleOffset_onCurve first firstOnCurve) =
      affinePoint (Exception.doubleOffset second) (doubleOffset_onCurve second secondOnCurve) := by
    simp only [affinePoint, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨congrArg AffineInput.x same, congrArg AffineInput.y same⟩
  have twice := firstDouble.symm.trans (doubles.trans secondDouble)
  have half : ∀ point : Point, (scalarFieldModulus / 2 + 1) • (point + point) = point := by
    intro point
    have order := GroupCertificate.groupOrder point
    have modulusOdd : scalarFieldModulus = 2 * (scalarFieldModulus / 2) + 1 := by decide
    rw [modulusOdd] at order
    calc (scalarFieldModulus / 2 + 1) • (point + point)
        = (2 * (scalarFieldModulus / 2 + 1)) • point := by rw [← two_nsmul, ← mul_nsmul]
      _ = (2 * (scalarFieldModulus / 2) + 1) • point + point := by
          rw [show 2 * (scalarFieldModulus / 2 + 1) = (2 * (scalarFieldModulus / 2) + 1) + 1 by ring,
            add_nsmul, one_nsmul]
      _ = point := by rw [order, zero_add]
  have points : affinePoint first firstOnCurve = affinePoint second secondOnCurve := by
    rw [← half (affinePoint first firstOnCurve), twice, half]
  simp only [affinePoint, WeierstrassCurve.Affine.Point.some.injEq] at points
  obtain ⟨x₁, y₁⟩ := first
  obtain ⟨x₂, y₂⟩ := second
  obtain ⟨rfl, rfl⟩ := points
  rfl

/-- **The tangent's other zero.** Off `x = kx`, the tangent at `-K` vanishes only at `2K`. -/
theorem tangentZero_double [FieldCertificate] [GroupCertificate] (offset input : AffineInput)
    (offsetOnCurve : OnCurve offset) (inputOnCurve : OnCurve input) (xNe : input.x ≠ offset.x)
    (lineZero : Coordinates.tangentLine offset input = 0) :
    input = Exception.doubleOffset offset := by
  have yNe : offset.y ≠ 0 := noAffineYZero offset offsetOnCurve
  have two : (2 : BaseField) ≠ 0 := twoNe
  have dNe : input.x - offset.x ≠ 0 := sub_ne_zero.mpr xNe
  have factor := Coordinates.tangentFactor offset input offsetOnCurve inputOnCurve
  rw [lineZero, zero_mul] at factor
  have linear : 4 * offset.y ^ 2 * input.x - 9 * offset.x ^ 4 + 8 * offset.x * offset.y ^ 2 = 0 :=
    (mul_eq_zero.mp factor.symm).resolve_left (pow_ne_zero 2 dNe)
  have curveK : offset.y ^ 2 = offset.x ^ 3 + 3 := offsetOnCurve
  have lineEq : 2 * offset.y * input.y + 3 * offset.x ^ 2 * input.x + 9 - offset.y ^ 2 = 0 :=
    lineZero
  have xValue : input.x = (3 * offset.x ^ 2 * (2 * offset.y)⁻¹) ^ 2 - 2 * offset.x := by
    field_simp
    linear_combination linear
  obtain ⟨ix, iy⟩ := input
  simp only at xValue lineEq ⊢
  simp only [Exception.doubleOffset, AffineInput.mk.injEq]
  refine ⟨xValue, ?_⟩
  rw [← xValue]
  field_simp
  linear_combination lineEq + 3 * curveK

/-- For `x' ≠ kx` and `L ≠ 0` the rows decode to the affine sum. -/
theorem decodeSignOfXNe [FieldCertificate] [GroupCertificate]
    (offset input : AffineInput) (offsetOnCurve : OnCurve offset) (inputOnCurve : OnCurve input)
    (xNe : input.x ≠ offset.x) (lineNe : Coordinates.tangentLine offset input ≠ 0)
    (rho tau : BaseField) (rhoNe : rho ≠ 0) (tauNe : tau ≠ 0) (digit tripleDigit : Digit)
    (inputPoint : Point) :
    Garbling.decodeHomogeneous
      { x := rho ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset) input
        y := tau ^ 2 * Coordinates.evaluate (Coordinates.signCoefficients offset) input
        z := rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input }
      digit tripleDigit inputPoint =
      some (affinePoint input inputOnCurve + affinePoint offset offsetOnCurve) := by
  have dNe : input.x - offset.x ≠ 0 := sub_ne_zero.mpr xNe
  have zValue : Coordinates.evaluate (Coordinates.zCoefficients offset) input =
      input.x - offset.x := Coordinates.evaluateZ offset input
  have zNe : rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input ≠ 0 := by
    rw [zValue]
    exact mul_ne_zero rhoNe dNe
  have sumOnCurve := sumOnCurve_of_X_ne offset input offsetOnCurve inputOnCurve xNe
  have sumYNe := noAffineYZero _ sumOnCurve
  have sValue : tau ^ 2 * Coordinates.evaluate (Coordinates.signCoefficients offset) input =
      (tau * Coordinates.tangentLine offset input) ^ 2 *
        curve.toAffine.addY input.x offset.x input.y
          (curve.toAffine.slope input.x offset.x input.y offset.y) := by
    rw [signValue offset input offsetOnCurve inputOnCurve xNe]
    ring
  have sNe : tau ^ 2 * Coordinates.evaluate (Coordinates.signCoefficients offset) input ≠ 0 := by
    rw [sValue]
    exact mul_ne_zero (pow_ne_zero 2 (mul_ne_zero tauNe lineNe)) sumYNe
  have xForm : rho ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset) input /
      (rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input) ^ 2 =
      curve.toAffine.addX input.x offset.x
        (curve.toAffine.slope input.x offset.x input.y offset.y) := by
    rw [zValue, ← xRow_div offset input offsetOnCurve inputOnCurve xNe]
    field_simp
  have cubic : curve.toAffine.addX input.x offset.x
        (curve.toAffine.slope input.x offset.x input.y offset.y) ^ 3 + 3 =
      curve.toAffine.addY input.x offset.x input.y
        (curve.toAffine.slope input.x offset.x input.y offset.y) ^ 2 := sumOnCurve.symm
  simp only [Garbling.decodeHomogeneous, if_neg zNe, if_neg sNe]
  rw [xForm, cubic, sValue, signRoot _ _ (mul_ne_zero tauNe lineNe),
    decodePoint_eq_affinePoint _ sumOnCurve]
  simp only [affinePoint]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne xNe]

/-- At `x = kx` with opposite `y` the rows decode to the identity. -/
theorem decodeJacobianNeg [FieldCertificate] [GroupCertificate]
    (offset input : AffineInput) (offsetOnCurve : OnCurve offset) (inputOnCurve : OnCurve input)
    (sameX : input.x = offset.x) (negY : input.y = -offset.y)
    (rho tau : BaseField) (rhoNe : rho ≠ 0) (digit tripleDigit : Digit) (inputPoint : Point) :
    Garbling.decodeHomogeneous
      { x := rho ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset) input
        y := tau ^ 2 * Coordinates.evaluate (Coordinates.signCoefficients offset) input
        z := rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input }
      digit tripleDigit inputPoint =
      some (affinePoint input inputOnCurve + affinePoint offset offsetOnCurve) := by
  have kyNe : offset.y ≠ 0 := noAffineYZero offset offsetOnCurve
  have zZero : rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input = 0 := by
    rw [Coordinates.exceptionalZ offset input sameX, mul_zero]
  have xNonzero : rho ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset) input ≠ 0 := by
    rw [Coordinates.exceptionalX offset input offsetOnCurve inputOnCurve sameX,
      show 2 * offset.y * (offset.y - input.y) = 4 * offset.y ^ 2 by rw [negY]; ring]
    exact mul_ne_zero (pow_ne_zero 2 rhoNe) (mul_ne_zero fourNe (pow_ne_zero 2 kyNe))
  have sumZero : affinePoint input inputOnCurve + affinePoint offset offsetOnCurve = 0 := by
    simp only [affinePoint]
    exact WeierstrassCurve.Affine.Point.add_of_Y_eq sameX
      (by simp [curve, WeierstrassCurve.Affine.negY, negY])
  rw [sumZero]
  simp only [Garbling.decodeHomogeneous]
  rw [if_pos zZero, if_neg xNonzero]

/-- At `x = kx` with equal `y` the gadget digit recovers the doubled point. -/
theorem decodeJacobianDouble [FieldCertificate] [GroupCertificate]
    (offset input : AffineInput) (offsetOnCurve : OnCurve offset) (inputOnCurve : OnCurve input)
    (sameX : input.x = offset.x) (sameY : input.y = offset.y)
    (rho tau : BaseField) (digit tripleDigit : Digit) (inputPoint : Point)
    (digitAction : digitEndomorphism digit inputPoint = affinePoint input inputOnCurve) :
    Garbling.decodeHomogeneous
      { x := rho ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset) input
        y := tau ^ 2 * Coordinates.evaluate (Coordinates.signCoefficients offset) input
        z := rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input }
      digit tripleDigit inputPoint =
      some (affinePoint input inputOnCurve + affinePoint offset offsetOnCurve) := by
  have zZero : rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input = 0 := by
    rw [Coordinates.exceptionalZ offset input sameX, mul_zero]
  have xZero : rho ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset) input = 0 := by
    rw [Coordinates.exceptionalX offset input offsetOnCurve inputOnCurve sameX, sameY]
    ring
  have offsetEq : offset = input := by
    obtain ⟨offsetX, offsetY⟩ := offset
    obtain ⟨inputX, inputY⟩ := input
    simp only [AffineInput.mk.injEq]
    exact ⟨sameX.symm, sameY.symm⟩
  simp only [Garbling.decodeHomogeneous]
  rw [if_pos zZero, if_pos xZero, digitAction]
  subst offsetEq
  exact congrArg some (two_smul ScalarField _)

/-- At the tangent's other zero `2K` the gadget digit recovers `(3/2)` times the input's image. -/
theorem decodeTriple [FieldCertificate] [GroupCertificate]
    (offset input : AffineInput) (offsetOnCurve : OnCurve offset) (inputOnCurve : OnCurve input)
    (xNe : input.x ≠ offset.x) (lineZero : Coordinates.tangentLine offset input = 0)
    (rho tau : BaseField) (rhoNe : rho ≠ 0) (digit tripleDigit : Digit) (inputPoint : Point)
    (digitAction : digitEndomorphism tripleDigit inputPoint = affinePoint input inputOnCurve) :
    Garbling.decodeHomogeneous
      { x := rho ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset) input
        y := tau ^ 2 * Coordinates.evaluate (Coordinates.signCoefficients offset) input
        z := rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input }
      digit tripleDigit inputPoint =
      some (affinePoint input inputOnCurve + affinePoint offset offsetOnCurve) := by
  have dNe : input.x - offset.x ≠ 0 := sub_ne_zero.mpr xNe
  have zNe : rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input ≠ 0 := by
    rw [Coordinates.evaluateZ offset input]
    exact mul_ne_zero rhoNe dNe
  have sZero : tau ^ 2 * Coordinates.evaluate (Coordinates.signCoefficients offset) input = 0 := by
    rw [signValue offset input offsetOnCurve inputOnCurve xNe, lineZero]
    ring
  have doubled := tangentZero_double offset input offsetOnCurve inputOnCurve xNe lineZero
  unfold Garbling.decodeHomogeneous
  rw [if_neg zNe, if_pos sZero, digitAction]
  refine congrArg some ?_
  subst doubled
  rw [affinePoint_double offset offsetOnCurve inputOnCurve]
  generalize affinePoint offset offsetOnCurve = K
  calc Garbling.threeHalves • (K + K) = Garbling.threeHalves • ((2 : ScalarField) • K) := by
        rw [two_smul]
    _ = (Garbling.threeHalves * 2) • K := by rw [smul_smul]
    _ = K + K + K := by
        rw [threeHalves_mul_two, show (3 : ScalarField) = 1 + 1 + 1 by norm_num, add_smul,
          add_smul, one_smul]

/-- Each output-key row decodes to the digit multiple of the input plus the offset. -/
theorem decodeEvaluateOutputKeyRow [FieldCertificate] [GroupCertificate]
    (key : FieldMacToECMac.OutputKey) (rho tau : NonZeroBase) (input : AffineInput)
    (inputOnCurve : OnCurve input) (exceptionDigit tripleDigit : Digit)
    (unlocked : (FieldMacToECMac.evaluateRow
        (Coordinates.rows key.offset.coordinates (digitEndomorphismBase key.digit) rho.value
          tau.value) input).z = 0 →
      (FieldMacToECMac.evaluateRow
        (Coordinates.rows key.offset.coordinates (digitEndomorphismBase key.digit) rho.value
          tau.value) input).x = 0 → exceptionDigit = key.digit)
    (tripled : (FieldMacToECMac.evaluateRow
        (Coordinates.rows key.offset.coordinates (digitEndomorphismBase key.digit) rho.value
          tau.value) input).z ≠ 0 →
      (FieldMacToECMac.evaluateRow
        (Coordinates.rows key.offset.coordinates (digitEndomorphismBase key.digit) rho.value
          tau.value) input).y = 0 → tripleDigit = key.digit) :
    Garbling.decodeHomogeneous
        (FieldMacToECMac.evaluateRow
          (Coordinates.rows key.offset.coordinates (digitEndomorphismBase key.digit) rho.value
            tau.value) input)
        exceptionDigit tripleDigit (affinePoint input inputOnCurve) =
      some (digitScalar key.digit • affinePoint input inputOnCurve + key.offset.point) := by
  have rhoNe : rho.value ≠ 0 := rho.nonzero
  have tauNe : tau.value ≠ 0 := tau.nonzero
  cases selected : digitEndomorphismBase key.digit with
  | none =>
      have digitZero : key.digit = .zero := by
        cases digitCase : key.digit
        case zero => rfl
        all_goals rw [digitCase] at selected; simp [digitEndomorphismBase] at selected
      have kyNe : key.offset.coordinates.y ≠ 0 := noAffineYZero _ key.offset.onCurve
      have curveK : key.offset.coordinates.x ^ 3 + 3 = key.offset.coordinates.y ^ 2 :=
        key.offset.onCurve.symm
      rw [FieldMacToECMac.evaluateRowsNone, digitZero]
      simp only [digitScalar, zero_smul, zero_add]
      simp only [Garbling.decodeHomogeneous]
      rw [if_neg rhoNe, if_neg (mul_ne_zero (pow_ne_zero 2 tauNe) kyNe), affineOffsetPoint_eq key.offset,
        mul_div_cancel_left₀ key.offset.coordinates.x (pow_ne_zero 2 rhoNe), curveK,
        signRoot _ _ tauNe]
      exact decodePoint_eq_affinePoint _ key.offset.onCurve
  | some phi =>
      rw [selected] at unlocked tripled
      have phiSix : phi ^ 6 = 1 := digitEndomorphismBasePowSix key.digit phi selected
      have tOnCurve : OnCurve (FieldMacToECMac.transformedInput phi input) := by
        simpa [FieldMacToECMac.transformedInput] using
          Coordinates.transformedOnCurve phi phiSix input inputOnCurve
      have digitPoint :
          affinePoint (FieldMacToECMac.transformedInput phi input) tOnCurve =
            digitEndomorphism key.digit (affinePoint input inputOnCurve) :=
        transformedInputPoint_eq_digitEndomorphism key.digit phi selected input
          (affinePoint input inputOnCurve) (decodePoint_eq_affinePoint input inputOnCurve) tOnCurve
      have target :
          some (affinePoint (FieldMacToECMac.transformedInput phi input) tOnCurve +
              affinePoint key.offset.coordinates key.offset.onCurve) =
            some (digitScalar key.digit • affinePoint input inputOnCurve + key.offset.point) := by
        rw [digitPoint, digitEndomorphismAction, affineOffsetPoint_eq]
      rw [FieldMacToECMac.evaluateRowsSome] at unlocked tripled ⊢
      rw [← target]
      by_cases xEq :
          (FieldMacToECMac.transformedInput phi input).x = key.offset.coordinates.x
      · have squares : (FieldMacToECMac.transformedInput phi input).y ^ 2 =
            key.offset.coordinates.y ^ 2 := by
          have transformedEquation := tOnCurve
          have offsetEquation := key.offset.onCurve
          simp only [OnCurve] at transformedEquation offsetEquation
          rw [xEq] at transformedEquation
          linear_combination transformedEquation - offsetEquation
        have product : ((FieldMacToECMac.transformedInput phi input).y -
            key.offset.coordinates.y) *
              ((FieldMacToECMac.transformedInput phi input).y +
                key.offset.coordinates.y) = 0 := by
          linear_combination squares
        rcases mul_eq_zero.mp product with equalY | oppositeY
        · have sameY : (FieldMacToECMac.transformedInput phi input).y =
              key.offset.coordinates.y := sub_eq_zero.mp equalY
          have digitEq : exceptionDigit = key.digit := by
            apply unlocked
            · show rho.value * _ = 0
              rw [Coordinates.exceptionalZ key.offset.coordinates _ xEq, mul_zero]
            · show rho.value ^ 2 * _ = 0
              rw [Coordinates.exceptionalX key.offset.coordinates _ key.offset.onCurve tOnCurve xEq,
                sameY]
              ring
          exact decodeJacobianDouble key.offset.coordinates
            (FieldMacToECMac.transformedInput phi input) key.offset.onCurve tOnCurve xEq sameY
            rho.value tau.value exceptionDigit tripleDigit (affinePoint input inputOnCurve)
            (by rw [digitEq]; exact digitPoint.symm)
        · have negativeY : (FieldMacToECMac.transformedInput phi input).y =
              -key.offset.coordinates.y := eq_neg_of_add_eq_zero_left oppositeY
          exact decodeJacobianNeg key.offset.coordinates
            (FieldMacToECMac.transformedInput phi input) key.offset.onCurve tOnCurve xEq
            negativeY rho.value tau.value rhoNe exceptionDigit tripleDigit
            (affinePoint input inputOnCurve)
      · by_cases lineEq : Coordinates.tangentLine key.offset.coordinates
            (FieldMacToECMac.transformedInput phi input) = 0
        · have digitEq : tripleDigit = key.digit := by
            apply tripled
            · show rho.value * _ ≠ 0
              rw [Coordinates.evaluateZ]
              exact mul_ne_zero rhoNe (sub_ne_zero.mpr xEq)
            · show tau.value ^ 2 * _ = 0
              rw [signValue _ _ key.offset.onCurve tOnCurve xEq, lineEq]
              ring
          exact decodeTriple key.offset.coordinates (FieldMacToECMac.transformedInput phi input)
            key.offset.onCurve tOnCurve xEq lineEq rho.value tau.value rhoNe exceptionDigit
            tripleDigit (affinePoint input inputOnCurve) (by rw [digitEq]; exact digitPoint.symm)
        · exact decodeSignOfXNe key.offset.coordinates
            (FieldMacToECMac.transformedInput phi input) key.offset.onCurve tOnCurve xEq lineEq
            rho.value tau.value rhoNe tauNe exceptionDigit tripleDigit
            (affinePoint input inputOnCurve)

/-- The row of one output key, as `Coordinates.rows`. -/
theorem rowsForOutputKeys_get (keys : FieldMacToECMac.OutputKeys)
    (randomness : FieldMacToECMac.Randomness) (index : Fin FieldMacToECMac.outputMacCount) :
    (FieldMacToECMac.rowsForOutputKeys keys randomness).get index =
      Coordinates.rows (keys.get index).offset.coordinates
        (digitEndomorphismBase (keys.get index).digit) (randomness.get index).rho.value
        (randomness.get index).tau.value := by
  simp [FieldMacToECMac.rowsForOutputKeys]

/-- A row with `Z = 0 = X` is the doubling case, and the gadget unlocks the digit that produced
it. -/
theorem exceptionDigitCorrect [FieldCertificate] [GroupCertificate]
    (keys : FieldMacToECMac.OutputKeys) (randomness : FieldMacToECMac.Randomness)
    (K : FieldMacToECMac.DigitValues) (inputKey : InputMacKey)
    (perms : FieldMacToECMac.GadgetPermutations) (pad : FieldMacToECMac.ExceptionPad)
    (input : AffineInput) (index : Fin FieldMacToECMac.outputMacCount)
    (inputOnCurve : OnCurve input)
    (offsetOnCurve : OnCurve (keys.get index).offset.coordinates)
    (zZeroRow : (FieldMacToECMac.evaluateRow
        ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input).z = 0)
    (xZeroRow : (FieldMacToECMac.evaluateRow
        ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input).x = 0) :
    (FieldMacToECMac.expectedResult keys (FieldMacToECMac.rowsForOutputKeys keys randomness)
        K inputKey perms pad input).exceptionDigits.get index =
      (keys.get index).digit := by
  have rhoNe : (randomness.get index).rho.value ≠ 0 := (randomness.get index).rho.nonzero
  rw [rowsForOutputKeys_get] at zZeroRow xZeroRow
  cases selected : digitEndomorphismBase (keys.get index).digit with
  | none =>
      rw [selected, FieldMacToECMac.evaluateRowsNone] at zZeroRow
      exact absurd zZeroRow rhoNe
  | some phi =>
      rw [selected, FieldMacToECMac.evaluateRowsSome] at zZeroRow xZeroRow
      have phiSix : phi ^ 6 = 1 := digitEndomorphismBasePowSix _ phi selected
      have tOnCurve : OnCurve (FieldMacToECMac.transformedInput phi input) := by
        simpa [FieldMacToECMac.transformedInput] using
          Coordinates.transformedOnCurve phi phiSix input inputOnCurve
      have zZero : (randomness.get index).rho.value *
          Coordinates.evaluate (Coordinates.zCoefficients (keys.get index).offset.coordinates)
            (FieldMacToECMac.transformedInput phi input) = 0 := zZeroRow
      have sameX : (FieldMacToECMac.transformedInput phi input).x =
          (keys.get index).offset.coordinates.x := by
        rw [Coordinates.evaluateZ] at zZero
        exact sub_eq_zero.mp ((mul_eq_zero.mp zZero).resolve_left rhoNe)
      have xZero : (randomness.get index).rho.value ^ 2 *
          Coordinates.evaluate (Coordinates.xCoefficients (keys.get index).offset.coordinates)
            (FieldMacToECMac.transformedInput phi input) = 0 := xZeroRow
      rw [Coordinates.exceptionalX _ _ offsetOnCurve tOnCurve sameX] at xZero
      have kyNe : (keys.get index).offset.coordinates.y ≠ 0 := noAffineYZero _ offsetOnCurve
      have sameY : (FieldMacToECMac.transformedInput phi input).y =
          (keys.get index).offset.coordinates.y :=
        (sub_eq_zero.mp
          ((mul_eq_zero.mp ((mul_eq_zero.mp xZero).resolve_left
            (pow_ne_zero 2 rhoNe))).resolve_left (mul_ne_zero twoNe kyNe))).symm
      have xValue : input.x = phi ^ 2 * (keys.get index).offset.coordinates.x := by
        have base : phi ^ 4 * input.x = (keys.get index).offset.coordinates.x := sameX
        calc input.x = phi ^ 6 * input.x := by rw [phiSix, one_mul]
          _ = phi ^ 2 * (phi ^ 4 * input.x) := by ring
          _ = phi ^ 2 * (keys.get index).offset.coordinates.x := by rw [base]
      have yValue : input.y = phi ^ 3 * (keys.get index).offset.coordinates.y := by
        have base : phi ^ 3 * input.y = (keys.get index).offset.coordinates.y := sameY
        calc input.y = phi ^ 6 * input.y := by rw [phiSix, one_mul]
          _ = phi ^ 3 * (phi ^ 3 * input.y) := by ring
          _ = phi ^ 3 * (keys.get index).offset.coordinates.y := by rw [base]
      have inputEq : input =
          Exception.exceptionalInput phi (keys.get index).offset.coordinates := by
        obtain ⟨inputX, inputY⟩ := input
        simp only [Exception.exceptionalInput, AffineInput.mk.injEq]
        exact ⟨xValue, yValue⟩
      rw [inputEq]
      exact FieldMacToECMac.unlockExceptional keys
        (FieldMacToECMac.rowsForOutputKeys keys randomness) K inputKey perms pad
        index phi selected

/-- A row with `S = 0 ≠ Z` is the tangent's other zero `2K`, and the gadget unlocks the digit that
produced it. -/
theorem tripleDigitCorrect [FieldCertificate] [GroupCertificate]
    (keys : FieldMacToECMac.OutputKeys) (randomness : FieldMacToECMac.Randomness)
    (K : FieldMacToECMac.DigitValues) (inputKey : InputMacKey)
    (perms : FieldMacToECMac.GadgetPermutations) (pad : FieldMacToECMac.ExceptionPad)
    (input : AffineInput) (index : Fin FieldMacToECMac.outputMacCount)
    (inputOnCurve : OnCurve input)
    (offsetOnCurve : OnCurve (keys.get index).offset.coordinates)
    (zNeRow : (FieldMacToECMac.evaluateRow
        ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input).z ≠ 0)
    (sZeroRow : (FieldMacToECMac.evaluateRow
        ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input).y = 0) :
    (FieldMacToECMac.expectedResult keys (FieldMacToECMac.rowsForOutputKeys keys randomness)
        K inputKey perms pad input).tripleDigits.get index =
      (keys.get index).digit := by
  have tauNe : (randomness.get index).tau.value ≠ 0 := (randomness.get index).tau.nonzero
  rw [rowsForOutputKeys_get] at zNeRow sZeroRow
  cases selected : digitEndomorphismBase (keys.get index).digit with
  | none =>
      rw [selected, FieldMacToECMac.evaluateRowsNone] at sZeroRow
      exact absurd sZeroRow (mul_ne_zero (pow_ne_zero 2 tauNe) (noAffineYZero _ offsetOnCurve))
  | some phi =>
      rw [selected, FieldMacToECMac.evaluateRowsSome] at zNeRow sZeroRow
      have phiSix : phi ^ 6 = 1 := digitEndomorphismBasePowSix _ phi selected
      have tOnCurve : OnCurve (FieldMacToECMac.transformedInput phi input) := by
        simpa [FieldMacToECMac.transformedInput] using
          Coordinates.transformedOnCurve phi phiSix input inputOnCurve
      have zNe : (randomness.get index).rho.value *
          Coordinates.evaluate (Coordinates.zCoefficients (keys.get index).offset.coordinates)
            (FieldMacToECMac.transformedInput phi input) ≠ 0 := zNeRow
      have xNe : (FieldMacToECMac.transformedInput phi input).x ≠
          (keys.get index).offset.coordinates.x := by
        intro same
        apply zNe
        rw [Coordinates.exceptionalZ _ _ same, mul_zero]
      have sZero : (randomness.get index).tau.value ^ 2 *
          Coordinates.evaluate (Coordinates.signCoefficients (keys.get index).offset.coordinates)
            (FieldMacToECMac.transformedInput phi input) = 0 := sZeroRow
      rw [signValue _ _ offsetOnCurve tOnCurve xNe] at sZero
      have sumYNe := noAffineYZero _
        (sumOnCurve_of_X_ne _ _ offsetOnCurve tOnCurve xNe)
      have lineZero : Coordinates.tangentLine (keys.get index).offset.coordinates
          (FieldMacToECMac.transformedInput phi input) = 0 :=
        pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          ((mul_eq_zero.mp ((mul_eq_zero.mp sZero).resolve_left (pow_ne_zero 2 tauNe))).resolve_right
            sumYNe)
      have doubled := tangentZero_double _ _ offsetOnCurve tOnCurve xNe lineZero
      have xValue : input.x = phi ^ 2 * (Exception.doubleOffset
          (keys.get index).offset.coordinates).x := by
        have base : phi ^ 4 * input.x = (Exception.doubleOffset
            (keys.get index).offset.coordinates).x := congrArg AffineInput.x doubled
        calc input.x = phi ^ 6 * input.x := by rw [phiSix, one_mul]
          _ = phi ^ 2 * (phi ^ 4 * input.x) := by ring
          _ = _ := by rw [base]
      have yValue : input.y = phi ^ 3 * (Exception.doubleOffset
          (keys.get index).offset.coordinates).y := by
        have base : phi ^ 3 * input.y = (Exception.doubleOffset
            (keys.get index).offset.coordinates).y := congrArg AffineInput.y doubled
        calc input.y = phi ^ 6 * input.y := by rw [phiSix, one_mul]
          _ = phi ^ 3 * (phi ^ 3 * input.y) := by ring
          _ = _ := by rw [base]
      have inputEq : input = Exception.tripleInput phi (keys.get index).offset.coordinates := by
        obtain ⟨inputX, inputY⟩ := input
        simp only [Exception.tripleInput, Exception.exceptionalInput, AffineInput.mk.injEq]
        exact ⟨xValue, yValue⟩
      rw [inputEq]
      exact FieldMacToECMac.unlockTriple keys
        (FieldMacToECMac.rowsForOutputKeys keys randomness) K inputKey perms pad
        index phi selected

/-- Every expected row decodes, with its gadget digits, to the digit multiple plus the offset. -/
theorem decodeExpectedRow [FieldCertificate] [GroupCertificate]
    (keys : FieldMacToECMac.OutputKeys) (randomness : FieldMacToECMac.Randomness)
    (K : FieldMacToECMac.DigitValues) (inputKey : InputMacKey)
    (perms : FieldMacToECMac.GadgetPermutations) (pad : FieldMacToECMac.ExceptionPad)
    (input : AffineInput) (inputOnCurve : OnCurve input)
    (index : Fin FieldMacToECMac.outputMacCount) :
    Garbling.decodeHomogeneous
        (FieldMacToECMac.evaluateRow
          ((FieldMacToECMac.rowsForOutputKeys keys randomness).get index) input)
        ((FieldMacToECMac.expectedResult keys
          (FieldMacToECMac.rowsForOutputKeys keys randomness) K inputKey perms pad
          input).exceptionDigits.get index)
        ((FieldMacToECMac.expectedResult keys
          (FieldMacToECMac.rowsForOutputKeys keys randomness) K inputKey perms pad
          input).tripleDigits.get index)
        (affinePoint input inputOnCurve) =
      some (digitScalar (keys.get index).digit • affinePoint input inputOnCurve +
        (keys.get index).offset.point) := by
  have rowEq := rowsForOutputKeys_get keys randomness index
  rw [rowEq]
  exact decodeEvaluateOutputKeyRow (keys.get index) (randomness.get index).rho
    (randomness.get index).tau input inputOnCurve _ _
    (fun zZero xZero => exceptionDigitCorrect keys randomness K inputKey perms pad input index
      inputOnCurve (keys.get index).offset.onCurve (by rw [rowEq]; exact zZero)
      (by rw [rowEq]; exact xZero))
    (fun zNe sZero => tripleDigitCorrect keys randomness K inputKey perms pad input index
      inputOnCurve (keys.get index).offset.onCurve (by rw [rowEq]; exact zNe)
      (by rw [rowEq]; exact sZero))

private theorem optionMapMOfFn {n : Nat} {α γ : Type}
    (f : Fin n → α) (h : Fin n → γ) (decode : α → Option γ)
    (decoded : ∀ index, decode (f index) = some (h index)) :
    (List.ofFn f).mapM decode = some (List.ofFn h) := by
  induction n with
  | zero => simp
  | succ n inductionHypothesis =>
      rw [List.ofFn_succ, List.ofFn_succ, List.mapM_cons, decoded,
        inductionHypothesis (fun index => f index.succ) (fun index => h index.succ)
          (fun index => decoded index.succ)]
      rfl

private theorem zipOfFn {n : Nat} {α β : Type} (f : Fin n → α) (g : Fin n → β) :
    List.zip (List.ofFn f) (List.ofFn g) = List.ofFn fun index => (f index, g index) := by
  induction n with
  | zero => simp
  | succ n inductionHypothesis =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.zip_cons_cons,
        inductionHypothesis (fun index => f index.succ) (fun index => g index.succ)]

/-- All 91 output rows decode together. -/
theorem decodeRowsForOutputKeys [FieldCertificate] [GroupCertificate]
    (keys : FieldMacToECMac.OutputKeys) (randomness : FieldMacToECMac.Randomness)
    (K : FieldMacToECMac.DigitValues) (inputKey : InputMacKey)
    (perms : FieldMacToECMac.GadgetPermutations) (pad : FieldMacToECMac.ExceptionPad)
    (input : AffineInput) (inputOnCurve : OnCurve input) :
    Garbling.decodePointMacs
        (FieldMacToECMac.expectedResult keys
          (FieldMacToECMac.rowsForOutputKeys keys randomness) K inputKey perms pad
          input).pointMacs
        (FieldMacToECMac.expectedResult keys
          (FieldMacToECMac.rowsForOutputKeys keys randomness) K inputKey perms pad
          input).exceptionDigits
        (FieldMacToECMac.expectedResult keys
          (FieldMacToECMac.rowsForOutputKeys keys randomness) K inputKey perms pad
          input).tripleDigits
        (affinePoint input inputOnCurve) =
      some ((Vector.ofFn fun index =>
        digitScalar (keys.get index).digit • affinePoint input inputOnCurve +
          (keys.get index).offset.point).toList) := by
  simp only [Garbling.decodePointMacs, FieldMacToECMac.expectedResult,
    FieldMacToECMac.evaluateRows, Vector.toList_ofFn]
  rw [zipOfFn, zipOfFn]
  apply optionMapMOfFn
  intro index
  simpa only [FieldMacToECMac.expectedResult, Vector.get_ofFn] using
    decodeExpectedRow keys randomness K inputKey perms pad input inputOnCurve index

def successfulOffsetRandomness [FieldCertificate]
    (offsets : FieldMacToECMac.SuccessfulOffsets) : OffsetRandomness := {
  freeOffsets := FieldMacToECMac.freeOffsetPoints offsets.free
  freeOffsetCount := by simp [FieldMacToECMac.freeOffsetPoints]
}

theorem successfulOffsetPoints [FieldCertificate] [GroupCertificate]
    (offsets : FieldMacToECMac.SuccessfulOffsets)
    (clamped : offsets.IsClamped) :
    (offsets.values.map FieldMacToECMac.AffineOffset.point).toList =
      construction.offsets (successfulOffsetRandomness offsets) := by
  simp only [FieldMacToECMac.SuccessfulOffsets.values, Vector.toList_map,
    Construction.offsets, clampOffsets, successfulOffsetRandomness]
  change FieldMacToECMac.AffineOffset.point offsets.first ::
      FieldMacToECMac.freeOffsetPoints offsets.free =
    -(radix • pointHorner radix (FieldMacToECMac.freeOffsetPoints offsets.free)) ::
      FieldMacToECMac.freeOffsetPoints offsets.free
  rw [clamped]
  rfl

private theorem encodeDigits_eq_zipWith [FieldCertificate] [GroupCertificate]
    (point : Point) (digits : List ScalarField) (offsets : List Point) :
    encodeDigits point digits offsets =
      List.zipWith (fun digit offset => digit • point + offset) digits offsets := by
  induction digits generalizing offsets with
  | nil => simp [encodeDigits]
  | cons digit digits inductionHypothesis =>
      cases offsets <;> simp [encodeDigits, inductionHypothesis]

private theorem vectorZipWithToList {n : Nat} {α β γ : Type}
    (f : α → β → γ) (left : Vector α n) (right : Vector β n) :
    (Vector.ofFn fun index => f (left.get index) (right.get index)).toList =
      List.zipWith f left.toList right.toList := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp only [Vector.toList_ofFn] at leftBound ⊢
    rw [List.getElem_ofFn, List.getElem_zipWith,
      Vector.getElem_toList, Vector.getElem_toList, Vector.get_eq_getElem,
      Vector.get_eq_getElem]

theorem outputKeyPoints [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (offsets : FieldMacToECMac.SuccessfulOffsets)
    (clamped : offsets.IsClamped) (point : Point) :
    (Vector.ofFn fun index =>
      digitScalar
          ((FieldMacToECMac.outputKeys construction scalar offsets).get index).digit • point +
        FieldMacToECMac.AffineOffset.point
          ((FieldMacToECMac.outputKeys construction scalar offsets).get index).offset).toList =
      construction.outputs scalar (successfulOffsetRandomness offsets) point := by
  let digits : Vector Digit FieldMacToECMac.outputMacCount :=
    ⟨(construction.digits scalar).toArray,
      by simpa [FieldMacToECMac.outputMacCount] using construction.digitCount scalar⟩
  calc
    (Vector.ofFn fun index =>
        digitScalar
            ((FieldMacToECMac.outputKeys construction scalar offsets).get index).digit • point +
          FieldMacToECMac.AffineOffset.point
            ((FieldMacToECMac.outputKeys construction scalar offsets).get index).offset).toList =
      (Vector.ofFn fun index =>
        digitScalar (digits.get index) • point +
          FieldMacToECMac.AffineOffset.point (offsets.values.get index)).toList := by
        simp [FieldMacToECMac.outputKeys, digits]
    _ = List.zipWith (fun digit offset => digit • point + offset)
        (digits.map digitScalar).toList
        (offsets.values.map FieldMacToECMac.AffineOffset.point).toList := by
      simpa only [Vector.get_map] using
        vectorZipWithToList (fun digit offset => digit • point + offset)
          (digits.map digitScalar)
          (offsets.values.map FieldMacToECMac.AffineOffset.point)
    _ = List.zipWith (fun digit offset => digit • point + offset)
        ((construction.digits scalar).map digitScalar)
        (construction.offsets (successfulOffsetRandomness offsets)) := by
      rw [successfulOffsetPoints offsets clamped]
      simp [digits]
    _ = construction.outputs scalar (successfulOffsetRandomness offsets) point := by
      rw [Construction.outputs, encodeDigits_eq_zipWith]

theorem decodeExpectedResult [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] (scalar : ScalarField)
    (offsets : FieldMacToECMac.SuccessfulOffsets) (clamped : offsets.IsClamped)
    (randomness : FieldMacToECMac.Randomness) (K : FieldMacToECMac.DigitValues)
    (inputKey : InputMacKey) (perms : FieldMacToECMac.GadgetPermutations)
    (pad : FieldMacToECMac.ExceptionPad)
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point) :
    Garbling.decodeResult
        (FieldMacToECMac.expectedResult (FieldMacToECMac.outputKeys construction scalar offsets)
          (FieldMacToECMac.rowsForOutputKeys
            (FieldMacToECMac.outputKeys construction scalar offsets) randomness)
          K inputKey perms pad input) =
      some (scalarMultiplication scalar point) := by
  have inputOnCurve : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
  have pointEq : affinePoint input inputOnCurve = point :=
    affinePoint_eq_of_decode input point decoded inputOnCurve
  have decodedPoint : decodePoint
      (FieldMacToECMac.expectedResult (FieldMacToECMac.outputKeys construction scalar offsets)
        (FieldMacToECMac.rowsForOutputKeys
          (FieldMacToECMac.outputKeys construction scalar offsets) randomness)
        K inputKey perms pad input).point = some point := decoded
  have step : Garbling.decodeResult
      (FieldMacToECMac.expectedResult (FieldMacToECMac.outputKeys construction scalar offsets)
        (FieldMacToECMac.rowsForOutputKeys
          (FieldMacToECMac.outputKeys construction scalar offsets) randomness)
        K inputKey perms pad input) =
      (Garbling.decodePointMacs
        (FieldMacToECMac.expectedResult (FieldMacToECMac.outputKeys construction scalar offsets)
          (FieldMacToECMac.rowsForOutputKeys
            (FieldMacToECMac.outputKeys construction scalar offsets) randomness)
          K inputKey perms pad input).pointMacs
        (FieldMacToECMac.expectedResult (FieldMacToECMac.outputKeys construction scalar offsets)
          (FieldMacToECMac.rowsForOutputKeys
            (FieldMacToECMac.outputKeys construction scalar offsets) randomness)
          K inputKey perms pad input).exceptionDigits
        (FieldMacToECMac.expectedResult (FieldMacToECMac.outputKeys construction scalar offsets)
          (FieldMacToECMac.rowsForOutputKeys
            (FieldMacToECMac.outputKeys construction scalar offsets) randomness)
          K inputKey perms pad input).tripleDigits
        point).map (pointHorner radix) := by
    unfold Garbling.decodeResult
    rw [decodedPoint]
  rw [step, ← pointEq,
    decodeRowsForOutputKeys (FieldMacToECMac.outputKeys construction scalar offsets) randomness
      K inputKey perms pad input inputOnCurve]
  simp only [Option.map_some]
  rw [outputKeyPoints scalar offsets clamped (affinePoint input inputOnCurve)]
  exact congrArg some
    (construction.correct scalar (successfulOffsetRandomness offsets)
      (affinePoint input inputOnCurve))

theorem pipelineEvaluateInvalid [FieldCertificate]
    (fixedKeyOracle : Cryptography.PermutationOracle PlanB.FixedIndex
      Cryptography.Block)
    (encPRFOracle : Cryptography.PermutationOracle EncPRF.PermutationIndex
      Cryptography.Block)
    (hashOracle : EncPRF.HashOracle) (table : PlanB.Public)
    (input : AffineInput) (inputMac : InputMac)
    (invalid : decodePoint input = none) :
    Pipeline.evaluate fixedKeyOracle encPRFOracle hashOracle table
      (BitInput.ofAffine input) inputMac = none := by
  simp [Pipeline.evaluate, BitInput.toAffineOfAffine, invalid]

private theorem optionBindSome {α β : Type} (result : Option α)
    (value : α) (output : β) (decode : α → Option β)
    (evaluated : result = some value) (decoded : decode value = some output) :
    result.bind decode = some output := by
  rw [evaluated]
  exact decoded

theorem evaluateCorrectInvalid [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] (scalar : NonZeroScalar)
    (randomness : Garbling.Randomness) (input : AffineInput)
    (invalid : decodePoint input = none) :
    Garbling.evaluate
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)
        (Garbling.garble construction scalar randomness).1
        (Garbling.encode (Garbling.garble construction scalar randomness).2
          (BitInput.ofAffine input)) =
      checkedScalarMultiplication scalar.value input := by
  change Garbling.evaluate
    (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)
    (Garbling.garble construction scalar randomness).1
    { input := BitInput.ofAffine input
      inputMac := randomness.inputMacKey.encode (BitInput.ofAffine input) } =
      checkedScalarMultiplication scalar.value input
  unfold Garbling.evaluate
  rw [pipelineEvaluateInvalid randomness.fixedKeyOracle
    randomness.encPRFOracle randomness.hashOracle
    (Garbling.garble construction scalar randomness).1 input
    (randomness.inputMacKey.encode (BitInput.ofAffine input)) invalid]
  simp [checkedScalarMultiplication, invalid]

theorem evaluateCorrectValid [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] (scalar : NonZeroScalar)
    (randomness : Garbling.Randomness) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    Garbling.evaluate
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)
        (Garbling.garble construction scalar randomness).1
        (Garbling.encode (Garbling.garble construction scalar randomness).2
          (BitInput.ofAffine input)) =
      checkedScalarMultiplication scalar.value input := by
  change Garbling.evaluate
    (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)
    (Garbling.garble construction scalar randomness).1
    { input := BitInput.ofAffine input
      inputMac := randomness.inputMacKey.encode (BitInput.ofAffine input) } =
      checkedScalarMultiplication scalar.value input
  unfold Garbling.evaluate
  change (Pipeline.evaluate randomness.fixedKeyOracle randomness.encPRFOracle
    randomness.hashOracle (Garbling.garble construction scalar randomness).1
    (BitInput.ofAffine input)
    (randomness.inputMacKey.encode (BitInput.ofAffine input))).bind
      Garbling.decodeResult = checkedScalarMultiplication scalar.value input
  have evaluated := Garbling.evaluateEncodeRows construction
    ({ scalar, randomness } : Garbling.EncodingKey)
    (PlanB.delivers randomness.fixedKeyOracle randomness.hashOracle) input point decoded
  simp only [Garbling.encode] at evaluated
  have offsetsClamped : randomness.offsets.IsClamped :=
    randomness.offsetsClamped
  have decodedRows := decodeExpectedResult scalar.value randomness.offsets
    offsetsClamped randomness.pointRandomness
    (Pipeline.digitK randomness.fixedKeyOracle randomness.hashOracle randomness.inputDelta
      (Pipeline.whitenedKey randomness.encPRFOracle randomness.hashOracle
        randomness.bridgeKey randomness.inputMacKey))
    (EncPRF.transformKey randomness.encPRFOracle
      (EncPRF.whiteningKeys randomness.hashOracle randomness.bridgeKey)
      randomness.inputMacKey)
    (Pipeline.gadgetPermutations randomness.fixedKeyOracle)
    randomness.exceptionPad input point decoded
  have bound := optionBindSome
    (Pipeline.evaluate randomness.fixedKeyOracle randomness.encPRFOracle
      randomness.hashOracle (Garbling.garble construction scalar randomness).1
      (BitInput.ofAffine input)
      (randomness.inputMacKey.encode (BitInput.ofAffine input)))
    (FieldMacToECMac.expectedResult
      (FieldMacToECMac.outputKeys construction scalar.value randomness.offsets)
      (FieldMacToECMac.rowsForOutputKeys
        (FieldMacToECMac.outputKeys construction scalar.value randomness.offsets)
        randomness.pointRandomness)
      (Pipeline.digitK randomness.fixedKeyOracle randomness.hashOracle randomness.inputDelta
      (Pipeline.whitenedKey randomness.encPRFOracle randomness.hashOracle
        randomness.bridgeKey randomness.inputMacKey))
      (EncPRF.transformKey randomness.encPRFOracle
        (EncPRF.whiteningKeys randomness.hashOracle randomness.bridgeKey)
        randomness.inputMacKey)
      (Pipeline.gadgetPermutations randomness.fixedKeyOracle)
      randomness.exceptionPad input)
    (scalarMultiplication scalar.value point) Garbling.decodeResult evaluated decodedRows
  exact bound.trans (by simp [checkedScalarMultiplication, decoded])

theorem evaluateCorrect [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] (scalar : NonZeroScalar)
    (randomness : Garbling.Randomness) (input : AffineInput) :
    Garbling.evaluate
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)
        (Garbling.garble construction scalar randomness).1
        (Garbling.encode (Garbling.garble construction scalar randomness).2
          (BitInput.ofAffine input)) =
      checkedScalarMultiplication scalar.value input := by
  cases decoded : decodePoint input with
  | none => exact evaluateCorrectInvalid scalar randomness input decoded
  | some point => exact evaluateCorrectValid scalar randomness input point decoded

/-- Every random tape gives the required evaluation result. -/
theorem perfectCorrectness [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] :
    GarbledCircuit.PerfectCorrectness (Garbling.garbledCircuit construction)
      (fun randomness =>
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)) := by
  intro securityParameter scalar randomness input
  exact congrArg some (evaluateCorrect scalar randomness input)


end Kriterion.ArgoMAC.JacobianMixed
