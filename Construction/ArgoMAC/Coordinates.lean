/-
This file defines the Jacobian mixed-addition rows of the BaBe paper
(`gc_argomac_new.tex`, equations `c2_coeffs_X`, `c2_coeffs_Y`, `c2_coeffs_Z`).
-/

import BN254
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Kriterion.ArgoMAC.Coordinates

/-- `Coefficients` contains the coefficients for the six input monomials. -/
structure Coefficients where
  constant : BN254.BaseField
  x : BN254.BaseField
  y : BN254.BaseField
  xy : BN254.BaseField
  xSquared : BN254.BaseField
  ySquared : BN254.BaseField
deriving DecidableEq

/-- `evaluate` computes one coordinate from the six input monomials. -/
def evaluate (coefficients : Coefficients) (input : BN254.AffineInput) :
    BN254.BaseField :=
  coefficients.constant + coefficients.x * input.x + coefficients.y * input.y +
    coefficients.xy * (input.x * input.y) + coefficients.xSquared * input.x ^ 2 +
    coefficients.ySquared * input.y ^ 2

/-- `jacobianX` is `(y - ky)^2 - (x - kx)^2 (x + kx)`, the Jacobian X of `P + K`. -/
def jacobianX (offset input : BN254.AffineInput) : BN254.BaseField :=
  (input.y - offset.y) ^ 2 - (input.x - offset.x) ^ 2 * (input.x + offset.x)

/-- `jacobianY` is `(y - ky) (kx (x - kx)^2 - X) - ky (x - kx)^3`. -/
def jacobianY (offset input : BN254.AffineInput) : BN254.BaseField :=
  (input.y - offset.y) * (offset.x * (input.x - offset.x) ^ 2 - jacobianX offset input) -
    offset.y * (input.x - offset.x) ^ 3

/-- `jacobianZ` is `x - kx`. -/
def jacobianZ (offset input : BN254.AffineInput) : BN254.BaseField :=
  input.x - offset.x

/-- `xCoefficients` is the degree-two form of `jacobianX` on the curve. -/
def xCoefficients (offset : BN254.AffineInput) : Coefficients := {
  constant := 6
  x := offset.x ^ 2
  y := -2 * offset.y
  xy := 0
  xSquared := offset.x
  ySquared := 0
}

/-- `yCoefficients` is the degree-two form of `jacobianY` on the curve. -/
def yCoefficients (offset : BN254.AffineInput) : Coefficients := {
  constant := 9 * offset.y
  x := 0
  y := -offset.x ^ 3 - 12
  xy := -3 * offset.x ^ 2
  xSquared := 3 * offset.x * offset.y
  ySquared := offset.y
}

/-- `zCoefficients` is `jacobianZ`. -/
def zCoefficients (offset : BN254.AffineInput) : Coefficients := {
  constant := -offset.x
  x := 1
  y := 0
  xy := 0
  xSquared := 0
  ySquared := 0
}

/-- On the curve the X row equals the Jacobian X formula. -/
theorem evaluateX (offset input : BN254.AffineInput)
    (offsetOnCurve : BN254.OnCurve offset) (inputOnCurve : BN254.OnCurve input) :
    evaluate (xCoefficients offset) input = jacobianX offset input := by
  simp only [evaluate, xCoefficients, jacobianX]
  unfold BN254.OnCurve at offsetOnCurve inputOnCurve
  linear_combination (-1) * inputOnCurve + (-1) * offsetOnCurve

/-- On the curve the Y row equals the Jacobian Y formula. -/
theorem evaluateY (offset input : BN254.AffineInput)
    (offsetOnCurve : BN254.OnCurve offset) (inputOnCurve : BN254.OnCurve input) :
    evaluate (yCoefficients offset) input = jacobianY offset input := by
  simp only [evaluate, yCoefficients, jacobianY, jacobianX]
  unfold BN254.OnCurve at offsetOnCurve inputOnCurve
  linear_combination (input.y - 2 * offset.y) * inputOnCurve +
    (3 * input.y - offset.y) * offsetOnCurve

/-- The Z row equals the Jacobian Z formula everywhere. -/
theorem evaluateZ (offset input : BN254.AffineInput) :
    evaluate (zCoefficients offset) input = jacobianZ offset input := by
  simp only [evaluate, zCoefficients, jacobianZ]
  ring

/-- At `x = kx` the X row is `2 ky (ky - y)`. -/
theorem exceptionalX (offset input : BN254.AffineInput)
    (offsetOnCurve : BN254.OnCurve offset) (inputOnCurve : BN254.OnCurve input)
    (sameX : input.x = offset.x) :
    evaluate (xCoefficients offset) input = 2 * offset.y * (offset.y - input.y) := by
  simp only [evaluate, xCoefficients]
  rw [sameX]
  unfold BN254.OnCurve at offsetOnCurve
  linear_combination (-2) * offsetOnCurve

/-- At `x = kx` the Y row is `4 (ky - y) ky^2`. -/
theorem exceptionalY (offset input : BN254.AffineInput)
    (offsetOnCurve : BN254.OnCurve offset) (inputOnCurve : BN254.OnCurve input)
    (sameX : input.x = offset.x) :
    evaluate (yCoefficients offset) input = 4 * (offset.y - input.y) * offset.y ^ 2 := by
  simp only [evaluate, yCoefficients]
  rw [sameX]
  unfold BN254.OnCurve at offsetOnCurve inputOnCurve
  rw [sameX] at inputOnCurve
  linear_combination offset.y * inputOnCurve +
    (4 * input.y - 4 * offset.y) * offsetOnCurve

/-- At `x = kx` the Z row vanishes. -/
theorem exceptionalZ (offset input : BN254.AffineInput) (sameX : input.x = offset.x) :
    evaluate (zCoefficients offset) input = 0 := by
  simp only [evaluate, zCoefficients]
  rw [sameX]
  ring

/-- `scale` applies one digit endomorphism and the Jacobian weights of one randomizer.
`weight` is the Jacobian weight of the row (2 for X, 3 for Y, 1 for Z); `fallback` is the
constant the row takes for digit zero, before the randomizer power. -/
def scale (endomorphismBase : Option BN254.BaseField) (randomizer : BN254.BaseField)
    (weight : Nat) (fallback : BN254.BaseField) (coefficients : Coefficients) : Coefficients :=
  let power := randomizer ^ weight
  match endomorphismBase with
  | none => {
      constant := fallback * power
      x := 0
      y := 0
      xy := 0
      xSquared := 0
      ySquared := 0 }
  | some phi =>
      let xScale := phi ^ 4
      let yScale := phi ^ 3
      { constant := coefficients.constant * power
        x := coefficients.x * xScale * power
        y := coefficients.y * yScale * power
        xy := coefficients.xy * (xScale * yScale) * power
        xSquared := coefficients.xSquared * xScale ^ 2 * power
        ySquared := coefficients.ySquared * yScale ^ 2 * power }

theorem evaluateScaleSome (phi randomizer : BN254.BaseField) (weight : Nat)
    (fallback : BN254.BaseField) (coefficients : Coefficients) (input : BN254.AffineInput) :
    evaluate (scale (some phi) randomizer weight fallback coefficients) input =
      randomizer ^ weight * evaluate coefficients
        { x := phi ^ 4 * input.x, y := phi ^ 3 * input.y } := by
  simp [scale, evaluate]
  ring

theorem evaluateScaleNone (randomizer : BN254.BaseField) (weight : Nat)
    (fallback : BN254.BaseField) (coefficients : Coefficients) (input : BN254.AffineInput) :
    evaluate (scale none randomizer weight fallback coefficients) input =
      fallback * randomizer ^ weight := by
  simp [scale, evaluate]

/-- `Rows` contains the three Jacobian rows for one output MAC. -/
structure Rows where
  x : Coefficients
  y : Coefficients
  z : Coefficients

/-- `rows` applies the digit endomorphism and the Jacobian weights of one randomizer. -/
def rows (offset : BN254.AffineInput) (endomorphismBase : Option BN254.BaseField)
    (randomizer : BN254.BaseField) : Rows := {
  x := scale endomorphismBase randomizer 2 offset.x (xCoefficients offset)
  y := scale endomorphismBase randomizer 3 offset.y (yCoefficients offset)
  z := scale endomorphismBase randomizer 1 1 (zCoefficients offset)
}

theorem evaluateRowsSome (offset input : BN254.AffineInput)
    (phi randomizer : BN254.BaseField) :
    let transformed : BN254.AffineInput :=
      { x := phi ^ 4 * input.x, y := phi ^ 3 * input.y }
    evaluate (rows offset (some phi) randomizer).x input =
        randomizer ^ 2 * evaluate (xCoefficients offset) transformed ∧
      evaluate (rows offset (some phi) randomizer).y input =
        randomizer ^ 3 * evaluate (yCoefficients offset) transformed ∧
      evaluate (rows offset (some phi) randomizer).z input =
        randomizer * evaluate (zCoefficients offset) transformed := by
  simp [rows, evaluateScaleSome]

/-- A sixth-root endomorphism preserves the affine curve equation. -/
theorem transformedOnCurve (phi : BN254.BaseField) (phiSix : phi ^ 6 = 1)
    (input : BN254.AffineInput) (inputOnCurve : BN254.OnCurve input) :
    BN254.OnCurve { x := phi ^ 4 * input.x, y := phi ^ 3 * input.y } := by
  have phiTwelve : phi ^ 12 = 1 := by
    calc
      phi ^ 12 = (phi ^ 6) ^ 2 := by ring
      _ = 1 := by rw [phiSix]; simp
  simp only [BN254.OnCurve, mul_pow]
  rw [show (phi ^ 3) ^ 2 = phi ^ 6 by ring,
    show (phi ^ 4) ^ 3 = phi ^ 12 by ring, phiSix, phiTwelve]
  simpa [BN254.OnCurve] using inputOnCurve

end Kriterion.ArgoMAC.Coordinates
