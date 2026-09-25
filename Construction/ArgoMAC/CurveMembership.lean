/-
This file defines the curve-membership check.

Plan B keeps DFB section 7.2's bridge polynomial `q(x, y) = t + Δ · (x³ + 3 − y²)`; only the
delivery of the five affine element values changes. The mask `Δ` rides in the slopes of `x3`
(`+Δ`, read with `x²`) and `y4` (`−Δ`, read with `y`), so the check publishes **one** field
constant and consumes five element slots -- three x-type and two y-type -- in the two system-A
lanes.
The plan source is `2026-09-17-planB.md`, sections D.4 and Task 17.
-/

import Construction.ArgoMAC.Input
import Construction.PGS.Elements

namespace Kriterion.ArgoMAC.CurveMembership

open BN254 Kriterion.ArgoMAC.PlanB

/-- The five element slots the curve check consumes: three x-type and two y-type. -/
abbrev Element := CurveXElement ⊕ CurveYElement

/-- One value per element slot of the curve check. -/
abbrev Values := Element → BaseField

/-- The one published constant `c0`. -/
abbrev Table := BaseField

/-- The coordinate an element slot is chunked against. -/
def coordValue (input : AffineInput) : Element → BaseField
  | .inl _ => input.x
  | .inr _ => input.y

@[simp] theorem coordValue_inl (input : AffineInput) (element : CurveXElement) :
    coordValue input (.inl element) = input.x := rfl

@[simp] theorem coordValue_inr (input : AffineInput) (element : CurveYElement) :
    coordValue input (.inr element) = input.y := rfl

/-- The slope of each curve element. The mask `Δ` itself is the slope of `x3` (read with `x²`)
and `−Δ` that of `y4` (read with `y`); the chain `x3 → x5 → x7`, `y4 → y6` derives the rest from
the element offsets. -/
def slopes (mask : BaseField) (K : Values) : Values
  | .inl .x3 => mask
  | .inl .x5 => -K (.inl .x3)
  | .inl .x7 => -K (.inl .x5)
  | .inr .y4 => -mask
  | .inr .y6 => -K (.inr .y4)

/-- The value the evaluator obtains for each curve element slot. -/
def delivered (mask : BaseField) (K : Values) (input : AffineInput) : Values :=
  fun element => slopes mask K element * coordValue input element + K element

/-- The one published constant `c0 = t + 3 Δ − K[y6] − K[x7]`. -/
def garble (bridgeKey mask : BaseField) (K : Values) : Table :=
  bridgeKey + 3 * mask - K (.inr .y6) - K (.inl .x7)

/-- The bridge value: `c0 + x3 · x² + y4 · y + x5 · x + y6 + x7`. -/
def evaluate (table : Table) (input : AffineInput) (values : Values) : BaseField :=
  table + values (.inl .x3) * input.x ^ 2 + values (.inr .y4) * input.y +
    values (.inl .x5) * input.x + values (.inr .y6) + values (.inl .x7)

/-- Correct element values produce the membership polynomial. -/
theorem evaluateEncoded (bridgeKey mask : BaseField) (K : Values) (input : AffineInput) :
    evaluate (garble bridgeKey mask K) input (delivered mask K input) =
      bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2) := by
  simp only [evaluate, garble, delivered, slopes, coordValue]
  ring

/-- Correct element values release the bridge key for an on-curve input. -/
theorem evaluateEncodedOnCurve (bridgeKey mask : BaseField) (K : Values)
    (input : AffineInput) (inputOnCurve : OnCurve input) :
    evaluate (garble bridgeKey mask K) input (delivered mask K input) = bridgeKey := by
  rw [evaluateEncoded]
  rw [show input.x ^ 3 + 3 - input.y ^ 2 = 0 by rw [inputOnCurve]; ring]
  ring

end Kriterion.ArgoMAC.CurveMembership
