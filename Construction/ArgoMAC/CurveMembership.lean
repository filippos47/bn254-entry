/-
This file defines the curve-membership check.

Plan B keeps DFB section 7.2's bridge polynomial `q(x, y) = (y² − x³ − 3) · Δ + ν` and its
masking algebra unchanged; only the delivery of the five affine element values changes. The
check therefore publishes three field constants (96 bytes) and consumes five element slots --
three x-type and two y-type -- which live inside the same 733-element vector the row layer
uses, so they cost no separate switch system.
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

/-- The three published constants `c0, c1, c2`. -/
abbrev Table := BaseField × BaseField × BaseField

/-- The coordinate an element slot is chunked against. -/
def coordValue (input : AffineInput) : Element → BaseField
  | .inl _ => input.x
  | .inr _ => input.y

@[simp] theorem coordValue_inl (input : AffineInput) (element : CurveXElement) :
    coordValue input (.inl element) = input.x := rfl

@[simp] theorem coordValue_inr (input : AffineInput) (element : CurveYElement) :
    coordValue input (.inr element) = input.y := rfl

/-- The slope of each curve element, from plan D.4: the garbler samples `r1` and `r2` and the
chain `x3 → x5 → x7`, `y4 → y6` derives the rest from the element offsets. -/
def slopes (r1 r2 : BaseField) (K : Values) : Values
  | .inl .x3 => -r1
  | .inl .x5 => -K (.inl .x3)
  | .inl .x7 => -K (.inl .x5)
  | .inr .y4 => -r2
  | .inr .y6 => -K (.inr .y4)

/-- The value the evaluator obtains for each curve element slot. -/
def delivered (r1 r2 : BaseField) (K : Values) (input : AffineInput) : Values :=
  fun element => slopes r1 r2 K element * coordValue input element + K element

/-- The garbler samples `r1` and `r2`; the element offsets supply `r3` through `r7`. -/
def garble (bridgeKey mask r1 r2 : BaseField) (K : Values) : Table :=
  (3 * mask + bridgeKey - K (.inr .y6) - K (.inl .x7), mask + r1, -mask + r2)

/-- The bridge value: `c0 + c1 x³ + c2 y² + x3 · x² + y4 · y + x5 · x + y6 + x7`. -/
def evaluate (table : Table) (input : AffineInput) (values : Values) : BaseField :=
  table.1 + table.2.1 * input.x ^ 3 + table.2.2 * input.y ^ 2 +
    values (.inl .x3) * input.x ^ 2 + values (.inr .y4) * input.y +
    values (.inl .x5) * input.x + values (.inr .y6) + values (.inl .x7)

/-- Correct element values produce the membership polynomial. -/
theorem evaluateEncoded (bridgeKey mask r1 r2 : BaseField) (K : Values) (input : AffineInput) :
    evaluate (garble bridgeKey mask r1 r2 K) input (delivered r1 r2 K input) =
      bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2) := by
  simp only [evaluate, garble, delivered, slopes, coordValue]
  ring

/-- Correct element values release the bridge key for an on-curve input. -/
theorem evaluateEncodedOnCurve (bridgeKey mask r1 r2 : BaseField) (K : Values)
    (input : AffineInput) (inputOnCurve : OnCurve input) :
    evaluate (garble bridgeKey mask r1 r2 K) input (delivered r1 r2 K input) = bridgeKey := by
  rw [evaluateEncoded]
  rw [show input.x ^ 3 + 3 - input.y ^ 2 = 0 by rw [inputOnCurve]; ring]
  ring

end Kriterion.ArgoMAC.CurveMembership
