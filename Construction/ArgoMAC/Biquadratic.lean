/-
This file defines the three sparse biquadratic rows of one recoded digit.

A row does not garble its own adaptors: it consumes the affine element values the
projectivized garbling scheme delivers. A digit consumes seven element slots -- four against the
`x` coordinate and three against the `y` coordinate -- and publishes exactly **three** field
elements, one per row (`RowGamma`: `gX`, `gY`, `gZ`).

The slopes carry the *true* scaled row coefficients (`Coordinates.rows offset digit ρ τ`), so the
rows need no randomisers of their own: the element offsets `K e = O[e]`, which the projectivized
garbling scheme forces to be uniform, are the only masks. Each row's published constant absorbs
the offsets of its collector and of the elements whose offsets reach the constant monomial:

* `X = gX + x7 · x + x9 + y10`, with slopes `c4`, `c1 − K[x7]`, `c2`;
* the sign row, in the `Y` slot, `S = gY · x² + cubic · x² + y8 · y + y10`, with slopes `-s`,
  `c5 + s` and `c2 − K[y8]`, where `s = (c0 − K[y10]) / 3`;
* `Z = gZ + x9`, with slope `c1`.

The `Y` slot carries Lazar's sign row `S = τ² S₀` (`Coordinates.signCoefficients`), whose
support is `1, y, x², y²`. Its `cubic` element rides on `x²` and contributes `-s x³`, which the
curve equation turns into `s (3 − y²)`; the `y8` slope absorbs the `y²` part and
`3 s = c0 − K[y10]` supplies the constant monomial. The row has no `x y` term, so it needs no
`mixed` element. It is exact on the curve (`evaluateEncodedY`); off the curve it is off by
`s (y² − x³ − 3)` (`evaluateEncodedY_raw`), and the evaluator never reaches it there, because it
refuses an off-curve input before any query. The `X` and `Z` rows are exact everywhere.
-/

import Construction.ArgoMAC.Coordinates
import Construction.ArgoMAC.Input
import Construction.ArgoMAC.Public
import Construction.PGS.Elements

namespace Kriterion.ArgoMAC.Biquadratic

open BN254 Kriterion.ArgoMAC.PlanB

/-- The seven element slots one digit consumes: four x-type and three y-type. -/
abbrev Element := XElement ⊕ YElement

/-- One value per element slot of a digit. The garbler uses this for the element offsets
`K e = b_e = O[e]`, the evaluator for the delivered values `a_e * coord + b_e`. -/
abbrev Values := Element → BaseField

/-- The coordinate an element slot is chunked against. -/
def coordValue (input : AffineInput) : Element → BaseField
  | .inl _ => input.x
  | .inr _ => input.y

@[simp] theorem coordValue_inl (input : AffineInput) (element : XElement) :
    coordValue input (.inl element) = input.x := rfl

@[simp] theorem coordValue_inr (input : AffineInput) (element : YElement) :
    coordValue input (.inr element) = input.y := rfl

/-- `3⁻¹` in the base field. -/
def inv3 : BaseField := (3 : BaseField)⁻¹

/-- `3` is a unit of the base field (`p` is not a multiple of `3`). -/
theorem three_mul_inv3 : (3 : BaseField) * inv3 = 1 := by
  have coprime : Nat.Coprime 3 baseFieldModulus := by
    unfold Nat.Coprime baseFieldModulus
    decide
  have := ZMod.coe_mul_inv_eq_one 3 coprime
  simpa [inv3] using this

/-! ### Slopes

`K e` is the element offset the projectivized garbling scheme delivers -- the PGS output mask
`O[e]`, which the garbler can compute from the tape alone before any slope exists. That is what
keeps the chains `x7 → x9`, `y10 → (cubic, y8)` and `y8 → y10` resolvable in one pass: every
slope reads offsets only, never another slope. -/

/-- The sign row's curve multiplier `s = (c0 − K[y10]) / 3`. -/
def cubicSlope (rows : Coordinates.Rows) (K : Values) : BaseField :=
  (rows.y.constant - K (.inr .rowY_y10)) * inv3

/-- The slope of every element slot of one digit: the true scaled row coefficients. -/
def slopes (rows : Coordinates.Rows) (K : Values) : Values
  | .inl .rowX_x7 => rows.x.xSquared
  | .inl .rowX_x9 => rows.x.x - K (.inl .rowX_x7)
  | .inr .rowX_y10 => rows.x.y
  | .inl .rowY_cubic => -cubicSlope rows K
  | .inr .rowY_y8 => rows.y.ySquared + cubicSlope rows K
  | .inr .rowY_y10 => rows.y.y - K (.inr .rowY_y8)
  | .inl .rowZ_x9 => rows.z.x

/-- The value the evaluator obtains for every element slot of one digit. -/
def delivered (rows : Coordinates.Rows) (K : Values) (input : AffineInput) : Values :=
  fun element => slopes rows K element * coordValue input element + K element

/-! ### Garbling and evaluation -/

/-- The three published constants of one digit: each row's constant absorbs the offsets that
reach its constant monomial (`X`: `x9`, `y10`; `Z`: `x9`), and the sign row's `x²` coefficient
absorbs the `cubic` offset. -/
def garble (rows : Coordinates.Rows) (K : Values) : RowGamma := {
  gX := rows.x.constant - K (.inl .rowX_x9) - K (.inr .rowX_y10)
  gY := rows.y.xSquared - K (.inl .rowY_cubic)
  gZ := rows.z.constant - K (.inl .rowZ_x9) }

/-- The `X` row value: `gX + x7 · x + x9 + y10`. -/
def evaluateX (gamma : RowGamma) (input : AffineInput) (values : Values) : BaseField :=
  gamma.gX + values (.inl .rowX_x7) * input.x + values (.inl .rowX_x9) + values (.inr .rowX_y10)

/-- The sign row value: `gY · x² + cubic · x² + y8 · y + y10`. -/
def evaluateY (gamma : RowGamma) (input : AffineInput) (values : Values) : BaseField :=
  gamma.gY * input.x ^ 2 + values (.inl .rowY_cubic) * input.x ^ 2 +
    values (.inr .rowY_y8) * input.y + values (.inr .rowY_y10)

/-- The `Z` row value: `gZ + x9`. -/
def evaluateZ (gamma : RowGamma) (values : Values) : BaseField :=
  gamma.gZ + values (.inl .rowZ_x9)

/-! ### Correctness

Each row's published constant cancels the offsets of the elements it consumes, and each chained
slope cancels the offset of the element it reads. -/

/-- The `X` row evaluates to its four-monomial value. -/
theorem evaluateEncodedX (rows : Coordinates.Rows) (K : Values) (input : AffineInput) :
    evaluateX (garble rows K) input (delivered rows K input) =
      rows.x.constant + rows.x.x * input.x + rows.x.y * input.y +
        rows.x.xSquared * input.x ^ 2 := by
  simp only [evaluateX, garble, delivered, slopes, coordValue]
  ring

/-- `3 s = c0 − K[y10]`. -/
theorem three_mul_cubicSlope (rows : Coordinates.Rows) (K : Values) :
    3 * cubicSlope rows K = rows.y.constant - K (.inr .rowY_y10) := by
  rw [cubicSlope, mul_comm, mul_assoc, mul_comm inv3, three_mul_inv3, mul_one]

/-- The sign row value at any input: its four-monomial value plus `s` times the curve
equation. -/
theorem evaluateEncodedY_raw (rows : Coordinates.Rows) (K : Values) (input : AffineInput) :
    evaluateY (garble rows K) input (delivered rows K input) =
      rows.y.constant + rows.y.y * input.y + rows.y.xSquared * input.x ^ 2 +
        rows.y.ySquared * input.y ^ 2 +
        cubicSlope rows K * (input.y ^ 2 - input.x ^ 3 - 3) := by
  have three := three_mul_cubicSlope rows K
  simp only [evaluateY, garble, delivered, slopes, coordValue]
  linear_combination three

/-- The sign row evaluates to its four-monomial value on the curve. -/
theorem evaluateEncodedY (rows : Coordinates.Rows) (K : Values) (input : AffineInput)
    (onCurve : OnCurve input) :
    evaluateY (garble rows K) input (delivered rows K input) =
      rows.y.constant + rows.y.y * input.y + rows.y.xSquared * input.x ^ 2 +
        rows.y.ySquared * input.y ^ 2 := by
  have curve : input.y ^ 2 = input.x ^ 3 + 3 := onCurve
  rw [evaluateEncodedY_raw]
  linear_combination cubicSlope rows K * curve

/-- The `Z` row evaluates to its two-monomial value. -/
theorem evaluateEncodedZ (rows : Coordinates.Rows) (K : Values) (input : AffineInput) :
    evaluateZ (garble rows K) (delivered rows K input) =
      rows.z.constant + rows.z.x * input.x := by
  simp only [evaluateZ, garble, delivered, slopes, coordValue]
  ring

end Kriterion.ArgoMAC.Biquadratic
