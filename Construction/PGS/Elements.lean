/-
This file defines the Plan B element index families.
Every `DigitAdaptor` of the baseline becomes one element index; the delivered value keeps
its shape `slope * coordinate + offset`, so the row algebra is untouched.
The plan source is `2026-09-17-planB.md`, section D.4.
-/

import Construction.PGS.Params

namespace Kriterion.ArgoMAC.PlanB

/-- The x-type element slots of one digit: two on the `X` row, one on the sign row (the
`Y` slot), one on the `Z` row. The sign row's `cubic` rides on `x²`. -/
inductive XElement
  | rowX_x7
  | rowX_x9
  | rowY_cubic
  | rowZ_x9
deriving DecidableEq

instance : Fintype XElement :=
  ⟨{.rowX_x7, .rowX_x9, .rowY_cubic, .rowZ_x9}, fun value => by
    cases value <;> simp⟩

/-- The y-type element slots of one digit: one on the `X` row and two on the sign row. -/
inductive YElement
  | rowX_y10
  | rowY_y8
  | rowY_y10
deriving DecidableEq

instance : Fintype YElement :=
  ⟨{.rowX_y10, .rowY_y8, .rowY_y10}, fun value => by cases value <;> simp⟩

/-- The x-type element slots of the curve-membership check. -/
inductive CurveXElement
  | x3
  | x5
  | x7
deriving DecidableEq

instance : Fintype CurveXElement :=
  ⟨{.x3, .x5, .x7}, fun value => by cases value <;> simp⟩

/-- The y-type element slots of the curve-membership check. -/
inductive CurveYElement
  | y4
  | y6
deriving DecidableEq

instance : Fintype CurveYElement :=
  ⟨{.y4, .y6}, fun value => by cases value <;> simp⟩

/-- The number of x-type element slots one digit consumes. -/
abbrev xSlotsPerDigit : Nat := 4

/-- The number of y-type element slots one digit consumes. -/
abbrev ySlotsPerDigit : Nat := 3

/-- The slot of an x-type element inside its digit. The three row collectors (`rowX_x9`,
`rowY_cubic`, `rowZ_x9`) sit at slots `1`, `2`, `3`, and the free element `rowX_x7` at slot `0`. -/
def XElement.slot : XElement → Fin xSlotsPerDigit
  | .rowX_x7 => 0
  | .rowX_x9 => 1
  | .rowY_cubic => 2
  | .rowZ_x9 => 3

/-- The slot of a y-type element inside its digit. -/
def YElement.slot : YElement → Fin ySlotsPerDigit
  | .rowX_y10 => 0
  | .rowY_y8 => 1
  | .rowY_y10 => 2

/-- The slot of a curve x-type element after the `91 * 4` digit slots. -/
def CurveXElement.slot : CurveXElement → Fin 3
  | .x3 => 0
  | .x5 => 1
  | .x7 => 2

/-- The slot of a curve y-type element after the `91 * 3` digit slots. -/
def CurveYElement.slot : CurveYElement → Fin 2
  | .y4 => 0
  | .y6 => 1

theorem XElement.slot_injective : Function.Injective XElement.slot := by decide

theorem YElement.slot_injective : Function.Injective YElement.slot := by decide

theorem CurveXElement.slot_injective : Function.Injective CurveXElement.slot := by decide

theorem CurveYElement.slot_injective : Function.Injective CurveYElement.slot := by decide

/-- The `pointX` lane's element index: `91 * 4` digit slots.

The curve check lives in its *own* lane (system A), so the point lanes carry the digit slots
alone; the two families no longer share a vector. -/
def xElementIndex (digit : Fin digitCount) (element : XElement) : Fin pointElementCountX :=
  ⟨xSlotsPerDigit * digit.val + element.slot.val, by
    have hd := digit.isLt
    have hs := element.slot.isLt
    unfold digitCount at hd
    unfold xSlotsPerDigit at hs
    unfold pointElementCountX xSlotsPerDigit
    omega⟩

/-- The `curveX` lane's element index: `0`, `1`, `2`. -/
def curveXElementIndex (element : CurveXElement) : Fin curveElementCountX :=
  ⟨element.slot.val, by
    have hs := element.slot.isLt
    unfold curveElementCountX
    omega⟩

/-- The `pointY` lane's element index: `91 * 3` digit slots. -/
def yElementIndex (digit : Fin digitCount) (element : YElement) : Fin pointElementCountY :=
  ⟨ySlotsPerDigit * digit.val + element.slot.val, by
    have hd := digit.isLt
    have hs := element.slot.isLt
    unfold digitCount at hd
    unfold ySlotsPerDigit at hs
    unfold pointElementCountY ySlotsPerDigit
    omega⟩

/-- The `curveY` lane's element index: `0`, `1`. -/
def curveYElementIndex (element : CurveYElement) : Fin curveElementCountY :=
  ⟨element.slot.val, by
    have hs := element.slot.isLt
    unfold curveElementCountY
    omega⟩

theorem xElementIndex_injective :
    Function.Injective fun pair : Fin digitCount × XElement => xElementIndex pair.1 pair.2 := by
  rintro ⟨digit, element⟩ ⟨digit', element'⟩ equality
  have value : xSlotsPerDigit * digit.val + element.slot.val
      = xSlotsPerDigit * digit'.val + element'.slot.val := congrArg Fin.val equality
  have hs := element.slot.isLt
  have hs' := element'.slot.isLt
  unfold xSlotsPerDigit at value hs hs'
  have digits : digit.val = digit'.val := by omega
  have slots : element.slot.val = element'.slot.val := by omega
  have : element = element' := XElement.slot_injective (Fin.ext slots)
  simp [Fin.ext_iff, digits, this]

theorem yElementIndex_injective :
    Function.Injective fun pair : Fin digitCount × YElement => yElementIndex pair.1 pair.2 := by
  rintro ⟨digit, element⟩ ⟨digit', element'⟩ equality
  have value : ySlotsPerDigit * digit.val + element.slot.val
      = ySlotsPerDigit * digit'.val + element'.slot.val := congrArg Fin.val equality
  have hs := element.slot.isLt
  have hs' := element'.slot.isLt
  unfold ySlotsPerDigit at value hs hs'
  have digits : digit.val = digit'.val := by omega
  have slots : element.slot.val = element'.slot.val := by omega
  have : element = element' := YElement.slot_injective (Fin.ext slots)
  simp [Fin.ext_iff, digits, this]

theorem curveXElementIndex_injective : Function.Injective curveXElementIndex := by
  intro element element' equality
  exact CurveXElement.slot_injective (Fin.ext (congrArg Fin.val equality))

theorem curveYElementIndex_injective : Function.Injective curveYElementIndex := by
  intro element element' equality
  exact CurveYElement.slot_injective (Fin.ext (congrArg Fin.val equality))

end Kriterion.ArgoMAC.PlanB
