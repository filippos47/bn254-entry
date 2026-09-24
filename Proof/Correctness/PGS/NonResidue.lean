/-
This file proves that `3` is not a square in the BN254 base field (Euler's criterion; the proof is
`Lazar955/bn254-planb`'s, for the four-element `Y` row).

Two consequences carry the four-element `Y` row. Every curve point has `x ≠ 0`, so the opening
may divide by `x ^ 2`, the coefficient of the `Y` row's collector `rowY_cubic`. No field element
has `y ^ 2 = 3`, so a map may divide by `y ^ 2 - 3` for every input, on or off the curve.
-/

import Mathlib.Tactic.ReduceModChar
import ScalarMultiplication

namespace Kriterion.ArgoMAC.PlanB

open BN254

private theorem three_pow_half_literal :
    (3 : ZMod 21888242871839275222246405745257275088696311157297823662689037894645226208583) ^
      10944121435919637611123202872628637544348155578648911831344518947322613104291 = -1 := by
  reduce_mod_char

/-- Euler's criterion value: three is a quadratic non-residue in the base field. -/
theorem three_pow_half [FieldCertificate] : (3 : BaseField) ^ (baseFieldModulus / 2) = -1 := by
  have half : baseFieldModulus / 2 =
      10944121435919637611123202872628637544348155578648911831344518947322613104291 := by
    unfold baseFieldModulus; norm_num
  rw [half]
  exact three_pow_half_literal

/-- Three is not a square in the base field. -/
theorem three_not_square [FieldCertificate] : ¬ IsSquare (3 : BaseField) := by
  intro square
  have three : (3 : BaseField) ≠ 0 := by
    intro zero
    have power : (3 : BaseField) ^ (baseFieldModulus / 2) = -1 := three_pow_half
    rw [zero, zero_pow (by unfold baseFieldModulus; norm_num)] at power
    have one : (1 : BaseField) = 0 := by linear_combination power
    exact one_ne_zero one
  have euler := (ZMod.euler_criterion baseFieldModulus three).mp square
  rw [three_pow_half] at euler
  have two : (2 : BaseField) = 0 := by linear_combination -euler
  have value : (2 : BaseField).val = 2 := by
    change ((2 : ℕ) : BaseField).val = 2
    exact ZMod.val_natCast_of_lt (by unfold baseFieldModulus; norm_num)
  rw [two, ZMod.val_zero] at value
  exact absurd value (by decide)

/-- No field element squares to `3`. -/
theorem sq_sub_three_ne_zero [FieldCertificate] (value : BaseField) : value ^ 2 - 3 ≠ 0 := by
  intro zero
  exact three_not_square ⟨value, by linear_combination -zero⟩

/-- Every curve point has a nonzero x-coordinate: `x = 0` would make `y ^ 2 = 3`. -/
theorem onCurve_x_ne_zero [FieldCertificate] (input : AffineInput) (onCurve : OnCurve input) :
    input.x ≠ 0 := by
  intro zero
  unfold OnCurve at onCurve
  rw [zero] at onCurve
  exact three_not_square ⟨input.y, by linear_combination -onCurve⟩

end Kriterion.ArgoMAC.PlanB
