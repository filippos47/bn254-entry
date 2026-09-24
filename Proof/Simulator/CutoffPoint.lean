/-
**The tail point sampler against the uniform affine offset.**

The machine draws a tail point as `x` by bounded rejection (`x < p` and `x³ + 3` a square,
witnessed by its `(p + 1) / 4`-th power) and a fair sign (`curvePointLaw`). Under the group
certificate (`r • P = 0` for every point, `r` an odd prime):

* `curveRhs_ne_zero`: `x³ + 3 ≠ 0` (no point of order two), so every accepted `x` carries exactly
  two points and the sign separates them;
* `affineCount_le`: `#A ≤ 2 · #accepted` (a square has at most two roots);
* `scalar_le_affineCount`: `r ≤ #A + 1` (the multiples of `(1, 2)` are distinct);
* `curvePoint_close`: the tail point sampler is abort-close to the uniform affine offset, with
  extra abort mass its rejection cutoff.

No group-order equality `#E = r` is used.
-/

import Proof.Simulator.CutoffSamplers

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Kriterion.ArgoMAC.Phase3.Glue
open WeierstrassCurve.Affine

noncomputable section

section Points

variable [FieldCertificate]

/-- The affine points are finite. -/
instance pointFinite : Finite Point :=
  Finite.of_injective (fun point : Point => match point with
    | .zero => (none : Option (BaseField × BaseField))
    | .some x y _ => some (x, y)) (by
      intro first second equal
      cases first <;> cases second <;> simp_all)

noncomputable instance affineOffsetFintype : Fintype FieldMacToECMac.AffineOffset :=
  Fintype.ofFinite _

instance affineOffsetNonempty : Nonempty FieldMacToECMac.AffineOffset :=
  ⟨⟨⟨1, 2⟩, generatorOnCurve⟩⟩

/-- A curve equation gives a nonsingular point. -/
theorem nonsingular_of_onCurve (input : AffineInput) (onCurve : OnCurve input) :
    curve.toAffine.Nonsingular input.x input.y :=
  (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mp
    ((equation_iff_onCurve input).mpr onCurve)

/-- An affine offset's point is its coordinates. -/
theorem affineOffset_point (offset : FieldMacToECMac.AffineOffset) :
    offset.point = Point.some offset.coordinates.x offset.coordinates.y
      (nonsingular_of_onCurve offset.coordinates offset.onCurve) := by
  have valid : validate offset.coordinates = true := (validate_eq_true_iff _).mpr offset.onCurve
  have lifted : some offset.point = decodePoint offset.coordinates := Option.some_get _
  rw [decodePoint, dif_pos valid] at lifted
  exact Option.some_injective _ lifted

/-- Offsets are determined by their points. -/
theorem affineOffset_point_injective :
    Function.Injective fun offset : FieldMacToECMac.AffineOffset => offset.point := by
  intro first second equal
  simp only [affineOffset_point, Point.some.injEq] at equal
  rcases first with ⟨⟨x, y⟩, _⟩
  rcases second with ⟨⟨x', y'⟩, _⟩
  simp only at equal
  obtain ⟨rfl, rfl⟩ := equal
  rfl

/-- The number of affine offsets. -/
def affineCount : Nat := Nat.card FieldMacToECMac.AffineOffset

theorem affineCount_eq : Fintype.card FieldMacToECMac.AffineOffset = affineCount :=
  (Nat.card_eq_fintype_card).symm

/-- Two in the base field is not zero. -/
theorem two_ne_zero_base : (2 : BaseField) ≠ 0 := by
  intro zero
  have cast : ((2 : ℕ) : BaseField) = 0 := by exact_mod_cast zero
  rw [ZMod.natCast_eq_zero_iff] at cast
  have := Nat.le_of_dvd (by norm_num) cast
  unfold baseFieldModulus at this
  omega

/-- The point of a nonzero point as an offset. -/
def pointOffset : Point → Option FieldMacToECMac.AffineOffset
  | .zero => none
  | .some x y h => some ⟨⟨x, y⟩, (equation_iff_onCurve ⟨x, y⟩).mp h.1⟩

theorem pointOffset_injective : Function.Injective pointOffset := by
  intro first second equal
  cases first <;> cases second <;> simp_all [pointOffset]

section Group

variable [GroupCertificate]

/-- Two in the scalar field is not zero. -/
theorem two_ne_zero_scalar : (2 : ScalarField) ≠ 0 := by
  intro zero
  have cast : ((2 : ℕ) : ScalarField) = 0 := by exact_mod_cast zero
  rw [ZMod.natCast_eq_zero_iff] at cast
  have := Nat.le_of_dvd (by norm_num) cast
  unfold scalarFieldModulus at this
  omega

/-- A nonzero scalar annihilates only the identity. -/
theorem smul_eq_zero_of_ne {scalar : ScalarField} (nonzero : scalar ≠ 0) {point : Point}
    (annihilated : scalar • point = 0) : point = 0 := by
  haveI : Fact (Nat.Prime scalarFieldModulus) := ⟨scalarFieldPrime⟩
  calc point = (scalar⁻¹ * scalar) • point := by rw [inv_mul_cancel₀ nonzero, one_smul]
    _ = scalar⁻¹ • (scalar • point) := mul_smul _ _ _
    _ = 0 := by rw [annihilated, smul_zero]

/-- **No point of order two**: `x³ + 3 ≠ 0`. -/
theorem curveRhs_ne_zero (x : BaseField) : x ^ 3 + 3 ≠ 0 := by
  intro zero
  have onCurve : OnCurve ⟨x, 0⟩ := by
    show (0 : BaseField) ^ 2 = x ^ 3 + 3
    rw [zero]
    ring
  have nonsingular := nonsingular_of_onCurve ⟨x, 0⟩ onCurve
  have double : Point.some x 0 nonsingular + Point.some x 0 nonsingular = 0 :=
    Point.add_self_of_Y_eq (by simp [curve])
  have twice : (2 : ScalarField) • Point.some x 0 nonsingular = 0 := by
    rw [two_smul]
    exact double
  exact Point.some_ne_zero nonsingular (smul_eq_zero_of_ne two_ne_zero_scalar twice)

/-- The generator `(1, 2)`. -/
def generatorPoint : Point := Point.some 1 2 (nonsingular_of_onCurve ⟨1, 2⟩ generatorOnCurve)

/-- **`r ≤ #A + 1`**: the multiples of `(1, 2)` are distinct points. -/
theorem scalar_le_affineCount : scalarFieldModulus ≤ affineCount + 1 := by
  haveI : Fact (Nat.Prime scalarFieldModulus) := ⟨scalarFieldPrime⟩
  have multiples : Function.Injective fun scalar : ScalarField => scalar • generatorPoint := by
    intro first second same
    by_contra different
    have difference : (first - second) • generatorPoint = 0 := by
      simp only at same
      rw [sub_smul, same, sub_self]
    exact Point.some_ne_zero _ (smul_eq_zero_of_ne (sub_ne_zero.mpr different) difference)
  have first := Nat.card_le_card_of_injective _ multiples
  have second := Nat.card_le_card_of_injective _ pointOffset_injective
  rw [Nat.card_zmod] at first
  rw [Finite.card_option] at second
  exact first.trans second

end Group

/-! ### The `x`-acceptance -/

theorem sqrtExponent_mul : 4 * sqrtExponent = baseFieldModulus + 1 := by
  unfold sqrtExponent baseFieldModulus
  norm_num

/-- `c ^ ((p + 1) / 4)` squares back to `c` exactly when `c` is a square. -/
theorem sqrtWitness_iff (c : BaseField) :
    c ^ sqrtExponent * c ^ sqrtExponent = c ↔ ∃ y : BaseField, y ^ 2 = c := by
  constructor
  · intro squares
    exact ⟨c ^ sqrtExponent, by rw [sq, squares]⟩
  · rintro ⟨y, rfl⟩
    by_cases zero : y = 0
    · subst zero
      have positive : sqrtExponent ≠ 0 := by unfold sqrtExponent; norm_num
      simp [zero_pow positive]
    · have key : (y ^ 2) ^ sqrtExponent * (y ^ 2) ^ sqrtExponent = y ^ (4 * sqrtExponent) := by
        rw [← pow_mul, ← pow_add]
        congr 1
      rw [key, sqrtExponent_mul, show baseFieldModulus + 1 = (baseFieldModulus - 1) + 2 by
        unfold baseFieldModulus; norm_num, pow_add, ZMod.pow_card_sub_one_eq_one zero, one_mul]

/-- **The `x`-acceptance**: `x < p` and `x³ + 3` a square. -/
theorem curveXAccept_iff (value : Nat) :
    curveXAccept value = true ↔
      value < pNat ∧ ∃ y : BaseField, y ^ 2 = (value : BaseField) ^ 3 + 3 := by
  unfold curveXAccept
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, sqrtWitness_iff]

/-- The accepted `x`s. -/
abbrev acceptedX : Finset (Fin (2 ^ fieldWidth)) := acceptedSet fieldWidth curveXAccept

/-- Negate an offset's `y`. -/
def negOffset (offset : FieldMacToECMac.AffineOffset) : FieldMacToECMac.AffineOffset :=
  ⟨⟨offset.coordinates.x, -offset.coordinates.y⟩, by
    show (-offset.coordinates.y) ^ 2 = offset.coordinates.x ^ 3 + 3
    rw [neg_sq]
    exact offset.onCurve⟩

/-- An offset's `x` as a draw. -/
def offsetDraw (offset : FieldMacToECMac.AffineOffset) : Fin (2 ^ fieldWidth) :=
  ⟨offset.coordinates.x.val, lt_trans offset.coordinates.x.val_lt pNat_lt⟩

theorem offsetDraw_accepted (offset : FieldMacToECMac.AffineOffset) :
    offsetDraw offset ∈ acceptedX := by
  simp only [acceptedX, acceptedSet, Finset.mem_filter, Finset.mem_univ, true_and, offsetDraw]
  rw [curveXAccept_iff]
  refine ⟨offset.coordinates.x.val_lt, offset.coordinates.y, ?_⟩
  rw [ZMod.natCast_zmod_val]
  exact offset.onCurve

/-- **`#A ≤ 2 · #accepted`**: an `x` carries at most two offsets. -/
theorem affineCount_le : affineCount ≤ 2 * acceptedX.card := by
  classical
  rw [← affineCount_eq, ← Finset.card_univ]
  refine (Finset.card_le_mul_card_image (f := offsetDraw) Finset.univ 2
    fun draw member => ?_).trans (Nat.mul_le_mul_left 2
      (Finset.card_le_card (s := Finset.univ.image offsetDraw) (t := acceptedX)
        fun draw member => ?_))
  · obtain ⟨base, _, rfl⟩ := Finset.mem_image.mp member
    refine (Finset.card_le_card (t := {base, negOffset base}) fun offset inside => ?_).trans
      Finset.card_le_two
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, offsetDraw, Fin.mk.injEq] at inside
    have sameX := ZMod.val_injective _ inside
    have squares : offset.coordinates.y ^ 2 = base.coordinates.y ^ 2 := by
      rw [offset.onCurve, base.onCurve, sameX]
    rcases offset with ⟨⟨x, y⟩, onCurve⟩
    rcases base with ⟨⟨x', y'⟩, onCurve'⟩
    simp only at sameX squares
    subst sameX
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp squares with same | same
    · subst same
      simp
    · subst same
      simp [negOffset]
  · obtain ⟨offset, _, rfl⟩ := Finset.mem_image.mp member
    exact offsetDraw_accepted offset

/-! ### The point of an accepted `x` -/

/-- A point from an `x`, a root candidate and a sign. -/
def pointFrom (x root : BaseField) (sign : Bool) : Option FieldMacToECMac.AffineOffset :=
  if onCurve : (if sign then -root else root) ^ 2 = x ^ 3 + 3 then
    some ⟨⟨x, if sign then -root else root⟩, onCurve⟩
  else none

theorem curvePointOf_eq (value : Nat) (sign : Bool) :
    curvePointOf value sign =
      pointFrom (value : BaseField) (((value : BaseField) ^ 3 + 3) ^ sqrtExponent) sign := rfl

/-- A drawn point has the drawn `x` and the signed root as `y`. -/
theorem pointFrom_coordinates {x root : BaseField} {sign : Bool}
    {offset : FieldMacToECMac.AffineOffset} (drawn : pointFrom x root sign = some offset) :
    offset.coordinates.x = x ∧ offset.coordinates.y = if sign then -root else root := by
  unfold pointFrom at drawn
  by_cases onCurve : (if sign then -root else root) ^ 2 = x ^ 3 + 3
  · rw [dif_pos onCurve] at drawn
    cases drawn
    exact ⟨rfl, rfl⟩
  · rw [dif_neg onCurve] at drawn
    cases drawn

theorem curvePointOf_x {value : Nat} {sign : Bool} {offset : FieldMacToECMac.AffineOffset}
    (drawn : curvePointOf value sign = some offset) :
    offset.coordinates.x = (value : BaseField) := by
  rw [curvePointOf_eq] at drawn
  exact (pointFrom_coordinates drawn).1

/-- A root candidate that squares back always yields a point. -/
theorem pointFrom_isSome {x root : BaseField} (squares : root * root = x ^ 3 + 3) (sign : Bool) :
    pointFrom x root sign ≠ none := by
  unfold pointFrom
  rw [dif_pos]
  · simp
  · cases sign
    · simp only [Bool.false_eq_true, if_false]
      rw [sq]
      exact squares
    · simp only [if_true]
      rw [neg_sq, sq]
      exact squares

/-- An accepted `x` always yields a point. -/
theorem curvePointOf_isSome {value : Nat} (accepted : curveXAccept value = true) (sign : Bool) :
    curvePointOf value sign ≠ none := by
  rw [curvePointOf_eq]
  apply pointFrom_isSome
  unfold curveXAccept at accepted
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at accepted
  exact accepted.2

/-- The two signs of a nonzero curve right-hand side give different points. -/
theorem pointFrom_signs [GroupCertificate] (x root : BaseField)
    (offset : FieldMacToECMac.AffineOffset)
    (positive : pointFrom x root false = some offset)
    (negative : pointFrom x root true = some offset) : False := by
  obtain ⟨sameX, positiveY⟩ := pointFrom_coordinates positive
  obtain ⟨_, negativeY⟩ := pointFrom_coordinates negative
  simp only [Bool.false_eq_true, if_false, if_true] at positiveY negativeY
  have opposite : root = -root := positiveY.symm.trans negativeY
  have zero : root = 0 := by
    have twice : (2 : BaseField) * root = 0 := by
      rw [two_mul]
      nth_rewrite 1 [opposite]
      exact neg_add_cancel _
    rcases mul_eq_zero.mp twice with two | zero
    · exact absurd two two_ne_zero_base
    · exact zero
  apply curveRhs_ne_zero x
  have onCurve := offset.onCurve
  unfold OnCurve at onCurve
  rw [positiveY, sameX, zero] at onCurve
  rw [← onCurve]
  exact zero_pow two_ne_zero

theorem curvePointOf_signs [GroupCertificate] (value : Nat) (offset : FieldMacToECMac.AffineOffset)
    (positive : curvePointOf value false = some offset)
    (negative : curvePointOf value true = some offset) : False := by
  rw [curvePointOf_eq] at positive negative
  exact pointFrom_signs _ _ offset positive negative

end Points

/-! ### The tail point sampler -/

section Close

variable [FieldCertificate] [GroupCertificate]

/-- The mass of a fair sign read through a map that separates the two signs. -/
theorem sign_mass_le (g : Bool → Option FieldMacToECMac.AffineOffset)
    (offset : FieldMacToECMac.AffineOffset)
    (separate : g false = some offset → g true = some offset → False) :
    ((PMF.uniformOfFintype Bool).map g) (some offset) ≤ 2⁻¹ := by
  classical
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
  by_cases hitTrue : some offset = g true
  · by_cases hitFalse : some offset = g false
    · exact (separate hitFalse.symm hitTrue.symm).elim
    · rw [if_pos hitTrue, if_neg hitFalse, add_zero]
  · rw [if_neg hitTrue, zero_add]
    split <;> simp

/-- **The tail point sampler is abort-close to the uniform affine offset.** -/
theorem curvePoint_close :
    AbortClose (rejectLaw fieldWidth curveXAccept attempts none) curvePointLaw
      ((PMF.uniformOfFintype FieldMacToECMac.AffineOffset).map some) := by
  classical
  refine ⟨fun offset => ?_, ?_⟩
  · unfold curvePointLaw
    rw [PMF.bind_apply, tsum_option]
    simp only [PMF.pure_apply, reduceCtorEq, if_false, mul_zero, zero_add]
    rw [tsum_eq_single offset.coordinates.x.val]
    · have accepted : curveXAccept offset.coordinates.x.val = true := by
        have := offsetDraw_accepted offset
        simp only [acceptedX, acceptedSet, Finset.mem_filter, Finset.mem_univ, true_and,
          offsetDraw] at this
        exact this
      have mass := rejectLaw_some_mul_le fieldWidth curveXAccept attempts
        offset.coordinates.x.val ⟨accepted, lt_trans offset.coordinates.x.val_lt pNat_lt⟩
      have positive : (0 : ENNReal) < acceptedX.card := by
        have : 0 < acceptedX.card := Finset.card_pos.mpr ⟨_, offsetDraw_accepted offset⟩
        exact_mod_cast this
      have signs := sign_mass_le (curvePointOf offset.coordinates.x.val) offset
        (curvePointOf_signs _ offset)
      have ideal : ((PMF.uniformOfFintype FieldMacToECMac.AffineOffset).map some) (some offset) =
          (affineCount : ENNReal)⁻¹ := by
        rw [PMF.map_apply, tsum_eq_single offset]
        · simp [PMF.uniformOfFintype_apply, affineCount_eq]
        · intro other different
          rw [if_neg (fun same => different (Option.some_injective _ same).symm)]
      rw [ideal]
      have countLe := affineCount_le
      calc rejectLaw fieldWidth curveXAccept attempts (some offset.coordinates.x.val) *
            ((PMF.uniformOfFintype Bool).map (curvePointOf offset.coordinates.x.val))
              (some offset)
          ≤ (acceptedX.card : ENNReal)⁻¹ * 2⁻¹ := by
            refine mul_le_mul' ?_ signs
            rw [ENNReal.le_inv_iff_mul_le]
            exact mass
        _ = ((acceptedX.card : ENNReal) * 2)⁻¹ :=
            (ENNReal.mul_inv (Or.inr (by norm_num)) (Or.inl (ENNReal.natCast_ne_top _))).symm
        _ ≤ (affineCount : ENNReal)⁻¹ := by
            rw [ENNReal.inv_le_inv]
            rw [mul_comm]
            exact_mod_cast countLe
    · intro value different
      by_cases good : curveXAccept value = true ∧ value < 2 ^ fieldWidth
      · have below : value < pNat := ((curveXAccept_iff value).mp good.1).1
        have none : ((PMF.uniformOfFintype Bool).map (curvePointOf value)) (some offset) = 0 := by
          rw [PMF.map_apply]
          apply ENNReal.tsum_eq_zero.mpr
          intro sign
          split
          · rename_i hit
            have sameX := curvePointOf_x hit.symm
            apply absurd _ different
            rw [sameX, ZMod.val_natCast]
            exact (Nat.mod_eq_of_lt below).symm
          · rfl
        rw [none, mul_zero]
      · rw [rejectLaw_off fieldWidth curveXAccept attempts value good, zero_mul]
  · unfold curvePointLaw
    rw [PMF.bind_apply, tsum_option]
    simp only [PMF.pure_apply, if_true, mul_one]
    have idealNone : ((PMF.uniformOfFintype FieldMacToECMac.AffineOffset).map some) none = 0 := by
      rw [PMF.map_apply]
      simp
    rw [idealNone, zero_add]
    apply le_of_eq
    convert add_zero (rejectLaw fieldWidth curveXAccept attempts none) using 2
    apply ENNReal.tsum_eq_zero.mpr
    intro value
    by_cases good : curveXAccept value = true ∧ value < 2 ^ fieldWidth
    · have none : ((PMF.uniformOfFintype Bool).map (curvePointOf value)) none = 0 := by
        rw [PMF.map_apply]
        apply ENNReal.tsum_eq_zero.mpr
        intro sign
        rw [if_neg (fun same => curvePointOf_isSome good.1 sign same.symm)]
      rw [none, mul_zero]
    · rw [rejectLaw_off fieldWidth curveXAccept attempts value good, zero_mul]

end Close

end

end Kriterion.ArgoMAC.PlanB.SimMachine
