/-
**Task 31l — the `91` exceptional points of `E1`, as a `Finset Point`.**

`ErrorBudget.t5Error` and `t8Error` are both `91 / #Point`, and
`ErrorBudget.ninetyOnePoints_le_240bits` bounds that *quantity*. What the tree did not have is
the excluded set itself: `Construction/ArgoMAC/Exception.lean` names the exceptional input of a
digit (`exceptionalInput`, `exceptionIndex`) but never collects the `91` curve points `E1`
excludes, so `Stage2Assembly.doublingIn_card` / `doublingOut_card` had nothing concrete to be
stated at.

This module collects them, without touching `Construction/`.

### What the points are

Output MAC `index` carries a digit and a non-identity affine offset
(`FieldMacToECMac.OutputKey`). Its Jacobian row degenerates — the doubling case — exactly when
the digit transform of the evaluated input lands on that key's offset
(`Proof/Correctness/JacobianMixed.lean`, `exceptionDigitCorrect`). By
`Exception.exceptionalInput_transform` there is exactly **one** such input per output MAC, namely
`Exception.exceptionalInput φ offset` at that digit's sixth root of unity φ; so `E1` excludes at
most `outputMacCount = 91` points, one per digit, and the excluded set is a function of the
output keys — i.e. of the adversary's context — which is precisely the shape
`PGS.ExclusionStep.excluded` asks for.

`exceptionalPoints` is that set. The bound is `≤ 91` rather than `= 91`: two output MACs may
carry the same digit *and* the same offset, and nothing in the construction forbids it, so
distinctness is not available. `≤ 91` is what `t5Error` and `t8Error` need.

### Rule O and Rule N

Nothing is enumerated. `exceptionalPoints` is `Finset.image` over `Finset.univ : Finset (Fin 91)`
and its cardinality is `Finset.card_image_le` plus `Fintype.card_fin`; no `Finset Point` is ever
materialised by listing, `Fintype.card Point` is not touched here at all, and there is no
`decide` and no `#eval`. The only numeral is `91`.
-/

import Construction.ArgoMAC.FieldMacToECMac
import Mathlib.Data.Finset.Card

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography Kriterion.ArgoMAC.FieldMacToECMac

/-! ### The digit's sixth root of unity -/

/-- **The base a digit's coordinate transform uses**, with the zero digit — whose row is not a
transform at all — sent to `1`. This is a total form of `digitEndomorphismBase`. -/
def digitPhi (digit : Digit) : BaseField := (digitEndomorphismBase digit).getD 1

/-- Every digit's base is a sixth root of unity. -/
theorem digitPhi_pow_six (digit : Digit) : digitPhi digit ^ 6 = 1 := by
  rw [digitPhi]
  cases selected : digitEndomorphismBase digit with
  | none => rw [Option.getD_none, one_pow]
  | some value =>
      rw [Option.getD_some]
      exact digitEndomorphismBasePowSix digit value selected

/-- At a digit the construction actually transforms with, `digitPhi` is that base. -/
theorem digitPhi_eq (digit : Digit) (phi : BaseField)
    (selected : digitEndomorphismBase digit = some phi) : digitPhi digit = phi := by
  rw [digitPhi, selected, Option.getD_some]

/-! ### The exceptional input of one output MAC -/

/-- **The one input that puts output MAC `index` in the doubling case**: the input whose digit
transform is exactly that key's offset. -/
def exceptionalAffine (keys : OutputKeys) (index : Fin outputMacCount) : AffineInput :=
  Exception.exceptionalInput (digitPhi (keys.get index).digit)
    (keys.get index).offset.coordinates

/-- **It is the doubling case.** The digit transform of the exceptional input recovers the
offset — `Exception.exceptionalInput_transform` at `digitPhi_pow_six`. -/
theorem exceptionalAffine_transform (keys : OutputKeys) (index : Fin outputMacCount) :
    ({ x := digitPhi (keys.get index).digit ^ 4 * (exceptionalAffine keys index).x,
       y := digitPhi (keys.get index).digit ^ 3 * (exceptionalAffine keys index).y } :
        AffineInput)
      = (keys.get index).offset.coordinates :=
  Exception.exceptionalInput_transform _ (digitPhi_pow_six _) _

/-- **And it is the only one.** If the digit transform of an input lands on the key's offset,
that input *is* the exceptional one: `φ⁴ x = offset.x` gives `x = φ² offset.x` because `φ⁶ = 1`,
and `φ³ y = offset.y` gives `y = φ³ offset.y`. This is what makes `E1` at most `91` points — one
per output MAC — rather than a set the adversary can enlarge. -/
theorem eq_exceptionalAffine_of_transform (keys : OutputKeys) (index : Fin outputMacCount)
    (input : AffineInput)
    (sameX : digitPhi (keys.get index).digit ^ 4 * input.x
      = (keys.get index).offset.coordinates.x)
    (sameY : digitPhi (keys.get index).digit ^ 3 * input.y
      = (keys.get index).offset.coordinates.y) :
    input = exceptionalAffine keys index := by
  have six : digitPhi (keys.get index).digit ^ 6 = 1 := digitPhi_pow_six _
  obtain ⟨x, y⟩ := input
  refine AffineInput.mk.injEq .. ▸ ?_
  refine ⟨?_, ?_⟩
  · show x = digitPhi (keys.get index).digit ^ 2 * (keys.get index).offset.coordinates.x
    rw [← sameX]
    linear_combination (-x) * six
  · show y = digitPhi (keys.get index).digit ^ 3 * (keys.get index).offset.coordinates.y
    rw [← sameY]
    linear_combination (-y) * six

/-- **And it is a curve point.** A sixth root of unity scales `x` by `φ²` and `y` by `φ³`, and
`φ⁶ = 1`, so the curve equation is preserved. -/
theorem exceptionalAffine_onCurve (keys : OutputKeys) (index : Fin outputMacCount) :
    OnCurve (exceptionalAffine keys index) := by
  have offsetOnCurve : OnCurve (keys.get index).offset.coordinates :=
    (keys.get index).offset.onCurve
  have six : digitPhi (keys.get index).digit ^ 6 = 1 := digitPhi_pow_six _
  show (digitPhi (keys.get index).digit ^ 3 * (keys.get index).offset.coordinates.y) ^ 2
    = (digitPhi (keys.get index).digit ^ 2 * (keys.get index).offset.coordinates.x) ^ 3 + 3
  rw [OnCurve] at offsetOnCurve
  linear_combination (digitPhi (keys.get index).digit ^ 6) * offsetOnCurve + 3 * six

/-- The exceptional input as a non-identity affine offset. -/
def exceptionalOffset (keys : OutputKeys) (index : Fin outputMacCount) : AffineOffset :=
  ⟨exceptionalAffine keys index, exceptionalAffine_onCurve keys index⟩

/-- **The exceptional point of output MAC `index`.** -/
def exceptionalPoint [FieldCertificate] (keys : OutputKeys) (index : Fin outputMacCount) :
    Point :=
  (exceptionalOffset keys index).point

/-- The exceptional point decodes the exceptional input. -/
theorem decodePoint_exceptionalAffine [FieldCertificate] (keys : OutputKeys)
    (index : Fin outputMacCount) :
    decodePoint (exceptionalAffine keys index) = some (exceptionalPoint keys index) :=
  (Option.some_get _).symm

/-! ### The excluded set

Equality of curve points is not decidable in the tree, and nothing here needs it to be: the
excluded set is a `Finset` only so that `PGS.ExclusionStep.excluded` can take its cardinality.
The instance is therefore the classical one, declared file-locally so that every statement below
is read at the same instance. -/

/-- Classical equality of curve points, for `Finset.image` alone. -/
noncomputable local instance pointDecidableEq [FieldCertificate] : DecidableEq Point :=
  Classical.decEq Point

/-- **`E1`'s excluded set**: the at most `91` curve points at which some output MAC's Jacobian
row degenerates. It is a function of the output keys, which is the dependence
`PGS.ExclusionStep.excluded` is stated over. -/
noncomputable def exceptionalPoints [FieldCertificate] (keys : OutputKeys) : Finset Point :=
  Finset.univ.image (exceptionalPoint keys)

/-- **`≤ 91`, which is what `t5Error` and `t8Error` pay for.** One point per output MAC, and
there are `outputMacCount = 91` of them; nothing forbids two MACs from sharing a point, so the
bound is an inequality. -/
theorem card_exceptionalPoints [FieldCertificate] (keys : OutputKeys) :
    (exceptionalPoints keys).card ≤ 91 := by
  rw [exceptionalPoints]
  refine Finset.card_image_le.trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fin]

/-- **Membership**: a point is excluded exactly when some output MAC is exceptional at it. -/
theorem mem_exceptionalPoints_iff [FieldCertificate] (keys : OutputKeys) (point : Point) :
    point ∈ exceptionalPoints keys ↔ ∃ index, exceptionalPoint keys index = point := by
  rw [exceptionalPoints]
  simp [Finset.mem_image]

/-- Each output MAC's own exceptional point is excluded. -/
theorem exceptionalPoint_mem [FieldCertificate] (keys : OutputKeys)
    (index : Fin outputMacCount) :
    exceptionalPoint keys index ∈ exceptionalPoints keys :=
  (mem_exceptionalPoints_iff keys _).mpr ⟨index, rfl⟩

/-- **Off the excluded set no output MAC is in the doubling case.** This is the form the three
`PGS.ExclusionStep.agree` clauses read the set at: a point outside `exceptionalPoints` differs
from every key's exceptional point, so every Jacobian row is non-degenerate at it. -/
theorem ne_exceptionalPoint_of_not_mem [FieldCertificate] (keys : OutputKeys) (point : Point)
    (outside : point ∉ exceptionalPoints keys) (index : Fin outputMacCount) :
    exceptionalPoint keys index ≠ point := by
  intro equal
  exact outside (equal ▸ exceptionalPoint_mem keys index)

end Kriterion.ArgoMAC.PlanB
