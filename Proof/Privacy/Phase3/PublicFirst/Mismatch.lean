/-
**Phase 3, P1e — two of P1b's shape mismatches between F4 and the games: (a) and (d).**

* **(a) `pack`/`assembleWord`.** `HW` publishes the scale joins of a uniform source as
  `pack (source.joins chunk)` over the whole `elementCount = 733` word; the real garbler publishes
  `pack (assembleWord pointX curveX pointY curveY)` of its four lanes' joins. `assembleWord` is a
  **bijection** of the four lane vectors onto the word's slots (`wordEquiv`: `readPointX`/
  `readCurveX`/`readPointY`/`readCurveY` invert it — `assembleWord_read`;
  `733 = 455 + 3 + 273 + 2`, no padding slot; the word's two bits above the slots are always
  zero), so uniform source joins are uniform lane joins (`uniform_joins_lanes`), and a source built
  from lane joins publishes exactly the garbler's scale words (`publicValue_scale_assemble`).
* **(d) `κ` against `κ⁻¹`.** F4's designated solve divides by `κ` (`simDesignated`), the Glue's
  collector targets multiply by `κ` (`collectorTargets`). At the note's shape (`JointShape.ofInput`,
  `j* = α₀ xor 1`) they are the same coefficient (`kappa_ofInput`), and `κ⁻¹ = κ`
  (`kappa_inv_ofInput`); the designated switch is the Glue's (`designatedSwitch_ofInput`).
-/

import Proof.Privacy.Phase3.AdaptiveCore
import Proof.Privacy.Phase3.Glue.AbstractSimulator

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source)

noncomputable section

variable [FieldCertificate]

/-! ### (a) The chunk word is the four lanes -/

/-- The four lanes' joins of one chunk. -/
abbrev LaneJoins := (Fin pointElementCountX → BaseField) × (Fin curveElementCountX → BaseField) ×
  (Fin pointElementCountY → BaseField) × (Fin curveElementCountY → BaseField)

/-- **Reading the lanes back reassembles the word.** -/
theorem assembleWord_read (values : Fin elementCount → BaseField) :
    Pipeline.assembleWord (Pipeline.readPointX values) (Pipeline.readCurveX values)
      (Pipeline.readPointY values) (Pipeline.readCurveY values) = values := by
  funext element
  obtain ⟨e, bound⟩ := element
  simp only [Pipeline.assembleWord, Pipeline.interleave, Pipeline.xSplit, Pipeline.ySplit,
    Pipeline.readPointX, Pipeline.readCurveX, Pipeline.readPointY, Pipeline.readCurveY,
    Pipeline.xPointPart, Pipeline.xCurvePart, Pipeline.yPointPart, Pipeline.yCurvePart,
    Pipeline.xPart, Pipeline.yPart]
  unfold elementCount at bound
  split_ifs with hx hp hq <;> congr 1 <;> apply Fin.ext <;> simp only <;>
    (try unfold elementCountX at *) <;> (try unfold pointElementCountX at *) <;>
    (try unfold pointElementCountY at *) <;> omega

/-- **`assembleWord` is a bijection** of the four lanes onto the chunk word. -/
def wordEquiv : LaneJoins ≃ (Fin elementCount → BaseField) where
  toFun lanes := Pipeline.assembleWord lanes.1 lanes.2.1 lanes.2.2.1 lanes.2.2.2
  invFun values := (Pipeline.readPointX values, Pipeline.readCurveX values,
    Pipeline.readPointY values, Pipeline.readCurveY values)
  left_inv lanes := by
    obtain ⟨pX, cX, pY, cY⟩ := lanes
    simp only [Pipeline.readPointX_assembleWord, Pipeline.readCurveX_assembleWord,
      Pipeline.readPointY_assembleWord, Pipeline.readCurveY_assembleWord]
  right_inv values := assembleWord_read values

/-- **Uniform source joins are uniform lane joins, chunk by chunk.** -/
theorem uniform_joins_lanes :
    (PMF.uniformOfFintype (Fin chunkCount → Fin elementCount → BaseField)).map
        (fun joins chunk => wordEquiv.symm (joins chunk))
      = PMF.uniformOfFintype (Fin chunkCount → LaneJoins) :=
  Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv
    (Equiv.arrowCongr (Equiv.refl _) wordEquiv.symm)

/-- **A source built from lane joins publishes the garbler's scale words.** -/
theorem publicValue_scale_assemble (source : Stage1Source) (lanes : Fin chunkCount → LaneJoins)
    (built : source.joins = fun chunk => wordEquiv (lanes chunk)) :
    source.publicValue.scale = Vector.ofFn fun chunk => pack (Pipeline.assembleWord (lanes chunk).1
      (lanes chunk).2.1 (lanes chunk).2.2.1 (lanes chunk).2.2.2) := by
  simp only [Stage1Source.publicValue, built]
  rfl

/-! ### (d) The designated coefficient -/

/-- The note's designated switch is the Glue's. -/
theorem designatedSwitch_ofInput (input : AffineInput) :
    ((JointShape.ofInput input).designatedSwitch : ℕ)
      = (Kriterion.ArgoMAC.Phase3.Glue.designatedSwitch (BitInput.ofAffine input) : ℕ) := rfl

/-- **F4's `κ` is the Glue's `κ`** at the note's shape. -/
theorem kappa_ofInput (input : AffineInput) :
    (JointShape.ofInput input).kappa
      = Kriterion.ArgoMAC.Phase3.Glue.kappa (BitInput.ofAffine input) := rfl

/-- **`κ⁻¹ = κ`**: F4's division and the Glue's multiplication agree. -/
theorem kappa_inv_ofInput (input : AffineInput) :
    (JointShape.ofInput input).kappa⁻¹
      = Kriterion.ArgoMAC.Phase3.Glue.kappa (BitInput.ofAffine input) := by
  rw [← kappa_ofInput]
  exact inv_eq_of_mul_eq_one_right (JointShape.ofInput_kappa_mul_self input)

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
