/-
**Phase 3, P4b — `pointPart_bound`: the `pointX` part of the per-prefix failure bound.**

From any state that agrees with stage 1 on the second half `i₁` of the inactive level-1 gate of
chunk 0 of `pointX`, and with nothing recorded, the `pointX`/`pointY` part of the run fails with
mass at most

  `1[W ∈ dom σ₁(i₁)] + (1/(2^128 − n(i₁))) · (Σ_{designated inputs} n)`,

where `W` is the whitened bit-0 label. Off the fold hit, the answer at `i₁` is uniform on the unused
outputs, and every chunk-0 label, `E*` included, is a fixed block XOR it (`foldLabels_linear`).
Every designated query of the rest of the run carries `E*` (`pointRest_labelled`), so the record is
`E*` at every limb it names (`runRefillT_record_labelled`), and the failure is the event that
`E*` is a stage-1 label at a designated input: mass `≤ n/(2^128 − n(i₁))` per stored designated
input. There is no output event (hash answers may collide), so nothing after the fold needs to be
independent of the labels.
-/

import Proof.Privacy.Phase3.Lazy.FailPoint

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

section Point

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]
  (stage : LState) (table : Public) (bits : BitInput) (mac : InputMac)
  (draw : Cell → PMF (Block × Block))

/-- The chunk-0 labels of `pointX` at material `m`. -/
abbrev pointHot (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (material : Block) : Fin (2 ^ chunkWidth chunkZero) → Block :=
  chunkHot bits table.pointXHot (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x) material

/-- The whitened level-1 label of chunk 0 of `pointX`. -/
abbrev pointLabel (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) : Block :=
  chunkLabel table.pointXHot (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)

/-- The `pointX` part of the run, the fold unfolded. -/
theorem pointPart_run (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (oracle : LState) (record : Record) (touched : Set Cell) :
    runRefillT bits draw (pointPart table bits mac pads) oracle record touched =
      (forwardAnswer (foldIndex .pointX bits false) (pointLabel table mac pads) oracle).bind
        fun first => (forwardAnswer (foldIndex .pointX bits true) (pointLabel table mac pads)
          first.2).bind fun second =>
            runRefillT bits draw
              (Programs.evalMasksM .pointX chunkZero (chunkWidth chunkZero)
                (pointHot table bits mac pads (first.1 ^^^ second.1))
                (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= pointRest table bits mac pads)
              second.2 record
              (touch (.fixedForward (foldIndex .pointX bits true) (pointLabel table mac pads))
                (touch (.fixedForward (foldIndex .pointX bits false)
                  (pointLabel table mac pads)) touched)) := by
  rw [pointPart_split]
  exact runRefillT_evalFold_two bits draw .pointX chunkZero _ _ _ _ oracle record touched

open Classical in
/-- The `pointPart` bound as a function of the pads. -/
def pointBound (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) : ℝ≥0∞ :=
  (if (stage.fixed (foldIndex .pointX bits true)).knownInput
      (pointLabel table mac pads).toFin then 1 else 0) +
    freshCharge (stage.fixed (foldIndex .pointX bits true)) * slotCharge stage bits

open Classical in
/-- **`pointPart_bound`.** -/
theorem pointPart_bound (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (oracle : LState) (touched : Set Cell)
    (sameState : oracle.fixed (foldIndex .pointX bits true) =
      stage.fixed (foldIndex .pointX bits true)) :
    expectO (runRefillT bits draw (pointPart table bits mac pads) oracle noRecord touched)
        (fun r => failObs stage bits r.2.2.1) ≤
      pointBound stage table bits mac pads := by
  unfold pointBound
  by_cases foldHit : (stage.fixed (foldIndex .pointX bits true)).knownInput
      (pointLabel table mac pads).toFin
  · rw [if_pos foldHit]
    exact le_trans (expectO_le_one _ fun r => failObs_le_one _ _ _) le_self_add
  rw [if_neg foldHit, zero_add, pointPart_run, expectO_bind]
  set i0 := foldIndex .pointX bits false
  set i1 := foldIndex .pointX bits true
  set W := pointLabel table mac pads
  set κ := freshCharge (stage.fixed i1)
  set bound : Block → ℝ≥0∞ := fun material =>
    ∑ limb, slotInput stage bits (pointHot table bits mac pads material (designatedSwitch bits))
      limb
  have i0ne : i0 ≠ i1 := foldIndex_ne .pointX bits
  -- per pair of fold answers: the record names `E*` only
  have perPair : ∀ second : Block × LState,
      expectO (runRefillT bits draw
          (Programs.evalMasksM .pointX chunkZero (chunkWidth chunkZero)
            (pointHot table bits mac pads second.1)
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= pointRest table bits mac pads)
          second.2 noRecord
          (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) touched)))
          (fun r => failObs stage bits r.2.2.1) ≤ bound second.1 := by
    intro second
    refine (expectO_mono_support _ fun r member => failObs_le stage bits r.2.2.1
      (pointHot table bits mac pads second.1 (designatedSwitch bits)) fun limb => ?_).trans
      (expectO_const_le _ _)
    exact runRefillT_record_labelled bits draw _ (pointRest_labelled bits table mac pads _)
      _ _ _ r member limb
  -- the sum over the second answer: it is fresh
  have perFirst : ∀ first ∈ (forwardAnswer i0 W oracle).support,
      ∑' second, (forwardAnswer i1 W first.2) second *
        expectO (runRefillT bits draw
          (Programs.evalMasksM .pointX chunkZero (chunkWidth chunkZero)
            (pointHot table bits mac pads (first.1 ^^^ second.1))
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= pointRest table bits mac pads)
          second.2 noRecord
          (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) touched)))
          (fun r => failObs stage bits r.2.2.1) ≤ κ * slotCharge stage bits := by
    intro first firstMember
    have atSecond : first.2.fixed i1 = stage.fixed i1 := by
      rw [forwardAnswer_frame i0 W oracle first firstMember i1 i0ne]
      exact sameState
    calc (∑' second, (forwardAnswer i1 W first.2) second *
          expectO (runRefillT bits draw
            (Programs.evalMasksM .pointX chunkZero (chunkWidth chunkZero)
              (pointHot table bits mac pads (first.1 ^^^ second.1))
              (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= pointRest table bits mac pads)
            second.2 noRecord
            (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) touched)))
            (fun r => failObs stage bits r.2.2.1))
        ≤ ∑' second, (forwardAnswer i1 W first.2) second * bound (first.1 ^^^ second.1) :=
          ENNReal.tsum_le_tsum fun second => mul_le_mul_of_nonneg_left
            (perPair (first.1 ^^^ second.1, second.2)) zero_le
      _ ≤ freshCharge (first.2.fixed i1) * ∑' a, bound (first.1 ^^^ a) :=
          forwardAnswer_sum_le i1 W first.2 (by rw [atSecond]; exact foldHit)
            fun a => bound (first.1 ^^^ a)
      _ = κ * slotCharge stage bits := by
          rw [atSecond]
          congr 1
          unfold bound slotCharge
          rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
          refine Finset.sum_congr rfl fun limb _ => ?_
          have shift : ∀ a, pointHot table bits mac pads (first.1 ^^^ a) (designatedSwitch bits) =
              (pointHot table bits mac pads 0 (designatedSwitch bits) ^^^ first.1) ^^^ a := by
            intro a
            exact (foldLabels_linear _ _ _ (first.1 ^^^ a) _).trans (BitVec.xor_assoc _ _ _).symm
          simp only [shift]
          exact slotInput_sum stage bits limb _
  calc (∑' first, (forwardAnswer i0 W oracle) first *
        expectO ((forwardAnswer i1 W first.2).bind fun second =>
          runRefillT bits draw
            (Programs.evalMasksM .pointX chunkZero (chunkWidth chunkZero)
              (pointHot table bits mac pads (first.1 ^^^ second.1))
              (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= pointRest table bits mac pads)
            second.2 noRecord
            (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) touched)))
          (fun r => failObs stage bits r.2.2.1))
      ≤ ∑' first, (forwardAnswer i0 W oracle) first * (κ * slotCharge stage bits) := by
        refine ENNReal.tsum_le_tsum fun first => ?_
        by_cases zero : (forwardAnswer i0 W oracle) first = 0
        · rw [zero, zero_mul, zero_mul]
        · rw [expectO_bind]
          exact mul_le_mul_of_nonneg_left (perFirst first ((PMF.mem_support_iff _ _).mpr zero))
            zero_le
    _ = κ * slotCharge stage bits := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Point

end

end Kriterion.ArgoMAC.Phase3.Lazy
