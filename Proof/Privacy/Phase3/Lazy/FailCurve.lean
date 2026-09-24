/-
**Phase 3, P4b — the `curveX` part of the per-prefix failure bound, and the failure mass as an
expectation over the refill run.**

* `failMass_le_runs` — the installation-failure mass of `I^U` is at most the tape average of the
  expected `failObs` of the refill run's record (a failed installation is a limb collision with
  stage 1, `run_fail_collides`, whatever hash answers are drawn).
* `opening_bound` — from the stage-1 oracle, the honest evaluation fails with mass at most
  `1[W_c ∈ dom σ₁(i₁ᶜ)] + (1/(2^128 − n(i₁ᶜ))) · (curveX chunk-0 hash entries)` plus the expected
  `pointBound` over the law of the pads. `W_c` is the raw bit-0 label: off its fold hit, the
  `curveX` chunk-0 labels are fresh; off a mask hit, the `curveX` chunk-0 masks are consumed from
  the tape, so the rest of system A, the bridge hash and the pads have a law that reads neither
  the fold answers nor the chunk-0 labels (`runRefillT_value_frame`).
-/

import Proof.Privacy.Phase3.Lazy.PointBound

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.Phase3 (simulatedRows)
open scoped ENNReal

noncomputable section

section Curve

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]
  (stage : LState) (table : Public) (input : AffineInput) (target : Point) (bits : BitInput)
  (mac : InputMac) (tape : Tape)

/-! ### The failure mass is an expectation over the run -/

/-- **On the run's support, a failed installation is a limb collision with stage 1**, whatever
hash answers are drawn. -/
theorem run_fail_collides (draw : Cell → PMF (Block × Block))
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)
    (member : some ran ∈ (runRefill bits draw (openingQueriesM table bits mac) stage
      noRecord ∅).support)
    (answers : DesignatedLimbs)
    (fails : programAll (programRequests bits ran.2.2 answers) ran.2.1 = none) :
    ∃ limb, SlotCollides stage bits ran.2.2 limb := by
  have present : ∀ request ∈ programRequests bits ran.2.2 answers, request.1 ≠ none := by
    intro request requestMember
    simp only [programRequests, List.mem_map, List.mem_finRange, true_and] at requestMember
    obtain ⟨limb, rfl⟩ := requestMember
    have recorded := runRefill_records bits draw limb
      (openingQueriesM_queriesAt table bits mac limb) stage _ ∅ _ member ran rfl
    simpa only [ne_eq, Option.map_eq_none_iff] using recorded
  obtain ⟨request, requestMember, collides⟩ := programAll_fail _ _ present
    (programRequests_inputs_nodup bits ran.2.2 answers) fails
  simp only [programRequests, List.mem_map, List.mem_finRange, true_and] at requestMember
  obtain ⟨limb, rfl⟩ := requestMember
  obtain ⟨stored, same, hit⟩ := collides
  obtain ⟨recorded, recordedEq, rfl⟩ := Option.map_eq_some_iff.mp same
  refine ⟨limb, recorded, recordedEq, ?_⟩
  rwa [runRefill_frame bits draw _ stage _ ∅ _ member ran rfl _
    (isDesignated_designatedInput bits limb recorded)] at hit

open Classical in
/-- The installation continuation after the run fails at most `failObs`. -/
theorem install_le_failObs
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)
    (collide : ∀ answers, programAll (programRequests bits ran.2.2 answers) ran.2.1 = none →
      ∃ limb, SlotCollides stage bits ran.2.2 limb) :
    ((simulatedRows input target).bind fun targets => match targets with
      | none => PMF.pure none
      | some targets =>
        (designatedLimbs idealSamplers table bits ran.1.1 ran.1.2 targets).bind
          fun answers => match answers with
          | none => PMF.pure none
          | some answers => PMF.pure (some (programRequests bits ran.2.2 answers, ran.2.1))
      ).toOuterMeasure {inputs | FailsInstall inputs} ≤
      failObs stage bits ran.2.2 := by
  unfold failObs
  split
  · rw [PMF.toOuterMeasure_apply]
    exact le_trans (ENNReal.tsum_le_tsum fun x => Set.indicator_le_self _ _ x)
      (le_of_eq (PMF.tsum_coe _))
  · rename_i never
    refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr ?_)
    refine Set.disjoint_left.mpr fun inputs member fails => ?_
    obtain ⟨requests, final, rfl, failed⟩ := fails
    obtain ⟨targets, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    cases targets with
    | none => simp at member
    | some targets =>
        obtain ⟨answers, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
        cases answers with
        | none => simp at member
        | some answers =>
            simp only [PMF.support_pure, Set.mem_singleton_iff, Option.some.injEq,
              Prod.mk.injEq] at member
            obtain ⟨rfl, rfl⟩ := member
            exact never (collide answers failed)

/-- A bind's mass on a set that its `none` branch avoids is at most an expectation bounding each
successful branch. -/
theorem bind_toOuterMeasure_le {X Y : Type} (μ : PMF (Option X)) (cont : Option X → PMF (Option Y))
    (S : Set (Option Y)) (f : X → ℝ≥0∞) (noneCont : (cont none).toOuterMeasure S = 0)
    (someCont : ∀ x, some x ∈ μ.support → (cont (some x)).toOuterMeasure S ≤ f x) :
    (μ.bind cont).toOuterMeasure S ≤ expectO μ f := by
  rw [PMF.toOuterMeasure_bind_apply]
  unfold expectO
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases zero : μ o = 0
  · rw [zero, zero_mul, zero_mul]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  cases o with
  | none =>
      rw [noneCont]
      exact zero_le
  | some x => exact someCont x ((PMF.mem_support_iff _ _).mpr zero)

/-- **The failure mass is at most the tape average of the run's expected `failObs`.** -/
theorem failMass_le_runs (labels : LamportSignature) :
    failMass table input labels target stage ≤
      ∑' tape, uniformMaskTape tape *
        expectO (runRefillT (Lamport.restore input labels).input (fun cell => PMF.pure (tape cell))
          (openingQueriesM table (Lamport.restore input labels).input
            (Lamport.restore input labels).inputMac)
          stage noRecord ∅) (fun r => failObs stage (Lamport.restore input labels).input
            r.2.2.1) := by
  set bits := (Lamport.restore input labels).input
  set mac := (Lamport.restore input labels).inputMac
  unfold failMass installInputs
  dsimp only
  refine (bind_toOuterMeasure_le _ _ _
    (fun ran => failObs stage bits ran.2.2) ?_ ?_).trans ?_
  · rw [PMF.toOuterMeasure_pure_apply, if_neg (by rintro ⟨_, _, same, _⟩; cases same)]
  · intro ran member
    obtain ⟨tape, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    exact install_le_failObs stage table input target bits ran
      (run_fail_collides stage table bits mac _ ran member)
  · unfold refillRun
    rw [expectO_bind]
    refine le_of_eq (tsum_congr fun tape => ?_)
    rw [runRefill_eq_runRefillT, expectO_map]
    rfl

/-! ### The `curveX` chunk 0 -/

/-- The raw level-1 label of chunk 0 of `curveX`. -/
abbrev curveLabel : Block := chunkLabel table.curveXHot (Pipeline.macLabels mac .x)

/-- The chunk-0 labels of `curveX` at material `m`. -/
abbrev curveHot (material : Block) : Fin (2 ^ chunkWidth chunkZero) → Block :=
  chunkHot bits table.curveXHot (Pipeline.macLabels mac .x) material

/-- The `curveX` chunk-0 mask vectors on the tape. -/
abbrev curveMasks : Fin (2 ^ chunkWidth chunkZero) → Vector BaseField curveElementCountX :=
  maskValues tape .curveX chunkZero (chunkOf (Pipeline.coordBits bits .x) chunkZero)

/-- No `curveX` input is designated. -/
theorem curve_not_designated (switch : Fin (2 ^ chunkWidth chunkZero))
    (limb : Fin (limbCount .curveX)) (label : Block) :
    ¬ IsDesignated bits (cellInput (maskCell .curveX chunkZero switch limb) label) :=
  fun designated => absurd (cellAt_unique (scaleInput_cellAt .curveX chunkZero switch limb label)
    (designated_cellAt designated)).1 (by decide)

open Classical in
/-- **`opening_bound`.** -/
theorem opening_bound :
    expectO (runRefillT bits (fun cell => PMF.pure (tape cell)) (openingQueriesM table bits mac)
        stage noRecord ∅) (fun r => failObs stage bits r.2.2.1) ≤
      (if (stage.fixed (foldIndex .curveX bits true)).knownInput
          (curveLabel table mac).toFin then 1 else 0) +
        freshCharge (stage.fixed (foldIndex .curveX bits true)) * maskCharge stage .curveX +
        expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
          (curveRest table bits mac (curveMasks bits tape)) stage noRecord ∅)
          (fun q => pointBound stage table bits mac q.1) := by
  set draw : Cell → PMF (Block × Block) := fun cell => PMF.pure (tape cell)
  set i0 := foldIndex .curveX bits false
  set i1 := foldIndex .curveX bits true
  set W := curveLabel table mac
  set X := expectO (runRefillT bits draw (curveRest table bits mac (curveMasks bits tape)) stage
    noRecord ∅) (fun q => pointBound stage table bits mac q.1)
  set κ := freshCharge (stage.fixed i1)
  set G : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) × LState ×
      Record × Set Cell → ℝ≥0∞ := fun r => failObs stage bits r.2.2.1
  have runEq : runRefillT bits draw (openingQueriesM table bits mac) stage noRecord ∅ =
      (forwardAnswer i0 W stage).bind fun first => (forwardAnswer i1 W first.2).bind fun second =>
        runRefillT bits draw (Programs.evalMasksM .curveX chunkZero (chunkWidth chunkZero)
            (curveHot table bits mac (first.1 ^^^ second.1))
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= fun masks =>
              curveRest table bits mac masks >>= pointPart table bits mac)
          second.2 noRecord (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) ∅)) := by
    rw [openingQueriesM_split]
    exact runRefillT_evalFold_two bits draw .curveX chunkZero _ _ _ _ stage _ ∅
  by_cases foldHit : (stage.fixed i1).knownInput W.toFin
  · rw [if_pos foldHit]
    refine le_trans (expectO_le_one _ fun r => failObs_le_one _ _ _) ?_
    rw [add_assoc]
    exact le_self_add
  rw [if_neg foldHit, zero_add, runEq, expectO_bind]
  have i0ne : i0 ≠ i1 := foldIndex_ne .curveX bits
  -- the fold touches no cell
  have touchedNone : ∀ cell, cell ∉ touch (.fixedForward i1 W) (touch (.fixedForward i0 W) ∅) := by
    intro cell member
    simp only [touch, Set.mem_ofPred_eq, touchedCell, Set.mem_empty_iff_false,
      false_or] at member
    rcases member with hit | hit <;> cases hit
  have perPair : ∀ first ∈ (forwardAnswer i0 W stage).support,
      ∀ second ∈ (forwardAnswer i1 W first.2).support,
        expectO (runRefillT bits draw (Programs.evalMasksM .curveX chunkZero (chunkWidth chunkZero)
            (curveHot table bits mac (first.1 ^^^ second.1))
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= fun masks =>
              curveRest table bits mac masks >>= pointPart table bits mac)
          second.2 noRecord (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) ∅))) G ≤
        maskHit stage bits .curveX (curveHot table bits mac (first.1 ^^^ second.1)) + X := by
    intro first firstMember second secondMember
    set hot := curveHot table bits mac (first.1 ^^^ second.1)
    have stateAt : ∀ index, index ≠ i0 → index ≠ i1 → second.2.fixed index = stage.fixed index :=
      fun index ne0 ne1 => by
        rw [forwardAnswer_frame i1 W first.2 second secondMember _ (Ne.symm ne1),
          forwardAnswer_frame i0 W stage first firstMember _ (Ne.symm ne0)]
    have encHash₁ := forwardAnswer_encHash i0 W stage first firstMember
    have encHash₂ := forwardAnswer_encHash i1 W first.2 second secondMember
    by_cases hit : ∃ switch, switch ≠ chunkOf (Pipeline.coordBits bits .x) chunkZero ∧
        ∃ limb : Fin (limbCount .curveX),
          stage.hash.lookup (cellInput (maskCell .curveX chunkZero switch limb) (hot switch)) ≠
            none
    · refine le_trans (expectO_le_one _ fun r => failObs_le_one _ _ _) ?_
      refine le_trans (le_of_eq ?_) le_self_add
      unfold maskHit
      rw [if_pos hit]
    refine le_trans ?_ le_add_self
    have ready := masks_detRun_ne_none bits tape .curveX chunkZero hot
      (chunkOf (Pipeline.coordBits bits .x) chunkZero) second.2 noRecord
      (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) ∅))
      (fun _ _ _ _ => touchedNone _)
      (fun switch active limb _ => by
        by_contra stored
        exact hit ⟨switch, active, limb, by
          rw [← encHash₁.2, ← encHash₂.2]
          exact stored⟩)
    obtain ⟨result, success⟩ := Option.ne_none_iff_exists'.mp ready
    rw [detRun_bind_spec bits tape _ _ _ _ _ result success]
    cases result with
    | none =>
        simp only [continueT, expectO_pure_none]
        exact zero_le
    | some r =>
        simp only [continueT]
        have value : r.1 = curveMasks bits tape :=
          (detRun_value bits tape _ _ _ _ r success).trans
            (masks_value bits tape .curveX chunkZero hot _
              fun switch limb => curve_not_designated bits switch limb _)
        obtain ⟨fixedSame, encSame, hashSame, touchedSame⟩ :=
          detRun_frame bits tape (CellAt .curveX chunkZero)
            (evalMasksM_allQ .curveX chunkZero hot _) _ _ _ r success
        have recordNone : r.2.2.1 = noRecord := detRun_record_plain bits tape
          ((evalMasksM_allQ .curveX chunkZero hot _).mono fun request inside => by
            intro asked same
            subst same
            exact fun designated => absurd (cellAt_unique inside (designated_cellAt designated)).1
              (by decide))
          _ _ _ r success
        rw [value, expectO_runBind]
        calc expectO (runRefillT bits draw (curveRest table bits mac (curveMasks bits tape)) r.2.1
              r.2.2.1 r.2.2.2) (fun q => expectO (runRefillT bits draw (pointPart table bits mac q.1)
                q.2.1 q.2.2.1 q.2.2.2) G)
            ≤ expectO (runRefillT bits draw (curveRest table bits mac (curveMasks bits tape)) r.2.1
                r.2.2.1 r.2.2.2) (fun q => pointBound stage table bits mac q.1) := by
              refine expectO_mono_support _ fun q member => ?_
              obtain ⟨qframe, qrecord⟩ := runRefillT_support_frame bits draw CurveRestIndex
                CurveRestInput (curveRest_plain bits table bits mac _) _ _ _ q member
              rw [qrecord, recordNone]
              refine pointPart_bound stage table bits mac draw q.1 q.2.1 q.2.2.2 ?_
              have notRest : ¬ CurveRestIndex (foldIndex .pointX bits true) := by
                rintro (⟨c, at'⟩ | ⟨c, at'⟩)
                · exact absurd (indexAt_unique (foldIndex_indexAt .pointX bits true) at').1
                    (by decide)
                · exact absurd (indexAt_unique (foldIndex_indexAt .pointX bits true) at').1
                    (by decide)
              have ne0 : foldIndex .pointX bits true ≠ i0 := by
                intro same
                have atCurve : IndexAt .curveX chunkZero i0 := foldIndex_indexAt .curveX bits false
                rw [← same] at atCurve
                exact absurd (indexAt_unique (foldIndex_indexAt .pointX bits true) atCurve).1
                  (by decide)
              have ne1 : foldIndex .pointX bits true ≠ i1 := by
                intro same
                have atCurve : IndexAt .curveX chunkZero i1 := foldIndex_indexAt .curveX bits true
                rw [← same] at atCurve
                exact absurd (indexAt_unique (foldIndex_indexAt .pointX bits true) atCurve).1
                  (by decide)
              rw [qframe _ notRest, fixedSame, stateAt _ ne0 ne1]
          _ = X := by
              refine expectO_value_eq _ _ ?_ (fun pads => pointBound stage table bits mac pads)
              refine runRefillT_value_frame bits draw CurveRestIndex CurveRestInput
                (curveRest_plain bits table bits mac _) _ _ _ _ _ _
                ⟨fun index inside => ?_, encSame.trans (encHash₂.1.trans encHash₁.1),
                  fun asked outside => ?_⟩ fun cell inside => ?_
              · have away : index ≠ i0 ∧ index ≠ i1 := by
                  have notZero : ¬ IndexAt .curveX chunkZero index := by
                    intro atZero
                    rcases inside with ⟨c, at'⟩ | ⟨c, at'⟩
                    · exact chunk_succ_ne_zero c (indexAt_unique at' atZero).2
                    · exact absurd (indexAt_unique at' atZero).1 (by decide)
                  exact ⟨fun same => notZero (same ▸ foldIndex_indexAt _ _ _),
                    fun same => notZero (same ▸ foldIndex_indexAt _ _ _)⟩
                rw [fixedSame, stateAt index away.1 away.2]
              · rw [hashSame asked outside, encHash₂.2, encHash₁.2]
              · obtain ⟨label, outside⟩ := inside
                have notCell : ∀ label', ¬ CellAt .curveX chunkZero (cellInput cell label') := by
                  intro label' atZero
                  apply outside
                  obtain ⟨lane, chunk⟩ := cellAt_unique atZero
                    ⟨cell, label', rfl, rfl, rfl⟩
                  exact ⟨cell, label, lane.symm, chunk.symm, rfl⟩
                rw [touchedSame cell notCell]
                exact ⟨fun member => (touchedNone cell member).elim,
                  fun member => member.elim⟩
  have perFirst : ∀ first ∈ (forwardAnswer i0 W stage).support,
      ∑' second, (forwardAnswer i1 W first.2) second *
        expectO (runRefillT bits draw (Programs.evalMasksM .curveX chunkZero (chunkWidth chunkZero)
            (curveHot table bits mac (first.1 ^^^ second.1))
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= fun masks =>
              curveRest table bits mac masks >>= pointPart table bits mac)
          second.2 noRecord (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) ∅))) G ≤
        κ * maskCharge stage .curveX + X := by
    intro first firstMember
    have atSecond : first.2.fixed i1 = stage.fixed i1 :=
      forwardAnswer_frame i0 W stage first firstMember i1 i0ne
    calc _ ≤ ∑' second, (forwardAnswer i1 W first.2) second *
            (maskHit stage bits .curveX (curveHot table bits mac (first.1 ^^^ second.1)) + X) := by
          refine ENNReal.tsum_le_tsum fun second => ?_
          by_cases zero : (forwardAnswer i1 W first.2) second = 0
          · rw [zero, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (perPair first firstMember second
              ((PMF.mem_support_iff _ _).mpr zero)) zero_le
      _ = ∑' second, (forwardAnswer i1 W first.2) second *
            maskHit stage bits .curveX (curveHot table bits mac (first.1 ^^^ second.1)) + X := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      _ ≤ κ * maskCharge stage .curveX + X := by
          refine add_le_add ?_ le_rfl
          refine (forwardAnswer_sum_le i1 W first.2 (by rw [atSecond]; exact foldHit)
            fun a => maskHit stage bits .curveX
              (curveHot table bits mac (first.1 ^^^ a))).trans ?_
          rw [atSecond]
          exact mul_le_mul_of_nonneg_left (maskHit_sum_le stage bits .curveX _ _ _) zero_le
  calc _ ≤ ∑' first, (forwardAnswer i0 W stage) first * (κ * maskCharge stage .curveX + X) := by
        refine ENNReal.tsum_le_tsum fun first => ?_
        by_cases zero : (forwardAnswer i0 W stage) first = 0
        · rw [zero, zero_mul, zero_mul]
        · rw [expectO_bind]
          exact mul_le_mul_of_nonneg_left (perFirst first ((PMF.mem_support_iff _ _).mpr zero))
            zero_le
    _ = κ * maskCharge stage .curveX + X := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Curve

end

end Kriterion.ArgoMAC.Phase3.Lazy
