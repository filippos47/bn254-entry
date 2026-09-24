/-
**Phase 3, P1e — the middle game `M` of `G1U → HW`, and `Below HW M`.**

`M` is `HW` (`publicFirstHybrid`) with its stage 2 run on a **private** empty oracle and merged into
the stage-1 state `σ₁` at the end (`mergeChoice`), flagged (`none`) at the first touch of `σ₁`, and
augmented by a **shadow** (`Shadow`): extra lazy queries for `G1U`'s own entries (the EncPRF bit-1
pads, the visible gadget entries including the collision ones — at a position whose two
Even–Mansour pads differ by `Δ` the two gadget labels coincide — and off the curve `G1U`'s system-A
and EncPRF entries), drawn with shadow coins and run privately after the path, and a **reveal** flag
(the generalised exceptional event: the input equals a nonzero digit's exceptional input at every
non-colliding position). The shadow is a parameter; the designed shadow and the tape-level F4 lift
`FlagMono (g1uLaterWith designedInstall) M'` are `Lift`, `LiftHop` and the `Laws*` modules.

**`middle_below`**: for **every** shadow, `Below HW M`. Stage 1 and the input choice are `HW`'s; at
stage 2 (`stage2_dominates`):

* the refill run: `runRefill_ge` (private and flagged against `HW`'s run on `σ₁`, related by
  `fullRel_base`);
* the rows and the designated draws: the same draws (`realRows` is the uniform coins, pushed
  forward);
* the designated installation: `programAllSkip_rel`;
* the shadow: `HW` does not run it, but running it on the shared state and discarding the answers
  changes nothing (`discard_run`), and the private flagged run is dominated (`runLazyQ_ge`);
* the reveal flag only lowers `M`;
* the merge: `mergeChoice_sameLookups` and `run_map_fst_congr` — the adversary's stage 2 reads the
  merged state exactly as `HW`'s.
-/

import Proof.Privacy.Phase3.PublicFirst.Private

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary Stage1Source idealSamplers openingQueriesM
  designatedLimbs programRequests noRecord)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell runRefill uniformMaskTape refillRun)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate]

/-- **The shadow of `M`**: coins, extra lazy queries on and off the curve, and the reveal flags. -/
structure Shadow where
  /-- The shadow's own coins (e.g. a coupled free-XOR offset). -/
  Coin : Type
  /-- Their law. -/
  law : PMF Coin
  /-- On the curve: extra queries after the path and the installation, from the source, the input,
  the garbler coins of the rows, the shadow coins and the path's result. -/
  onCurve : Stage1Source → AffineInput → Coins → Coin →
    ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) × Record →
      FreeQuery Programs.Spec Unit
  /-- Off the curve: extra queries from the source, the input and the shadow coins. -/
  offCurve : Stage1Source → AffineInput → Coin → FreeQuery Programs.Spec Unit
  /-- The reveal flag on the curve, read on the private final state. -/
  revealOn : Stage1Source → AffineInput → Coins → Coin → LState → Prop
  /-- The reveal flag off the curve. -/
  revealOff : Stage1Source → AffineInput → Coin → LState → Prop

/-- The selected labels of a source at an input (`HW`'s). -/
abbrev sourceLabels (source : Stage1Source) (input : AffineInput) : LamportSignature :=
  Lamport.selectedLabels (source.key.encode (BitInput.ofAffine input))

section Stage2

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

open Classical in
/-- **`M`'s stage 2 after its private refill run**: the rows' coins, the designated draws (free
coordinates, collector solve, the `452` hash answers), the designated installation (flagged), the
shadow (private, flagged), the reveal flag, the merge. Outer `none` is the flag, inner `none` an
abort. -/
def privateCont (shadow : Shadow) (scalar : NonZeroScalar) (planted : LState) (source : Stage1Source)
    (input : AffineInput)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) × LState ×
      Record) : PMF (Option (Option (LamportSignature × LState))) :=
  let labels := sourceLabels source input
  let restored := Lamport.restore input labels
  letI : Fintype Coins := Fintype.ofFinite Coins
  (PMF.uniformOfFintype Coins).bind fun coins =>
    (designatedLimbs idealSamplers source.publicValue restored.input ran.1.1 ran.1.2
        (fun digit => trueRows scalar coins input digit)).bind fun answers =>
      match answers with
      | none => PMF.pure (some none)
      | some answers =>
        match programAllSkipFlag planted (programRequests restored.input ran.2.2 answers) ran.2.1 with
        | none => PMF.pure none
        | some installed =>
          shadow.law.bind fun coin =>
            (runLazyQFlag planted (shadow.onCurve source input coins coin (ran.1, ran.2.2))
                installed).bind fun shadowed =>
              match shadowed with
              | none => PMF.pure none
              | some result => if shadow.revealOn source input coins coin result.2 then PMF.pure none
                  else PMF.pure (some (some (labels, mergeChoice planted result.2)))

/-- A continuation after a flagged run (outer `none` a flag, inner `none` an abort). -/
def flagCont {α β : Type} (continuation : α → PMF (Option (Option β))) :
    Option (Option α) → PMF (Option (Option β))
  | none => PMF.pure none
  | some none => PMF.pure (some none)
  | some (some ran) => continuation ran

/-- A continuation after a run that may abort. -/
def abortCont {α γ : Type} (continuation : α → PMF (Option γ)) : Option α → PMF (Option γ)
  | none => PMF.pure none
  | some ran => continuation ran

/-- `M`'s refill stage: the private flagged refill run from the empty oracle, then a continuation. -/
def refillStageM {α β : Type} (planted : LState) (bits : BitInput)
    (computation : FreeQuery Programs.Spec α)
    (continuation : α × LState × Record → PMF (Option (Option β))) : PMF (Option (Option β)) :=
  uniformMaskTape.bind fun tape =>
    (runRefillFlag planted bits (fun cell => PMF.pure (tape cell)) computation LazyOracle.empty
      noRecord ∅).bind (flagCont continuation)

/-- `HW`'s refill stage: P4's refill run on the stage-1 state, then a continuation. -/
def refillStageH {α γ : Type} (planted : LState) (bits : BitInput)
    (computation : FreeQuery Programs.Spec α)
    (continuation : α × LState × Record → PMF (Option γ)) : PMF (Option γ) :=
  (refillRun bits computation planted).bind (abortCont continuation)

open Classical in
/-- **`M`'s stage 2**, from the source, the input, its output and the stage-1 state. -/
def middleStage2 (shadow : Shadow) (scalar : NonZeroScalar) (source : Stage1Source)
    (input : AffineInput) (output : Option Point) (planted : LState) :
    PMF (Option (Option (LamportSignature × LState))) :=
  let labels := sourceLabels source input
  let restored := Lamport.restore input labels
  match output with
  | none => shadow.law.bind fun coin =>
      (runLazyQFlag planted (shadow.offCurve source input coin) LazyOracle.empty).bind fun shadowed =>
        match shadowed with
        | none => PMF.pure none
        | some result => if shadow.revealOff source input coin result.2 then PMF.pure none
            else PMF.pure (some (some (labels, mergeChoice planted result.2)))
  | some _ => refillStageM planted restored.input
      (openingQueriesM source.publicValue restored.input restored.inputMac)
      (privateCont shadow scalar planted source input)

/-- The adversary's stage 2 after `HW`'s stage 2, at one bit (an abort is `false`). -/
def contHW {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex)
      Bool budget) (b : Bool) : Option (LamportSignature × LState) → ℝ≥0∞
  | none => PMF.pure false b
  | some (labels, state) => ((LazyOracle.run (decide labels) state).map Prod.fst) b

/-- The same after `M`'s stage 2, flag-down (a flag weighs `0`). -/
def contM {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex)
      Bool budget) (b : Bool) : Option (Option (LamportSignature × LState)) → ℝ≥0∞
  | none => 0
  | some result => contHW decide b result

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]

/-- The merged state reads like any state related to the private one. -/
theorem contHW_merge {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex)
      Bool budget) (b : Bool) (labels : LamportSignature) {planted sF sL : LState}
    (rel : FullRel planted sF sL) :
    contHW decide b (some (labels, mergeChoice planted sL)) = contHW decide b (some (labels, sF)) := by
  simp only [contHW]
  rw [run_map_fst_congr (decide labels) (mergeChoice_sameLookups rel)]

/-- Discarded extra queries, at one bit. -/
theorem contHW_discard {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex)
      Bool budget) (b : Bool) (labels : LamportSignature) (extra : FreeQuery Programs.Spec Unit)
    (state : LState) :
    ∑' o, runLazyQ extra state o * contHW decide b (some (labels, o.2))
      = contHW decide b (some (labels, state)) := by
  have law := congrArg (fun distribution : PMF Bool => distribution b)
    (discard_run (decide labels) extra state)
  simp only [PMF.bind_apply] at law
  simpa only [contHW] using law

open Classical in
/-- **The shadow step**: the private flagged shadow, the reveal flag and the merge are dominated by
`HW`, which runs nothing. -/
theorem shadow_step {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex)
      Bool budget) (b : Bool) (labels : LamportSignature) (planted sF sL : LState)
    (rel : FullRel planted sF sL) (extra : FreeQuery Programs.Spec Unit) (reveal : LState → Prop) :
    ∑' o, (runLazyQFlag planted extra sL).bind (fun shadowed =>
        match shadowed with
        | none => PMF.pure none
        | some result => if reveal result.2 then PMF.pure none
            else PMF.pure (some (some (labels, mergeChoice planted result.2)))) o * contM decide b o
      ≤ contHW decide b (some (labels, sF)) := by
  rw [tsum_bind_mul, ← contHW_discard decide b labels extra sF]
  refine le_trans (le_of_eq (tsum_congr fun shadowed => ?_))
    (runLazyQ_ge planted (fun o => contHW decide b (some (labels, o.2)))
      (fun o => if reveal o.2 then 0 else contHW decide b (some (labels, mergeChoice planted o.2)))
      (fun a sF' sL' related => ?_) extra sF sL rel)
  · congr 1
    rcases shadowed with _ | result
    · simp [tsum_pure_mul, contM, flagged]
    · by_cases hit : reveal result.2
      · simp [hit, tsum_pure_mul, contM, flagged]
      · simp [hit, tsum_pure_mul, contM, flagged]
  · by_cases hit : reveal sL'
    · simp [hit]
    · simp only [hit, if_false]
      exact le_of_eq (contHW_merge decide b labels related)

/-- A flagged shadow step, averaged over the shadow coins. -/
theorem shadow_law_step {budget : ℕ} {Coin : Type} (law : PMF Coin)
    (decide : LamportSignature → OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex)
      Bool budget) (b : Bool) (labels : LamportSignature) (planted sF sL : LState)
    (rel : FullRel planted sF sL) (inner : Coin → PMF (Option (Option (LamportSignature × LState))))
    (each : ∀ coin, ∑' o, inner coin o * contM decide b o ≤ contHW decide b (some (labels, sF))) :
    ∑' o, (law.bind inner) o * contM decide b o ≤ contHW decide b (some (labels, sF)) := by
  rw [tsum_bind_mul]
  calc ∑' coin, law coin * ∑' o, inner coin o * contM decide b o
      ≤ ∑' coin, law coin * contHW decide b (some (labels, sF)) :=
        ENNReal.tsum_le_tsum fun coin => mul_le_mul' le_rfl (each coin)
    _ = contHW decide b (some (labels, sF)) := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **After the refill run**: `M`'s private continuation is dominated by `HW`'s `openedCont`. -/
theorem privateCont_dominates (shadow : Shadow) (scalar : NonZeroScalar) (source : Stage1Source)
    (input : AffineInput) (target : Point) (planted : LState) {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex)
      Bool budget) (b : Bool)
    (lanes : (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField))
    (record : Record) (sF sL : LState) (rel : FullRel planted sF sL) :
    ∑' o, privateCont shadow scalar planted source input (lanes, sL, record) o * contM decide b o
      ≤ ∑' o, openedCont (realRows scalar) skipInstallation source.publicValue input
          (sourceLabels source input) target (lanes, sF, record) o
          * contHW decide b (o.map fun updated => (sourceLabels source input, updated)) := by
  unfold privateCont openedCont realRows
  dsimp only
  rw [PMF.bind_map, tsum_bind_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun coins => mul_le_mul' le_rfl ?_
  dsimp only [Function.comp]
  rw [tsum_bind_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun answers => mul_le_mul' le_rfl ?_
  rcases answers with _ | answers
  · simp only [tsum_pure_mul, contM, Option.map_none]
    exact le_rfl
  · dsimp only
    rw [tsum_pure_mul]
    cases flagDown : programAllSkipFlag planted (programRequests
        (Lamport.restore input (sourceLabels source input)).input record answers) sL with
    | none =>
      simp only [tsum_pure_mul, contM]
      exact zero_le
    | some installed =>
      dsimp only
      have related := programAllSkip_rel planted _ sF sL rel installed flagDown
      refine shadow_law_step shadow.law decide b _ planted _ installed related _ fun coin => ?_
      exact shadow_step decide b _ planted _ installed related _ _

/-- `HW`'s stage 2 at a valid input, for any rows kernel and installation (kept abstract, so that
no definitional check unfolds the construction). -/
theorem stage2_some_eq (rows : RowsKernel) (install : Installation) (source : Stage1Source)
    (input : AffineInput) (target : Point) (planted : LState) :
    (openedSimulator rows install).stage2 source input (some target) planted =
      (openedOpening rows install source.publicValue input (sourceLabels source input) target
        planted).map (Option.map fun updated => (sourceLabels source input, updated)) := by
  simp only [openedSimulator]

/-- **The refill stage, generically in the computation** (which is never unfolded): the private
flagged refill run with any dominated continuation is dominated by the shared one. -/
theorem refill_stage_ge {α β γ : Type} (planted : LState) (bits : BitInput)
    (computation : FreeQuery Programs.Spec α)
    (contPrivate : α × LState × Record → PMF (Option (Option β)))
    (contShared : α × LState × Record → PMF (Option γ))
    (weightM : Option (Option β) → ℝ≥0∞) (weightH : Option γ → ℝ≥0∞)
    (flagZero : weightM none = 0) (abortLe : weightM (some none) ≤ weightH none)
    (mono : ∀ a sF sL record, FullRel planted sF sL →
      ∑' o, contPrivate (a, sL, record) o * weightM o
        ≤ ∑' o, contShared (a, sF, record) o * weightH o) :
    ∑' o, refillStageM planted bits computation contPrivate o * weightM o
      ≤ ∑' o, refillStageH planted bits computation contShared o * weightH o := by
  unfold refillStageM refillStageH refillRun
  rw [PMF.bind_bind, tsum_bind_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
  rw [tsum_bind_mul, tsum_bind_mul]
  let hL : Option (α × LState × Record) → ℝ≥0∞ := fun r => match r with
    | none => weightM (some none)
    | some ran => ∑' o, contPrivate ran o * weightM o
  let hF : Option (α × LState × Record) → ℝ≥0∞ := fun r => match r with
    | none => weightH none
    | some ran => ∑' o, contShared ran o * weightH o
  have left : ∀ r : Option (Option (α × LState × Record)),
      ∑' o, flagCont contPrivate r o * weightM o = flagged hL r := by
    rintro (_ | _ | ran)
    · simp only [flagCont, tsum_pure_mul, flagZero, flagged]
    · simp only [flagCont, tsum_pure_mul]; rfl
    · rfl
  have right : ∀ r : Option (α × LState × Record),
      ∑' o, abortCont contShared r o * weightH o = hF r := by
    rintro (_ | ran)
    · simp only [abortCont, tsum_pure_mul]; rfl
    · rfl
  calc _ = ∑' r, runRefillFlag planted bits (fun cell => PMF.pure (tape cell)) computation
          LazyOracle.empty noRecord ∅ r * flagged hL r :=
        tsum_congr fun r => by rw [left r]
    _ ≤ ∑' r, runRefill bits (fun cell => PMF.pure (tape cell)) computation planted
          noRecord ∅ r * hF r :=
        runRefill_ge planted bits _ hF hL abortLe mono computation planted LazyOracle.empty _ ∅
          (fullRel_base planted)
    _ = _ := tsum_congr fun r => by rw [right r]

/-- **`M`'s stage 2 is dominated by `HW`'s**, for every shadow, stage-1 state and adversary stage 2. -/
theorem stage2_dominates (shadow : Shadow) (scalar : NonZeroScalar) (source : Stage1Source)
    (input : AffineInput) (output : Option Point) (planted : LState) {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex)
      Bool budget) (b : Bool) :
    ∑' o, middleStage2 shadow scalar source input output planted o * contM decide b o
      ≤ ∑' o, (openedSimulator (realRows scalar) skipInstallation).stage2 source input output planted o
          * contHW decide b o := by
  cases output with
  | none =>
    have rhs : ∑' o, (openedSimulator (realRows scalar) skipInstallation).stage2 source input none
        planted o * contHW decide b o = contHW decide b (some (sourceLabels source input, planted)) :=
      tsum_pure_mul _ _
    rw [rhs]
    exact shadow_law_step shadow.law decide b _ planted planted LazyOracle.empty
      (fullRel_base planted) _ fun coin => shadow_step decide b _ planted planted LazyOracle.empty
        (fullRel_base planted) _ _
  | some target =>
    have eqO : openedOpening (realRows scalar) skipInstallation source.publicValue input
        (sourceLabels source input) target planted =
        refillStageH planted (Lamport.restore input (sourceLabels source input)).input
          (openingQueriesM source.publicValue (Lamport.restore input (sourceLabels source input)).input
            (Lamport.restore input (sourceLabels source input)).inputMac)
          (openedCont (realRows scalar) skipInstallation source.publicValue input
            (sourceLabels source input) target) := by
      unfold openedOpening refillStageH
      dsimp only
      congr 1
      funext ran
      cases ran <;> rfl
    rw [stage2_some_eq, tsum_map_mul, eqO]
    exact refill_stage_ge planted _ _ (privateCont shadow scalar planted source input)
      (openedCont (realRows scalar) skipInstallation source.publicValue input
        (sourceLabels source input) target) (contM decide b)
      (fun o => contHW decide b (o.map fun updated => (sourceLabels source input, updated)))
      rfl le_rfl (fun lanes sF sL record rel => privateCont_dominates shadow scalar source input
        target planted decide b lanes record sF sL rel)

/-! ### The game -/

/-- The adversary's stage 2 after `M`'s stage 2 (a flag stays up, an abort is `false`). -/
def finishM {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex)
      Bool budget) : Option (Option (LamportSignature × LState)) → PMF (Option Bool)
  | none => PMF.pure none
  | some none => PMF.pure (some false)
  | some (some (labels, updated)) => ((LazyOracle.run (decide labels) updated).map Prod.fst).map some

theorem finishM_some {budget : ℕ}
    (decide : LamportSignature → OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex)
      Bool budget) (b : Bool) (o : Option (Option (LamportSignature × LState))) :
    finishM decide o (some b) = contM decide b o := by
  rcases o with _ | _ | ⟨labels, updated⟩
  · simp [finishM, contM]
  · by_cases hb : b = false <;> simp [finishM, contM, contHW, PMF.pure_apply, hb]
  · simp only [finishM, contM, contHW]
    exact map_some_apply _ _

/-- **The middle game `M` of a shadow**: `HW`'s stage 1 and input choice, `M`'s stage 2. -/
def middleGame (shadow : Shadow) (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) : PMF (Option Bool) :=
  (PMF.uniformOfFintype Stage1Source).bind fun source =>
    (LazyOracle.run (adversary.chooseInput parameter source.publicValue ()) LazyOracle.empty).bind
      fun selected =>
        (middleStage2 shadow scalar source selected.1.1 (Scheme.scheme.function scalar selected.1.1)
            selected.2).bind
          (finishM fun labels => adversary.decide parameter source.publicValue labels () selected.1.2)

/-- **`Below HW M`, for every shadow.** -/
theorem middle_below (shadow : Shadow) (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    Below (publicFirstHybrid adversary parameter scalar) (middleGame shadow adversary parameter scalar) := by
  intro b
  unfold publicFirstHybrid
  rw [abstractIdealGame_eq_staged]
  unfold stagedGame middleGame
  rw [PMF.bind_apply, PMF.bind_apply]
  have stage1 : (openedSimulator (realRows scalar) skipInstallation).stage1 parameter LazyOracle.empty
      = ((PMF.uniformOfFintype Stage1Source).map some).map
          (Option.map fun (source : Stage1Source) => ((source.publicValue, source, LazyOracle.empty) :
            Public × (openedSimulator (realRows scalar) skipInstallation).State × LState)) := rfl
  rw [stage1, tsum_map_mul, tsum_map_mul]
  refine ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl ?_
  dsimp only [Option.map_some]
  rw [PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun selected => mul_le_mul' le_rfl ?_
  rw [PMF.bind_apply, PMF.bind_apply]
  let decide := fun labels => adversary.decide parameter source.publicValue labels () selected.1.2
  calc ∑' second, middleStage2 shadow scalar source selected.1.1
          (Scheme.scheme.function scalar selected.1.1) selected.2 second
          * finishM decide second (some b)
      = ∑' second, middleStage2 shadow scalar source selected.1.1
          (Scheme.scheme.function scalar selected.1.1) selected.2 second * contM decide b second :=
        tsum_congr fun second => by rw [finishM_some]
    _ ≤ ∑' second, (openedSimulator (realRows scalar) skipInstallation).stage2 source selected.1.1
          (Scheme.scheme.function scalar selected.1.1) selected.2 second
          * contHW decide b second :=
        stage2_dominates shadow scalar source selected.1.1 _ selected.2 decide b
    _ = _ := tsum_congr fun second => by
        congr 1
        rcases second with _ | ⟨labels, updated⟩ <;> rfl

end Stage2

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
