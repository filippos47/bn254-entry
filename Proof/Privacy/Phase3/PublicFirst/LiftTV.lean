/-
**Phase 3, P1j — the lift, part 3: the designed shadow and the refined mask-tape distance.**

**The designed shadow** (`designedShadow scalar := planBShadow scalar designedOff`): on the curve
P1i's (the prefix again, the bit-`true` pads, the whole evaluator, the generalised exceptional
reveal); **off the curve** `designedOff`: both pads of every position at a uniform coin `k₁`
(`Programs.padsM`, the garbler's own EncPRF questions) and system A's two lanes (`systemAM`, the
evaluator's; exactly the designed entries of `G1U°` off the curve), no reveal flag.

**The refined distance** (`designedShadow_etvDist_le`): the two tape readings of `M'` are within
the curve lanes' share of the mask swap, `Σ_{v curve site} laneDelta v.lane = 1396·(δ_curveX +
δ_curveY)` (`LiftHop.curveSwapError`), not the whole swap:

* the off-curve fill of the designed shadow asks the hash only at cell inputs of the two curve
  lanes (`designedOffM_allQ`: `evalLaneM_allQ`; the pads are EncPRF questions and the fold gates
  fixed-key ones), so it reads the tape only at the curve sites' limbs
  (`runFillFlag_tape_congr_on`);
* the mask tape restricted to those limbs is the mask tape of the curve sites
  (`maskTape_restrict`, from `Hidden.fibreLaw_masksOf_split`: given the vectors the two families of
  limbs are independent), and the uniform tape restricts to the uniform one (`uniform_restrict`);
* so the distance is the batched sampler's bias at the curve sites (`fill_etvDist_le`,
  `masksOf_etvDist_le`), and the curve sites are `1396` vectors per curve lane
  (`sum_curveSite_laneDelta`).

**`planB_publicFirst_of_lift`**: the Glue's `publicFirst` at its constant
`stageOneHitError q₁ + exceptionalError + maskSwapError + coincidenceError`, from `DesignedLift`
(the F4 lift for the designed shadow, at the designed rule), `DesignedBounds` (P1k's (B1)/(B2) for
the designed shadow) and `CoincidenceBound coincidenceError`.
-/

import Proof.Privacy.Phase3.PublicFirst.LiftHop
import Proof.Privacy.Phase3.PublicFirst.Shadow
import Proof.Privacy.Phase3.Lazy.Decompose
import Proof.Privacy.Phase3.Hidden.Split

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary Stage1Source maskSwapError coincidenceError
  laneVectorCount)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Tape Cell Request uniformMaskTape AllQ LaneAt EncAt
  cellOf cellOf_cellInput consumeCell_spec evalLaneM_allQ padM_allQ etvDist_bind_le_of_support)
open scoped ENNReal

noncomputable section

/-! ### 1. The designed off-curve shadow -/

section Shadow

variable [FieldCertificate] [GroupCertificate]

/-- **System A's two lanes**: the evaluator's prefix without the bridge hash. -/
def systemAM (table : Public) (bits : BitInput) (mac : InputMac) : Programs.M Unit :=
  Programs.evalLaneM .curveX table.curveXHot
      (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x) >>= fun _ =>
    Programs.evalLaneM .curveY table.curveYHot
        (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
        (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y) >>= fun _ => pure ()

/-- **The designed off-curve questions**: both pads of every position at the key `k₁`, then
system A. -/
def designedOffM (table : Public) (bits : BitInput) (mac : InputMac) (first : Block) :
    Programs.M Unit :=
  Programs.padsM ⟨first, 0⟩ >>= fun _ => systemAM table bits mac

/-- **The designed off-curve shadow**: a uniform `k₁`, the pads and system A, no reveal. -/
def designedOff : OffShadow where
  Coin := Block
  law := PMF.uniformOfFintype Block
  offCurve source input first :=
    designedOffM source.publicValue (Lamport.restore input (sourceLabels source input)).input
      (Lamport.restore input (sourceLabels source input)).inputMac first
  revealOff _ _ _ _ := False

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The designed shadow of `M'`**: P1i's on the curve, `designedOff` off it. -/
def designedShadow (scalar : NonZeroScalar) : Shadow := planBShadow scalar designedOff

end Shadow

/-! ### 2. The curve sites and their limbs -/

/-- A curve-lane (system A) vector site. -/
def CurveSiteP (site : VectorSite) : Prop := laneIsCurve site.lane = true

instance : DecidablePred CurveSiteP := fun site =>
  inferInstanceAs (Decidable (laneIsCurve site.lane = true))

/-- The lane of a curve site. -/
abbrev curveLane : {site : VectorSite // CurveSiteP site} → Lane :=
  onLane VectorSite.lane CurveSiteP

/-- The limbs of the curve sites. -/
abbrev CurveSlot := LimbSlot curveLane

/-- The curve limbs of a tape. -/
def curvePart (tape : Tape) : CurveSlot → Block × Block :=
  (splitSlots VectorSite.lane CurveSiteP tape).2

theorem curvePart_apply (tape : Tape) (slot : CurveSlot) :
    curvePart tape slot = tape ⟨slot.1.1, slot.2⟩ := rfl

/-- **The curve sites carry the curve lanes' share of the swap**: `1396` vectors per curve lane. -/
theorem sum_curveSite_laneDelta :
    ∑ site : {site : VectorSite // CurveSiteP site}, laneDelta (curveLane site) =
      (laneVectorCount : ℝ≥0∞) * (laneDelta .curveX + laneDelta .curveY) := by
  classical
  let g : Lane → ℝ≥0∞ := fun lane => if laneIsCurve lane = true then laneDelta lane else 0
  have subtype : ∑ site : {site : VectorSite // CurveSiteP site}, laneDelta (curveLane site) =
      ∑ site : VectorSite, g site.lane := by
    rw [← Finset.sum_subtype (Finset.univ.filter CurveSiteP) (fun site => by simp)
      (fun site : VectorSite => laneDelta site.lane), Finset.sum_filter]
    rfl
  rw [subtype, sum_vectorSite_lane g]
  have pair : ∑ lane : Lane, 1396 • g lane =
      ∑ lane ∈ ({.curveX, .curveY} : Finset Lane), 1396 • g lane := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun lane _ notPair => ?_).symm
    cases lane
    · exact absurd (by simp) notPair
    · exact absurd (by simp) notPair
    · simp [g, laneIsCurve]
    · simp [g, laneIsCurve]
  rw [pair, Finset.sum_pair (by decide), ← smul_add, nsmul_eq_mul]
  rfl

/-- The second marginal of a product. -/
theorem productPMF_map_snd {A C : Type} (first : PMF A) (second : PMF C) :
    (productPMF first second).map Prod.snd = second := by
  rw [productPMF, PMF.map_bind]
  have constant : ∀ value : A, (second.map (Prod.mk value)).map Prod.snd = second :=
    fun value => by rw [PMF.map_comp]; exact PMF.map_id second
  simp only [constant]
  exact PMF.bind_const first second

/-- A map along an equivalence reads the uniform law at the second factor. -/
theorem uniform_map_snd_of_equiv {X A B : Type} [Fintype X] [Nonempty X] [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (split : X ≃ A × B) :
    (PMF.uniformOfFintype X).map (fun x => (split x).2) = PMF.uniformOfFintype B := by
  have factor : (fun x => (split x).2) = Prod.snd ∘ split := rfl
  rw [factor, ← PMF.map_comp, Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv,
    uniformOfFintype_productPMF, productPMF_map_snd]

/-- The mask tape of the curve sites: their vectors uniform, then their limbs uniform on the
vectors' fibre. -/
def curveMaskTape : PMF (CurveSlot → Block × Block) := swapLimbLaw curveLane

/-! ### 3. The mask tape restricts to the curve sites -/

/-- **The mask tape restricted to the curve limbs is the curve mask tape.** -/
theorem maskTape_restrict : uniformMaskTape.map curvePart = curveMaskTape := by
  unfold uniformMaskTape curveMaskTape swapLimbLaw curvePart
  rw [PMF.map_bind]
  have step : ∀ vectors : MaskVectors,
      (fibreLaw (masksOf VectorSite.lane) (masksOf_surjective VectorSite.lane) vectors).map
          (fun tape => (splitSlots VectorSite.lane CurveSiteP tape).2) =
        fibreLaw (masksOf curveLane) (masksOf_surjective _)
          (splitVectors VectorSite.lane CurveSiteP vectors).2 := by
    intro vectors
    have split := fibreLaw_masksOf_split VectorSite.lane CurveSiteP vectors
    have factor : (fun tape : Tape => (splitSlots VectorSite.lane CurveSiteP tape).2) =
        Prod.snd ∘ splitSlots VectorSite.lane CurveSiteP := rfl
    rw [factor, ← PMF.map_comp, split, productPMF_map_snd]
  simp only [step]
  rw [← uniform_map_snd_of_equiv (splitVectors VectorSite.lane CurveSiteP), PMF.bind_map]
  rfl

/-- **The uniform tape restricts to the uniform one.** -/
theorem uniform_restrict :
    (PMF.uniformOfFintype Tape).map curvePart =
      PMF.uniformOfFintype (CurveSlot → Block × Block) :=
  uniform_map_snd_of_equiv (splitSlots VectorSite.lane CurveSiteP)

/-- **The refined distance**: a law read off the curve limbs only moves by the curve sites' bias. -/
theorem fill_etvDist_le {β : Type} (read : Tape → PMF β)
    (local_ : ∀ first second, curvePart first = curvePart second → read first = read second) :
    (uniformMaskTape.bind read).etvDist ((PMF.uniformOfFintype Tape).bind read)
      ≤ ∑ site : {site : VectorSite // CurveSiteP site}, laneDelta (curveLane site) := by
  let extend : (CurveSlot → Block × Block) → Tape := fun curve =>
    (splitSlots VectorSite.lane CurveSiteP).symm (fun _ => (0, 0), curve)
  have restrictExtend : ∀ curve, curvePart (extend curve) = curve := fun curve =>
    congrArg Prod.snd ((splitSlots VectorSite.lane CurveSiteP).apply_symm_apply (fun _ => (0, 0),
      curve))
  have factor : read = (read ∘ extend) ∘ curvePart :=
    funext fun tape => local_ tape _ (restrictExtend (curvePart tape)).symm
  rw [factor, ← PMF.bind_map uniformMaskTape curvePart (read ∘ extend),
    ← PMF.bind_map (PMF.uniformOfFintype Tape) curvePart (read ∘ extend), maskTape_restrict,
    uniform_restrict]
  refine le_trans (PMF.etvDist_bind_right_le _ _ _) ?_
  unfold curveMaskTape swapLimbLaw
  rw [uniform_eq_bind_fibreLaw (masksOf curveLane) (masksOf_surjective curveLane)]
  refine le_trans (PMF.etvDist_bind_right_le _ _ _) ?_
  rw [PMF.etvDist_comm]
  exact masksOf_etvDist_le curveLane

/-! ### 4. The designed off-curve fill reads only the curve limbs -/

/-- A question consumes, if anything, a curve limb: a hash question at a cell input names a curve
site. -/
def CurveCellsOnly : Request → Prop
  | .hash input => ∀ cell : Cell, cellOf input = some cell → CurveSiteP cell.1
  | _ => True

theorem curveCellsOnly_of_lane (lane : Lane) (curve : laneIsCurve lane = true) (request : Request)
    (inside : ∃ c, LaneAt lane c request) : CurveCellsOnly request := by
  cases request with
  | hash input =>
    intro cell found
    obtain ⟨c, fixedAt | ⟨cell', label, laneEq, _, rfl⟩⟩ := inside
    · exact fixedAt.elim
    · rw [cellOf_cellInput] at found
      cases found
      unfold CurveSiteP
      rw [laneEq]
      exact curve
  | fixedForward _ _ => trivial
  | fixedInverse _ _ => trivial
  | encForward _ _ => trivial
  | encInverse _ _ => trivial

theorem curveCellsOnly_of_enc (request : Request) (_inside : EncAt request) :
    CurveCellsOnly request := by
  cases request with
  | hash _ => exact _inside.elim
  | fixedForward _ _ => trivial
  | fixedInverse _ _ => trivial
  | encForward _ _ => trivial
  | encInverse _ _ => trivial

theorem padsM_allQ (keys : WhiteningKeys) : AllQ EncAt (Programs.padsM keys) := by
  unfold Programs.padsM
  exact (AllQ.vector fun _ => (padM_allQ _ _ _ _).bind fun _ =>
    (padM_allQ _ _ _ _).bind fun _ => .pure _).bind fun _ =>
      (AllQ.vector fun _ => (padM_allQ _ _ _ _).bind fun _ =>
        (padM_allQ _ _ _ _).bind fun _ => .pure _).bind fun _ => .pure _

theorem designedOffM_allQ [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac)
    (first : Block) : AllQ CurveCellsOnly (designedOffM table bits mac first) := by
  unfold designedOffM systemAM
  refine ((padsM_allQ _).mono curveCellsOnly_of_enc).bind fun _ => ?_
  refine ((evalLaneM_allQ _ _ _ _ _).mono (curveCellsOnly_of_lane .curveX rfl)).bind fun _ => ?_
  exact ((evalLaneM_allQ _ _ _ _ _).mono (curveCellsOnly_of_lane .curveY rfl)).bind fun _ =>
    .pure _

section Fill

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The fill reads the tape only at the limbs its questions consume.** -/
theorem runFillFlag_tape_congr_on (planted : LState) {α : Type}
    {computation : FreeQuery Programs.Spec α} (holds : AllQ CurveCellsOnly computation) :
    ∀ (oracle : LState) (touched : Set Cell) (first second : Tape),
      curvePart first = curvePart second →
      runFillFlag planted (fun cell => PMF.pure (first cell)) computation oracle touched =
        runFillFlag planted (fun cell => PMF.pure (second cell)) computation oracle touched := by
  induction holds with
  | pure value => intros; rfl
  | query request next here _ ih =>
      intro oracle touched first second agree
      simp only [runFillFlag]
      split
      · rename_i cell consumed
        obtain ⟨input, rfl, _, _, found⟩ := consumeCell_spec consumed
        have curve : CurveSiteP cell.1 := here cell found
        have same : first cell = second cell := by
          have limb := congrFun agree ⟨⟨cell.1, curve⟩, cell.2⟩
          rw [curvePart_apply, curvePart_apply] at limb
          exact limb
        rw [same, PMF.pure_bind, PMF.pure_bind]
        split
        · rfl
        · split
          · rfl
          · exact ih _ _ _ _ _ agree
      · refine congrArg (PMF.bind _) (funext fun answer => ?_)
        split
        · rfl
        · exact ih _ _ _ _ _ agree

end Fill

/-! ### 5. The refined distance of the designed shadow's `M'` -/

section Distance

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **The two tape readings of the designed shadow's `M'` are within the curve sites' bias.** -/
theorem designedShadow_etvDist_le (scalar : NonZeroScalar) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) :
    (middleGameFill uniformMaskTape (designedShadow scalar) adversary parameter scalar).etvDist
        (middleGameFill (PMF.uniformOfFintype Tape) (designedShadow scalar) adversary parameter
          scalar)
      ≤ ∑ site : {site : VectorSite // CurveSiteP site}, laneDelta (curveLane site) := by
  unfold middleGameFill
  refine etvDist_bind_le_of_support _ _ _ _ fun source _ => ?_
  refine etvDist_bind_le_of_support _ _ _ _ fun selected _ => ?_
  refine le_trans (PMF.etvDist_bind_right_le _ _ _) ?_
  generalize Scheme.scheme.function scalar selected.1.1 = output
  cases output with
  | some target =>
    simp only [middleStage2Fill, PMF.etvDist_self]
    exact zero_le
  | none =>
    simp only [middleStage2Fill]
    refine etvDist_bind_le_of_support _ _ _ _ fun coin _ => ?_
    refine le_trans (PMF.etvDist_bind_right_le _ _ _) ?_
    exact fill_etvDist_le _ fun first second agree =>
      runFillFlag_tape_congr_on selected.2 (designedOffM_allQ _ _ _ _) _ _ first second agree

end Distance

/-! ### 6. The obligation of `LiftHop.lean` for the designed shadow -/

/-- **The lift at the designed rule, for the designed shadow** (the remaining content of (A)). -/
def DesignedLift : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      (letI := field
       letI := group
       letI : Fintype FixedIndex := Fintype.ofFinite FixedIndex
       letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
       letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
       letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
       FlagMono (g1uLaterWith designedInstall adversary parameter scalar)
         (middleGameFill uniformMaskTape (designedShadow scalar) adversary parameter scalar))

/-- **P1k's two (B) bounds, for the designed shadow.** -/
def DesignedBounds : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (scalar : NonZeroScalar),
    (letI := field
     letI := group
     letI : Fintype FixedIndex := Fintype.ofFinite FixedIndex
     letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
     letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
     letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
     PerPairBound (designedShadow scalar) scalar (4 / 2 ^ 128) ∧
       RevealBound (designedShadow scalar) scalar
         (ENNReal.ofReal Kriterion.ArgoMAC.Phase3.Glue.exceptionalError))

/-- **`LiftHop.lean`'s shadow obligation, from the lift and the bounds**: the refined distance is
real for the designed shadow. -/
theorem shadowObligationDesigned_of (lift : DesignedLift) (bounds : DesignedBounds) :
    ShadowObligationDesigned := by
  intro field group adversary parameter scalar small
  refine ⟨designedShadow (letI := field; letI := group; scalar), ?_⟩
  obtain ⟨perPair, reveal⟩ := bounds field group scalar
  refine ⟨lift field group adversary parameter scalar small, perPair, reveal, ?_⟩
  letI := field
  letI := group
  letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
  letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
  have distance := designedShadow_etvDist_le scalar adversary parameter
  rw [sum_curveSite_laneDelta] at distance
  exact distance

/-- **The Glue's `publicFirst`, from the lift, P1k's bounds and the coincidence bound.** -/
theorem planB_publicFirst_of_lift (lift : DesignedLift) (bounds : DesignedBounds)
    (coincidence : CoincidenceBound coincidenceError) :
    Kriterion.ArgoMAC.Phase3.Glue.GameCoreUntilBad
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.hiddenDeleted
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.publicFirst fun first _ =>
        Kriterion.ArgoMAC.Phase3.Glue.stageOneHitError first +
          Kriterion.ArgoMAC.Phase3.Glue.exceptionalError + maskSwapError + coincidenceError :=
  planB_publicFirst_of_designed (shadowObligationDesigned_of lift bounds) coincidence

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
