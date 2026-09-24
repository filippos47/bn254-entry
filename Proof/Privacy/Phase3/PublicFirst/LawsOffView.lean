/-
**Phase 3, P1n — the off-curve law, step (ii), part 4: system A reads only the view.**

* `systemAM_view`: off the curve, system A on any published value and MAC asks only the view's
  fold gates (`viewIdx`: at every paid fold step of every chunk, both halves of every curve-lane
  gate off the step's active parent) and the view's limbs (the `limbCount ℓ` hash limbs of every
  inactive switch of the curve lanes, `ViewSiteP`, at any label), so its transcript on fixed-key
  answers and a limb tape `(v, T)` is its transcript on the answers rebuilt from `v ∘ viewIdx` and
  the view limbs of `T` (`extV`, `replaceView`);
* `tsum_maskTape_view`: given the mask vectors, the mask tape's view limbs are uniform on the view
  vectors' fibre (`Hidden.fibreLaw_masksOf_split`); so a weight of the vectors and the view limbs,
  averaged over the mask tape, is its average over uniform vectors and the view fibre;
* `viewMasks_eq`: the view vectors are F4's visible curve masks, reorganised (`visEquiv`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOffLaw

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape cellInput uniformMaskTape)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate] (input : AffineInput)

/-! ### 1. The view's vector sites and limbs -/

/-- A view vector site: an inactive switch of a curve lane. -/
def ViewSiteP (site : VectorSite) : Prop :=
  laneIsCurve site.lane = true ∧ site.switch ≠ chunkOf (inputBits input site.lane.coord) site.chunk

instance : DecidablePred (ViewSiteP input) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- The lane of a view site. -/
abbrev viewLane : {site : VectorSite // ViewSiteP input site} → Lane :=
  onLane VectorSite.lane (ViewSiteP input)

/-- The view's limbs. -/
abbrev ViewSlot := LimbSlot (viewLane input)

/-- A tape's view limbs. -/
def viewCells (T : Tape) : ViewSlot input → Block × Block :=
  (splitSlots VectorSite.lane (ViewSiteP input) T).2

/-- A tape with its view limbs replaced. -/
def replaceView (T : Tape) (t : ViewSlot input → Block × Block) : Tape :=
  (splitSlots VectorSite.lane (ViewSiteP input)).symm
    ((splitSlots VectorSite.lane (ViewSiteP input) T).1, t)

theorem replaceView_view (T : Tape) (t : ViewSlot input → Block × Block)
    (site : {site : VectorSite // ViewSiteP input site}) (limb : Fin (limbCount site.1.lane)) :
    replaceView input T t ⟨site.1, limb⟩ = t ⟨site, limb⟩ := by
  show (if h : ViewSiteP input site.1 then t ⟨⟨site.1, h⟩, limb⟩ else _) = _
  rw [dif_pos site.2]

/-! ### 2. The mask tape at the view limbs -/

/-- The view's mask vectors. -/
def viewMasks (m : MaskVectors) : LaneVectors (viewLane input) :=
  (splitVectors VectorSite.lane (ViewSiteP input) m).2

/-- **Given the vectors, the view limbs are uniform on the view vectors' fibre.** -/
theorem fibreLaw_view (m : MaskVectors) :
    (fibreLaw (masksOf VectorSite.lane) (masksOf_surjective VectorSite.lane) m).map
        (viewCells input) =
      fibreLaw (masksOf (viewLane input)) (masksOf_surjective _) (viewMasks input m) := by
  have factor : viewCells input = Prod.snd ∘ splitSlots VectorSite.lane (ViewSiteP input) := rfl
  rw [factor, ← PMF.map_comp, fibreLaw_masksOf_split VectorSite.lane (ViewSiteP input) m,
    productPMF_map_snd]
  rfl

/-- **A weight of the vectors and the view limbs, averaged over the mask tape**, is its average
over uniform vectors and the view's fibre. -/
theorem tsum_maskTape_view (G : MaskVectors → (ViewSlot input → Block × Block) → ℝ≥0∞) :
    ∑' T, uniformMaskTape T * G (masksOf VectorSite.lane T) (viewCells input T) =
      ∑' m, PMF.uniformOfFintype MaskVectors m *
        ∑' t, fibreLaw (masksOf (viewLane input)) (masksOf_surjective _) (viewMasks input m) t *
          G m t := by
  unfold uniformMaskTape
  rw [tsum_bind_mul]
  refine tsum_congr fun m => congrArg _ ?_
  have onFibre : ∀ T, fibreLaw (masksOf VectorSite.lane) (masksOf_surjective VectorSite.lane) m T *
      G (masksOf VectorSite.lane T) (viewCells input T) =
      fibreLaw (masksOf VectorSite.lane) (masksOf_surjective VectorSite.lane) m T *
        G m (viewCells input T) := by
    intro T
    rw [fibreLaw_apply]
    split_ifs with hit
    · rw [hit]
    · rw [zero_mul, zero_mul]
  rw [tsum_congr onFibre, ← fibreLaw_view input m, tsum_map_mul]

/-- **Uniform vectors have uniform view vectors.** -/
theorem viewMasks_uniform :
    (PMF.uniformOfFintype MaskVectors).map (viewMasks input) =
      PMF.uniformOfFintype (LaneVectors (viewLane input)) :=
  uniform_map_snd_of_equiv (splitVectors VectorSite.lane (ViewSiteP input))

/-! ### 3. The view vectors are F4's visible curve masks -/

/-- The visible curve masks' coordinates: a curve element and an inactive (chunk, switch). -/
abbrev CurveW :=
  Σ e : CurveMembership.Element, {cs : ChunkSwitch // ¬ Active ((offShape input).curveAlpha e) cs}

/-- The view vectors' coordinates: a view site and an element slot of its lane. -/
abbrev ViewCoord :=
  Σ site : {site : VectorSite // ViewSiteP input site}, Fin (laneCount site.1.lane)

/-- A visible curve mask is a coordinate of a view vector. -/
def viewCoordEquiv : CurveW input ≃ ViewCoord input where
  toFun
    | ⟨.inl e, cs⟩ => ⟨⟨⟨.curveX, cs.1.1, cs.1.2⟩, ⟨rfl, cs.2⟩⟩, curveXSlots e⟩
    | ⟨.inr e, cs⟩ => ⟨⟨⟨.curveY, cs.1.1, cs.1.2⟩, ⟨rfl, cs.2⟩⟩, curveYSlots e⟩
  invFun
    | ⟨⟨⟨.curveX, c, j⟩, view⟩, i⟩ => ⟨.inl (curveXSlots.symm i), ⟨⟨c, j⟩, view.2⟩⟩
    | ⟨⟨⟨.curveY, c, j⟩, view⟩, i⟩ => ⟨.inr (curveYSlots.symm i), ⟨⟨c, j⟩, view.2⟩⟩
    | ⟨⟨⟨.pointX, _, _⟩, view⟩, _⟩ => (Bool.false_ne_true view.1).elim
    | ⟨⟨⟨.pointY, _, _⟩, view⟩, _⟩ => (Bool.false_ne_true view.1).elim
  left_inv := by
    rintro ⟨e | e, cs⟩
    · show (⟨.inl (curveXSlots.symm (curveXSlots e)), ⟨⟨cs.1.1, cs.1.2⟩, cs.2⟩⟩ :
        CurveW input) = _
      rw [Equiv.symm_apply_apply]
    · show (⟨.inr (curveYSlots.symm (curveYSlots e)), ⟨⟨cs.1.1, cs.1.2⟩, cs.2⟩⟩ :
        CurveW input) = _
      rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨⟨lane, c, j⟩, view⟩, i⟩
    cases lane
    · show (⟨⟨⟨.curveX, c, j⟩, view⟩, curveXSlots (curveXSlots.symm i)⟩ : ViewCoord input) = _
      rw [Equiv.apply_symm_apply]
    · show (⟨⟨⟨.curveY, c, j⟩, view⟩, curveYSlots (curveYSlots.symm i)⟩ : ViewCoord input) = _
      rw [Equiv.apply_symm_apply]
    · exact (Bool.false_ne_true view.1).elim
    · exact (Bool.false_ne_true view.1).elim

/-- **The visible curve masks are the view vectors.** -/
def visEquiv : CurveVisible (offShape input) ≃ LaneVectors (viewLane input) :=
  (Equiv.piCurry fun (e : CurveMembership.Element)
      (_ : {cs : ChunkSwitch // ¬ Active ((offShape input).curveAlpha e) cs}) =>
        BaseField).symm.trans
    ((Equiv.arrowCongr (viewCoordEquiv input) (Equiv.refl BaseField)).trans
      (Equiv.piCurry fun (site : {site : VectorSite // ViewSiteP input site})
        (_ : Fin (laneCount site.1.lane)) => BaseField))

/-- **The view vectors of the mask vectors are their visible curve masks.** -/
theorem viewMasks_eq (m : MaskVectors) :
    viewMasks input m =
      visEquiv input (curveVisible (offShape input) (maskSiteEquiv (maskCoordEquiv m)).2) := by
  funext site i
  obtain ⟨⟨lane, c, j⟩, view⟩ := site
  cases lane
  · show m ⟨.curveX, c, j⟩ i =
      (maskSiteEquiv (maskCoordEquiv m)).2 (.inl (curveXSlots.symm i)) ⟨c, j⟩
    rw [masks_curveX, Equiv.apply_symm_apply]
  · show m ⟨.curveY, c, j⟩ i =
      (maskSiteEquiv (maskCoordEquiv m)).2 (.inr (curveYSlots.symm i)) ⟨c, j⟩
    rw [masks_curveY, Equiv.apply_symm_apply]
  · exact (Bool.false_ne_true view.1).elim
  · exact (Bool.false_ne_true view.1).elim

/-! ### 4. System A reads only the view -/

/-- A question system A may ask off the curve: a view gate, or a view limb at any label. -/
def ViewQ : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward index _ => IsView input index
  | .hash key =>
      ∃ (cell : Cell) (label : Block), ViewSiteP input cell.1 ∧ key = cellInput cell label
  | _ => False

theorem transcript_agree_on {α : Type} {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}
    {P : FreeQuery Programs.Spec α} (only : Hidden.QueryOnly S P)
    (a b : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (same : ∀ q, S q → a q = b q) : transcript a P = transcript b P := by
  induction only with
  | pure value => rfl
  | query request next holds rest ih =>
      show ⟨request, a request⟩ :: transcript a (next (a request)) =
        ⟨request, b request⟩ :: transcript b (next (b request))
      rw [same request holds, ih]

theorem evalStepM_view (lane : Lane) (curve : laneIsCurve lane = true) (chunk : Fin chunkCount)
    (step : Nat) (below : step < chunkWidth chunk) (bitLabel join : Block)
    (parent : Fin (2 ^ step) → Block) :
    Hidden.QueryOnly (ViewQ input) (Programs.evalStepM lane chunk step bitLabel join
      (activeAt (chunkOf (inputBits input lane.coord) chunk).val step) parent) := by
  unfold Programs.evalStepM
  refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun e => ?_) fun _ =>
    Hidden.QueryOnly.pure' _
  by_cases active : e = activeAt (chunkOf (inputBits input lane.coord) chunk).val step
  · rw [if_pos active]
    exact Hidden.QueryOnly.pure' _
  · rw [if_neg active]
    have off : e.val ≠ (chunkOf (inputBits input lane.coord) chunk).val % 2 ^ step :=
      fun same => active (Fin.ext same)
    have positive : 0 < step := by
      rcases Nat.eq_zero_or_pos step with zero | positive
      · subst zero
        have small := e.isLt
        simp only [pow_zero, Nat.lt_one_iff] at small
        exact absurd (by rw [small, pow_zero, Nat.mod_one]) off
      · exact positive
    have gate : ∀ half, ViewQ input (.fixedForward (hotIndexNat lane chunk step e.val half)
        (parent e)) :=
      fun half => ⟨lane, chunk, step, e.val, half, curve, positive, below, e.isLt, off, rfl⟩
    exact Hidden.QueryOnly.bind (hashM_only _ _ (gate false)) fun _ =>
      Hidden.QueryOnly.bind (hashM_only _ _ (gate true)) fun _ => Hidden.QueryOnly.pure' _

theorem evalFoldM_view (lane : Lane) (curve : laneIsCurve lane = true) (chunk : Fin chunkCount)
    (bitLabel join : Nat → Block) : ∀ n, n ≤ chunkWidth chunk →
      Hidden.QueryOnly (ViewQ input) (Programs.evalFoldM lane chunk
        (chunkOf (inputBits input lane.coord) chunk).val bitLabel join n)
  | 0, _ => Hidden.QueryOnly.pure' _
  | n + 1, bound =>
      Hidden.QueryOnly.bind (evalFoldM_view lane curve chunk bitLabel join n (by omega))
        fun previous => Hidden.QueryOnly.bind
          (evalStepM_view input lane curve chunk n (by omega) _ _ previous) fun _ =>
            Hidden.QueryOnly.pure' _

theorem evalMasksM_view (lane : Lane) (curve : laneIsCurve lane = true) (chunk : Fin chunkCount)
    (hot : HotLabels (chunkWidth chunk)) :
    Hidden.QueryOnly (ViewQ input) (Programs.evalMasksM lane chunk (chunkWidth chunk) hot
      (chunkOf (inputBits input lane.coord) chunk)) := by
  unfold Programs.evalMasksM
  refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun switch => ?_) fun _ =>
    Hidden.QueryOnly.pure' _
  by_cases active : switch = chunkOf (inputBits input lane.coord) chunk
  · rw [if_pos active]
    exact Hidden.QueryOnly.pure' _
  · rw [if_neg active]
    refine (Hidden.switchMaskM_only lane chunk switch.val (hot switch)).imp fun q hit => ?_
    obtain ⟨limb, rfl⟩ := hit
    exact ⟨⟨⟨lane, chunk, switch⟩, limb⟩, hot switch, ⟨curve, active⟩, rfl⟩

theorem evalLaneM_view (lane : Lane) (curve : laneIsCurve lane = true)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (labels : Fin coordinateBitCount → Block) :
    Hidden.QueryOnly (ViewQ input)
      (Programs.evalLaneM lane joins scale (inputBits input lane.coord) labels) := by
  unfold Programs.evalLaneM
  refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun c => ?_) fun _ =>
    Hidden.QueryOnly.pure' _
  unfold Programs.evalChunkM
  rw [chunkValue_toNat]
  exact Hidden.QueryOnly.bind (evalFoldM_view input lane curve c _ _ _ le_rfl) fun hot =>
    Hidden.QueryOnly.bind (evalMasksM_view input lane curve c hot) fun _ => Hidden.QueryOnly.pure' _

/-- **System A asks only view questions**, off the curve, on any published value and MAC. -/
theorem systemAM_only (P : Public) (mac : InputMac) :
    Hidden.QueryOnly (ViewQ input) (systemAM P (BitInput.ofAffine input) mac) := by
  unfold systemAM
  exact Hidden.QueryOnly.bind (evalLaneM_view input .curveX rfl _ _ _) fun _ =>
    Hidden.QueryOnly.bind (evalLaneM_view input .curveY rfl _ _ _) fun _ => Hidden.QueryOnly.pure' _

open Classical in
/-- Fixed-key answers rebuilt from the view's fold answers. -/
def extV (w : ViewIdx input → Block) : FixedIndex → Block := fun i =>
  if h : IsView input i then w ⟨i, h⟩ else 0

/-- **System A's transcript on fixed-key answers and a limb tape is its transcript on the
view.** -/
theorem systemAM_view (P : Public) (mac : InputMac) (v : FixedIndex → Block) (T : Tape) :
    transcript (fixedAnswer v T) (systemAM P (BitInput.ofAffine input) mac) =
      transcript (fixedAnswer (extV input (v ∘ viewIdx input))
        (replaceView input (fun _ => (0, 0)) (viewCells input T)))
        (systemAM P (BitInput.ofAffine input) mac) := by
  refine transcript_agree_on (systemAM_only input P mac) _ _ fun q view => ?_
  cases q with
  | fixedForward index x =>
      show v index = extV input (v ∘ viewIdx input) index
      unfold extV
      rw [dif_pos (show IsView input index from view)]
      rfl
  | hash key =>
      obtain ⟨cell, label, site, rfl⟩ := view
      rw [fixedAnswer, fixedAnswer, tableAnswer_cell, tableAnswer_cell]
      exact (replaceView_view input (fun _ => (0, 0)) (viewCells input T) ⟨cell.1, site⟩
        cell.2).symm
  | _ => exact view.elim

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
