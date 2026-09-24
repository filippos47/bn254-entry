/-
**Phase 3, P1m — (B1): the hash conjunct of `PerPairBound`, on the curve.**

On the curve every hash key of `M'`'s private points is the opening's bridge input
`bridgeInput t` or a limb input `scaleInput lane c s limb L` of an inactive switch at its one-hot
label `L` (`final_hash`, the designated requests included). The two ranges are disjoint
(`bridgeInput_not_lt`, `scaleInput_val_lt_scaleRange`), so a key costs one of:

* **a scale key: `≤ 1/2^128`** — it names one (switch, limb) and one label (`cellInput_injective`),
  and the one-hot label of a switch hits a point with mass `≤ 1/2^128` (fold-label entropy,
  `opening_level_le`, at the chunk's last level `chunkWidth c ≥ 2`);
* **the bridge: `≤ 2/p`** — system A's values are functions of the tape's mask vectors
  (`lane_eval_tape`: every limb question of a lane reads its tape cell), so `t` is `curveMap` of the
  mask vectors (`tOf_tape`), affine in the `x7` coordinate of the chunk-`0` `curveX` vector of the
  switch `α₀ ⊕ 1` with the nonzero coefficient `ι(α₀ ⊕ 1) − ι(α₀)` (`curveMap_shift`); under
  `uniformMaskTape` the vectors are uniform, so `Pr[t = t₀] ≤ 1/p` (`uniform_affine_le`), and a key
  has at most two bridge preimages (`bridgeInput_filter_card_le_two`).

* **`hash_onCurve_le`** — on the curve, `Pr[k ∈ hashIn] ≤ max(1/2^128, 2/p) ≤ 4/2^128`, for the
  shadow `planBShadow scalar off` at any off-curve part.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedPoint

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM activeSwitch designatedSwitch
  chunkZero IsDesignated)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request queriesAlong cellInput cellOf
  cellOf_spec cellOf_cellInput cellInput_injective maskCell uniformMaskTape consumedCell
  queriesAlong_evalMasksM queriesAlong_switchMaskM designated_cellAt cellAt_unique
  scaleInput_cellAt interceptAnswer_plain)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### A lane's value from the mask vectors -/

section Value

/-- **The free fold is `ι(α)·join + Σ_{s ≠ α} (ι(s) − ι(α))·mask_s`.** -/
theorem evalScaleOf_linear {count : ℕ} (w : ℕ) (masks : Fin (2 ^ w) → Vector BaseField count)
    (alpha : Fin (2 ^ w)) (join : Fin count → BaseField) (el : Fin count) :
    Programs.evalScaleOf w masks alpha join el =
      iota _ alpha * join el +
        ∑ s ∈ Finset.univ.erase alpha, (iota _ s - iota _ alpha) * (masks s).get el := by
  unfold Programs.evalScaleOf
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ alpha), if_pos rfl]
  have rest : ∑ s ∈ Finset.univ.erase alpha, iota _ s *
      (if s = alpha then join el - ∑ other ∈ Finset.univ.erase alpha, (masks other).get el
        else (masks s).get el) =
      ∑ s ∈ Finset.univ.erase alpha, iota _ s * (masks s).get el :=
    Finset.sum_congr rfl fun s member => by rw [if_neg (Finset.ne_of_mem_erase member)]
  rw [rest, mul_sub, Finset.mul_sum]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- The mask vectors of chunk `c` of a lane, from a family of mask vectors (the active switch's slot
holds zeros, which the free fold never reads). -/
def laneMasks (m : MaskVectors) (lane : Lane) (word : BitVec coordinateBitCount)
    (c : Fin chunkCount) :
    Fin (2 ^ chunkWidth c) → Vector BaseField (laneCount lane) :=
  fun s => if s = chunkOf word c then Vector.ofFn fun _ => 0 else Vector.ofFn (m ⟨lane, c, s⟩)

theorem laneMasks_get {m : MaskVectors} {lane : Lane} {word : BitVec coordinateBitCount}
    {c : Fin chunkCount} {s : Fin (2 ^ chunkWidth c)} (inactive : s ≠ chunkOf word c)
    (el : Fin (laneCount lane)) : (laneMasks m lane word c s).get el = m ⟨lane, c, s⟩ el := by
  unfold laneMasks
  rw [if_neg inactive, Vector.get_ofFn]

/-- **A lane's value from a family of mask vectors.** -/
def laneValueM (m : MaskVectors) (lane : Lane)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (word : BitVec coordinateBitCount) :
    Fin (laneCount lane) → BaseField :=
  fun el => ∑ c : Fin chunkCount, Programs.evalScaleOf (chunkWidth c) (laneMasks m lane word c)
    (chunkOf word c) (scale c) el

variable [FieldCertificate]

/-- A limb question of an inactive switch is on its lane's path. -/
theorem lane_limb_question (ans : (request : Request) → request.Answer) (lane : Lane)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (word : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block)
    (c : Fin chunkCount) (s : Fin (2 ^ chunkWidth c)) (inactive : s ≠ chunkOf word c)
    (limb : Fin (limbCount lane)) :
    .hash (cellInput (maskCell lane c s limb)
      (laneFoldLevel ans lane joins word labels c (chunkWidth c) s))
      ∈ queriesAlong ans (Programs.evalLaneM lane joins scale word labels) := by
  rw [queriesAlong_evalLaneM]
  refine List.mem_flatMap.mpr ⟨c, List.mem_finRange c, ?_⟩
  rw [queriesAlong_evalChunkM]
  refine List.mem_append_right _ ?_
  rw [queriesAlong_evalMasksM]
  refine List.mem_flatMap.mpr ⟨s, List.mem_finRange s, ?_⟩
  rw [if_neg inactive, queriesAlong_switchMaskM]
  exact List.mem_map.mpr ⟨limb, List.mem_finRange limb, rfl⟩

/-- **A lane's value is its mask vectors' `laneValueM`** when every limb question on its path
reads its tape cell (whatever the labels). -/
theorem lane_eval_tape (ans : (request : Request) → request.Answer) (tape : Tape) (lane : Lane)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (word : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block)
    (reads : ∀ (cell : Cell) (label : Block), .hash (cellInput cell label) ∈
      queriesAlong ans (Programs.evalLaneM lane joins scale word labels) →
        ans (.hash (cellInput cell label)) = tape cell) :
    FreeQuery.eval ans (Programs.evalLaneM lane joins scale word labels) =
      laneValueM (masksOf VectorSite.lane tape) lane scale word := by
  funext el
  simp only [Programs.evalLaneM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    Vector.get_ofFn, laneValueM]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Programs.evalChunkM, FreeQuery.eval_bind, FreeQuery.eval_pure]
  congr 1
  funext s
  simp only [Programs.evalMasksM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    Vector.get_ofFn, laneMasks]
  split
  · rfl
  · rename_i inactive
    simp only [Programs.switchMaskM, FreeQuery.eval_bind, FreeQuery.eval_pure,
      FreeQuery.eval_vector]
    show _ = Vector.ofFn (sampleLane (laneCount lane) (limbCount lane) fun limb =>
      tape (maskCell lane c s limb))
    congr 1
    refine congrArg (sampleLane (laneCount lane) (limbCount lane)) (funext fun limb => ?_)
    rw [Vector.get_ofFn, eval_askHash]
    exact reads (maskCell lane c s limb) _ (lane_limb_question ans lane joins scale word labels c s
      inactive limb)

end Value

/-! ### The opening's bridge value from the tape's mask vectors -/

section Bridge

variable [FieldCertificate] (table : Public) (bits : BitInput)

/-- **The bridge value, as a function of the mask vectors.** -/
def curveMap (m : MaskVectors) : BaseField :=
  CurveMembership.evaluate table.curve bits.toAffine
    (Pipeline.curveValues (laneValueM m .curveX (laneScale table .curveX) (laneWord bits .curveX))
      (laneValueM m .curveY (laneScale table .curveY) (laneWord bits .curveY)))

variable [GroupCertificate]

/-- **System A's lanes on the opening read the tape's mask vectors.** -/
theorem opening_curve_value (source : Stage1Source) (input : AffineInput) (tape : Tape)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record) (member : some ran ∈ (openingRun source input tape).support) (lane : Lane)
    (curve : lane = .curveX ∨ lane = .curveY) :
    FreeQuery.eval (refillAns (restoredBits source input) ran.2.1)
        (laneProg source.publicValue (restoredBits source input) (restoredMac source input)
          (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1)) lane) =
      laneValueM (masksOf VectorSite.lane tape) lane (laneScale source.publicValue lane)
        (laneWord (restoredBits source input) lane) := by
  have d := opening_described source input tape ran (openingRun_mem member)
  refine lane_eval_tape _ tape lane _ _ _ _ fun cell label onLane => ?_
  have inside := mem_queriesAlong_allQ _
    (Kriterion.ArgoMAC.Phase3.Lazy.evalLaneM_allQ _ _ _ _ _) _ onLane
  have plain := curve_notIntercepted (restoredBits source input) lane curve _ inside
  rw [refillAns_plain plain]
  refine d.tape _ cell (lane_mem_opening _ _ _ _ lane _ onLane) ?_
  rw [consumedCell_plain (notDesignated_of_intercept plain), cellOf_cellInput]

/-- **The opening's bridge value is `curveMap` of the tape's mask vectors.** -/
theorem tOf_tape (source : Stage1Source) (input : AffineInput) (tape : Tape)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record) (member : some ran ∈ (openingRun source input tape).support) :
    tOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1) =
      curveMap source.publicValue (restoredBits source input) (masksOf VectorSite.lane tape) := by
  have x : FreeQuery.eval (refillAns (restoredBits source input) ran.2.1)
      (curveXM source.publicValue (restoredBits source input) (restoredMac source input)) =
        laneValueM (masksOf VectorSite.lane tape) .curveX (laneScale source.publicValue .curveX)
          (laneWord (restoredBits source input) .curveX) :=
    opening_curve_value source input tape ran member .curveX (Or.inl rfl)
  have y : FreeQuery.eval (refillAns (restoredBits source input) ran.2.1)
      (curveYM source.publicValue (restoredBits source input) (restoredMac source input)) =
        laneValueM (masksOf VectorSite.lane tape) .curveY (laneScale source.publicValue .curveY)
          (laneWord (restoredBits source input) .curveY) :=
    opening_curve_value source input tape ran member .curveY (Or.inr rfl)
  unfold tOf curveMap
  rw [x, y]

end Bridge

/-! ### The shift of one mask coordinate -/

section Shift

variable [FieldCertificate] (table : Public) (bits : BitInput)

/-- The shifted vector: chunk `0` of `curveX`, at the switch `α₀ ⊕ 1`. -/
def starSite : VectorSite := ⟨.curveX, chunkZero, designatedSwitch bits⟩

theorem eq_starSite {lane : Lane} {c : Fin chunkCount} {s : Fin (2 ^ chunkWidth c)}
    (same : (⟨lane, c, s⟩ : VectorSite) = starSite bits) : lane = .curveX ∧ c = chunkZero := by
  unfold starSite at same
  exact ⟨(VectorSite.mk.inj same).1, (VectorSite.mk.inj same).2.1⟩

theorem eq_starSite_zero {s : Fin (2 ^ chunkWidth chunkZero)}
    (same : (⟨.curveX, chunkZero, s⟩ : VectorSite) = starSite bits) :
    s = designatedSwitch bits := by
  unfold starSite at same
  exact eq_of_heq (VectorSite.mk.inj same).2.2

/-- **The shift of the `x7` coordinate of the starred vector.** -/
def maskShift (δ : BaseField) : MaskVectors ≃ MaskVectors where
  toFun m site el := m site el + (if site = starSite bits ∧ el.val = 2 then δ else 0)
  invFun m site el := m site el - (if site = starSite bits ∧ el.val = 2 then δ else 0)
  left_inv m := by
    funext site el
    simp
  right_inv m := by
    funext site el
    simp

theorem maskShift_apply (δ : BaseField) (m : MaskVectors) (site : VectorSite)
    (el : Fin (laneCount site.lane)) :
    maskShift bits δ m site el = m site el + (if site = starSite bits ∧ el.val = 2 then δ else 0) :=
  rfl

/-- The coefficient of the shifted coordinate. -/
def shiftCoeff : BaseField :=
  iota _ (designatedSwitch bits) - iota _ (activeSwitch bits)

theorem shiftCoeff_ne : shiftCoeff bits ≠ 0 := by
  unfold shiftCoeff
  intro zero
  have same := sub_eq_zero.mp zero
  exact Kriterion.ArgoMAC.Phase3.Lazy.designatedSwitch_ne bits
    (iota_injective (Nat.pow_le_pow_right (by norm_num) (chunkWidth_le chunkZero)) same)

theorem laneValueM_shift_curveY (δ : BaseField) (m : MaskVectors)
    (scale : Fin chunkCount → Fin (laneCount .curveY) → BaseField)
    (word : BitVec coordinateBitCount) :
    laneValueM (maskShift bits δ m) .curveY scale word = laneValueM m .curveY scale word := by
  funext el
  unfold laneValueM
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  funext s
  unfold laneMasks
  split
  · rfl
  · congr 1
    funext e
    rw [maskShift_apply, if_neg, add_zero]
    rintro ⟨h, -⟩
    cases (eq_starSite bits h).1

/-- The starred coordinate's contribution to chunk `c` of `curveX`. -/
theorem star_sum (δ : BaseField) (c : Fin chunkCount) (el : Fin (laneCount .curveX)) :
    ∑ s ∈ Finset.univ.erase (chunkOf (Pipeline.coordBits bits .x) c),
        (iota _ s - iota _ (chunkOf (Pipeline.coordBits bits .x) c)) *
          (if (⟨.curveX, c, s⟩ : VectorSite) = starSite bits ∧ el.val = 2 then δ else 0) =
      if c = chunkZero ∧ el.val = 2 then shiftCoeff bits * δ else 0 := by
  by_cases zero : c = chunkZero
  · subst zero
    by_cases two : el.val = 2
    · rw [if_pos ⟨rfl, two⟩, Finset.sum_eq_single (designatedSwitch bits)]
      · rw [if_pos ⟨rfl, two⟩]
        rfl
      · intro s _ different
        rw [if_neg fun h => different (eq_starSite_zero bits h.1), mul_zero]
      · intro outside
        exact absurd (Finset.mem_erase.mpr ⟨Kriterion.ArgoMAC.Phase3.Lazy.designatedSwitch_ne bits,
          Finset.mem_univ _⟩) outside
    · rw [if_neg fun h => two h.2]
      exact Finset.sum_eq_zero fun s _ => by rw [if_neg fun h => two h.2, mul_zero]
  · rw [if_neg fun h => zero h.1]
    exact Finset.sum_eq_zero fun s _ => by
      rw [if_neg fun h => zero (eq_starSite bits h.1).2, mul_zero]

/-- **The `curveX` lane under the shift**: only the `x7` coordinate moves, by `coeff · δ`. -/
theorem laneValueM_shift_curveX (δ : BaseField) (m : MaskVectors)
    (scale : Fin chunkCount → Fin (laneCount .curveX) → BaseField) (el : Fin (laneCount .curveX)) :
    laneValueM (maskShift bits δ m) .curveX scale (Pipeline.coordBits bits .x) el =
      laneValueM m .curveX scale (Pipeline.coordBits bits .x) el +
        (if el.val = 2 then shiftCoeff bits * δ else 0) := by
  have each : ∀ c : Fin chunkCount,
      Programs.evalScaleOf (chunkWidth c) (laneMasks (maskShift bits δ m) .curveX
          (Pipeline.coordBits bits .x) c) (chunkOf (Pipeline.coordBits bits .x) c) (scale c) el =
        Programs.evalScaleOf (chunkWidth c) (laneMasks m .curveX (Pipeline.coordBits bits .x) c)
          (chunkOf (Pipeline.coordBits bits .x) c) (scale c) el +
          (if c = chunkZero ∧ el.val = 2 then shiftCoeff bits * δ else 0) := by
    intro c
    rw [evalScaleOf_linear, evalScaleOf_linear, add_assoc, ← star_sum bits δ c el,
      ← Finset.sum_add_distrib, add_right_inj]
    refine Finset.sum_congr rfl fun s member => ?_
    rw [laneMasks_get (Finset.ne_of_mem_erase member),
      laneMasks_get (Finset.ne_of_mem_erase member), maskShift_apply, mul_add]
  have star : (∑ c : Fin chunkCount, if c = chunkZero ∧ el.val = 2 then shiftCoeff bits * δ
      else 0) = if el.val = 2 then shiftCoeff bits * δ else 0 := by
    by_cases two : el.val = 2
    · simp only [two, and_true, if_true]
      rw [Finset.sum_ite_eq' Finset.univ chunkZero, if_pos (Finset.mem_univ _)]
    · simp only [two, and_false, if_false, Finset.sum_const_zero]
  unfold laneValueM
  rw [Finset.sum_congr rfl fun c _ => each c, Finset.sum_add_distrib, star]

/-- **The bridge value under the shift.** -/
theorem curveMap_shift (δ : BaseField) (m : MaskVectors) :
    curveMap table bits (maskShift bits δ m) = curveMap table bits m + shiftCoeff bits * δ := by
  unfold curveMap
  rw [laneValueM_shift_curveY]
  simp only [CurveMembership.evaluate, Pipeline.curveValues]
  have x7 : (curveXElementIndex .x7).val = 2 := rfl
  have x5 : (curveXElementIndex .x5).val = 1 := rfl
  have x3 : (curveXElementIndex .x3).val = 0 := rfl
  have shifted : ∀ el : Fin (laneCount .curveX),
      laneValueM (maskShift bits δ m) .curveX (laneScale table .curveX) (laneWord bits .curveX) el =
        laneValueM m .curveX (laneScale table .curveX) (laneWord bits .curveX) el +
          (if el.val = 2 then shiftCoeff bits * δ else 0) :=
    laneValueM_shift_curveX bits δ m (laneScale table .curveX)
  rw [shifted, shifted, shifted, x7, x5, x3]
  simp only [if_true, show (1 : ℕ) ≠ 2 from by decide, show (0 : ℕ) ≠ 2 from by decide, if_false,
    add_zero]
  ring

end Shift

/-! ### A uniform family shifted affinely -/

section Uniform

variable [FieldCertificate]

/-- **An affine function of a uniform family, shifted along one coordinate, hits a point with mass
`1/p`.** -/
theorem uniform_affine_le {X : Type} [Fintype X] [Nonempty X] (Φ : X → BaseField)
    (shift : BaseField → X ≃ X) (a : BaseField) (nonzero : a ≠ 0)
    (shifted : ∀ δ x, Φ (shift δ x) = Φ x + a * δ) (k : BaseField) :
    ∑' x, PMF.uniformOfFintype X x * ind (Φ x = k) ≤
      ((Fintype.card BaseField : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  set S := ∑' x, PMF.uniformOfFintype X x * ind (Φ x = k) with hS
  have each : ∀ δ : BaseField, S = ∑' x, PMF.uniformOfFintype X x * ind (Φ x + a * δ = k) := by
    intro δ
    rw [hS, ← (shift δ).tsum_eq]
    refine tsum_congr fun x => ?_
    rw [PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, shifted]
  have one : ∀ x, ∑ δ : BaseField, ind (Φ x + a * δ = k) = 1 := by
    intro x
    have iff : ∀ δ, Φ x + a * δ = k ↔ δ = a⁻¹ * (k - Φ x) := by
      intro δ
      constructor
      · intro h
        rw [← h, add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]
      · rintro rfl
        rw [← mul_assoc, mul_inv_cancel₀ nonzero, one_mul, add_sub_cancel]
    simp only [iff]
    rw [Finset.sum_eq_single (a⁻¹ * (k - Φ x))]
    · exact ind_pos rfl
    · intro δ _ different
      exact ind_neg different
    · intro outside
      exact absurd (Finset.mem_univ _) outside
  have total : (Fintype.card BaseField : ℝ≥0∞) * S = 1 := by
    calc (Fintype.card BaseField : ℝ≥0∞) * S = ∑ _δ : BaseField, S := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ δ : BaseField, ∑' x, PMF.uniformOfFintype X x * ind (Φ x + a * δ = k) :=
          Finset.sum_congr rfl fun δ _ => each δ
      _ = ∑' x, ∑ δ : BaseField, PMF.uniformOfFintype X x * ind (Φ x + a * δ = k) :=
          (Summable.tsum_finsetSum fun _ _ => ENNReal.summable).symm
      _ = ∑' x, PMF.uniformOfFintype X x * 1 := tsum_congr fun x => by
          rw [← Finset.mul_sum, one x]
      _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  refine le_of_eq ?_
  rw [← ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact total)]

/-- **The bridge input of an affine function of a uniform family hits a point with mass `≤ 2/p`**
(at most two bridge preimages). -/
theorem uniform_bridge_le {X : Type} [Fintype X] [Nonempty X] (Φ : X → BaseField)
    (shift : BaseField → X ≃ X) (a : BaseField) (nonzero : a ≠ 0)
    (shifted : ∀ δ x, Φ (shift δ x) = Φ x + a * δ) (k : BaseField) :
    ∑' x, PMF.uniformOfFintype X x * ind (k = bridgeInput (Φ x)) ≤
      2 * ((Fintype.card BaseField : ℕ) : ℝ≥0∞)⁻¹ := by
  have point : ∀ x, ind (k = bridgeInput (Φ x)) ≤
      ∑ t ∈ Finset.univ.filter (fun t : BaseField => bridgeInput t = k), ind (Φ x = t) := by
    intro x
    by_cases hit : k = bridgeInput (Φ x)
    · rw [ind_pos hit]
      calc (1 : ℝ≥0∞) = ind (Φ x = Φ x) := (ind_pos rfl).symm
        _ ≤ _ := Finset.single_le_sum (f := fun t => ind (Φ x = t)) (fun _ _ => zero_le)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit.symm⟩)
    · rw [ind_neg hit]
      exact zero_le
  calc ∑' x, PMF.uniformOfFintype X x * ind (k = bridgeInput (Φ x))
      ≤ ∑' x, PMF.uniformOfFintype X x *
          ∑ t ∈ Finset.univ.filter (fun t : BaseField => bridgeInput t = k), ind (Φ x = t) :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (point x)
    _ = ∑ t ∈ Finset.univ.filter (fun t : BaseField => bridgeInput t = k),
          ∑' x, PMF.uniformOfFintype X x * ind (Φ x = t) := by
        rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        exact tsum_congr fun x => Finset.mul_sum _ _ _
    _ ≤ ∑ _t ∈ Finset.univ.filter (fun t : BaseField => bridgeInput t = k),
          ((Fintype.card BaseField : ℕ) : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum fun t _ => uniform_affine_le Φ shift a nonzero shifted t
    _ ≤ 2 * ((Fintype.card BaseField : ℕ) : ℝ≥0∞)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul' (by exact_mod_cast bridgeInput_filter_card_le_two k) le_rfl

/-- `2/p ≤ 4/2^128`. -/
theorem two_inv_modulus_le : 2 * ((Fintype.card BaseField : ℕ) : ℝ≥0∞)⁻¹ ≤ 4 / 2 ^ 128 := by
  have card : Fintype.card BaseField = baseFieldModulus := ZMod.card _
  have big : 2 ^ 128 ≤ baseFieldModulus := by
    unfold baseFieldModulus
    norm_num
  rw [card]
  calc 2 * ((baseFieldModulus : ℕ) : ℝ≥0∞)⁻¹ ≤ 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ :=
        mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr (by exact_mod_cast big))
    _ ≤ 4 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := mul_le_mul' (by norm_num) le_rfl
    _ = 4 / 2 ^ 128 := by rw [div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat]

/-- `1/2^128 ≤ 4/2^128`. -/
theorem delta_le_four : delta ≤ 4 / 2 ^ 128 := by
  calc delta ≤ 4 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := le_mul_of_one_le_left zero_le (by norm_num)
    _ = 4 / 2 ^ 128 := by rw [div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat]

/-- **The masks of the uniform mask tape are uniform.** -/
theorem uniformMaskTape_masks (f : MaskVectors → ℝ≥0∞) :
    ∑' tape, uniformMaskTape tape * f (masksOf VectorSite.lane tape) =
      ∑' m, PMF.uniformOfFintype MaskVectors m * f m := by
  unfold uniformMaskTape
  rw [tsum_bind_mul]
  refine tsum_congr fun m => congrArg _ ?_
  rw [← tsum_map_mul, Kriterion.ArgoMAC.Security.Phase3.fibreLaw_map, tsum_pure_mul]

end Uniform

/-! ### The hash conjunct on the curve -/

section Conjunct

variable [FieldCertificate] [GroupCertificate]

theorem two_le_chunkWidth (c : Fin chunkCount) : 2 ≤ chunkWidth c := by
  unfold chunkWidth chunkWidthNat firstChunkBits chunkBits narrowChunkBits
  split_ifs <;> omega

/-- **Fold-label entropy on the opening, at any level `2 ≤ s ≤ chunkWidth c`.** -/
theorem opening_level_le' (source : Stage1Source) (input : AffineInput) (tape : Tape) (lane : Lane)
    (c : Fin chunkCount) (s : ℕ) (two : 2 ≤ s) (le : s ≤ chunkWidth c) (n : Fin (2 ^ s))
    (L : Block) :
    ∑' ran, openingRun source input tape ran *
      optWeight (fun state => ind (openLevel source.publicValue (restoredBits source input)
        (restoredMac source input) (refillAns (restoredBits source input) state) lane c s n =
          L)) ran ≤ delta := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  exact opening_level_le source input tape lane c t (by omega) (by omega) n L

/-- An event bounded by an indicator of the opening's final state, per run of the shadow. -/
theorem shadow_ind_le {γ : Type} (μ : PMF γ) (event : γ → Prop) (bound : Prop)
    (implies : ∀ result ∈ μ.support, event result → bound) :
    ∑' result, μ result * ind (event result) ≤ ind bound := by
  refine le_trans (tsum_mul_le_of_support _ _ (fun _ => ind bound) fun result member =>
    ind_mono (implies result member)) (le_of_eq ?_)
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **On the curve, a hash key has mass `≤ 4/2^128`.** -/
theorem hash_onCurve_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (k : BaseField) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).hashIn k) ≤ 4 / 2 ^ 128 := by
  classical
  by_cases scale : k.val < scaleRange
  · -- a scale key names one limb of one switch and one label
    cases cellEq : cellOf k with
    | none =>
      refine le_trans (onCurve_event_le scalar off source input target (fun p => p.hashIn k)
        (fun _ => ind False) fun tape ran member answers => shadow_ind_le _ _ _ fun result
          resultMember hit => ?_) ?_
      · rcases final_hash source input tape ran member answers result resultMember k hit with
          bridge | ⟨lane, c, s, limb, rfl⟩
        · rw [bridge] at scale
          exact bridgeInput_not_lt _ scale
        · rw [cellOf_cellInput] at cellEq
          cases cellEq
      · have zero : ∀ tape ran, openingRun source input tape ran *
            optWeight (fun _ => ind False) ran = 0 := fun tape ran => by
          rcases ran with _ | ran <;> simp only [optWeight, ind_neg not_false, mul_zero]
        simp only [zero, tsum_zero, mul_zero]
        exact zero_le
    | some cell =>
      obtain ⟨label, same⟩ := cellOf_spec cellEq
      refine le_trans (onCurve_event_le scalar off source input target (fun p => p.hashIn k)
        (fun state => ind (openLevel source.publicValue (restoredBits source input)
          (restoredMac source input) (refillAns (restoredBits source input) state) cell.1.lane
          cell.1.chunk (chunkWidth cell.1.chunk) cell.1.switch = label))
        fun tape ran member answers => shadow_ind_le _ _ _ fun result resultMember hit => ?_) ?_
      · rcases final_hash source input tape ran member answers result resultMember k hit with
          bridge | ⟨lane, c, s, limb, keyEq⟩
        · rw [bridge] at scale
          exact absurd scale (bridgeInput_not_lt _)
        · have pair := cellInput_injective (a₁ := (cell, label))
            (a₂ := (maskCell lane c s limb, _)) (same.trans keyEq)
          simp only [Prod.mk.injEq] at pair
          obtain ⟨rfl, rfl⟩ := pair
          rfl
      · exact le_trans (tsum_le_of_support _ _ delta fun tape _ =>
          opening_level_le' source input tape _ _ _ (two_le_chunkWidth _) le_rfl _ _)
          delta_le_four
  · -- the bridge key
    refine le_trans (onCurve_event_le scalar off source input target (fun p => p.hashIn k)
      (fun state => ind (k = bridgeInput (tOf source.publicValue (restoredBits source input)
        (restoredMac source input) (refillAns (restoredBits source input) state))))
      fun tape ran member answers => shadow_ind_le _ _ _ fun result resultMember hit => ?_) ?_
    · rcases final_hash source input tape ran member answers result resultMember k hit with
        bridge | ⟨lane, c, s, limb, rfl⟩
      · exact bridge
      · exact absurd (scaleInput_val_lt_scaleRange _ _ _ _ _) scale
    · refine le_trans (ENNReal.tsum_le_tsum (g := fun tape => uniformMaskTape tape *
        ind (k = bridgeInput (curveMap source.publicValue (restoredBits source input)
          (masksOf VectorSite.lane tape)))) fun tape => mul_le_mul' le_rfl ?_) ?_
      · refine le_trans (tsum_mul_le_of_support _ _ (fun _ => ind (k = bridgeInput
          (curveMap source.publicValue (restoredBits source input)
            (masksOf VectorSite.lane tape)))) fun ran member => ?_)
          (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
        rcases ran with _ | ran
        · exact zero_le
        · simp only [optWeight]
          rw [tOf_tape source input tape ran member]
      · rw [uniformMaskTape_masks (fun m => ind (k = bridgeInput
          (curveMap source.publicValue (restoredBits source input) m)))]
        exact le_trans (uniform_bridge_le _ (maskShift (restoredBits source input))
          (shiftCoeff (restoredBits source input)) (shiftCoeff_ne _)
          (fun δ m => curveMap_shift _ _ δ m) k) two_inv_modulus_le

end Conjunct

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
