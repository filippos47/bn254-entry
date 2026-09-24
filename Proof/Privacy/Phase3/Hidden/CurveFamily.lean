/-
**Phase 3, P1h — the curve family: moving the bridge key off the curve.**

Fix the input `u = (x, y)` and write `s = x³ + 3 − y²` (`curveGap`). For `c ∈ F_p^*`, with
`δ = (c − 1) · mask`:

```
mask ↦ c · mask,   r1 ↦ r1 − δ,   r2 ↦ r2 + δ,   t ↦ t − δ · s,
hash ↦ hash ∘ swap(bridgeInput t, bridgeInput (t − δ s))   (off the scale range),
Y(curve lane, chunk k, the active switch α_k)[e] −= Δ(e) · 2^{off k}
```

where `Δ = (δ, δx, δx², −δ, −δy)` on `(x3, x5, x7, y4, y6)` (`curveDelta`). Every published curve join
`Σ_j Y + slope·2^{off k}` is kept (the slopes move by exactly `Δ`), the element offsets move by
`−Δ(e) · coord`, the three curve constants are kept (`c0` absorbs `δ(3 − s − y² + x³) = 0`), the
point lanes, the rows and the gadget are untouched (`hash'(bridgeInput t') = hash(bridgeInput t)`):
**the published value is kept** (`publishedOf_curve`), and so are the EncPRF entries (`encOf_curve`)
and every garbler key (`restKeys_curve`). Only the hidden (active-switch) curve vectors move. The
family is a permutation of the rest (`curveRestEquiv`, inverse `c⁻¹`).
-/

import Proof.Privacy.Phase3.Hidden.StageTwo
import Proof.Privacy.Phase3.Hidden.Split

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open scoped ENNReal

noncomputable section

/-! ### The hidden curve sites and the corrections -/

/-- The curve gap `x³ + 3 − y²`: nonzero exactly off the curve. -/
def curveGap (input : AffineInput) : BaseField := input.x ^ 3 + 3 - input.y ^ 2

theorem curveGap_ne_zero (input : AffineInput) (invalid : validate input = false) : curveGap input ≠ 0 := by
  intro zero
  have onCurve : OnCurve input := by
    unfold OnCurve
    unfold curveGap at zero
    linear_combination -zero
  rw [← validate_eq_true_iff, invalid] at onCurve
  cases onCurve

/-- A hidden curve site at the input: a curve lane's active switch. -/
def IsHidden (input : AffineInput) (site : VectorSite) : Prop :=
  laneIsCurve site.lane = true ∧
    site.switch.val = (chunkOf (inputBits input site.lane.coord) site.chunk).val

instance (input : AffineInput) : DecidablePred (IsHidden input) := fun site => by
  unfold IsHidden
  infer_instance

/-- The slope moves `Δ` of the curve family. -/
def curveDelta (input : AffineInput) (δ : BaseField) : CurveMembership.Values
  | .inl .x3 => δ
  | .inl .x5 => δ * input.x
  | .inl .x7 => δ * input.x ^ 2
  | .inr .y4 => -δ
  | .inr .y6 => -δ * input.y

/-- The correction of one curve vector: `Δ(e) · 2^{off k}` at each coordinate. -/
def siteCorr (input : AffineInput) (δ : BaseField) :
    (site : VectorSite) → Fin (laneCount site.lane) → BaseField
  | ⟨.curveX, k, _⟩ => fun e =>
      Pipeline.curveXAssemble (curveDelta input δ) e * (2 : BaseField) ^ chunkOffset k
  | ⟨.curveY, k, _⟩ => fun e =>
      Pipeline.curveYAssemble (curveDelta input δ) e * (2 : BaseField) ^ chunkOffset k
  | _ => fun _ => 0

/-- **The vectors of the curve family**: the hidden curve vectors move by the correction. -/
def curveMasks (input : AffineInput) (δ : BaseField) (masks : MaskVectors) : MaskVectors :=
  fun site e => if IsHidden input site then masks site e - siteCorr input δ site e else masks site e

theorem isHidden_curveX (input : AffineInput) (k : Fin chunkCount) (sw : Fin (2 ^ chunkWidth k)) :
    IsHidden input ⟨.curveX, k, sw⟩ ↔ sw = chunkOf (inputBits input .x) k :=
  ⟨fun h => Fin.ext h.2, fun h => ⟨rfl, congrArg Fin.val h⟩⟩

theorem curveMasks_curveX (input : AffineInput) (δ : BaseField) (masks : MaskVectors)
    (k : Fin chunkCount) (sw : Fin (2 ^ chunkWidth k)) (e : Fin (laneCount .curveX)) :
    curveMasks input δ masks ⟨.curveX, k, sw⟩ e = masks ⟨.curveX, k, sw⟩ e -
      (if sw = chunkOf (inputBits input .x) k then
        Pipeline.curveXAssemble (curveDelta input δ) e * (2 : BaseField) ^ chunkOffset k else 0) := by
  unfold curveMasks
  by_cases h : sw = chunkOf (inputBits input .x) k
  · rw [if_pos ((isHidden_curveX input k sw).mpr h), if_pos h]
    rfl
  · rw [if_neg (mt (isHidden_curveX input k sw).mp h), if_neg h, sub_zero]

theorem isHidden_curveY (input : AffineInput) (k : Fin chunkCount) (sw : Fin (2 ^ chunkWidth k)) :
    IsHidden input ⟨.curveY, k, sw⟩ ↔ sw = chunkOf (inputBits input .y) k :=
  ⟨fun h => Fin.ext h.2, fun h => ⟨rfl, congrArg Fin.val h⟩⟩

theorem curveMasks_curveY (input : AffineInput) (δ : BaseField) (masks : MaskVectors)
    (k : Fin chunkCount) (sw : Fin (2 ^ chunkWidth k)) (e : Fin (laneCount .curveY)) :
    curveMasks input δ masks ⟨.curveY, k, sw⟩ e = masks ⟨.curveY, k, sw⟩ e -
      (if sw = chunkOf (inputBits input .y) k then
        Pipeline.curveYAssemble (curveDelta input δ) e * (2 : BaseField) ^ chunkOffset k else 0) := by
  unfold curveMasks
  by_cases h : sw = chunkOf (inputBits input .y) k
  · rw [if_pos ((isHidden_curveY input k sw).mpr h), if_pos h]
    rfl
  · rw [if_neg (mt (isHidden_curveY input k sw).mp h), if_neg h, sub_zero]

theorem curveMasks_point (input : AffineInput) (δ : BaseField) (masks : MaskVectors)
    (site : VectorSite) (point : laneIsCurve site.lane = false) :
    curveMasks input δ masks site = masks site := by
  funext e
  unfold curveMasks
  refine if_neg fun both => ?_
  have curve := both.1
  rw [point] at curve
  cases curve

/-! ### Sums over one chunk's switches -/

theorem sum_sub_single {n : Nat} (f : Fin n → BaseField) (α : Fin n) (d : BaseField) :
    (∑ sw : Fin n, (f sw - if sw = α then d else 0)) = (∑ sw : Fin n, f sw) - d := by
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ α (fun _ => d), if_pos (Finset.mem_univ _)]

theorem sum_iota_sub_single {n : Nat} (f : Fin n → BaseField) (α : Fin n) (d : BaseField) :
    (∑ sw : Fin n, iota n sw * (f sw - if sw = α then d else 0)) =
      (∑ sw : Fin n, iota n sw * f sw) - iota n α * d := by
  simp only [mul_sub, mul_ite, mul_zero]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ α (fun sw => iota n sw * d),
    if_pos (Finset.mem_univ _)]

/-- The chunks of `u`'s coordinate recompose it. -/
theorem recompose (value : BaseField) :
    (∑ k : Fin chunkCount, iota _ (chunkOf (coordWord value) k) *
      (2 : BaseField) ^ chunkOffset k) = value := by
  conv_rhs => rw [← chunk_recomposition value]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem inputBits_x (input : AffineInput) : inputBits input .x = coordWord input.x := rfl

theorem inputBits_y (input : AffineInput) : inputBits input .y = coordWord input.y := rfl

section Instances

variable [FieldCertificate] [GroupCertificate]

/-! ### The curve lanes' tables under the family -/

theorem curveX_offsets (input : AffineInput) (δ : BaseField) (rest : RestTape TapeRest)
    (masks : MaskVectors) (e : Fin (laneCount .curveX)) :
    (tablesOf rest (curveMasks input δ masks) .curveX).offsets e =
      (tablesOf rest masks .curveX).offsets e - Pipeline.curveXAssemble (curveDelta input δ) e * input.x := by
  unfold Programs.LaneTables.offsets tablesOf
  simp only
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun sw _ => by rw [curveMasks_curveX]]
  rw [Finset.sum_congr rfl fun k _ => sum_iota_sub_single _ _ _, Finset.sum_sub_distrib, sub_right_inj]
  rw [← recompose input.x, Finset.mul_sum, ← inputBits_x]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem curveY_offsets (input : AffineInput) (δ : BaseField) (rest : RestTape TapeRest)
    (masks : MaskVectors) (e : Fin (laneCount .curveY)) :
    (tablesOf rest (curveMasks input δ masks) .curveY).offsets e =
      (tablesOf rest masks .curveY).offsets e - Pipeline.curveYAssemble (curveDelta input δ) e * input.y := by
  unfold Programs.LaneTables.offsets tablesOf
  simp only
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun sw _ => by rw [curveMasks_curveY]]
  rw [Finset.sum_congr rfl fun k _ => sum_iota_sub_single _ _ _, Finset.sum_sub_distrib, sub_right_inj]
  rw [← recompose input.y, Finset.mul_sum, ← inputBits_y]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem curveX_scaleJoins (input : AffineInput) (δ : BaseField) (rest : RestTape TapeRest)
    (masks : MaskVectors) (slopes : Fin curveElementCountX → BaseField) :
    (tablesOf rest (curveMasks input δ masks) .curveX).scaleJoins
        (fun e => slopes e + Pipeline.curveXAssemble (curveDelta input δ) e) =
      (tablesOf rest masks .curveX).scaleJoins slopes := by
  funext k e
  unfold Programs.LaneTables.scaleJoins tablesOf chunkScalar
  simp only
  rw [Finset.sum_congr rfl fun sw _ => by rw [curveMasks_curveX], sum_sub_single]
  ring

theorem curveY_scaleJoins (input : AffineInput) (δ : BaseField) (rest : RestTape TapeRest)
    (masks : MaskVectors) (slopes : Fin curveElementCountY → BaseField) :
    (tablesOf rest (curveMasks input δ masks) .curveY).scaleJoins
        (fun e => slopes e + Pipeline.curveYAssemble (curveDelta input δ) e) =
      (tablesOf rest masks .curveY).scaleJoins slopes := by
  funext k e
  unfold Programs.LaneTables.scaleJoins tablesOf chunkScalar
  simp only
  rw [Finset.sum_congr rfl fun sw _ => by rw [curveMasks_curveY], sum_sub_single]
  ring

theorem tablesOf_point (input : AffineInput) (δ : BaseField) (rest : RestTape TapeRest)
    (masks : MaskVectors) (ℓ : Lane) (point : laneIsCurve ℓ = false) :
    tablesOf rest (curveMasks input δ masks) ℓ = tablesOf rest masks ℓ := by
  unfold tablesOf
  congr 1
  funext k sw
  exact curveMasks_point input δ masks ⟨ℓ, k, sw⟩ point

/-! ### The curve algebra -/

theorem curveValues_shift (input : AffineInput) (δ : BaseField)
    (xs xs' : Fin curveElementCountX → BaseField) (ys ys' : Fin curveElementCountY → BaseField)
    (hx : ∀ e, xs' e = xs e - Pipeline.curveXAssemble (curveDelta input δ) e * input.x)
    (hy : ∀ e, ys' e = ys e - Pipeline.curveYAssemble (curveDelta input δ) e * input.y) :
    Pipeline.curveValues xs' ys' = fun element =>
      Pipeline.curveValues xs ys element - curveDelta input δ element * CurveMembership.coordValue input element := by
  funext element
  rcases element with (_ | _ | _) | (_ | _) <;>
    simp only [Pipeline.curveValues, hx, hy, CurveMembership.coordValue] <;> rfl

theorem slopes_shift (input : AffineInput) (δ r1 r2 : BaseField) (K : CurveMembership.Values) :
    CurveMembership.slopes (r1 - δ) (r2 + δ)
        (fun element => K element - curveDelta input δ element * CurveMembership.coordValue input element) =
      fun element => CurveMembership.slopes r1 r2 K element + curveDelta input δ element := by
  funext element
  rcases element with (_ | _ | _) | (_ | _) <;>
    simp only [CurveMembership.slopes, curveDelta, CurveMembership.coordValue] <;> ring

theorem garble_shift_curve (input : AffineInput) (δ t mask r1 r2 : BaseField) (K : CurveMembership.Values) :
    CurveMembership.garble (t - δ * curveGap input) (mask + δ) (r1 - δ) (r2 + δ)
        (fun element => K element - curveDelta input δ element * CurveMembership.coordValue input element) =
      CurveMembership.garble t mask r1 r2 K := by
  simp only [CurveMembership.garble, curveDelta, CurveMembership.coordValue, curveGap, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

theorem curveXAssemble_add (slopes delta : CurveMembership.Values) :
    Pipeline.curveXAssemble (fun element => slopes element + delta element) =
      fun e => Pipeline.curveXAssemble slopes e + Pipeline.curveXAssemble delta e := rfl

theorem curveYAssemble_add (slopes delta : CurveMembership.Values) :
    Pipeline.curveYAssemble (fun element => slopes element + delta element) =
      fun e => Pipeline.curveYAssemble slopes e + Pipeline.curveYAssemble delta e := rfl

/-- **The assembly is kept by the curve family.** -/
theorem assemble_curve (input : AffineInput) (δ : BaseField) (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (t : BaseField) (mask mask' : NonZeroBase)
    (maskEq : mask'.value = mask.value + δ) (r1 r2 : BaseField)
    (cx cx' : Programs.LaneTables curveElementCountX) (cy cy' : Programs.LaneTables curveElementCountY)
    (px : Programs.LaneTables pointElementCountX) (py : Programs.LaneTables pointElementCountY)
    (gadget : Vector Exception.Entry FieldMacToECMac.outputMacCount)
    (hx : ∀ e, cx'.offsets e = cx.offsets e - Pipeline.curveXAssemble (curveDelta input δ) e * input.x)
    (hy : ∀ e, cy'.offsets e = cy.offsets e - Pipeline.curveYAssemble (curveDelta input δ) e * input.y)
    (sx : ∀ slopes, cx'.scaleJoins (fun e => slopes e + Pipeline.curveXAssemble (curveDelta input δ) e) =
      cx.scaleJoins slopes)
    (sy : ∀ slopes, cy'.scaleJoins (fun e => slopes e + Pipeline.curveYAssemble (curveDelta input δ) e) =
      cy.scaleJoins slopes)
    (jx : cx'.hotJoins = cx.hotJoins) (jy : cy'.hotJoins = cy.hotJoins) :
    Programs.assemble outputKeys pointRandomness (t - δ * curveGap input) mask' (r1 - δ) (r2 + δ)
        cx' cy' px py gadget =
      Programs.assemble outputKeys pointRandomness t mask r1 r2 cx cy px py gadget := by
  unfold Programs.assemble
  dsimp only
  rw [curveValues_shift input δ _ _ _ _ hx hy, slopes_shift, curveXAssemble_add, curveYAssemble_add, sx, sy,
    jx, jy, maskEq, garble_shift_curve]

/-! ### The family on the rest -/

theorem nonZeroBase_ext {a b : NonZeroBase} (same : a.value = b.value) : a = b := by
  cases a
  cases b
  simp only at same
  subst same
  rfl

/-- **The curve family on the coins.** -/
def curveCoins (input : AffineInput) (c : BaseFieldˣ) (coins : Coins) : Coins :=
  { coins with
    bridgeKey := coins.bridgeKey - ((c : BaseField) - 1) * coins.curveMask.value * curveGap input
    curveMask := ⟨(c : BaseField) * coins.curveMask.value, mul_ne_zero c.ne_zero coins.curveMask.nonzero⟩
    curveR1 := coins.curveR1 - ((c : BaseField) - 1) * coins.curveMask.value
    curveR2 := coins.curveR2 + ((c : BaseField) - 1) * coins.curveMask.value }

/-- **The curve family on the rest**: the coins, and the hash swapped at the old and new bridge
inputs. -/
def curveRest (input : AffineInput) (c : BaseFieldˣ) (rest : RestTape TapeRest) : RestTape TapeRest :=
  ((curveCoins input c rest.1.1, rest.1.2.1, rest.1.2.2),
    rest.2 ∘ bridgeSwap rest.1.1.bridgeKey (curveCoins input c rest.1.1).bridgeKey)

/-- The `δ` of the family at a rest. -/
def curveStep (c : BaseFieldˣ) (rest : RestTape TapeRest) : BaseField :=
  ((c : BaseField) - 1) * rest.1.1.curveMask.value

theorem curveCoins_curveCoins (input : AffineInput) (c : BaseFieldˣ) (coins : Coins) :
    curveCoins input c⁻¹ (curveCoins input c coins) = coins := by
  apply Scheme.Coins.data_injective
  have unit : ((c⁻¹ : BaseFieldˣ) : BaseField) * (c : BaseField) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have mask : ((c⁻¹ : BaseFieldˣ) : BaseField) * ((c : BaseField) * coins.curveMask.value) =
      coins.curveMask.value := by
    rw [← mul_assoc, unit, one_mul]
  have nz : (⟨((c⁻¹ : BaseFieldˣ) : BaseField) * ((c : BaseField) * coins.curveMask.value),
      mul_ne_zero (c⁻¹).ne_zero (mul_ne_zero c.ne_zero coins.curveMask.nonzero)⟩ : NonZeroBase) =
      coins.curveMask := nonZeroBase_ext mask
  simp only [Scheme.Coins.data, curveCoins, nz, Prod.mk.injEq, and_true, true_and]
  have expand : ∀ a : BaseField, (((c⁻¹ : BaseFieldˣ) : BaseField) - 1) * ((c : BaseField) * a) =
      -(((c : BaseField) - 1) * a) := by
    intro a
    have : ((c⁻¹ : BaseFieldˣ) : BaseField) * (c : BaseField) * a = a := by rw [unit, one_mul]
    linear_combination this
  refine ⟨?_, ?_, ?_⟩
  · rw [expand]
    ring
  · rw [expand]
    ring
  · rw [expand]
    ring

theorem curveRest_curveRest (input : AffineInput) (c : BaseFieldˣ) (rest : RestTape TapeRest) :
    curveRest input c⁻¹ (curveRest input c rest) = rest := by
  obtain ⟨⟨coins, fixed, enc⟩, other⟩ := rest
  unfold curveRest
  simp only [curveCoins_curveCoins]
  refine Prod.ext rfl ?_
  funext value
  simp only [Function.comp_apply]
  unfold bridgeSwap
  rw [Equiv.swap_comm, Equiv.swap_apply_self]

/-- **The curve family is a permutation of the rest.** -/
def curveRestEquiv (input : AffineInput) (c : BaseFieldˣ) : RestTape TapeRest ≃ RestTape TapeRest where
  toFun := curveRest input c
  invFun := curveRest input c⁻¹
  left_inv := curveRest_curveRest input c
  right_inv rest := by
    have := curveRest_curveRest input c⁻¹ rest
    rwa [inv_inv] at this

theorem curveRest_hash (input : AffineInput) (c : BaseFieldˣ) (rest : RestTape TapeRest) :
    hashOf (curveRest input c rest).2 blankScale (bridgeInput (curveRest input c
        rest).1.1.bridgeKey) =
      hashOf rest.2 blankScale (bridgeInput rest.1.1.bridgeKey) := by
  rw [hashOf_bridgeInput, hashOf_bridgeInput]
  show rest.2 (bridgeSwap rest.1.1.bridgeKey (curveCoins input c rest.1.1).bridgeKey
    ⟨bridgeInput (curveCoins input c rest.1.1).bridgeKey, _⟩) = _
  unfold bridgeSwap
  rw [Equiv.swap_apply_right]

theorem whiteningKeys_curve (input : AffineInput) (c : BaseFieldˣ) (rest : RestTape TapeRest) :
    EncPRF.whiteningKeys (hashOf (curveRest input c rest).2 blankScale)
        (curveRest input c rest).1.1.bridgeKey =
      EncPRF.whiteningKeys (hashOf rest.2 blankScale) rest.1.1.bridgeKey := by
  unfold EncPRF.whiteningKeys
  rw [curveRest_hash]

theorem restKeys_curve (input : AffineInput) (c : BaseFieldˣ) (rest : RestTape TapeRest) :
    restKeys (curveRest input c rest) = restKeys rest := by
  have white : Pipeline.whitenedKey (curveRest input c rest).1.2.2
      (hashOf (curveRest input c rest).2 blankScale) (curveRest input c rest).1.1.bridgeKey
        (curveRest input c rest).1.1.inputMacKey =
      Pipeline.whitenedKey rest.1.2.2 (hashOf rest.2 blankScale) rest.1.1.bridgeKey
        rest.1.1.inputMacKey := by
    unfold Pipeline.whitenedKey
    rw [whiteningKeys_curve]
    rfl
  unfold restKeys garblerKeys
  rw [white]
  rfl

theorem tablesOf_curveRest (input : AffineInput) (c : BaseFieldˣ) (rest : RestTape TapeRest)
    (masks : MaskVectors) (ℓ : Lane) :
    tablesOf (curveRest input c rest) masks ℓ = tablesOf rest masks ℓ := by
  unfold tablesOf
  rw [restKeys_curve]
  rfl

/-- **The published value is kept.** -/
theorem publishedOf_curve (scalar : NonZeroScalar) (input : AffineInput) (c : BaseFieldˣ)
    (rest : RestTape TapeRest) (masks : MaskVectors) :
    publishedOf scalar (curveRest input c rest, curveMasks input (curveStep c rest) masks) =
      publishedOf scalar (rest, masks) := by
  unfold publishedOf
  simp only [tablesOf_curveRest]
  rw [tablesOf_point input _ rest masks .pointX rfl, tablesOf_point input _ rest masks .pointY rfl,
    whiteningKeys_curve]
  have maskEq : (curveRest input c rest).1.1.curveMask.value = rest.1.1.curveMask.value + curveStep c rest := by
    show (c : BaseField) * rest.1.1.curveMask.value = _
    unfold curveStep
    ring
  exact assemble_curve input (curveStep c rest) _ _ rest.1.1.bridgeKey rest.1.1.curveMask
    (curveRest input c rest).1.1.curveMask maskEq rest.1.1.curveR1 rest.1.1.curveR2 _ _ _ _ _ _ _
    (curveX_offsets input _ rest masks) (curveY_offsets input _ rest masks)
    (curveX_scaleJoins input _ rest masks) (curveY_scaleJoins input _ rest masks) rfl rfl

/-- **The EncPRF entries are kept.** -/
theorem encOf_curve (input : AffineInput) (c : BaseFieldˣ) (rest : RestTape TapeRest) :
    encOf (curveRest input c rest) = encOf rest := by
  unfold encOf
  rw [curveRest_hash]
  have same : ∀ request : PublicQuery FixedIndex EncPRF.PermutationIndex, IsEncForward request →
      publicAnswer (restOracle (curveRest input c rest)) request = publicAnswer (restOracle rest) request := by
    intro request enc
    cases request with
    | encForward index input => rfl
    | _ => exact enc.elim
  exact ((padsM_encOnly _).agree (restOracle rest) (restOracle (curveRest input c rest)) same).1

/-- **The bridge key moves by `−(c − 1) · mask · s`.** -/
theorem curveRest_bridgeKey (input : AffineInput) (c : BaseFieldˣ) (rest : RestTape TapeRest) :
    (curveRest input c rest).1.1.bridgeKey =
      rest.1.1.bridgeKey - ((c : BaseField) - 1) * rest.1.1.curveMask.value * curveGap input := rfl

/-- Off the curve, distinct `c` move the bridge key to distinct keys. -/
theorem curveRest_bridgeKey_injective (input : AffineInput) (invalid : validate input = false)
    (rest : RestTape TapeRest) (c c' : BaseFieldˣ)
    (same : (curveRest input c rest).1.1.bridgeKey = (curveRest input c' rest).1.1.bridgeKey) : c = c' := by
  rw [curveRest_bridgeKey, curveRest_bridgeKey] at same
  have gap := curveGap_ne_zero input invalid
  have mask := rest.1.1.curveMask.nonzero
  have : ((c : BaseField) - (c' : BaseField)) * (rest.1.1.curveMask.value * curveGap input) = 0 := by
    linear_combination -same
  rcases mul_eq_zero.mp this with h | h
  · exact Units.ext (sub_eq_zero.mp h)
  · exact absurd h (mul_ne_zero mask gap)

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
