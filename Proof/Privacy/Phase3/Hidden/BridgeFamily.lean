/-
**Phase 3, P1f — `StageOneBridgeGuess`, real.**

On the (rest, vectors) coordinates, where the swapped tape is uniform × uniform
(`swapped_restMasks`), the family over `δ ∈ F_p`

```
t ↦ t + δ,   hash ↦ hash ∘ swap(bridgeInput t, bridgeInput (t + δ))   (off the scale range),
Y(curveX, chunk 0, switch 1)[x7] += δ,   Y(curveX, chunk 0, switch 0)[x7] −= δ
```

keeps the stage-1 view: `K_x7` moves by `ι 1 − ι 0 = 1` and absorbs `t` in `c0`; every published
switch sum `Σ_j Y` is kept; no slope reads `K_x7`;
`hash'(bridgeInput (t + δ)) = hash(bridgeInput t)` keeps the pads, the whitened keys and the gadget.
It moves `t` by `δ`, and `bridgeInput` is at most two-to-one (`bridgeInput_fibre_card_le_two`), so
at most two `δ` move `bridgeInput t` onto a given key: `bridgeInput t` hits a key with conditional
mass at most `2/p` (`event_le_of_symmetry_count`).
-/

import Proof.Privacy.Phase3.Hidden.Bridge

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open scoped ENNReal

noncomputable section

/-- The `x7` slot of the `curveX` lane. -/
def x7Slot : Fin curveElementCountX := curveXElementIndex .x7

/-- The swap of the rest of the hash table at two bridge inputs. -/
def bridgeSwap (t t' : BaseField) : OtherInput ≃ OtherInput :=
  Equiv.swap ⟨bridgeInput t, bridgeInput_not_lt t⟩ ⟨bridgeInput t', bridgeInput_not_lt t'⟩

/-- The bridge family on the rest. -/
def bridgeRest (δ : BaseField) (rest : RestTape TapeRest) : RestTape TapeRest :=
  (({ rest.1.1 with bridgeKey := rest.1.1.bridgeKey + δ }, rest.1.2.1, rest.1.2.2),
    rest.2 ∘ bridgeSwap rest.1.1.bridgeKey (rest.1.1.bridgeKey + δ))

/-- The bridge family on the vectors. -/
def bridgeMasks (δ : BaseField) (masks : MaskVectors) : MaskVectors := fun site e =>
  masks site e +
    (if site.lane = .curveX ∧ site.chunk.val = 0 ∧ site.switch.val = 1 ∧ e.val = x7Slot.val
      then δ else 0) -
    (if site.lane = .curveX ∧ site.chunk.val = 0 ∧ site.switch.val = 0 ∧ e.val = x7Slot.val
      then δ else 0)

/-- The bridge family. -/
def bridgeShift (δ : BaseField) (z : RestTape TapeRest × MaskVectors) :
    RestTape TapeRest × MaskVectors :=
  (bridgeRest δ z.1, bridgeMasks δ z.2)

theorem bridgeShift_neg (δ : BaseField) (z : RestTape TapeRest × MaskVectors) :
    bridgeShift (-δ) (bridgeShift δ z) = z := by
  obtain ⟨⟨⟨coins, fixed, enc⟩, other⟩, masks⟩ := z
  refine Prod.ext (Prod.ext (Prod.ext ?_ rfl) ?_) ?_
  · show { coins with bridgeKey := coins.bridgeKey + δ + -δ } = coins
    simp
  · funext input
    show other (bridgeSwap coins.bridgeKey (coins.bridgeKey + δ)
      (bridgeSwap (coins.bridgeKey + δ) (coins.bridgeKey + δ + -δ) input)) = other input
    rw [add_neg_cancel_right]
    unfold bridgeSwap
    rw [Equiv.swap_comm, Equiv.swap_apply_self]
  · funext site e
    obtain ⟨ℓ, c, switch⟩ := site
    simp only [bridgeShift, bridgeMasks]
    split_ifs <;> ring

/-- The bridge family, as a permutation. -/
def bridgeEquiv (δ : BaseField) : (RestTape TapeRest × MaskVectors) ≃
    (RestTape TapeRest × MaskVectors) where
  toFun := bridgeShift δ
  invFun := bridgeShift (-δ)
  left_inv := bridgeShift_neg δ
  right_inv z := by
    have := bridgeShift_neg (-δ) z
    rwa [neg_neg] at this

theorem chunk_zero_lt : 0 < chunkCount := by unfold chunkCount; omega

theorem switch_lt (c : Fin chunkCount) (k : Nat) (small : k < 2) : k < 2 ^ chunkWidth c :=
  lt_of_lt_of_le small (by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ chunkWidth c := Nat.pow_le_pow_right (by omega) (chunkWidth_pos c))

/-- A double sum with one live cell. -/
theorem double_single (k : Nat) (small : k < 2)
    (f : (c : Fin chunkCount) → Fin (2 ^ chunkWidth c) → BaseField) :
    (∑ c : Fin chunkCount, ∑ sw : Fin (2 ^ chunkWidth c),
        if c.val = 0 ∧ sw.val = k then f c sw else 0) =
      f ⟨0, chunk_zero_lt⟩ ⟨k, switch_lt _ k small⟩ := by
  rw [Finset.sum_eq_single ⟨0, chunk_zero_lt⟩]
  · rw [Finset.sum_eq_single ⟨k, switch_lt _ k small⟩]
    · simp
    · intro sw _ ne
      have : sw.val ≠ k := fun same => ne (Fin.ext same)
      simp [this]
    · intro absent
      exact absurd (Finset.mem_univ _) absent
  · intro c _ ne
    have : c.val ≠ 0 := fun same => ne (Fin.ext same)
    exact Finset.sum_eq_zero fun sw _ => by simp [this]
  · intro absent
    exact absurd (Finset.mem_univ _) absent

/-- A sum over one chunk's switches with one live cell. -/
theorem single_switch (c : Fin chunkCount) (k : Nat) (small : k < 2) (value : BaseField) :
    (∑ sw : Fin (2 ^ chunkWidth c), if sw.val = k then value else 0) = value := by
  rw [Finset.sum_eq_single ⟨k, switch_lt _ k small⟩]
  · simp
  · intro sw _ ne
    have : sw.val ≠ k := fun same => ne (Fin.ext same)
    simp [this]
  · intro absent
    exact absurd (Finset.mem_univ _) absent

section Instances

variable [FieldCertificate] [GroupCertificate]

theorem bridgeMasks_curveX (δ : BaseField) (masks : MaskVectors) (c : Fin chunkCount)
    (sw : Fin (2 ^ chunkWidth c)) (e : Fin curveElementCountX) :
    bridgeMasks δ masks ⟨.curveX, c, sw⟩ e = masks ⟨.curveX, c, sw⟩ e +
      (if e = x7Slot then ((if c.val = 0 ∧ sw.val = 1 then δ else 0) -
        (if c.val = 0 ∧ sw.val = 0 then δ else 0)) else 0) := by
  simp only [bridgeMasks, true_and]
  by_cases he : e = x7Slot
  · subst he
    simp only [if_true, and_true]
    split_ifs <;> ring
  · have : e.val ≠ x7Slot.val := fun same => he (Fin.ext same)
    simp [this, he]

/-- **The published switch sums are kept.** -/
theorem sum_bridgeMasks (δ : BaseField) (masks : MaskVectors) (c : Fin chunkCount)
    (e : Fin curveElementCountX) :
    (∑ sw : Fin (2 ^ chunkWidth c), bridgeMasks δ masks ⟨.curveX, c, sw⟩ e) =
      ∑ sw : Fin (2 ^ chunkWidth c), masks ⟨.curveX, c, sw⟩ e := by
  rw [Finset.sum_congr rfl fun sw _ => bridgeMasks_curveX δ masks c sw e, Finset.sum_add_distrib]
  suffices rest : (∑ sw : Fin (2 ^ chunkWidth c), (if e = x7Slot then
      ((if c.val = 0 ∧ sw.val = 1 then δ else 0) - (if c.val = 0 ∧ sw.val = 0 then δ else 0))
      else 0)) = 0 by rw [rest, add_zero]
  by_cases he : e = x7Slot
  · rw [Finset.sum_congr rfl fun sw _ => if_pos he, Finset.sum_sub_distrib]
    by_cases hc : c.val = 0
    · simp only [hc, true_and]
      rw [single_switch c 1 (by omega) δ, single_switch c 0 (by omega) δ, sub_self]
    · rw [Finset.sum_eq_zero fun sw _ => if_neg (fun h => hc h.1),
        Finset.sum_eq_zero fun sw _ => if_neg (fun h => hc h.1), sub_self]
  · exact Finset.sum_eq_zero fun sw _ => if_neg he

/-- **`K_x7` moves by `δ`; no other offset moves.** -/
theorem offsets_bridgeMasks (δ : BaseField) (masks : MaskVectors) (e : Fin curveElementCountX) :
    (∑ c : Fin chunkCount, ∑ sw : Fin (2 ^ chunkWidth c),
        iota _ sw * bridgeMasks δ masks ⟨.curveX, c, sw⟩ e) =
      (∑ c : Fin chunkCount, ∑ sw : Fin (2 ^ chunkWidth c), iota _ sw * masks ⟨.curveX, c, sw⟩ e) +
        (if e = x7Slot then δ else 0) := by
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun sw _ => by
    rw [bridgeMasks_curveX, mul_add]]
  simp only [Finset.sum_add_distrib]
  rw [add_right_inj]
  by_cases he : e = x7Slot
  · simp only [he, if_true, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib]
    rw [double_single 1 (by omega) fun c sw => iota _ sw * δ,
      double_single 0 (by omega) fun c sw => iota _ sw * δ]
    simp [iota]
  · simp only [he, if_false, mul_zero, Finset.sum_const_zero]

end Instances

section Invariance

variable [FieldCertificate] [GroupCertificate]

theorem bridgeRest_hash (δ : BaseField) (rest : RestTape TapeRest) :
    hashOf (bridgeRest δ rest).2 blankScale (bridgeInput (bridgeRest δ rest).1.1.bridgeKey) =
      hashOf rest.2 blankScale (bridgeInput rest.1.1.bridgeKey) := by
  rw [hashOf_bridgeInput, hashOf_bridgeInput]
  show rest.2 (bridgeSwap rest.1.1.bridgeKey (rest.1.1.bridgeKey + δ)
    ⟨bridgeInput (rest.1.1.bridgeKey + δ), _⟩) = _
  unfold bridgeSwap
  rw [Equiv.swap_apply_right]

theorem whiteningKeys_bridge (δ : BaseField) (rest : RestTape TapeRest) :
    EncPRF.whiteningKeys (hashOf (bridgeRest δ rest).2 blankScale) (bridgeRest δ
        rest).1.1.bridgeKey =
      EncPRF.whiteningKeys (hashOf rest.2 blankScale) rest.1.1.bridgeKey := by
  unfold EncPRF.whiteningKeys
  rw [bridgeRest_hash]

theorem restKeys_bridge (δ : BaseField) (rest : RestTape TapeRest) :
    restKeys (bridgeRest δ rest) = restKeys rest := by
  have white : Pipeline.whitenedKey (bridgeRest δ rest).1.2.2 (hashOf (bridgeRest δ rest).2
      blankScale)
      (bridgeRest δ rest).1.1.bridgeKey (bridgeRest δ rest).1.1.inputMacKey =
      Pipeline.whitenedKey rest.1.2.2 (hashOf rest.2 blankScale) rest.1.1.bridgeKey
        rest.1.1.inputMacKey := by
    unfold Pipeline.whitenedKey
    rw [whiteningKeys_bridge]
    rfl
  unfold restKeys garblerKeys
  rw [white]
  rfl

theorem tablesOf_bridgeRest (δ : BaseField) (rest : RestTape TapeRest) (masks : MaskVectors)
    (ℓ : Lane) : tablesOf (bridgeRest δ rest) masks ℓ = tablesOf rest masks ℓ := by
  unfold tablesOf
  rw [restKeys_bridge]
  rfl

theorem tablesOf_bridgeMasks (δ : BaseField) (rest : RestTape TapeRest) (masks : MaskVectors)
    (ℓ : Lane) (other : ℓ ≠ .curveX) :
    tablesOf rest (bridgeMasks δ masks) ℓ = tablesOf rest masks ℓ := by
  unfold tablesOf
  congr 1
  funext c switch element
  simp only [bridgeMasks, other, false_and, if_false, add_zero, sub_zero]

/-- **The EncPRF entries are kept.** -/
theorem encOf_bridge (δ : BaseField) (rest : RestTape TapeRest) :
    encOf (bridgeRest δ rest) = encOf rest := by
  unfold encOf
  rw [bridgeRest_hash]
  have same : ∀ request : PublicQuery FixedIndex EncPRF.PermutationIndex, IsEncForward request →
      publicAnswer (restOracle (bridgeRest δ rest)) request =
        publicAnswer (restOracle rest) request := by
    intro request enc
    cases request with
    | encForward index input => rfl
    | _ => exact enc.elim
  exact ((padsM_encOnly _).agree (restOracle rest) (restOracle (bridgeRest δ rest)) same).1

theorem curveValues_bridge (δ : BaseField) (xs : Fin curveElementCountX → BaseField)
    (ys : Fin curveElementCountY → BaseField) :
    Pipeline.curveValues (fun e => xs e + (if e = x7Slot then δ else 0)) ys =
      fun element => Pipeline.curveValues xs ys element +
        (if element = .inl .x7 then δ else 0) := by
  funext element
  rcases element with (_ | _ | _) | (_ | _) <;> simp [Pipeline.curveValues, x7Slot, curveXElementIndex,
    CurveXElement.slot]

theorem assemble_bridge (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (t δ : BaseField) (curveMask : NonZeroBase)
    (curveR1 curveR2 : BaseField) (cx cx' : Programs.LaneTables curveElementCountX)
    (cy : Programs.LaneTables curveElementCountY) (px : Programs.LaneTables pointElementCountX)
    (py : Programs.LaneTables pointElementCountY)
    (gadget : Vector Exception.Entry FieldMacToECMac.outputMacCount)
    (offsets : cx'.offsets = fun e => cx.offsets e + (if e = x7Slot then δ else 0))
    (joins : ∀ slopes, cx'.scaleJoins slopes = cx.scaleJoins slopes) (hot : cx'.hotJoins = cx.hotJoins) :
    Programs.assemble outputKeys pointRandomness (t + δ) curveMask curveR1 curveR2 cx' cy px py gadget =
      Programs.assemble outputKeys pointRandomness t curveMask curveR1 curveR2 cx cy px py gadget := by
  have slopes : ∀ K : CurveMembership.Values,
      CurveMembership.slopes curveR1 curveR2
          (fun element => K element + (if element = .inl .x7 then δ else 0)) =
        CurveMembership.slopes curveR1 curveR2 K := by
    intro K
    funext element
    rcases element with (_ | _ | _) | (_ | _) <;> simp [CurveMembership.slopes]
  have garbled : ∀ K : CurveMembership.Values,
      CurveMembership.garble (t + δ) curveMask.value curveR1 curveR2
          (fun element => K element + (if element = .inl .x7 then δ else 0)) =
        CurveMembership.garble t curveMask.value curveR1 curveR2 K := by
    intro K
    simp only [CurveMembership.garble, reduceCtorEq, if_false, if_true, add_zero, Prod.mk.injEq]
    first | trivial | exact ⟨by ring, rfl, rfl⟩ | (refine ⟨?_, trivial⟩; ring)
  unfold Programs.assemble
  simp only [offsets, joins, hot, curveValues_bridge, slopes, garbled]

/-- **The published value is kept.** -/
theorem publishedOf_bridge (scalar : NonZeroScalar) (δ : BaseField)
    (z : RestTape TapeRest × MaskVectors) :
    publishedOf scalar (bridgeShift δ z) = publishedOf scalar z := by
  obtain ⟨rest, masks⟩ := z
  unfold publishedOf
  simp only [bridgeShift, tablesOf_bridgeRest]
  rw [tablesOf_bridgeMasks δ rest masks .curveY (by decide),
    tablesOf_bridgeMasks δ rest masks .pointX (by decide),
    tablesOf_bridgeMasks δ rest masks .pointY (by decide), whiteningKeys_bridge]
  exact assemble_bridge _ _ rest.1.1.bridgeKey δ _ _ _ (tablesOf rest masks .curveX)
    (tablesOf rest (bridgeMasks δ masks) .curveX) _ _ _ _
    (funext fun e => offsets_bridgeMasks δ masks e)
    (fun slopes => funext fun c => funext fun e => congrArg (· + _) (sum_bridgeMasks δ masks c e))
    rfl

end Invariance

/-- At most two shifts move the bridge input onto a key. -/
theorem bridge_few (t key : BaseField) (s : Finset BaseField)
    (all : ∀ δ ∈ s, bridgeInput (t + δ) = key) : s.card ≤ 2 :=
  le_trans (Finset.card_le_card_of_injOn (fun δ => t + δ)
    (fun δ member => Finset.mem_filter.mpr ⟨Finset.mem_univ _, all δ member⟩)
    fun _ _ _ _ same => add_left_cancel same) (bridgeInput_filter_card_le_two key)

/-- **`StageOneBridgeGuess`, real.** -/
theorem stageOneBridgeGuess : StageOneBridgeGuess := by
  intro field group parameter scalar view key
  let Φ : Coins × Oracle → RestTape TapeRest × MaskVectors := fun tape => (restOf tape, maskOf tape)
  let V : RestTape TapeRest × MaskVectors → Public × List (Entry FixedIndex
      EncPRF.PermutationIndex) :=
    fun z => (publishedOf scalar z, encOf z.1)
  have factor : ∀ tape, stageOneView parameter scalar tape = V (Φ tape) := fun tape => by
    show ((Scheme.scheme.garble parameter scalar tape).1, encEntries scalar tape) = _
    rw [published_eq, encEntries_eq]
  have law : swappedChallengeTape.map Φ =
      PMF.uniformOfFintype (RestTape TapeRest × MaskVectors) := by
    rw [swapped_restMasks, restLaw, restUniform, ← uniformOfFintype_productPMF,
      ← uniformOfFintype_productPMF]
  have transfer : ∀ S : Set (RestTape TapeRest × MaskVectors),
      swappedChallengeTape.toOuterMeasure (Φ ⁻¹' S) =
        (PMF.uniformOfFintype (RestTape TapeRest × MaskVectors)).toOuterMeasure S := by
    intro S
    rw [← law, PMF.toOuterMeasure_map_apply]
  have left : {tape : Coins × Oracle | stageOneView parameter scalar tape = view ∧
      bridgeInput tape.1.bridgeKey = key} =
        Φ ⁻¹' {z | V z = view ∧ bridgeInput z.1.1.1.bridgeKey = key} := by
    ext tape
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, factor]
    rfl
  have right : {tape : Coins × Oracle | stageOneView parameter scalar tape = view} =
      Φ ⁻¹' {z | V z = view} := by
    ext tape
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, factor]
  rw [left, right, transfer, transfer]
  have bound := event_le_of_symmetry_count
    (PMF.uniformOfFintype (RestTape TapeRest × MaskVectors)) V
    (fun z => bridgeInput z.1.1.1.bridgeKey = key) (fun δ => bridgeShift δ)
    (fun δ => Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv (bridgeEquiv δ))
    (fun δ z => by
      show (publishedOf scalar (bridgeShift δ z), encOf (bridgeShift δ z).1) =
        (publishedOf scalar z, encOf z.1)
      rw [publishedOf_bridge]
      exact congrArg _ (encOf_bridge δ z.1))
    2 (fun z => bridge_few z.1.1.1.bridgeKey key) view
  refine le_trans bound (le_of_eq ?_)
  rw [ZMod.card, Nat.cast_two]

end

end Kriterion.ArgoMAC.Security.Phase3
