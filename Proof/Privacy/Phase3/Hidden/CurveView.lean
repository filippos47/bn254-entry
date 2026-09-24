/-
**Phase 3, P1h — `StageTwoBridgeGuess`, real: off the curve, `bridgeInput t` is `2/(p−1)`-hidden
given the stage-2 view.**

The curve family changes the hidden (active-switch) curve vectors, and the swapped tape's density is
not invariant under a map that changes vectors but not their limbs. So work on the **curve
coordinates** `(rest, the limb values of the non-hidden sites, the hidden vectors)` (`curveCoord`):

* under the swapped tape they are `rest × swapLimbLaw(non-hidden) × uniform` (`swapped_curveCoord`,
  from `Split.swapKernel_split_law`): given all the vectors the limbs of the non-hidden sites are
  uniform on their own fibres, independent of the hidden vectors;
* off the curve the stage-2 view factors through them (`view_eq`): the published value through
  `publishedOf` of the combined vectors, the EncPRF entries and the labels through the rest, the
  designed entries through the curve lanes' fold gates and non-hidden limbs (`CurveDesigned`);
* the curve family acts on them (`curveShiftCoord`: the rest by `curveRest`, the hidden vectors by
  the correction), keeps their law (`curveLaw_shift`) and the view (`curveView_shift`), and moves
  `t` injectively in `c ∈ F_p^*` (`curveRest_bridgeKey_injective`), so at most two units move
  `bridgeInput t` onto a given key.

`event_le_of_symmetry_count` over the `p − 1` units with `k = 2`, transferred back:
`stageTwoBridgeGuess`. With `stageTwoGuess_of_bridge` this is `stageTwoGuess`, and with
`stageOneGuess` and the reduction, **hop (1)**:

```
hidden : GameUntilBad maskSwappedHybrid hiddenDeletedHybrid fun q₁ q₂ => hiddenPointError (q₁ + q₂)
```

per query exactly `3/2^128 + 2/(p − 1)` (L1's constant), no additive constant.
-/

import Proof.Privacy.Phase3.Hidden.CurveDesigned

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv)
open scoped ENNReal

noncomputable section

section Instances

variable [FieldCertificate] [GroupCertificate]

/-! ### The curve coordinates -/

/-- The limb slots of the non-hidden sites at an input. -/
abbrev OffSlots (input : AffineInput) := LimbSlot (offLane VectorSite.lane (IsHidden input))

/-- The vectors of the hidden sites at an input. -/
abbrev OnVectors (input : AffineInput) := LaneVectors (onLane VectorSite.lane (IsHidden input))

/-- **The curve coordinates.** -/
abbrev CurveCoord (input : AffineInput) :=
  RestTape TapeRest × (OffSlots input → Block × Block) × OnVectors input

/-- The garbler's vectors are the batched sampler of its scale table at its limb points. -/
theorem maskOf_eq (tape : Coins × Oracle) :
    maskOf tape = maskMap (limbPoint (garblerLabels (restOf tape))) (scaleTableOf tape.2.2.2) := by
  show switchMasks tape.2.2.2 (garblerLabelOf tape) = _
  rw [garblerLabelOf_eq]
  conv_lhs => rw [← hashOf_tables tape.2.2.2]
  exact switchMasks_hashOf _ _ _

/-- **The curve coordinates of a tape.** -/
def curveCoord (input : AffineInput) (tape : Coins × Oracle) : CurveCoord input :=
  (restOf tape, (splitSlots VectorSite.lane (IsHidden input)
      (evalAt (limbPoint (garblerLabels (restOf tape))) (scaleTableOf tape.2.2.2))).1,
    (splitVectors VectorSite.lane (IsHidden input) (maskOf tape)).2)

/-- The vectors from the curve coordinates. -/
def combineMasks (input : AffineInput) (z : CurveCoord input) : MaskVectors :=
  (splitVectors VectorSite.lane (IsHidden input)).symm
    (masksOf (offLane VectorSite.lane (IsHidden input)) z.2.1, z.2.2)

theorem maskOf_combine (input : AffineInput) (tape : Coins × Oracle) :
    maskOf tape = combineMasks input (curveCoord input tape) := by
  unfold combineMasks curveCoord
  apply (splitVectors VectorSite.lane (IsHidden input)).injective
  rw [Equiv.apply_symm_apply]
  refine Prod.ext ?_ rfl
  show (splitVectors VectorSite.lane (IsHidden input) (maskOf tape)).1 = _
  rw [maskOf_eq]
  rfl

/-- A tape with the given rest and non-hidden limb values (zero at the hidden limbs and off the
limb points of the scale table). -/
def curveTape (input : AffineInput) (rest : RestTape TapeRest)
    (off : OffSlots input → Block × Block) : Coins × Oracle :=
  reassembleEquiv (assemble (rest, Function.extend (limbPoint (garblerLabels rest))
    ((splitSlots VectorSite.lane (IsHidden input)).symm (off, fun _ => (0, 0))) blankScale))

theorem restOf_assemble (rest : RestTape TapeRest) (scale : ScaleTable) :
    restOf (reassembleEquiv (assemble (rest, scale))) = rest := by
  obtain ⟨⟨coins, fixed, enc⟩, other⟩ := rest
  exact Prod.ext rfl (otherTableOf_hashOf other scale)

theorem curveTape_coins (input : AffineInput) (rest : RestTape TapeRest)
    (off : OffSlots input → Block × Block) : (curveTape input rest off).1 = rest.1.1 := rfl

theorem curveTape_fixed (input : AffineInput) (rest : RestTape TapeRest)
    (off : OffSlots input → Block × Block) : (curveTape input rest off).2.1 = rest.1.2.1 := rfl

theorem restOf_curveTape (input : AffineInput) (rest : RestTape TapeRest)
    (off : OffSlots input → Block × Block) : restOf (curveTape input rest off) = rest :=
  restOf_assemble _ _

/-- The curve tape's hash at a non-hidden limb point is the given limb value. -/
theorem curveTape_hash (input : AffineInput) (rest : RestTape TapeRest)
    (off : OffSlots input → Block × Block) (slot : LimbSite) (notHidden : ¬ IsHidden input slot.1) :
    (curveTape input rest off).2.2.2 (labelInput slot (garblerLabels rest slot.1)) =
      off ⟨⟨slot.1, notHidden⟩, slot.2⟩ := by
  show hashOf rest.2 _ (limbInput (garblerLabels rest) slot).1 = _
  rw [hashOf_scale]
  show Function.extend (limbPoint (garblerLabels rest)) _ blankScale
    (limbPoint (garblerLabels rest) slot) = _
  rw [(limbPoint (garblerLabels rest)).injective.extend_apply]
  show (if h : IsHidden input slot.1 then _ else _) = _
  rw [dif_neg notHidden]

/-- **The stage-2 view on the curve coordinates.** -/
def curveView (scalar : NonZeroScalar) (input : AffineInput) (z : CurveCoord input) :
    (Public × List (Entry FixedIndex EncPRF.PermutationIndex)) × LamportSignature ×
      List (Entry FixedIndex EncPRF.PermutationIndex) :=
  ((publishedOf scalar (z.1, combineMasks input z), encOf z.1),
    Scheme.scheme.encode z.1.1.1.inputMacKey input, curveDesigned scalar (curveTape input z.1
        z.2.1) input)

/-- **Off the curve, the stage-2 view factors through the curve coordinates.** -/
theorem view_eq (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (invalid : validate input = false) (tape : Coins × Oracle) :
    stageTwoView designedRule parameter scalar input tape =
      curveView scalar input (curveCoord input tape) := by
  have designed : curveDesigned scalar (curveTape input (restOf tape) (curveCoord input tape).2.1)
      input = curveDesigned scalar tape input := by
    refine curveDesigned_congr scalar tape _ input rfl rfl rfl fun slot _ notHidden => ?_
    rw [garblerLabelOf_eq, curveTape_hash input (restOf tape) _ slot notHidden]
    show scaleTableOf tape.2.2.2 (limbInput (garblerLabels (restOf tape)) slot) = _
    rfl
  unfold stageTwoView stageOneView curveView
  rw [published_eq, encEntries_eq, designedEntries_offCurve parameter scalar tape input invalid,
    maskOf_combine input tape]
  exact Prod.ext (Prod.ext rfl rfl) (Prod.ext rfl designed.symm)

/-! ### The law of the curve coordinates -/

/-- **The law of the curve coordinates under the swapped tape.** -/
def curveLaw (input : AffineInput) : PMF (CurveCoord input) :=
  productPMF (restLaw restUniform)
    (productPMF (swapLimbLaw (offLane VectorSite.lane (IsHidden input)))
      (PMF.uniformOfFintype (OnVectors input)))

theorem curveCoord_assemble (input : AffineInput) (rest : RestTape TapeRest) (scale : ScaleTable) :
    curveCoord input (reassembleEquiv (assemble (rest, scale))) =
      (rest, (splitSlots VectorSite.lane (IsHidden input)
          (evalAt (limbPoint (garblerLabels rest)) scale)).1,
        (splitVectors VectorSite.lane (IsHidden input)
          (maskMap (limbPoint (garblerLabels rest)) scale)).2) := by
  unfold curveCoord
  rw [maskOf_eq, restOf_assemble]
  show (rest, _, _) = (rest, _, _)
  rw [show scaleTableOf (reassembleEquiv (assemble (rest, scale))).2.2.2 = scale from
    scaleTableOf_hashOf rest.2 scale]

/-- **Under the swapped tape the curve coordinates have `curveLaw`.** -/
theorem swapped_curveCoord (input : AffineInput) :
    swappedChallengeTape.map (curveCoord input) = curveLaw input := by
  unfold swappedChallengeTape swappedTape swapLaw curveLaw
  rw [PMF.map_comp, PMF.map_comp, PMF.map_bind, productPMF]
  refine congrArg _ (funext fun rest => ?_)
  rw [PMF.map_comp, ← swapKernel_split_law VectorSite.lane (IsHidden input)
    (limbPoint (garblerLabels rest)), PMF.map_comp]
  refine congrArg (fun f => PMF.map f (swapKernel (limbPoint (garblerLabels rest))))
    (funext fun scale => ?_)
  exact curveCoord_assemble input rest scale

/-! ### The family on the curve coordinates -/

/-- **The curve family on the coordinates.** -/
def curveShiftCoord (input : AffineInput) (c : BaseFieldˣ) (z : CurveCoord input) :
    CurveCoord input :=
  (curveRest input c z.1, z.2.1, fun h e => z.2.2 h e - siteCorr input (curveStep c z.1) h.1 e)

theorem garblerLabels_curve (input : AffineInput) (c : BaseFieldˣ) (rest : RestTape TapeRest) :
    garblerLabels (curveRest input c rest) = garblerLabels rest := by
  funext site
  show garblerLabel (curveRest input c rest).1.2.1 (restKeys (curveRest input c rest)).1
      (restKeys (curveRest input c rest)).2 site =
    garblerLabel rest.1.2.1 (restKeys rest).1 (restKeys rest).2 site
  have fixed : (curveRest input c rest).1.2.1 = rest.1.2.1 := rfl
  rw [restKeys_curve, fixed]

/-- **The curve family keeps the law of the curve coordinates.** -/
theorem curveLaw_shift (input : AffineInput) (c : BaseFieldˣ) :
    (curveLaw input).map (curveShiftCoord input c) = curveLaw input := by
  unfold curveLaw
  rw [productPMF, PMF.map_bind]
  have each : ∀ rest : RestTape TapeRest,
      ((productPMF (swapLimbLaw (offLane VectorSite.lane (IsHidden input)))
          (PMF.uniformOfFintype (OnVectors input))).map (Prod.mk rest)).map
        (curveShiftCoord input c) =
      (productPMF (swapLimbLaw (offLane VectorSite.lane (IsHidden input)))
          (PMF.uniformOfFintype (OnVectors input))).map (Prod.mk (curveRest input c rest)) := by
    intro rest
    rw [PMF.map_comp]
    have factor : (curveShiftCoord input c ∘ Prod.mk rest) =
        Prod.mk (curveRest input c rest) ∘ Prod.map id
          (Equiv.subRight fun (h : {site // IsHidden input site}) e =>
            siteCorr input (curveStep c rest) h.1 e) := rfl
    rw [factor, ← PMF.map_comp, productPMF_map, PMF.map_id, uniformOfFintype_map_equiv]
  simp only [each]
  rw [restLaw_uniform]
  conv_rhs => rw [← uniformOfFintype_map_equiv (curveRestEquiv input c)]
  rw [PMF.bind_map]
  rfl

theorem combineMasks_shift (input : AffineInput) (c : BaseFieldˣ) (z : CurveCoord input) :
    combineMasks input (curveShiftCoord input c z) =
      curveMasks input (curveStep c z.1) (combineMasks input z) := by
  funext site e
  unfold combineMasks curveShiftCoord curveMasks
  simp only [splitVectors, Equiv.coe_fn_symm_mk]
  by_cases h : IsHidden input site
  · rw [dif_pos h, if_pos h, dif_pos h]
  · rw [dif_neg h, if_neg h, dif_neg h]

/-- **The curve family keeps the view.** -/
theorem curveView_shift (scalar : NonZeroScalar) (input : AffineInput)
    (c : BaseFieldˣ) (z : CurveCoord input) :
    curveView scalar input (curveShiftCoord input c z) =
      curveView scalar input z := by
  have e1 : publishedOf scalar ((curveShiftCoord input c z).1,
      curveMasks input (curveStep c z.1) (combineMasks input z)) =
        publishedOf scalar (z.1, combineMasks input z) :=
    publishedOf_curve scalar input c z.1 (combineMasks input z)
  have e2 : encOf (curveShiftCoord input c z).1 = encOf z.1 := encOf_curve input c z.1
  have e3 : curveDesigned scalar (curveTape input (curveShiftCoord input c z).1
      (curveShiftCoord input c z).2.1) input = curveDesigned scalar (curveTape input z.1 z.2.1)
          input := by
    refine curveDesigned_congr scalar (curveTape input z.1 z.2.1) _ input ?_ ?_ ?_
      fun slot _ notHidden => ?_
    · rw [curveTape_coins, curveTape_coins]
      rfl
    · rw [curveTape_coins, curveTape_coins]
      rfl
    · rw [curveTape_fixed, curveTape_fixed]
      rfl
    rw [garblerLabelOf_eq, restOf_curveTape, curveTape_hash input z.1 _ slot notHidden,
      ← garblerLabels_curve input c z.1,
      show (curveShiftCoord input c z).1 = curveRest input c z.1 from rfl,
      curveTape_hash input _ _ slot notHidden]
    rfl
  have e4 : (curveShiftCoord input c z).1.1.1.inputMacKey = z.1.1.1.inputMacKey := rfl
  unfold curveView
  rw [combineMasks_shift, e1, e2, e3, e4]

/-! ### The bound -/

theorem card_units_base : Fintype.card BaseFieldˣ = baseFieldModulus - 1 := by
  rw [← ZMod.card_units baseFieldModulus]

/-- At most two units move the bridge input onto a key. -/
theorem curve_few (input : AffineInput) (invalid : validate input = false) (rest : RestTape
    TapeRest)
    (key : BaseField) (s : Finset BaseFieldˣ)
    (all : ∀ c ∈ s, bridgeInput (curveRest input c rest).1.1.bridgeKey = key) : s.card ≤ 2 :=
  le_trans (Finset.card_le_card_of_injOn (fun c => (curveRest input c rest).1.1.bridgeKey)
    (fun c member => Finset.mem_filter.mpr ⟨Finset.mem_univ _, all c member⟩)
    fun c _ c' _ same => curveRest_bridgeKey_injective input invalid rest c c' same)
    (bridgeInput_filter_card_le_two key)

/-- **`StageTwoBridgeGuess`, real.** -/
theorem stageTwoBridgeGuess : StageTwoBridgeGuess := by
  intro field group parameter scalar input view key invalid
  let Φ := curveCoord input
  have transfer : ∀ S : Set (CurveCoord input),
      swappedChallengeTape.toOuterMeasure (Φ ⁻¹' S) = (curveLaw input).toOuterMeasure S := by
    intro S
    rw [← swapped_curveCoord input, PMF.toOuterMeasure_map_apply]
  have left : {tape : Coins × Oracle | stageTwoView designedRule parameter scalar input tape = view ∧
      bridgeInput tape.1.bridgeKey = key} =
        Φ ⁻¹' {z | curveView scalar input z = view ∧ bridgeInput z.1.1.1.bridgeKey = key} := by
    ext tape
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, view_eq parameter scalar input invalid tape]
    rfl
  have right : {tape : Coins × Oracle | stageTwoView designedRule parameter scalar input tape = view} =
      Φ ⁻¹' {z | curveView scalar input z = view} := by
    ext tape
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, view_eq parameter scalar input invalid tape]
    rfl
  rw [left, right, transfer, transfer]
  have bound := event_le_of_symmetry_count (curveLaw input) (curveView scalar input)
    (fun z => bridgeInput z.1.1.1.bridgeKey = key) (fun c => curveShiftCoord input c)
    (fun c => curveLaw_shift input c) (fun c z => curveView_shift scalar input c z) 2
    (fun z => curve_few input invalid z.1 key) view
  refine le_trans bound (le_of_eq ?_)
  rw [card_units_base, Nat.cast_two]

end Instances

/-- **`StageTwoGuess designedRule` at L1's constant, real.** -/
theorem stageTwoGuess : StageTwoGuess designedRule (ENNReal.ofReal hiddenCharge) :=
  stageTwoGuess_of_bridge stageTwoBridgeGuess

/-- **Hop (1), `G0U → G1U`, real**: identical until a hidden entry is touched, at
`L1 = hiddenPointError (q₁ + q₂)`, per query `3/2^128 + 2/(p − 1)`. -/
theorem hidden :
    Kriterion.ArgoMAC.Phase3.Glue.GameUntilBad maskSwappedHybrid hiddenDeletedHybrid
      fun first second => Kriterion.ArgoMAC.Phase3.Glue.hiddenPointError (first + second) :=
  hidden_of_stageTwo stageTwoGuess

end

end Kriterion.ArgoMAC.Security.Phase3
