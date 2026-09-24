/-
**Phase 3, P1f — the swapped tape is invariant under every join-keeping tape shift.**

`swapped_shift_invariant`: `swappedChallengeTape.map (shiftTape T scalar) = swappedChallengeTape`
for every `TapeShift` that keeps every join. On the split tape (`RestTape TapeRest × ScaleTable`,
`MaskSwap`) the shift acts on the rest -- the coins, the fixed-key permutations and the hash off the
scale range -- by an involution (`restShift`), so it keeps the uniform rest; it moves the garbler's
one-hot label at every vector site by the site's level shift (`garblerLabels_shift`, from
`sim_garbleChunkM`); and it relabels the scale table by the involution `relabel` of the scale range
(`scaleShift`), which carries the limb points of the old labels onto those of the moved labels, so
it maps the swap kernel at the old points onto the swap kernel at the new ones
(`swapKernel_map_comp`): every switch-mask vector keeps its value, only its hash inputs move.
-/

import Proof.Privacy.Phase3.Hidden.GarblerSim

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv)
open scoped ENNReal

noncomputable section

/-! ### The swap kernel under a relabelling of the table -/

section Generic

variable {V : Type} [Fintype V] [DecidableEq V] {laneOf : V → Lane} {D : Type} [Fintype D]
  [DecidableEq D]

/-- Overwriting then relabelling is relabelling then overwriting at the relabelled points. -/
theorem extend_comp_equiv {L X : Type} (point point' : L ↪ D) (σ : D ≃ D)
    (compat : ∀ l, σ (point' l) = point l) (values : L → X) (table : D → X) :
    Function.extend point values table ∘ σ = Function.extend point' values (table ∘ σ) := by
  funext x
  by_cases hit : ∃ l, point' l = x
  · obtain ⟨l, rfl⟩ := hit
    rw [Function.comp_apply, compat, point.injective.extend_apply, point'.injective.extend_apply]
  · rw [Function.comp_apply, Function.extend_apply' _ _ _ hit]
    refine Function.extend_apply' _ _ _ fun ⟨l, same⟩ => hit ⟨l, σ.injective ?_⟩
    rw [compat, same]

/-- A uniform table stays uniform under a relabelling. -/
theorem uniform_map_comp_equiv (σ : D ≃ D) :
    (PMF.uniformOfFintype (D → Block × Block)).map (fun table => table ∘ σ) =
      PMF.uniformOfFintype (D → Block × Block) :=
  uniformOfFintype_map_equiv (Equiv.arrowCongr σ.symm (Equiv.refl (Block × Block)))

/-- **The shared kernel under a relabelling** that carries the new points onto the old ones. -/
theorem fibreKernel_map_comp (point point' : LimbSlot laneOf ↪ D) (σ : D ≃ D)
    (compat : ∀ slot, σ (point' slot) = point slot) (vectors : LaneVectors laneOf) :
    (fibreKernel point vectors).map (fun table => table ∘ σ) = fibreKernel point' vectors := by
  unfold fibreKernel
  rw [PMF.map_bind]
  refine congrArg _ (funext fun values => ?_)
  rw [PMF.map_comp]
  have commute : ((fun table => table ∘ σ) ∘ Function.extend point values) =
      Function.extend point' values ∘ fun table : D → Block × Block => table ∘ σ :=
    funext fun table => extend_comp_equiv point point' σ compat values table
  rw [commute, ← PMF.map_comp, uniform_map_comp_equiv]

/-- **The swap kernel under a relabelling** that carries the new points onto the old ones. -/
theorem swapKernel_map_comp (point point' : LimbSlot laneOf ↪ D) (σ : D ≃ D)
    (compat : ∀ slot, σ (point' slot) = point slot) :
    (swapKernel point).map (fun table => table ∘ σ) = swapKernel point' := by
  unfold swapKernel
  rw [PMF.map_bind]
  exact congrArg _ (funext (fibreKernel_map_comp point point' σ compat))

end Generic

/-! ### The two parts of the shift -/

section Parts

variable [FieldCertificate] [GroupCertificate]

/-- The shift of the hash off the scale range: `k₂` at the bridge input. -/
def shiftOther (T : TapeShift) (key : BaseField) (other : OtherTable) : OtherTable := fun input =>
  if input.1 = bridgeInput key then ((other input).1, (other input).2 ^^^ T.key2) else other input

theorem shiftOther_involutive (T : TapeShift) (key : BaseField) :
    Function.Involutive (shiftOther T key) := by
  intro other
  funext input
  unfold shiftOther
  by_cases hit : input.1 = bridgeInput key
  · simp only [if_pos hit, xor_cancel_right]
  · simp only [if_neg hit]

/-- The relabelling of the scale range. -/
def relabelScale (T : TapeShift) (input : ScaleInput) : ScaleInput :=
  ⟨relabel (siteShift T) input.1, relabel_val_lt _ _ input.2⟩

theorem relabelScale_involutive (T : TapeShift) : Function.Involutive (relabelScale T) :=
  fun input => Subtype.ext (relabel_involutive _ input.1)

/-- The relabelling of the scale range, as a permutation. -/
def relabelScaleEquiv (T : TapeShift) : ScaleInput ≃ ScaleInput :=
  (relabelScale_involutive T).toPerm _

/-- **The shift of the scale table**: relabelled. -/
def scaleShift (T : TapeShift) (scale : ScaleTable) : ScaleTable := scale ∘ relabelScaleEquiv T

/-- **The shift of the rest of the tape**: coins, fixed-key permutations, the hash off the scale
range. -/
def restShift (T : TapeShift) (scalar : NonZeroScalar) (rest : RestTape TapeRest) :
    RestTape TapeRest :=
  ((shiftCoins T rest.1.1, ⟨fun index => shiftPerm (indexShift T scalar rest.1.1 index).1
      (indexShift T scalar rest.1.1 index).2 (rest.1.2.1.permutation index)⟩, rest.1.2.2),
    shiftOther T rest.1.1.bridgeKey rest.2)

theorem shiftCoins_offsets (T : TapeShift) (coins : Coins) :
    (shiftCoins T coins).offsets = coins.offsets :=
  rfl

theorem indexShift_shiftCoins (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) :
    indexShift T scalar (shiftCoins T coins) = indexShift T scalar coins := by
  funext index
  cases index with
  | gadget o κ position =>
      simp only [indexShift, gadgetShift, shiftCoins_offsets]
      rfl
  | _ => rfl

theorem shiftCoins_shiftCoins (T : TapeShift) (coins : Coins) :
    shiftCoins T (shiftCoins T coins) = coins := by
  apply Scheme.Coins.data_injective
  simp only [Scheme.Coins.data, shiftCoins, xor_cancel_right]

theorem restShift_involutive (T : TapeShift) (scalar : NonZeroScalar) :
    Function.Involutive (restShift T scalar) := by
  rintro ⟨⟨coins, ⟨fixed⟩, enc⟩, other⟩
  simp only [restShift, shiftCoins_shiftCoins, indexShift_shiftCoins]
  refine Prod.ext (Prod.ext rfl (Prod.ext ?_ rfl)) (shiftOther_involutive T _ other)
  exact congrArg PermutationOracle.mk (funext fun index => shiftPerm_involutive _ _ _)

/-- The rest shift, as a permutation. -/
def restShiftEquiv (T : TapeShift) (scalar : NonZeroScalar) :
    RestTape TapeRest ≃ RestTape TapeRest :=
  (restShift_involutive T scalar).toPerm _

/-- **The shifted hash is the split shift**: the bridge input's `k₂` on the rest of the table, the
relabelling on the scale table. -/
theorem shiftHash_hashOf (T : TapeShift) (key : BaseField) (other : OtherTable)
    (scale : ScaleTable) :
    shiftHash T key (hashOf other scale) = hashOf (shiftOther T key other) (scaleShift T scale) :=
        by
  funext value
  unfold shiftHash
  by_cases low : value.val < scaleRange
  · have notBridge : value ≠ bridgeInput key := fun same => bridgeInput_not_lt key (same ▸ low)
    rw [if_neg notBridge, hashOf_scale other scale ⟨relabel (siteShift T) value,
      relabel_val_lt _ _ low⟩, hashOf_scale _ _ ⟨value, low⟩]
    rfl
  · have right : hashOf (shiftOther T key other) (scaleShift T scale) value =
        shiftOther T key other ⟨value, low⟩ := hashOf_other _ _ ⟨value, low⟩
    rw [right]
    unfold shiftOther
    by_cases hit : value = bridgeInput key
    · rw [if_pos hit, if_pos hit, hashOf_other other scale ⟨value, low⟩]
    · rw [if_neg hit, if_neg hit, relabel_of_not_lt _ value low,
        hashOf_other other scale ⟨value, low⟩]

/-! ### The garbler's keys and labels move by the shift -/

/-- The whitening keys on the shifted rest: `k₂` moves. -/
theorem whiteningKeys_shiftOther (T : TapeShift) (key : BaseField) (other : OtherTable)
    (scale : ScaleTable) :
    EncPRF.whiteningKeys (hashOf (shiftOther T key other) scale) key =
      ⟨(EncPRF.whiteningKeys (hashOf other scale) key).first,
        (EncPRF.whiteningKeys (hashOf other scale) key).second ^^^ T.key2⟩ := by
  unfold EncPRF.whiteningKeys
  rw [hashOf_bridgeInput, hashOf_bridgeInput]
  unfold shiftOther
  rw [if_pos rfl]

theorem realPads_shift (T : TapeShift) (enc : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount)
    (bit : Bool) :
    Programs.realPads enc ⟨keys.first, keys.second ^^^ T.key2⟩ coordinate index bit =
      Programs.realPads enc keys coordinate index bit ^^^ T.key2 := by
  simp only [Programs.realPads, EncPRF.evenMansourPad, evenMansour, Cryptography.xor]
  ac_rfl

/-- The garbler's keys on a rest: `garblerKeys` with the scale range blank (never read). -/
def restKeys (rest : RestTape TapeRest) :
    (Lane → Block) × (Lane → Fin PlanB.coordinateBits → Block × Block) :=
  garblerKeys rest.1 (hashOf rest.2 blankScale)

theorem garblerKeys_delta (T : TapeShift) (scalar : NonZeroScalar) (rest : RestTape TapeRest)
    (lane : Lane) :
    (restKeys (restShift T scalar rest)).1 lane = (restKeys rest).1 lane ^^^ (T.lane lane).delta :=
  rfl

theorem garblerKeys_zero (T : TapeShift) (scalar : NonZeroScalar) (rest : RestTape TapeRest)
    (lane : Lane) (position : Fin PlanB.coordinateBits) :
    ((restKeys (restShift T scalar rest)).2 lane position).1 =
      ((restKeys rest).2 lane position).1 ^^^ (T.lane lane).zero position := by
  have pads : ∀ coordinate index bit,
      Programs.realPads rest.1.2.2
          (EncPRF.whiteningKeys (hashOf (shiftOther T rest.1.1.bridgeKey rest.2) blankScale)
            rest.1.1.bridgeKey) coordinate index bit =
        Programs.realPads rest.1.2.2
          (EncPRF.whiteningKeys (hashOf rest.2 blankScale) rest.1.1.bridgeKey) coordinate index bit
          ^^^ T.key2 := fun coordinate index bit => by
    rw [whiteningKeys_shiftOther]
    exact realPads_shift T rest.1.2.2 _ coordinate index bit
  cases lane
  · rw [lane_zero_curveX]
    exact shift_curve_key T rest.1.1 .x position
  · rw [lane_zero_curveY]
    exact shift_curve_key T rest.1.1 .y position
  · rw [lane_zero_pointX]
    exact shift_point_key T rest.1.1 _ _ pads .x position
  · rw [lane_zero_pointY]
    exact shift_point_key T rest.1.1 _ _ pads .y position

/-- **Every garbler label moves by its site's level shift.** -/
theorem garblerLabels_shift (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar)
    (rest : RestTape TapeRest) :
    garblerLabels (restShift T scalar rest) =
      fun site => garblerLabels rest site ^^^ siteShift T site := by
  funext site
  obtain ⟨lane, c, switch⟩ := site
  let O : Oracle := (rest.1.2.1, rest.1.2.2, fun _ => (0, 0))
  let O' : Oracle := ((restShift T scalar rest).1.2.1, rest.1.2.2, fun _ => (0, 0))
  have sim := sim_garbleChunkM (rel := fun _ _ => True) O O' (T.lane lane) (valid lane) lane
    ((restKeys rest).1 lane) ((restKeys rest).2 lane) ((restKeys (restShift T scalar rest)).2 lane)
    (garblerKeys_zero T scalar rest lane) c
    (fun n r half x small entry => by
      show shiftPerm (indexShift T scalar rest.1.1 _).1 (indexShift T scalar rest.1.1 _).2 _ _ = _
      rw [indexShift_hotIndexNat T scalar rest.1.1 lane c n r half small entry, shiftPerm_shift])
    (fun _ _ _ _ _ => trivial)
  have moved := sim.2.2.1 switch
  erw [Programs.eval_garbleChunkM O', Programs.eval_garbleChunkM O] at moved
  show (garbleChunk (restShift T scalar rest).1.2.1 lane
    ((restKeys (restShift T scalar rest)).1 lane) ((restKeys (restShift T scalar rest)).2 lane)
      c).1 switch = _
  rw [garblerKeys_delta]
  exact moved

end Parts

/-! ### The swapped tape is invariant -/

section Main

variable [FieldCertificate] [GroupCertificate]

/-- The shift on the split tape. -/
def splitShift (T : TapeShift) (scalar : NonZeroScalar) (tape : RestTape TapeRest × ScaleTable) :
    RestTape TapeRest × ScaleTable :=
  (restShift T scalar tape.1, scaleShift T tape.2)

theorem shiftTape_split (T : TapeShift) (scalar : NonZeroScalar)
    (tape : RestTape TapeRest × ScaleTable) :
    shiftTape T scalar (reassembleEquiv (assemble tape)) =
      reassembleEquiv (assemble (splitShift T scalar tape)) := by
  obtain ⟨⟨⟨coins, fixed, enc⟩, other⟩, scale⟩ := tape
  show (shiftCoins T coins, shiftOracle T scalar coins (fixed, enc, hashOf other scale)) =
    (shiftCoins T coins, _, enc, hashOf (shiftOther T coins.bridgeKey other) (scaleShift T scale))
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
  exact shiftHash_hashOf T coins.bridgeKey other scale

theorem restLaw_uniform : restLaw restUniform = PMF.uniformOfFintype (RestTape TapeRest) := by
  rw [restLaw, restUniform, ← uniformOfFintype_productPMF]

/-- **The swapped tape is invariant under every join-keeping tape shift.** -/
theorem swapped_shift_invariant (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar) :
    swappedChallengeTape.map (shiftTape T scalar) = swappedChallengeTape := by
  have law : (swapLaw (restLaw restUniform) fun rest => limbPoint (garblerLabels rest)).map
      (splitShift T scalar) =
        swapLaw (restLaw restUniform) fun rest => limbPoint (garblerLabels rest) := by
    unfold swapLaw
    rw [PMF.map_bind]
    have each : ∀ rest : RestTape TapeRest,
        (((swapKernel (limbPoint (garblerLabels rest))).map (Prod.mk rest)).map
          (splitShift T scalar)) =
          (swapKernel (limbPoint (garblerLabels (restShift T scalar rest)))).map
            (Prod.mk (restShift T scalar rest)) := by
      intro rest
      rw [PMF.map_comp]
      have factor : (splitShift T scalar ∘ Prod.mk rest) =
          Prod.mk (restShift T scalar rest) ∘ fun scale : ScaleTable =>
            scale ∘ relabelScaleEquiv T := rfl
      rw [factor, ← PMF.map_comp, swapKernel_map_comp _ _ (relabelScaleEquiv T)]
      intro slot
      apply Subtype.ext
      show relabel (siteShift T)
          (labelInput slot (garblerLabels (restShift T scalar rest) slot.1)) =
        labelInput slot (garblerLabels rest slot.1)
      rw [garblerLabels_shift T valid scalar rest, relabel_labelInput, xor_cancel_right]
    simp only [each]
    have restInvariant :
        (restLaw restUniform).map (restShiftEquiv T scalar) = restLaw restUniform := by
      rw [restLaw_uniform]
      exact uniformOfFintype_map_equiv _
    conv_rhs => rw [← restInvariant]
    rw [PMF.bind_map]
    rfl
  unfold swappedChallengeTape swappedTape
  rw [PMF.map_comp, PMF.map_comp, PMF.map_comp]
  have factor : ((shiftTape T scalar ∘ reassembleEquiv) ∘ assemble) =
      (reassembleEquiv ∘ assemble) ∘ splitShift T scalar := by
    funext tape
    exact shiftTape_split T scalar tape
  rw [factor, ← PMF.map_comp, law]

/-! ### The garbler's labels on a shifted tape -/

/-- The rest of a tape, in `MaskSwap`'s split: the coins, the fixed-key and EncPRF oracles, the hash
off the scale range. -/
def restOf (tape : Coins × Oracle) : RestTape TapeRest :=
  ((tape.1, tape.2.1, tape.2.2.1), otherTableOf tape.2.2.2)

/-- The garbler's labels are those of the rest of the tape. -/
theorem garblerLabelOf_eq (tape : Coins × Oracle) : garblerLabelOf tape = garblerLabels (restOf
    tape) := by
  have same := garblerLabel_hashOf (tape.1, tape.2.1, tape.2.2.1) (otherTableOf tape.2.2.2)
    (scaleTableOf tape.2.2.2)
  rw [hashOf_tables] at same
  exact same

/-- The rest of a shifted tape is the shifted rest. -/
theorem restOf_shiftTape (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    restOf (shiftTape T scalar tape) = restShift T scalar (restOf tape) := by
  refine Prod.ext rfl ?_
  show otherTableOf (shiftHash T tape.1.bridgeKey tape.2.2.2) =
    shiftOther T tape.1.bridgeKey (otherTableOf tape.2.2.2)
  conv_lhs => rw [← hashOf_tables tape.2.2.2]
  rw [shiftHash_hashOf, otherTableOf_hashOf]

/-- **On a shifted tape every garbler label moves by its site's level shift.** -/
theorem garblerLabelOf_shift (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) :
    garblerLabelOf (shiftTape T scalar tape) = fun site => garblerLabelOf tape site ^^^ siteShift T
        site := by
  rw [garblerLabelOf_eq, restOf_shiftTape, garblerLabels_shift T valid, garblerLabelOf_eq]

end Main

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
