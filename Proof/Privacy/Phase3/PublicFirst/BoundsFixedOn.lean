/-
**Phase 3, P1m — (B1) the fixed-key part on the curve: inputs, per index.**

Every fixed-key pair of `M'`'s private state is at its index's canonical input (`final_fixed`):

* at a fold index of step `f` of chunk `c` (`hot_reduce`): the level-`f` label of its entry; there
  is no pair at `f = 0`, at `f ≥ chunkWidth c` or at an entry `≥ 2^f` (`hotAbsent_le`). At `f = 1`
  the label is the chunk's first-bit label (`laneLevel_one`: the step-`0` join is free): the
  source's own MAC label for system A (`hotCurveIn_le`: `≤ ind`, averaged over the key in
  `BoundsFixedKey`), a whitened label `pad ⊕ L` for system B (`hotPointIn_le`: `≤ 1/(2^128 − 1)`,
  `pad_le`). At `2 ≤ f` it carries fresh fold material (`hotLevelIn_le`: `≤ 1/2^128`, fold-label
  entropy, at both chunk widths);
* at a gadget index: a transformed label `pad_u ⊕ L` (`gadgetIn_le`: `≤ 1/(2^128 − 1)`).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedDesig

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM whitePadsM programRequests
  DesignatedLimbs)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Tape Request queriesAlong uniformMaskTape)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Level one: the chunk's first-bit label -/

section Level

/-- The first bit of a chunk, as a label position. -/
def firstBit (c : Fin chunkCount) : Fin coordinateBitCount :=
  ⟨(chunkBitIndex c ⟨0, chunkWidth_pos c⟩).val, (chunkBitIndex c ⟨0, chunkWidth_pos c⟩).isLt⟩

theorem fin_two_pow_zero (u v : Fin (2 ^ 0)) : u = v :=
  Fin.ext (by have := u.isLt; have := v.isLt; simp only [pow_zero] at *; omega)

/-- The free step `0` outputs the join and the bit label. -/
theorem stepOut_zero (ans : (request : Request) → request.Answer) (lane : Lane) (c : Fin chunkCount)
    (bit join : Block) (active : Fin (2 ^ 0)) (parent : Fin (2 ^ 0) → Block) (r : Fin (2 ^ 0)) :
    stepOut ans lane c 0 bit join active parent r = join ^^^ bit := by
  have empty : Finset.univ.erase active = ∅ :=
    Finset.eq_empty_of_forall_notMem fun u member =>
      Finset.ne_of_mem_erase member (fin_two_pow_zero u active)
  unfold stepOut
  rw [if_pos (fin_two_pow_zero r active), xorFoldExcept_eq_bigXor, empty, bigXor,
    Finset.fold_empty, xor_zero_block]

/-- **A level-1 fold input is the label of the chunk's first bit** (its join is free). -/
theorem laneLevel_one [FieldCertificate] (ans : (request : Request) → request.Answer) (lane : Lane)
    (joins : Vector Block foldStepCount) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (c : Fin chunkCount) (e : Fin (2 ^ 1)) :
    laneFoldLevel ans lane joins word labels c 1 e = labels (firstBit c) := by
  have j0 : joinAt (hotSlice joins c) 0 = 0 := by
    unfold joinAt
    rw [if_pos rfl]
  have l0 : labelAt (chunkLabels labels c) 0 = labels (firstBit c) := by
    unfold labelAt
    rw [dif_pos (chunkWidth_pos c)]
    rfl
  show levelAt ans lane c _ _ _ (0 + 1) e = _
  rw [levelAt_succ]
  unfold extendLevel
  split
  · rw [stepOut_zero, j0, l0]
    show (0 : Block) ^^^ ((0 : Block) ^^^ _) = _
    rw [zero_xor_block, zero_xor_block]
  · rw [stepOut_zero, j0, l0]
    exact zero_xor_block _

end Level

/-! ### Labels through the pads -/

section Labels

/-- An EncPRF answer, as a block. -/
def encAns (ans : (request : Request) → request.Answer) (j : EncPRF.PermutationIndex)
    (w : Block) : Block :=
  ans (.encForward j w)

/-- The EncPRF coordinate of a coordinate. -/
def encCoord : Coord → EncPRF.Coordinate
  | .x => .x
  | .y => .y

/-- The bits of an EncPRF coordinate. -/
def encWord (bits : BitInput) : EncPRF.Coordinate → BitVec coordinateBitCount
  | .x => bits.xBits
  | .y => bits.yBits

theorem eval_padM' (ans : (request : Request) → request.Answer) (keys : WhiteningKeys)
    (coord : EncPRF.Coordinate) (index : Fin coordinateBitCount) (bit : Bool) :
    FreeQuery.eval ans (Programs.padM keys coord index bit) =
      encAns ans (coord, index) (encodeBit bit ^^^ keys.first) ^^^ keys.second := rfl

theorem evalPads_snd (bits : BitInput) (keys : WhiteningKeys)
    (ans : (request : Request) → request.Answer) (coord : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) :
    (FreeQuery.eval ans (Programs.evalPadsM keys bits) coord index).2 =
      FreeQuery.eval ans (Programs.padM keys coord index ((encWord bits coord).getLsb index)) := by
  cases coord <;>
  · simp only [Programs.evalPadsM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
      Vector.get_ofFn, encWord]
    split
    · rename_i bitSet
      simp only [bitSet, FreeQuery.eval_bind, FreeQuery.eval_pure]
    · rename_i bitClear
      simp only [Bool.not_eq_true] at bitClear
      simp only [bitClear, FreeQuery.eval_pure]

theorem whiten_label (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (mac : InputMac) (κ : Coord) (p : Fin coordinateBitCount) :
    Pipeline.macLabels (Programs.whitenMacOf pads mac) κ p =
      (pads (encCoord κ) p).1 ^^^ Pipeline.macLabels mac κ p := by
  cases κ <;> simp only [Pipeline.macLabels, Programs.whitenMacOf, Vector.get_ofFn, encCoord] <;>
    rfl

theorem transform_label (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (mac : InputMac) (κ : Coord) (p : Fin coordinateBitCount) :
    Pipeline.macLabels (Programs.transformMacOf pads mac) κ p =
      (pads (encCoord κ) p).2 ^^^ Pipeline.macLabels mac κ p := by
  cases κ <;> simp only [Pipeline.macLabels, Programs.transformMacOf, Vector.get_ofFn, encCoord] <;>
    rfl

theorem xor_solve (a k w x : Block) (same : (a ^^^ k) ^^^ w = x) : a = x ^^^ w ^^^ k := by
  rw [← same, BitVec.xor_assoc (a ^^^ k) w w, BitVec.xor_self, BitVec.xor_zero, BitVec.xor_assoc,
    BitVec.xor_self, BitVec.xor_zero]

end Labels

/-! ### The final pairs, reduced -/

section Reduce

variable [FieldCertificate] [GroupCertificate] (source : Stage1Source) (input : AffineInput)
  (tape : Tape)
  (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
    LState × Record)
  (member : some ran ∈ (openingRun source input tape).support)
  (answers : DesignatedLimbs) (result : Unit × LState)
  (resultMember : result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
    (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
      ran.2.2 answers) ran.2.1)).support)

include member resultMember

/-- **A pair at a fold index is at the level label of its entry.** -/
theorem hot_reduce (lane : Lane) (c : Fin chunkCount) (f : Fin chunkBits) (e : Fin (2 ^ chunkBits))
    (h : Bool) (x : Block)
    (hit : ((pointsOf result.2).union (requestPoints (programRequests (restoredBits source input)
      ran.2.2 answers))).fixedIn (.hot lane c f e h) x) :
    1 ≤ f.val ∧ f.val < chunkWidth c ∧ ∃ small : e.val < 2 ^ f.val,
      x = openLevel source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1) lane c f.val ⟨e.val, small⟩ := by
  rcases hit with inside | never
  · obtain ⟨y, found⟩ := Option.ne_none_iff_exists'.mp inside
    rcases final_fixed source input tape ran member answers result resultMember _ _ y found with
      ⟨lane', c', s, small, e', inactive, h', iEq, xEq⟩ | ⟨d, κ, pos, same⟩
    · rw [hotIndexNat_eq _ _ _ _ _ (step_lt_chunkBits small) (entry_lt_chunkBits small e')] at iEq
      injection iEq with laneEq chunkEq stepEq entryEq _
      subst laneEq
      subst chunkEq
      have stepVal : f.val = s := congrArg Fin.val stepEq
      have entryVal : e.val = e'.val := congrArg Fin.val entryEq
      subst stepVal
      refine ⟨?_, small, by rw [entryVal]; exact e'.isLt, ?_⟩
      · by_contra zero
        have zero' : f.val = 0 := by omega
        apply inactive
        apply Fin.ext
        have first : e'.val < 1 := lt_of_lt_of_le e'.isLt (by rw [zero', pow_zero])
        have second : (activeAt (chunkValue (laneWord (restoredBits source input) lane) c).toNat
            f.val).val < 1 := lt_of_lt_of_le (Fin.isLt _) (by rw [zero', pow_zero])
        omega
      · calc x = BitVec.ofFin x.toFin := (BitVec.ofFin_toFin x).symm
          _ = _ := xEq
          _ = _ := congrArg _ (Fin.ext entryVal.symm)
    · injection same with iEq
      cases iEq
  · exact never.elim

/-- **A pair at a gadget index is at the transformed label.** -/
theorem gadget_reduce (d : Fin digitCount) (κ : Coord) (pos : Fin coordinateBitCount) (x : Block)
    (hit : ((pointsOf result.2).union (requestPoints (programRequests (restoredBits source input)
      ran.2.2 answers))).fixedIn (.gadget d κ pos) x) :
    encAns (answerOf result.2) (encCoord κ, pos)
        (encodeBit ((encWord (restoredBits source input) (encCoord κ)).getLsb pos) ^^^
          (kOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1)).1) =
      x ^^^ Pipeline.macLabels (restoredMac source input) κ pos ^^^
        (kOf source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1)).2 := by
  rcases hit with inside | never
  · obtain ⟨y, found⟩ := Option.ne_none_iff_exists'.mp inside
    rcases final_fixed source input tape ran member answers result resultMember _ _ y found with
      ⟨lane', c', s, small, e', _, h', iEq, _⟩ | ⟨d', κ', pos', same⟩
    · rw [hotIndexNat_eq _ _ _ _ _ (step_lt_chunkBits small) (entry_lt_chunkBits small e')] at iEq
      cases iEq
    · injection same with iEq xEq
      injection iEq with _ κEq posEq
      subst posEq
      have κSame : κ = Pipeline.gadgetCoord κ' := κEq
      subst κSame
      rw [BitVec.ofFin_toFin] at xEq
      have label : Pipeline.macLabels (Programs.transformMacOf (ePadsOf source.publicValue
          (restoredBits source input) (restoredMac source input) (answerOf result.2))
            (restoredMac source input)) (Pipeline.gadgetCoord κ') pos = x := xEq.symm
      rw [transform_label, evalPads_snd, eval_padM',
        kOf_final source input tape ran member answers result resultMember] at label
      exact xor_solve _ _ _ _ label
  · exact never.elim

/-- The whitening pads' EncPRF answers are the final state's. -/
theorem whitePad_final (j : EncPRF.PermutationIndex) :
    encAns (refillAns (restoredBits source input) ran.2.1) j (encodeBit false ^^^
      (kOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1)).1) =
      encAns (answerOf result.2) j (encodeBit false ^^^
        (kOf source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1)).1) := by
  have onPath : .encForward j (encodeBit false ^^^ (kOf source.publicValue
      (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1)).1) ∈
      queriesAlong (refillAns (restoredBits source input) ran.2.1)
        (openingQueriesM source.publicValue (restoredBits source input)
          (restoredMac source input)) := by
    rw [queriesAlong_opening]
    refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ ?_)))
    exact mem_queriesAlong_of_transcript _ _ _ (whitePad_mem_transcript _ _ j)
  exact (opening_agree source input tape ran member result.2
    (final_grows source input tape ran member answers result resultMember) _ onPath rfl).symm

/-- **A system-B level-1 fold input, reduced to its whitening pad.** -/
theorem hotPoint_reduce (lane : Lane) (κ : Coord)
    (labelsEq : ∀ mac pads, laneLabels mac pads lane =
      Pipeline.macLabels (Programs.whitenMacOf pads mac) κ)
    (c : Fin chunkCount) (e : Fin (2 ^ 1)) (x : Block)
    (same : x = openLevel source.publicValue (restoredBits source input) (restoredMac source input)
      (refillAns (restoredBits source input) ran.2.1) lane c 1 e) :
    encAns (answerOf result.2) (encCoord κ, firstBit c)
        (encodeBit false ^^^ (kOf source.publicValue (restoredBits source input)
          (restoredMac source input) (refillAns (restoredBits source input) ran.2.1)).1) =
      x ^^^ Pipeline.macLabels (restoredMac source input) κ (firstBit c) ^^^
        (kOf source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1)).2 := by
  rw [openLevel, laneLevel_one, labelsEq, whiten_label, whitePads_fst, eval_padM',
    whitePad_final source input tape ran member answers result resultMember] at same
  exact xor_solve _ _ _ _ same.symm

end Reduce

/-! ### The input bounds -/

section Bounds

variable [FieldCertificate] [GroupCertificate]

/-- **A deterministic event**: if every run's event forces `Q`, its mass is `≤ ind Q`. -/
theorem onCurve_const_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (Q : Prop)
    (reduce : ∀ (tape : Tape)
      (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
        LState × Record), some ran ∈ (openingRun source input tape).support →
      ∀ (answers : DesignatedLimbs) (result : Unit × LState),
        result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
            ran.2.2 answers) ran.2.1)).support →
        event ((pointsOf result.2).union (requestPoints (programRequests
          (restoredBits source input) ran.2.2 answers))) → Q) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind (event (outcomePoints o)) ≤ ind Q :=
  onCurve_whole_le scalar off source input target event (fun _ => ind Q)
    (fun _ _ _ _ _ => rfl)
    (fun request state _ => le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
    fun tape ran member answers result resultMember =>
      ind_mono (reduce tape ran member answers result resultMember)

/-- **No pair at a fold index off the fold's shape.** -/
theorem hotAbsent_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (lane : Lane) (c : Fin chunkCount) (f : Fin chunkBits)
    (e : Fin (2 ^ chunkBits)) (h : Bool) (x : Block)
    (absent : ¬ (1 ≤ f.val ∧ f.val < chunkWidth c ∧ e.val < 2 ^ f.val)) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedIn (.hot lane c f e h) x) ≤ 0 := by
  refine le_trans (onCurve_const_le scalar off source input target
    (fun p => p.fixedIn (.hot lane c f e h) x) False
    fun tape ran member answers result resultMember hit => absent ?_) (le_of_eq (ind_neg id))
  obtain ⟨one, small, lt, _⟩ := hot_reduce source input tape ran member answers result
    resultMember lane c f e h x hit
  exact ⟨one, small, lt⟩

/-- **A fold input of step `f ≥ 2`**: `≤ 1/2^128` (fold-label entropy). -/
theorem hotLevelIn_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (lane : Lane) (c : Fin chunkCount) (f : Fin chunkBits)
    (e : Fin (2 ^ chunkBits)) (h : Bool) (x : Block) (two : 2 ≤ f.val)
    (small : f.val < chunkWidth c) (lt : e.val < 2 ^ f.val) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedIn (.hot lane c f e h) x) ≤ delta := by
  refine le_trans (onCurve_event_le scalar off source input target
    (fun p => p.fixedIn (.hot lane c f e h) x)
    (fun state => ind (openLevel source.publicValue (restoredBits source input)
      (restoredMac source input) (refillAns (restoredBits source input) state) lane c f.val
        ⟨e.val, lt⟩ = x))
    fun tape ran member answers => shadow_ind_le _ _ _ fun result resultMember hit => ?_) ?_
  · obtain ⟨_, _, _, same⟩ := hot_reduce source input tape ran member answers result resultMember
      lane c f e h x hit
    exact same.symm
  · exact tsum_le_of_support _ _ delta fun tape _ =>
      opening_level_le' source input tape lane c f.val two small.le _ x

/-- **A system-A fold input of step `1`** is the source's own MAC label of the chunk's first bit. -/
theorem hotCurveIn_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (lane : Lane) (κ : Coord)
    (labelsEq : ∀ mac pads, laneLabels mac pads lane = Pipeline.macLabels mac κ)
    (c : Fin chunkCount) (f : Fin chunkBits) (e : Fin (2 ^ chunkBits)) (h : Bool) (x : Block)
    (one : f.val = 1) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedIn (.hot lane c f e h) x) ≤
      ind (Pipeline.macLabels (restoredMac source input) κ (firstBit c) = x) := by
  refine onCurve_const_le scalar off source input target (fun p => p.fixedIn (.hot lane c f e h) x)
    _ fun tape ran member answers result resultMember hit => ?_
  obtain ⟨_, _, lt, same⟩ := hot_reduce source input tape ran member answers result resultMember
    lane c f e h x hit
  revert lt same
  rw [one]
  intro lt same
  rw [same, openLevel, laneLevel_one, labelsEq]

/-- **A system-B fold input of step `1`**: `≤ 1/(2^128 − 1)` (its whitening pad). -/
theorem hotPointIn_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (lane : Lane) (κ : Coord)
    (labelsEq : ∀ mac pads, laneLabels mac pads lane =
      Pipeline.macLabels (Programs.whitenMacOf pads mac) κ)
    (c : Fin chunkCount) (f : Fin chunkBits) (e : Fin (2 ^ chunkBits)) (h : Bool) (x : Block)
    (one : f.val = 1) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedIn (.hot lane c f e h) x) ≤ epsOne :=
  pad_le scalar off source input target (fun p => p.fixedIn (.hot lane c f e h) x)
    (encCoord κ, firstBit c) false
    (fun k => x ^^^ Pipeline.macLabels (restoredMac source input) κ (firstBit c) ^^^ k.2)
    fun tape ran member answers result resultMember hit => by
      obtain ⟨_, _, lt, same⟩ := hot_reduce source input tape ran member answers result
        resultMember lane c f e h x hit
      revert lt same
      rw [one]
      intro lt same
      exact hotPoint_reduce source input tape ran member answers result resultMember lane κ
        labelsEq c _ x same

/-- **A gadget input**: `≤ 1/(2^128 − 1)` (its evaluation pad). -/
theorem gadgetIn_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (d : Fin digitCount) (κ : Coord)
    (pos : Fin coordinateBitCount) (x : Block) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedIn (.gadget d κ pos) x) ≤ epsOne :=
  pad_le scalar off source input target (fun p => p.fixedIn (.gadget d κ pos) x) (encCoord κ, pos)
    ((encWord (restoredBits source input) (encCoord κ)).getLsb pos)
    (fun k => x ^^^ Pipeline.macLabels (restoredMac source input) κ pos ^^^ k.2)
    fun tape ran member answers result resultMember hit =>
      gadget_reduce source input tape ran member answers result resultMember d κ pos x hit

end Bounds

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
