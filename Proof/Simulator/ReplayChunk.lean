/-
**The replay, one chunk** (`Replay.chunkBody` against the evaluator's `evalChunkM`).

* `det_chunkPrefix`: the chunk value `α = (coord >> off_c) mod 2^w` to `tmpAlpha`, and level `1` of
  the fold (the bit-`0` label twice);
* `det_designatedPrefix`: in the designated chunk (lane `pointX`, chunk `0`), `j* = α ⊕ 1` to
  `tmpJStar`, `E* = E_{j*}` to `designatedLabel`, `κ = ι(j*) − ι(α)` to `tmpKappa`;
* `agree_chunkCore`: the fold (`agree_fold`), the designated extras, the `2^w` switches
  (`agree_switches`) and the published-join terms (`det_joinTerms`), against the body of
  `evalChunkM`, intercepted; `agree_chunkBody`: the same from a lane's cells (`LaneCells`).
-/

import Proof.Simulator.ReplayFold

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### The cells a chunk writes -/

/-- An address a plain chunk of a lane leaves alone: outside the lane's accumulators, the
digit-extraction region, the level and step-material cells, `tmpAlpha` and `tmpActive`. -/
def ChunkFrame (spec : Replay.LaneSpec) (address : Word) : Prop :=
  OffAcc spec address ∧ OffVector address ∧ FoldFrame address ∧ address ≠ word tmpAlpha

/-- An address the designated chunk leaves alone: also outside `E*`, `j*` and `κ`. -/
def DesFrame (address : Word) : Prop :=
  ChunkFrame Replay.pointXSpec address ∧ address ≠ word designatedLabel ∧
    address ≠ word tmpJStar ∧ address ≠ word tmpKappa

/-- The RAM a lane reads: its coordinate, its `254` labels, its `202` fold joins, and its scale
joins of every chunk. -/
structure LaneCells (spec : Replay.LaneSpec) (coord : Nat)
    (labels : Fin coordinateBitCount → Block) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount spec.lane) → BaseField) (memory : Memory) : Prop where
  coordCell : memory.ram (word spec.coordinate) = word coord
  labelCells : ∀ i : Fin coordinateBitCount,
    memory.ram (word (spec.labels + i.val)) = blockWord (labels i)
  hotCells : ∀ s : Fin foldStepCount,
    memory.ram (word (hotBase + foldStepCount * spec.hotRow + s.val)) = blockWord (joins.get s)
  scaleCells : ∀ (c : Fin chunkCount) (e : Fin (laneCount spec.lane)),
    memory.ram (word (scaleCellBase + elementCount * c.val + spec.slot + e.val)) =
      fieldWord (scale c e)

omit [FieldCertificate] in
theorem chunkFin_val (chunk : Fin chunkCount) : Replay.chunkFin chunk.val = chunk :=
  Fin.ext (Nat.mod_eq_of_lt chunk.isLt)

/-! ### The chunk prefix -/

omit [FieldCertificate] in
theorem chunkValue_word (coord offset width : Nat) (coordSmall : coord < 2 ^ 256)
    (offsetSmall : offset < 2 ^ 256) (widthSmall : width ≤ 5) :
    Arithmetic.and.eval (Arithmetic.shiftRight.eval (word coord) (word offset))
        (word (2 ^ width - 1)) = word (coord >>> offset % 2 ^ width) := by
  have powSmall : 2 ^ width ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) widthSmall
  apply BitVec.eq_of_toNat_eq
  simp only [Arithmetic.eval, BitVec.toNat_and, BitVec.toNat_ushiftRight, word_small coordSmall,
    word_small offsetSmall, word_small (show 2 ^ width - 1 < 2 ^ 256 by omega)]
  rw [Nat.and_two_pow_sub_one_eq_mod,
    word_small (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (by omega))]

omit [FieldCertificate] in
theorem plain_chunkPrefix (spec : Replay.LaneSpec) (chunk : Nat) :
    BigInt.IsPlain (Replay.chunkPrefix spec chunk) := by
  unfold Replay.chunkPrefix loadAt storeAt cst ar
  plain_split

omit [FieldCertificate] in
/-- **The chunk prefix.** -/
theorem det_chunkPrefix (spec : Replay.LaneSpec) (chunk : Fin chunkCount) (memory : Memory)
    (coord : Nat) (coordSmall : coord < 2 ^ 256)
    (coordCell : memory.ram (word spec.coordinate) = word coord)
    (labelAway : word (Replay.bitLabel spec chunk.val 0) ≠ word tmpAlpha) :
    ∃ after, BigInt.det (Replay.chunkPrefix spec chunk.val) memory = some after ∧
      after.ram = Function.update (Function.update (Function.update memory.ram (word tmpAlpha)
          (word (coord >>> chunkOffset chunk % 2 ^ chunkWidthNat chunk.val))) (word (hotLabel 0))
          (memory.ram (word (Replay.bitLabel spec chunk.val 0)))) (word (hotLabel 1))
          (memory.ram (word (Replay.bitLabel spec chunk.val 0))) ∧
      after.bits = memory.bits := by
  have offsetSmall : chunkOffset chunk < 2 ^ 256 := by
    have := chunkOffset_add_width_le chunk
    unfold coordinateBits at this
    omega
  refine ⟨_, rfl, ?_, by reg_eval⟩
  reg_eval
  rw [coordCell, chunkFin_val, chunkValue_word coord _ _ coordSmall offsetSmall
      (chunkWidthNat_le chunk.val), Function.update_of_ne labelAway]

/-! ### The designated prefix -/

/-- `ι(α ⊕ 1) − ι(α) = 1 − 2 · (α mod 2)` for a two-bit switch. -/
theorem kappa_value (alpha : Nat) (small : alpha < 4) :
    ((alpha ^^^ 1 : Nat) : BaseField) - (alpha : BaseField) =
      1 - (((alpha % 2 : Nat) : BaseField) + ((alpha % 2 : Nat) : BaseField)) := by
  interval_cases alpha <;>
    simp only [show (0 : Nat) ^^^ 1 = 1 from rfl, show (1 : Nat) ^^^ 1 = 0 from rfl,
      show (2 : Nat) ^^^ 1 = 3 from rfl, show (3 : Nat) ^^^ 1 = 2 from rfl] <;> norm_num

omit [FieldCertificate] in
theorem word_xor_one (alpha : Nat) (small : alpha < 4) :
    Arithmetic.xor.eval (word alpha) (word 1) = word (alpha ^^^ 1) := by
  apply BitVec.eq_of_toNat_eq
  have xorSmall : alpha ^^^ 1 < 2 ^ 256 := lt_trans (Nat.xor_lt_two_pow
    (show alpha < 2 ^ 2 by omega) (by norm_num)) (by norm_num)
  simp only [Arithmetic.eval, BitVec.toNat_xor, word_small (show alpha < 2 ^ 256 by omega),
    word_small (show 1 < 2 ^ 256 by norm_num), word_small xorSmall]

omit [FieldCertificate] in
theorem word_and_one (alpha : Nat) (small : alpha < 4) :
    Arithmetic.and.eval (word alpha) (word 1) = word (alpha % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Arithmetic.eval, BitVec.toNat_and, word_small (show alpha < 2 ^ 256 by omega),
    word_small (show 1 < 2 ^ 256 by norm_num)]
  rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, pow_one,
    word_small (show alpha % 2 < 2 ^ 256 by omega)]

omit [FieldCertificate] in
theorem plain_designatedPrefix : BigInt.IsPlain Replay.designatedPrefix := by
  unfold Replay.designatedPrefix loadAt storeAt cst ar
  plain_split

/-- **The designated prefix.** -/
theorem det_designatedPrefix (memory : Memory) (alpha : Nat) (alphaSmall : alpha < 4)
    (star : Block) (alphaCell : memory.ram (word tmpAlpha) = word alpha)
    (starCell : memory.ram (word (hotLabel (alpha ^^^ 1))) = blockWord star) :
    ∃ after, BigInt.det Replay.designatedPrefix memory = some after ∧
      after.ram = Function.update (Function.update (Function.update memory.ram (word tmpJStar)
        (word (alpha ^^^ 1))) (word designatedLabel) (blockWord star)) (word tmpKappa)
        (fieldWord (((alpha ^^^ 1 : Nat) : BaseField) - (alpha : BaseField))) ∧
      after.bits = memory.bits := by
  have xorSmall : alpha ^^^ 1 < 4 := Nat.xor_lt_two_pow (show alpha < 2 ^ 2 by omega) (by norm_num)
  have jstarAlpha : word tmpAlpha ≠ word tmpJStar :=
    tmp_ne (show 0 < 16 by omega) (show 6 < 16 by omega) (by omega)
  have labelAlpha : word tmpAlpha ≠ word designatedLabel :=
    (hot_ne_tmp 48 0 (by omega) (by omega)).symm
  have starJstar : word (hotLabel (alpha ^^^ 1)) ≠ word tmpJStar :=
    hot_ne_tmp (alpha ^^^ 1) 6 (by omega) (by omega)
  refine ⟨_, rfl, ?_, by reg_eval⟩
  reg_eval
  rw [alphaCell, word_xor_one alpha alphaSmall, BigInt.eval_add_word, Nat.add_comm,
    show hotLabelBase + (alpha ^^^ 1) = hotLabel (alpha ^^^ 1) from rfl,
    Function.update_of_ne starJstar, starCell, Function.update_of_ne labelAlpha,
    Function.update_of_ne jstarAlpha, alphaCell, word_and_one alpha alphaSmall, eval_fieldAdd,
    word_small (show alpha % 2 < 2 ^ 256 by omega), eval_fieldSub,
    word_small (show 1 < 2 ^ 256 by norm_num), fieldWord_cast, Nat.cast_one,
    kappa_value alpha alphaSmall]

/-! ### One chunk -/

/-- What a chunk leaves: every accumulator cell advanced by the chunk's value; in the designated
chunk also `E*`, `j*`, `κ` and the complete record. -/
def ChunkPost (bits : BitInput) (spec : Replay.LaneSpec) (designated : Bool)
    (acc0 : Nat → BaseField) (start : Memory) (record : DesignatedRecord)
    (result : (Fin (laneCount spec.lane) → BaseField) × DesignatedRecord) (after : Memory) : Prop :=
  (∀ e : Fin (laneCount spec.lane),
      after.ram (accCell spec e.val) = fieldWord (acc0 e.val + result.1 e)) ∧
    (∀ address, ChunkFrame spec address →
      (designated = true → address ≠ word designatedLabel ∧ address ≠ word tmpJStar ∧
        address ≠ word tmpKappa) → after.ram address = start.ram address) ∧
    after.bits = start.bits ∧
    (designated = false → result.2 = record) ∧
    (designated = true → ∃ star, result.2 = (fun _ => some star) ∧
      after.ram (word designatedLabel) = blockWord star ∧
      after.ram (word tmpJStar) = word (designatedSwitch bits).val ∧
      after.ram (word tmpKappa) = fieldWord (kappa bits))

/-- Every address below the accumulators is outside every work cell of the replay. -/
theorem lowFrame {spec : Replay.LaneSpec} (ok : SpecOK spec) {value : Nat}
    (small : value < 2 ^ 46) :
    ChunkFrame spec (word value) ∧ word value ≠ word designatedLabel ∧
      word value ≠ word tmpJStar ∧ word value ≠ word tmpKappa := by
  have fits := ok.fits
  refine ⟨⟨fun e bound => word_ne (by omega) (by unfold accBase; omega)
      (by unfold accBase; omega),
    fun index bound => word_ne (by omega) (by unfold vectorLimbBase; omega)
      (by unfold vectorLimbBase; omega),
    ⟨word_ne (by omega) (by unfold tmpActive tmpBase; omega) (by unfold tmpActive tmpBase; omega),
      fun index bound => word_ne (by omega) (by unfold hotLabelBase; omega)
        (by unfold hotLabelBase; omega)⟩,
    word_ne (by omega) (by unfold tmpAlpha tmpBase; omega) (by unfold tmpAlpha tmpBase; omega)⟩,
    word_ne (by omega) (by unfold designatedLabel hotLabelBase; omega)
      (by unfold designatedLabel hotLabelBase; omega),
    word_ne (by omega) (by unfold tmpJStar tmpBase; omega) (by unfold tmpJStar tmpBase; omega),
    word_ne (by omega) (by unfold tmpKappa tmpBase; omega) (by unfold tmpKappa tmpBase; omega)⟩

theorem hotLabel_offAcc {spec : Replay.LaneSpec} (ok : SpecOK spec) (index : Nat)
    (small : index < 49) :
    OffAcc spec (word (hotLabelBase + index)) ∧ OffVector (word (hotLabelBase + index)) :=
  ⟨fun e bound => word_ne (by unfold hotLabelBase; omega)
      (by have := ok.fits; unfold accBase; omega)
      (by have := ok.fits; unfold hotLabelBase accBase; omega),
    fun e bound => word_ne (by unfold hotLabelBase; omega) (by unfold vectorLimbBase; omega)
      (by unfold hotLabelBase vectorLimbBase; omega)⟩

theorem tmp_offAcc {spec : Replay.LaneSpec} (ok : SpecOK spec) (index : Nat)
    (small : index < 16) :
    OffAcc spec (word (tmpBase + index)) ∧ OffVector (word (tmpBase + index)) :=
  ⟨fun e bound => word_ne (by unfold tmpBase; omega)
      (by have := ok.fits; unfold accBase; omega)
      (by have := ok.fits; unfold tmpBase accBase; omega),
    fun e bound => word_ne (by unfold tmpBase; omega) (by unfold vectorLimbBase; omega)
      (by unfold tmpBase vectorLimbBase; omega)⟩

/-- **One chunk**, core form: the machine's chunk body against the body of `evalChunkM`, for a
width `w`, a chunk value `α`, the chunk's labels and joins, and its scale joins. -/
theorem agree_chunkCore (bits : BitInput) (spec : Replay.LaneSpec) (ok : SpecOK spec)
    (designated : Bool) (chunk : Fin chunkCount) (width : Nat)
    (widthIs : width = chunkWidthNat chunk.val) (alpha : Fin (2 ^ width))
    (bitLabel join : Nat → Block) (scaleJ : Fin (laneCount spec.lane) → BaseField)
    (memory : Memory) (record : DesignatedRecord) (acc0 : Nat → BaseField) (coord : Nat)
    (coordSmall : coord < 2 ^ 256)
    (alphaIs : alpha.val = coord >>> chunkOffset chunk % 2 ^ width)
    (coordCell : memory.ram (word spec.coordinate) = word coord)
    (labelCells : ∀ step, step < width →
      memory.ram (word (Replay.bitLabel spec chunk.val step)) = blockWord (bitLabel step))
    (joinZero : join 0 = 0)
    (joinCells : ∀ step, 1 ≤ step → step < width →
      memory.ram (word (Replay.hotJoin spec chunk.val step)) = blockWord (join step))
    (scaleCells : ∀ e : Fin (laneCount spec.lane),
      memory.ram (word (scaleCellBase + elementCount * chunk.val + spec.slot + e.val)) =
        fieldWord (scaleJ e))
    (cells : ∀ e, e < laneCount spec.lane → memory.ram (accCell spec e) = fieldWord (acc0 e))
    (plainChunk : designated = false → spec.lane ≠ .pointX ∨ chunk ≠ chunkZero)
    (desChunk : designated = true → spec = Replay.pointXSpec ∧ chunk = chunkZero ∧
      (designatedSwitch bits).val = alpha.val ^^^ 1 ∧ (activeSwitch bits).val = alpha.val) :
    Agree (ChunkPost bits spec designated acc0 memory record)
      (rtree (Replay.chunkBody ordF0 spec designated chunk.val) memory)
      (interceptT bits (FreeQuery.bind (Programs.evalFoldM spec.lane chunk alpha.val bitLabel join
          width) fun hot =>
        FreeQuery.bind (Programs.evalMasksM spec.lane chunk width hot alpha) fun masks =>
          .pure (Programs.evalScaleOf width masks alpha scaleJ)) record) := by
  obtain ⟨steps, rfl⟩ : ∃ steps, width = steps + 1 :=
    ⟨width - 1, by have := chunkWidthNat_pos chunk.val; omega⟩
  have stepsSmall : steps < 5 := by
    have := chunkWidthNat_le chunk.val
    unfold chunkBits at this
    omega
  have alphaSmall : alpha.val < 32 :=
    lt_of_lt_of_le alpha.isLt (Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (show steps + 1 ≤ 5 by omega))
  have fits := ok.fits
  have labelsLow := ok.labelsLow
  have offsetBound := chunkOffset_add_width_le chunk
  have baseBound := foldBase_add_le chunk
  have hotLow := ok.hotLow
  have chunkBound := chunk.isLt
  unfold chunkCount at chunkBound
  unfold coordinateBits at offsetBound
  change foldBase chunk + (chunkWidthNat chunk.val - 1) ≤ foldStepCount at baseBound
  unfold foldStepCount at baseBound
  have labelLow : ∀ step, step < steps + 1 → Replay.bitLabel spec chunk.val step < 2 ^ 46 := by
    intro step bound
    unfold Replay.bitLabel
    rw [chunkFin_val]
    change chunkOffset chunk + chunkWidthNat chunk.val ≤ 254 at offsetBound
    omega
  have joinLow : ∀ step, 1 ≤ step → step < steps + 1 →
      Replay.hotJoin spec chunk.val step < 2 ^ 46 := by
    intro step low bound
    unfold Replay.hotJoin foldStepCount hotBase
    rw [chunkFin_val]
    omega
  have scaleLow : ∀ e, e < laneCount spec.lane →
      scaleCellBase + elementCount * chunk.val + spec.slot + e < 2 ^ 46 := by
    intro e bound
    unfold scaleCellBase fieldBase curveCellCount rowCellCount elementCount
    omega
  -- the chunk prefix
  obtain ⟨m1, run1, ram1, bits1⟩ := det_chunkPrefix spec chunk memory coord coordSmall coordCell
    ((lowFrame ok (labelLow 0 (by omega))).1.2.2.2)
  have alphaHot1 : word tmpAlpha ≠ word (hotLabel 1) := (hot_ne_tmp 1 0 (by omega) (by omega)).symm
  have alphaHot0 : word tmpAlpha ≠ word (hotLabel 0) := (hot_ne_tmp 0 0 (by omega) (by omega)).symm
  have hot01 : word (hotLabel 0) ≠ word (hotLabel 1) :=
    hot_ne (show 0 < 49 by omega) (show 1 < 49 by omega) (by omega)
  have alpha1 : m1.ram (word tmpAlpha) = word alpha.val := by
    rw [ram1, Function.update_of_ne alphaHot1, Function.update_of_ne alphaHot0, Function.update_self,
      alphaIs, ← widthIs]
  have prefixFrame : ∀ address, FoldFrame address → address ≠ word tmpAlpha →
      m1.ram address = memory.ram address := by
    intro address framed notAlpha
    have not1 : address ≠ word (hotLabel 1) := framed.2 1 (by omega)
    have not0 : address ≠ word (hotLabel 0) := framed.2 0 (by omega)
    rw [ram1, Function.update_of_ne not1, Function.update_of_ne not0, Function.update_of_ne notAlpha]
  have level1 : LevelCells (fun _ : Fin (2 ^ 1) => bitLabel 0) m1 := by
    intro e
    rw [ram1]
    have label0 := labelCells 0 (by omega)
    fin_cases e
    · show Function.update _ (word (hotLabel 1)) _ (word (hotLabel 0)) = _
      rw [Function.update_of_ne hot01, Function.update_self, label0]
    · show Function.update _ (word (hotLabel 1)) _ (word (hotLabel 1)) = _
      rw [Function.update_self, label0]
  unfold Replay.chunkBody
  simp only [Prog.seqList]
  rw [rtree_plain_seq (plain_chunkPrefix spec chunk.val) run1, rtree_seq, ← widthIs,
    Nat.add_sub_cancel]
  -- the fold is clean
  have foldClean : Clean bits (Programs.evalFoldM spec.lane chunk alpha.val bitLabel join
      (steps + 1)) := clean_evalFoldM bits spec.lane chunk alpha.val bitLabel join (steps + 1)
  rw [interceptT_bind, interceptT_clean bits record foldClean, TreeLaws.bind_assoc]
  simp only [TreeLaws.bind_pure_left]
  refine Agree.bindOpt (fun hot m2 foldPost => ?_)
    (agree_fold spec chunk alpha.val alphaSmall bitLabel join joinZero steps stepsSmall m1 alpha1
      level1 fun step low high => ⟨by
          rw [prefixFrame _ (lowFrame ok (joinLow step low (by omega))).1.2.2.1
            (lowFrame ok (joinLow step low (by omega))).1.2.2.2, joinCells step low (by omega)],
        by rw [prefixFrame _ (lowFrame ok (labelLow step (by omega))).1.2.2.1
            (lowFrame ok (labelLow step (by omega))).1.2.2.2, labelCells step (by omega)],
        (lowFrame ok (joinLow step low (by omega))).1.2.2.1,
        (lowFrame ok (labelLow step (by omega))).1.2.2.1⟩)
  obtain ⟨levels, foldFrame, foldBits⟩ := foldPost
  have alphaFold : FoldFrame (word tmpAlpha) :=
    ⟨tmp_ne (show 0 < 16 by omega) (show 1 < 16 by omega) (by omega), fun index small =>
      (hot_ne_tmp index 0 (by omega) (by omega)).symm⟩
  have alpha2 : m2.ram (word tmpAlpha) = word alpha.val := by
    rw [foldFrame _ alphaFold, alpha1]
  have low2 : ∀ value, value < 2 ^ 46 → m2.ram (word value) = memory.ram (word value) :=
    fun value small => by
      rw [foldFrame _ (lowFrame ok small).1.2.2.1, prefixFrame _ (lowFrame ok small).1.2.2.1
        (lowFrame ok small).1.2.2.2]
  have acc2 : ∀ e, e < laneCount spec.lane → m2.ram (accCell spec e) = fieldWord (acc0 e) := by
    intro e bound
    have accFold : FoldFrame (accCell spec e) :=
      ⟨word_ne (by unfold accBase; omega) (by unfold tmpActive tmpBase; omega)
          (by unfold accBase tmpActive tmpBase; omega),
        fun index small => word_ne (by unfold accBase; omega) (by unfold hotLabelBase; omega)
          (by unfold accBase hotLabelBase; omega)⟩
    rw [foldFrame _ accFold, prefixFrame _ accFold (word_ne (by unfold accBase; omega)
      (by unfold tmpAlpha tmpBase; omega) (by unfold accBase tmpAlpha tmpBase; omega)),
      cells e bound]
  -- the masks and the scale term, abstractly
  unfold Programs.evalMasksM
  simp only [TreeLaws.monad_bind, TreeLaws.monad_pure, interceptT_bind, TreeLaws.bind_assoc,
    TreeLaws.bind_pure_left, interceptT]
  -- the record along the switches
  have jstarSmall : alpha.val ^^^ 1 < 2 ^ (steps + 1) :=
    Nat.xor_lt_two_pow alpha.isLt (Nat.one_lt_two_pow (by omega))
  set jstar : Fin (2 ^ (steps + 1)) := ⟨alpha.val ^^^ 1, jstarSmall⟩ with jstarDef
  set recordAt : Nat → DesignatedRecord := fun count =>
    if designated = true ∧ alpha.val ^^^ 1 < count then fun _ => some (hot jstar) else record
    with recordAtDef
  have recordStep : ∀ switch : Fin (2 ^ (steps + 1)), recordAt (switch.val + 1) =
      switchRecord designated (alpha.val ^^^ 1) (hot switch) (recordAt switch.val) switch.val := by
    intro switch
    simp only [recordAtDef, switchRecord]
    by_cases designatedTrue : designated = true
    · by_cases hit : switch.val = alpha.val ^^^ 1
      · have lhs : designated = true ∧ alpha.val ^^^ 1 < switch.val + 1 :=
          ⟨designatedTrue, by omega⟩
        have rhs : designated = true ∧ switch.val = alpha.val ^^^ 1 := ⟨designatedTrue, hit⟩
        rw [if_pos lhs, if_pos rhs, show switch = jstar from Fin.ext hit]
      · have rhs : ¬ (designated = true ∧ switch.val = alpha.val ^^^ 1) := fun both => hit both.2
        rw [if_neg rhs]
        by_cases below : alpha.val ^^^ 1 < switch.val
        · have lhs : designated = true ∧ alpha.val ^^^ 1 < switch.val + 1 :=
            ⟨designatedTrue, by omega⟩
          have mid : designated = true ∧ alpha.val ^^^ 1 < switch.val := ⟨designatedTrue, below⟩
          rw [if_pos lhs, if_pos mid]
        · have lhs : ¬ (designated = true ∧ alpha.val ^^^ 1 < switch.val + 1) := fun both =>
            below (by have := both.2; omega)
          have mid : ¬ (designated = true ∧ alpha.val ^^^ 1 < switch.val) := fun both =>
            below both.2
          rw [if_neg lhs, if_neg mid]
    · simp [designatedTrue]
  have recordZero : recordAt 0 = record := by
    simp only [recordAtDef]
    rw [if_neg (fun both => Nat.not_lt_zero _ both.2)]
  -- the designated extras
  have labelKappa : word designatedLabel ≠ word tmpKappa := hot_ne_tmp 48 5 (by omega) (by omega)
  have jstarKappa : word tmpJStar ≠ word tmpKappa :=
    tmp_ne (show 6 < 16 by omega) (show 5 < 16 by omega) (by omega)
  have jstarLabel : word tmpJStar ≠ word designatedLabel :=
    (hot_ne_tmp 48 6 (by omega) (by omega)).symm
  have desCase : ∀ (start : Memory), start.ram (word tmpAlpha) = word alpha.val →
      LevelCells hot start → ∃ m3, rtree (Prog.seq (Replay.designatedPart designated)
        (Prog.seq (Prog.rep (2 ^ (steps + 1)) fun switch =>
          Replay.switchStep spec designated chunk.val switch)
        (Prog.seq (loadAt rF tmpAlpha) (Prog.seq (Prog.rep spec.count fun element =>
          Replay.joinTerm spec chunk.val element) (Prog.skip 0))))) start =
        rtree (Prog.seq (Prog.rep (2 ^ (steps + 1)) fun switch =>
          Replay.switchStep spec designated chunk.val switch)
        (Prog.seq (loadAt rF tmpAlpha) (Prog.seq (Prog.rep spec.count fun element =>
          Replay.joinTerm spec chunk.val element) (Prog.skip 0)))) m3 ∧
        (∀ address, (designated = true → address ≠ word designatedLabel ∧
          address ≠ word tmpJStar ∧ address ≠ word tmpKappa) → m3.ram address = start.ram address) ∧
        m3.bits = start.bits ∧
        (designated = true → m3.ram (word designatedLabel) = blockWord (hot jstar) ∧
          m3.ram (word tmpJStar) = word (alpha.val ^^^ 1) ∧
          m3.ram (word tmpKappa) = fieldWord (((alpha.val ^^^ 1 : Nat) : BaseField) -
            (alpha.val : BaseField))) := by
    intro start startAlpha startLevels
    cases designated with
    | false =>
        exact ⟨start, by rw [rtree_seq]; rfl, fun _ _ => rfl, rfl, fun absurdity => by
          cases absurdity⟩
    | true =>
        obtain ⟨-, chunkIs, -, -⟩ := desChunk rfl
        have twoWide : steps + 1 = 2 := by
          rw [widthIs, chunkIs]
          rfl
        have alpha4 : alpha.val < 4 :=
          lt_of_lt_of_eq alpha.isLt (by rw [twoWide]; rfl)
        obtain ⟨m3, run3, ram3, bits3⟩ := det_designatedPrefix start alpha.val alpha4 (hot jstar)
          startAlpha (startLevels jstar)
        refine ⟨m3, by
            show rtree (Prog.seq Replay.designatedPrefix _) start = _
            rw [rtree_plain_seq plain_designatedPrefix run3], fun address away => ?_,
          bits3, fun _ => ⟨?_, ?_, ?_⟩⟩
        · obtain ⟨notLabel, notJstar, notKappa⟩ := away rfl
          rw [ram3, Function.update_of_ne notKappa, Function.update_of_ne notLabel,
            Function.update_of_ne notJstar]
        · rw [ram3, Function.update_of_ne labelKappa, Function.update_self]
        · rw [ram3, Function.update_of_ne jstarKappa, Function.update_of_ne jstarLabel,
            Function.update_self]
        · rw [ram3, Function.update_self]
  obtain ⟨m3, desRun, desFrame, desBits, desCells⟩ := desCase m2 alpha2 levels
  have away3 : ∀ address, OffAcc spec address → OffVector address → FoldFrame address →
      address ≠ word tmpAlpha → address ≠ word designatedLabel → address ≠ word tmpJStar →
      address ≠ word tmpKappa → m3.ram address = memory.ram address := by
    intro address offAcc offVector framed notAlpha notLabel notJstar notKappa
    rw [desFrame address fun _ => ⟨notLabel, notJstar, notKappa⟩, foldFrame address framed,
      prefixFrame address framed notAlpha]
  have alpha3 : m3.ram (word tmpAlpha) = word alpha.val := by
    rw [desFrame (word tmpAlpha) fun _ => ⟨(hot_ne_tmp 48 0 (by omega) (by omega)).symm,
      tmp_ne (show 0 < 16 by omega) (show 6 < 16 by omega) (by omega),
      tmp_ne (show 0 < 16 by omega) (show 5 < 16 by omega) (by omega)⟩, alpha2]
  have hot3 : ∀ switch : Fin (2 ^ (steps + 1)),
      m3.ram (word (hotLabel switch.val)) = blockWord (hot switch) := by
    intro switch
    have small : switch.val < 32 :=
      lt_of_lt_of_le switch.isLt (le_trans (Nat.pow_le_pow_right (by norm_num)
        (by omega : steps + 1 ≤ 5)) (by norm_num))
    rw [desFrame (word (hotLabel switch.val)) fun _ => ⟨hot_ne (by omega) (show 48 < 49 by omega)
      (by omega),
      hot_ne_tmp switch.val 6 (by omega) (by omega),
      hot_ne_tmp switch.val 5 (by omega) (by omega)⟩, levels switch]
  have acc3 : ∀ e, e < laneCount spec.lane → m3.ram (accCell spec e) = fieldWord (acc0 e) := by
    intro e bound
    rw [desFrame _ fun _ => ⟨word_ne (by unfold accBase; omega)
        (by unfold designatedLabel hotLabelBase; omega)
        (by unfold accBase designatedLabel hotLabelBase; omega),
      word_ne (by unfold accBase; omega) (by unfold tmpJStar tmpBase; omega)
        (by unfold accBase tmpJStar tmpBase; omega),
      word_ne (by unfold accBase; omega) (by unfold tmpKappa tmpBase; omega)
        (by unfold accBase tmpKappa tmpBase; omega)⟩, acc2 e bound]
  rw [desRun, rtree_seq]
  have switches := agree_switches bits spec ok designated chunk (steps + 1) (by omega) alpha hot m3
    recordAt acc0 plainChunk
    (fun designatedTrue => by
      obtain ⟨specIs, chunkIs, jstarIs, -⟩ := desChunk designatedTrue
      refine ⟨specIs, chunkIs, ?_, jstarIs⟩
      rw [widthIs, chunkIs]
      rfl)
    recordStep alpha3 hot3 (fun switch => hotLabel_offAcc ok switch.val
      (lt_of_lt_of_le switch.isLt (le_trans (Nat.pow_le_pow_right (by norm_num)
        (by omega : steps + 1 ≤ 5)) (by norm_num)))) (tmp_offAcc ok 0 (by omega)) acc3
  rw [recordZero] at switches
  refine Agree.bindOpt (fun state m4 swInv => ?_) switches
  obtain ⟨accs4, frame4, bits4, record4⟩ := swInv
  set accNow : Nat → BaseField := fun e => if bound : e < laneCount spec.lane then
    acc0 e + ∑ switch : Fin (2 ^ (steps + 1)), state.1[switch].get ⟨e, bound⟩ *
      ((switch.val : BaseField) - (alpha.val : BaseField)) else 0 with accNowDef
  have alpha4 : m4.ram (word tmpAlpha) = word alpha.val := by
    rw [frame4 (word tmpAlpha) (tmp_offAcc ok 0 (by omega)).1 (tmp_offAcc ok 0 (by omega)).2, alpha3]
  obtain ⟨m5, run5, accs5, frame5, bits5⟩ := det_joinTerms spec ok chunk.val chunkBound
    (setReg (setReg m4 rAddr (word tmpAlpha)) rF (m4.ram (word tmpAlpha)))
    (fun e => if bound : e < laneCount spec.lane then scaleJ ⟨e, bound⟩ else 0) accNow
    (alpha.val : BaseField)
    (by rw [reg_same, alpha4, word_small (by omega)])
    (fun e bound => by
      simp only [setReg_ram, dif_pos bound]
      have small := scaleLow e bound
      rw [frame4 _ (lowFrame ok small).1.1 (lowFrame ok small).1.2.1,
        away3 _ (lowFrame ok small).1.1 (lowFrame ok small).1.2.1 (lowFrame ok small).1.2.2.1
          (lowFrame ok small).1.2.2.2 (lowFrame ok small).2.1 (lowFrame ok small).2.2.1
          (lowFrame ok small).2.2.2]
      exact scaleCells ⟨e, bound⟩)
    (fun e bound => by
      simp only [setReg_ram, accNowDef, dif_pos bound]
      exact accs4 ⟨e, bound⟩)
  rw [rtree_loadAt_seq]
  unfold Replay.LaneSpec.count
  rw [rtree_plain_seq (plain_joinTerms spec chunk.val) run5, rtree_skip]
  refine .leaf ⟨fun e => ?_, fun address framed away => ?_, ?_, fun designatedFalse => ?_,
    fun designatedTrue => ?_⟩
  · dsimp only
    rw [accs5 e.val e.isLt, evalScaleOf_eq]
    simp only [accNowDef, dif_pos e.isLt]
    rw [add_assoc]
    rfl
  · obtain ⟨offAcc, offVector, framedFold, notAlpha⟩ := framed
    rw [frame5 address offAcc]
    simp only [setReg_ram]
    rw [frame4 address offAcc offVector]
    cases designated with
    | false =>
        rw [desFrame address (fun absurdity => by cases absurdity), foldFrame address framedFold,
          prefixFrame address framedFold notAlpha]
    | true =>
        obtain ⟨notLabel, notJstar, notKappa⟩ := away rfl
        exact away3 address offAcc offVector framedFold notAlpha notLabel notJstar notKappa
  · rw [bits5]
    simp only [setReg_bits]
    rw [bits4, desBits, foldBits, bits1]
  · rw [record4]
    simp [recordAtDef, designatedFalse]
  · obtain ⟨labelCell, jstarCell, kappaCell⟩ := desCells designatedTrue
    obtain ⟨-, -, jstarIs, activeIs⟩ := desChunk designatedTrue
    have labelAway : OffAcc spec (word designatedLabel) ∧ OffVector (word designatedLabel) :=
      hotLabel_offAcc ok 48 (by omega)
    refine ⟨hot jstar, ?_, ?_, ?_, ?_⟩
    · rw [record4]
      simp only [recordAtDef]
      rw [if_pos ⟨designatedTrue, jstarSmall⟩]
    · rw [frame5 _ labelAway.1]
      simp only [setReg_ram]
      rw [frame4 _ labelAway.1 labelAway.2, labelCell]
    · rw [frame5 (word tmpJStar) (tmp_offAcc ok 6 (by omega)).1]
      simp only [setReg_ram]
      rw [frame4 (word tmpJStar) (tmp_offAcc ok 6 (by omega)).1 (tmp_offAcc ok 6 (by omega)).2, jstarCell,
        jstarIs]
    · rw [frame5 (word tmpKappa) (tmp_offAcc ok 5 (by omega)).1]
      simp only [setReg_ram]
      rw [frame4 (word tmpKappa) (tmp_offAcc ok 5 (by omega)).1 (tmp_offAcc ok 5 (by omega)).2, kappaCell]
      unfold kappa iota
      rw [jstarIs, activeIs]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
