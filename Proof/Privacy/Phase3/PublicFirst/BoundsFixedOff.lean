/-
**Phase 3, P1m — (B1) off the curve: the designed run, described and bounded.**

Off the curve the designed shadow runs the pads at `k₁` and system A through the fill runner with
nothing planted. With nothing planted the fill runner never flags, and the pads and system A are
never intercepted, so it is P4's refill runner (`runFillFlag_eq_runRefill`, `off_whole_le`):

* `designedOff_laneSplit`, **`designedOff_level_le`** — fold-label entropy for system A's lanes
  after the pads;
* `off_fixed`, `off_used_le`, `off_hash` — every stored fixed-key pair is a fold pair of system A at
  its level label (at most one per index), every hash key a limb input of a system-A switch at its
  one-hot label;
* `offOut_le` (`≤ 1/2^128`), `offHotAbsent_le` (`0`), `offCurveIn_le` (level 1: the source's own
  MAC label), `offLevelIn_le` (levels `≥ 2`: `≤ 1/2^128`), `offGadget_le` (`0`) — the fixed-key
  points per index; **`offHash_le`** — a hash key has mass `≤ 1/2^128`.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedOn
import Proof.Privacy.Phase3.PublicFirst.BoundsEncOff

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source interceptAnswer noRecord)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request AllQ EncAt IndexAt runRefill
  consumeCell refillAnswer queriesAlong queriesAlong_bind queriesAlong_pure uniformMaskTape
  cellInput cellOf cellOf_spec cellOf_cellInput cellInput_injective maskCell evalLaneM_allQ)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### With nothing planted, the fill runner is the refill runner -/

section Bridge

/-- **The fill runner with nothing planted is the refill runner**, on intercept-free programs. -/
theorem runFillFlag_eq_runRefill (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (computation : FreeQuery Programs.Spec α)
    (free : AllQ (fun r => interceptAnswer bits r = none) computation) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell),
      runFillFlag LazyOracle.empty draw computation oracle touched =
        (runRefill bits draw computation oracle record touched).map
          (Option.map fun o => (o.1, o.2.1)) := by
  induction computation with
  | pure value =>
    intro oracle record touched
    simp only [runFillFlag, runRefill, PMF.pure_map, Option.map_some]
  | query request next ih =>
    intro oracle record touched
    have intercept : interceptAnswer bits request = none := AllQ.head free
    simp only [runFillFlag, runRefill, intercept]
    cases consume : consumeCell touched oracle request with
    | some cell =>
      simp only [PMF.map_bind]
      refine congrArg _ (funext fun value => ?_)
      rw [if_neg (not_fullTouch_empty _ _)]
      cases LazyOracle.program request (refillAnswer request value) oracle with
      | none => simp only [PMF.pure_map, Option.map_none]
      | some updated => exact ih _ (AllQ.tail free _) updated record _
    | none =>
      simp only [PMF.map_bind]
      refine congrArg _ (funext fun answer => ?_)
      rw [if_neg (not_fullTouch_empty _ _)]
      exact ih _ (AllQ.tail free _) _ record _

end Bridge

/-! ### The designed off-curve program -/

section Program

variable [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac)

theorem queriesAlong_designedOffM (first : Block) (ans : (request : Request) → request.Answer) :
    queriesAlong ans (designedOffM table bits mac first) =
      queriesAlong ans (Programs.padsM ⟨first, 0⟩) ++ (queriesAlong ans (curveXM table bits mac) ++
        queriesAlong ans (curveYM table bits mac)) := by
  unfold designedOffM systemAM
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil]

theorem intercept_none_of_encAt {bits : BitInput} {q : Request} (inside : EncAt q) :
    interceptAnswer bits q = none := by
  cases q with
  | encForward _ _ => rfl
  | _ => exact inside.elim

theorem designedOffM_free (first : Block) :
    AllQ (fun r => interceptAnswer bits r = none) (designedOffM table bits mac first) := by
  unfold designedOffM systemAM
  refine ((padsM_allQ _).mono fun _ inside => intercept_none_of_encAt inside).bind fun _ => ?_
  exact ((evalLaneM_allQ _ _ _ _ _).mono (curve_notIntercepted bits .curveX (Or.inl rfl))).bind
    fun _ => ((evalLaneM_allQ _ _ _ _ _).mono
      (curve_notIntercepted bits .curveY (Or.inr rfl))).bind fun _ => .pure _

theorem designedOff_fresh (first : Block) : Fresh bits ∅ (designedOffM table bits mac first) := by
  have padsNone : AllQ (fun r => Kriterion.ArgoMAC.Phase3.Lazy.consumedCell bits r = none)
      (Programs.padsM ⟨first, 0⟩) :=
    (padsM_allQ _).mono fun _ inside => consumedCell_none_of_encAt inside
  unfold designedOffM systemAM
  refine Fresh.bind (S := ∅) (Fresh.of_none padsNone _)
    (padsNone.mono fun _ none => inCells_of_none none) fun _ => ?_
  refine Fresh.bind (S := laneCells .curveX)
    (lane_fresh_avoid bits _ _ _ _ _ _ fun cell inside outside => ?_)
    (evalLaneM_inCells bits _ _ _ _ _) fun _ => ?_
  · rcases outside with outside | outside
    · exact outside
    · exact outside
  refine Fresh.bind (S := laneCells .curveY)
    (lane_fresh_avoid bits _ _ _ _ _ _ fun cell inside outside => ?_)
    (evalLaneM_inCells bits _ _ _ _ _) fun _ => .pure _ _
  rcases outside with (outside | outside) | outside
  · exact outside
  · exact outside
  · exact laneCells_ne (by decide) inside outside

/-- **System A's lanes run inside the designed off-curve program as parts of it.** -/
theorem designedOff_laneSplit (first : Block) (lane : Lane)
    (curve : lane = .curveX ∨ lane = .curveY) :
    LaneSplit (designedOffM table bits mac first) lane (laneJoins table lane)
      (laneScale table lane) (laneWord bits lane)
      (fun _ => laneLabels mac (fun _ _ => (0, 0)) lane) := by
  intro ans
  have padsAway : ∀ q ∈ queriesAlong ans (Programs.padsM ⟨first, 0⟩), AwayFrom lane q :=
    fun q member => awayFrom_of_encAt (mem_queriesAlong_allQ ans (padsM_allQ _) q member)
  have path := queriesAlong_designedOffM table bits mac first ans
  rcases curve with rfl | rfl
  · refine ⟨queriesAlong ans (Programs.padsM ⟨first, 0⟩), queriesAlong ans (curveYM table bits mac),
      ?_, padsAway, fun q member => awayFrom_of_lane (by decide) _ _ _ _ ans q member,
      fun _ _ => rfl⟩
    show _ = _ ++ queriesAlong ans (curveXM table bits mac) ++ _
    rw [path, List.append_assoc]
  · refine ⟨queriesAlong ans (Programs.padsM ⟨first, 0⟩) ++
      queriesAlong ans (curveXM table bits mac), [], ?_, ?_,
      fun q member => absurd member List.not_mem_nil, fun _ _ => rfl⟩
    · show _ = _ ++ queriesAlong ans (curveYM table bits mac) ++ []
      rw [path]
      simp only [List.append_assoc, List.append_nil]
    · intro q member
      rcases List.mem_append.mp member with pads | x
      · exact padsAway q pads
      · exact awayFrom_of_lane (by decide) _ _ _ _ ans q x

/-- **A level label of system A off the curve**, along `ans`. -/
abbrev offLevel (ans : (request : Request) → request.Answer) (lane : Lane) (c : Fin chunkCount)
    (s : ℕ) : Fin (2 ^ s) → Block :=
  laneFoldLevel ans lane (laneJoins table lane) (laneWord bits lane)
    (laneLabels mac (fun _ _ => (0, 0)) lane) c s

/-- **Fold-label entropy for system A after the pads.** -/
theorem designedOff_level_le (first : Block) (tape : Tape) (lane : Lane)
    (curve : lane = .curveX ∨ lane = .curveY) (c : Fin chunkCount) (s : ℕ) (two : 2 ≤ s)
    (le : s ≤ chunkWidth c) (n : Fin (2 ^ s)) (L : Block) :
    ∑' ran, runRefill bits (fun cell => PMF.pure (tape cell)) (designedOffM table bits mac first)
        LazyOracle.empty noRecord ∅ ran *
      optWeight (fun state => ind (offLevel table bits mac (refillAns bits state) lane c s n = L))
        ran ≤ delta := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  exact runRefill_level_le bits tape _ (designedOffM_forwardOnly table bits mac first)
    (designedOff_fresh table bits mac first) lane _ _ _ _
    (designedOff_laneSplit table bits mac first lane curve) c t (by omega) (by omega) n L

end Program

/-! ### The designed off-curve run -/

section Run

variable [FieldCertificate] [GroupCertificate]

/-- The designed off-curve run of a source, a key `k₁` and a tape. (A `def`: the unifier must never
compare it with the unfolded runner.) -/
def offRun (source : Stage1Source) (input : AffineInput) (first : Block) (tape : Tape) :
    PMF (Option (Unit × LState × Record)) :=
  runRefill (restoredBits source input) (fun cell => PMF.pure (tape cell))
    (designedOffM source.publicValue (restoredBits source input) (restoredMac source input) first)
    LazyOracle.empty noRecord ∅

/-- **Off the curve, an event bounded by a potential of the run has mass at most its bound.** -/
theorem off_whole_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (Φ : Block → Tape → LState → ℝ≥0∞)
    (hashSame : ∀ first tape (state updated : LState) (input' : BaseField) (answer : Block × Block),
      LazyOracle.program (.hash input') answer state = some updated →
        Φ first tape updated = Φ first tape state)
    (step : ∀ first tape (request : Request) (state : LState), ForwardOnly request →
      ∑' answer, LazyOracle.query request state answer * Φ first tape answer.2 ≤
        Φ first tape state)
    (c : ℝ≥0∞) (initial : ∀ first tape, Φ first tape LazyOracle.empty ≤ c)
    (final : ∀ (first : Block) (tape : Tape) (o : Unit × LState × Record),
      some o ∈ (offRun source input first tape).support →
        ind (event (pointsOf o.2.1)) ≤ Φ first tape o.2.1) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind (event (outcomePoints o)) ≤ c := by
  refine le_trans (off_event_le scalar source input event (fun _ _ => c) fun first tape => ?_)
    (le_of_eq (by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, PMF.tsum_coe, PMF.tsum_coe,
      one_mul, one_mul]))
  rw [runFillFlag_eq_runRefill (restoredBits source input) _ _
    (designedOffM_free _ _ _ first) LazyOracle.empty noRecord ∅, tsum_map_mul]
  refine le_trans (tsum_mul_le_of_support _ _ (optWeight (Φ first tape)) fun o member => ?_) ?_
  · rcases o with _ | o
    · exact zero_le
    · exact final first tape o (by unfold offRun; exact member)
  · exact le_trans (runRefill_potential_prog _ _ (Φ first tape) (hashSame first tape)
      (step first tape) _ (designedOffM_forwardOnly _ _ _ first) _ _ _) (initial first tape)

/-- **A deterministic event off the curve.** -/
theorem off_const_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (Q : Prop)
    (reduce : ∀ (first : Block) (tape : Tape) (o : Unit × LState × Record),
      some o ∈ (offRun source input first tape).support → event (pointsOf o.2.1) → Q) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind (event (outcomePoints o)) ≤ ind Q :=
  off_whole_le scalar source input event (fun _ _ _ => ind Q) (fun _ _ _ _ _ _ _ => rfl)
    (fun _ _ request state _ => le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
    (ind Q) (fun _ _ => le_rfl) fun first tape o member => ind_mono (reduce first tape o member)

variable (source : Stage1Source) (input : AffineInput) (first : Block) (tape : Tape)
  (o : Unit × LState × Record) (member : some o ∈ (offRun source input first tape).support)

include member

theorem off_described :
    Described (restoredBits source input) tape
      (designedOffM source.publicValue (restoredBits source input) (restoredMac source input) first)
      LazyOracle.empty noRecord o := by
  unfold offRun at member
  exact runRefill_describe (restoredBits source input) tape _
    (designedOffM_forwardOnly _ _ _ first) ∅ (designedOff_fresh _ _ _ first) LazyOracle.empty
    noRecord ∅ (fun _ _ => ⟨fun h => h, fun _ => rfl⟩) o member

/-- A question of the designed off-curve program: a pad or a question of a system-A lane. -/
theorem off_cases (q : Request)
    (onPath : q ∈ queriesAlong (refillAns (restoredBits source input) o.2.1)
      (designedOffM source.publicValue (restoredBits source input) (restoredMac source input)
        first)) :
    EncAt q ∨ ∃ lane, (lane = .curveX ∨ lane = .curveY) ∧
      q ∈ queriesAlong (refillAns (restoredBits source input) o.2.1)
        (laneProg source.publicValue (restoredBits source input) (restoredMac source input)
          (fun _ _ => (0, 0)) lane) := by
  rw [queriesAlong_designedOffM] at onPath
  rcases List.mem_append.mp onPath with pads | rest
  · exact Or.inl (mem_queriesAlong_allQ _ (padsM_allQ _) q pads)
  · rcases List.mem_append.mp rest with x | y
    · exact Or.inr ⟨.curveX, Or.inl rfl, x⟩
    · exact Or.inr ⟨.curveY, Or.inr rfl, y⟩

/-- **Every stored fixed-key pair off the curve is a system-A fold pair at its level label.** -/
theorem off_fixed (i : FixedIndex) (x y : Fin (2 ^ 128)) (found : lk (o.2.1.fixed i) x = some y) :
    ∃ (lane : Lane), (lane = .curveX ∨ lane = .curveY) ∧ ∃ (c : Fin chunkCount) (s : ℕ),
      s < chunkWidth c ∧ ∃ e : Fin (2 ^ s),
        e ≠ activeAt (chunkValue (laneWord (restoredBits source input) lane) c).toNat s ∧
          ∃ h : Bool, i = hotIndexNat lane c s e.val h ∧
            BitVec.ofFin x = offLevel source.publicValue (restoredBits source input)
              (restoredMac source input) (refillAns (restoredBits source input) o.2.1) lane c s
              e := by
  rcases (off_described source input first tape o member).fixed i x y found with old | onPath
  · rw [show lk ((LazyOracle.empty : LState).fixed i) x = none from lk_empty x] at old
    cases old
  · rcases off_cases source input first tape o member _ onPath with enc | ⟨lane, curve, inLane⟩
    · exact enc.elim
    · obtain ⟨c, s, small, e, inactive, h, iEq, xEq⟩ :=
        (lane_fold_question _ lane _ _ _ _ _ _).mp inLane
      exact ⟨lane, curve, c, s, small, e, inactive, h, iEq, xEq⟩

/-- **At most one pair per fixed-key index off the curve.** -/
theorem off_used_le (i : FixedIndex) : (o.2.1.fixed i).used ≤ 1 := by
  classical
  by_cases some : ∃ x y, lk (o.2.1.fixed i) x = some y
  · obtain ⟨x₀, y₀, found₀⟩ := some
    refine used_le_one _ x₀ fun x y found => ?_
    obtain ⟨lane, _, c, s, small, e, _, h, iEq, xEq⟩ :=
      off_fixed source input first tape o member i x y found
    obtain ⟨lane', _, c', s', small', e', _, h', iEq', xEq'⟩ :=
      off_fixed source input first tape o member i x₀ y₀ found₀
    obtain ⟨laneEq, chunkEq, stepEq, entryEq, _⟩ := hotIndexNat_inj
      (step_lt_chunkBits small) (step_lt_chunkBits small') (entry_lt_chunkBits small e)
      (entry_lt_chunkBits small' e') (iEq.symm.trans iEq')
    subst laneEq
    subst chunkEq
    subst stepEq
    rw [← BitVec.toFin_ofFin x, xEq, show e = e' from Fin.ext entryEq, ← xEq', BitVec.toFin_ofFin]
  · exact used_le_one _ 0 fun x y found => absurd ⟨x, y, found⟩ some

/-- **Every hash key off the curve is a system-A limb input at its one-hot label.** -/
theorem off_hash (k : BaseField) (v : Fin (Fintype.card (Block × Block)))
    (found : o.2.1.hash.lookup k = some v) :
    ∃ (lane : Lane), (lane = .curveX ∨ lane = .curveY) ∧ ∃ (c : Fin chunkCount)
      (s : Fin (2 ^ chunkWidth c)) (limb : Fin (limbCount lane)),
        k = cellInput (maskCell lane c s limb) (offLevel source.publicValue
          (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) o.2.1) lane c (chunkWidth c) s) := by
  rcases (off_described source input first tape o member).hash k v found with old | onPath
  · cases old
  · rcases off_cases source input first tape o member _ onPath with enc | ⟨lane, curve, inLane⟩
    · exact enc.elim
    · obtain ⟨c, s, limb, _, same⟩ := lane_hash_mem _ lane _ _ _ _ k inLane
      exact ⟨lane, curve, c, s, limb, same⟩

end Run

/-! ### The points off the curve -/

section Bounds

variable [FieldCertificate] [GroupCertificate]

/-- **A fixed-key output off the curve**: `≤ 1/2^128`. -/
theorem offOut_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (i : FixedIndex) (y : Block) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind ((outcomePoints o).fixedOut i y) ≤ delta := by
  refine off_whole_le scalar source input (fun p => p.fixedOut i y)
    (fun _ _ state => singleF y.toFin (state.fixed i))
    (fun _ _ state updated input' answer success => by
      rw [(program_hash_pairs input' answer state updated success).1])
    (fun _ _ request state forward => fixed_lift_step i _ (singleF_step _) request forward state)
    delta (fun _ _ => le_of_eq ?_) fun first tape o member => ?_
  · show singleF y.toFin (SparsePermutation.empty _) = delta
    unfold singleF
    rw [if_pos (show (SparsePermutation.empty (2 ^ 128)).used = 0 from rfl)]
  · exact singleF_bound _ _ (off_used_le source input first tape o member i)

/-- **No fixed-key pair off the curve outside system A's fold shape.** -/
theorem offHotAbsent_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) (f : Fin chunkBits) (e : Fin (2 ^ chunkBits)) (h : Bool)
    (x : Block)
    (absent : ¬ ((lane = .curveX ∨ lane = .curveY) ∧ 1 ≤ f.val ∧ f.val < chunkWidth c ∧
      e.val < 2 ^ f.val)) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind ((outcomePoints o).fixedIn (.hot lane c f e h) x) ≤ 0 := by
  refine le_trans (off_const_le scalar source input (fun p => p.fixedIn (.hot lane c f e h) x) False
    fun first tape o member hit => absent ?_) (le_of_eq (ind_neg id))
  obtain ⟨y, found⟩ := Option.ne_none_iff_exists'.mp hit
  obtain ⟨lane', curve, c', s, small, e', inactive, h', iEq, _⟩ :=
    off_fixed source input first tape o member _ _ y found
  rw [hotIndexNat_eq _ _ _ _ _ (step_lt_chunkBits small) (entry_lt_chunkBits small e')] at iEq
  injection iEq with laneEq chunkEq stepEq entryEq _
  subst laneEq
  subst chunkEq
  have stepVal : f.val = s := congrArg Fin.val stepEq
  have entryVal : e.val = e'.val := congrArg Fin.val entryEq
  subst stepVal
  refine ⟨curve, ?_, small, by rw [entryVal]; exact e'.isLt⟩
  by_contra zero
  have zero' : f.val = 0 := by omega
  apply inactive
  apply Fin.ext
  have first : e'.val < 1 := lt_of_lt_of_le e'.isLt (by rw [zero', pow_zero])
  have second : (activeAt (chunkValue (laneWord (restoredBits source input) lane) c).toNat
      f.val).val < 1 := lt_of_lt_of_le (Fin.isLt _) (by rw [zero', pow_zero])
  omega

/-- **A system-A fold input of step `1` off the curve** is the source's own MAC label of the
chunk's first bit. -/
theorem offCurveIn_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (lane : Lane) (κ : Coord)
    (labelsEq : ∀ mac pads, laneLabels mac pads lane = Pipeline.macLabels mac κ)
    (c : Fin chunkCount) (f : Fin chunkBits) (e : Fin (2 ^ chunkBits)) (h : Bool) (x : Block)
    (one : f.val = 1) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind ((outcomePoints o).fixedIn (.hot lane c f e h) x) ≤
      ind (Pipeline.macLabels (restoredMac source input) κ (firstBit c) = x) := by
  refine off_const_le scalar source input (fun p => p.fixedIn (.hot lane c f e h) x) _
    fun first tape o member hit => ?_
  obtain ⟨y, found⟩ := Option.ne_none_iff_exists'.mp hit
  obtain ⟨lane', _, c', s, small, e', _, h', iEq, xEq⟩ :=
    off_fixed source input first tape o member _ _ y found
  rw [hotIndexNat_eq _ _ _ _ _ (step_lt_chunkBits small) (entry_lt_chunkBits small e')] at iEq
  injection iEq with laneEq chunkEq stepEq _ _
  subst laneEq
  subst chunkEq
  have stepVal : f.val = s := congrArg Fin.val stepEq
  rw [one] at stepVal
  subst stepVal
  rw [BitVec.ofFin_toFin] at xEq
  rw [xEq, offLevel, laneLevel_one, labelsEq]

/-- **A system-A fold input of step `f ≥ 2` off the curve**: `≤ 1/2^128`. -/
theorem offLevelIn_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (lane : Lane) (curve : lane = .curveX ∨ lane = .curveY) (c : Fin chunkCount) (f : Fin chunkBits)
    (e : Fin (2 ^ chunkBits)) (h : Bool) (x : Block) (two : 2 ≤ f.val)
    (small : f.val < chunkWidth c) (lt : e.val < 2 ^ f.val) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind ((outcomePoints o).fixedIn (.hot lane c f e h) x) ≤ delta := by
  refine le_trans (off_event_le scalar source input (fun p => p.fixedIn (.hot lane c f e h) x)
    (fun first tape => delta) fun first tape => ?_)
    (le_of_eq (by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, PMF.tsum_coe, PMF.tsum_coe,
      one_mul, one_mul]))
  rw [runFillFlag_eq_runRefill (restoredBits source input) _ _
    (designedOffM_free _ _ _ first) LazyOracle.empty noRecord ∅, tsum_map_mul]
  refine le_trans (tsum_mul_le_of_support _ _ (optWeight fun state => ind (offLevel
    source.publicValue (restoredBits source input) (restoredMac source input)
    (refillAns (restoredBits source input) state) lane c f.val ⟨e.val, lt⟩ = x))
    fun o member => ?_) (designedOff_level_le _ _ _ first tape lane curve c f.val two small.le _ x)
  rcases o with _ | o
  · exact zero_le
  · refine ind_mono fun hit => ?_
    obtain ⟨y, found⟩ := Option.ne_none_iff_exists'.mp hit
    obtain ⟨lane', _, c', s, small', e', _, h', iEq, xEq⟩ :=
      off_fixed source input first tape o (by unfold offRun; exact member) _ _ y found
    rw [hotIndexNat_eq _ _ _ _ _ (step_lt_chunkBits small') (entry_lt_chunkBits small' e')] at iEq
    injection iEq with laneEq chunkEq stepEq entryEq _
    subst laneEq
    subst chunkEq
    have stepVal : f.val = s := congrArg Fin.val stepEq
    have entryVal : e.val = e'.val := congrArg Fin.val entryEq
    subst stepVal
    rw [BitVec.ofFin_toFin] at xEq
    rw [xEq, show (⟨e.val, lt⟩ : Fin (2 ^ f.val)) = e' from Fin.ext entryVal]

/-- **No gadget pair off the curve.** -/
theorem offGadget_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (d : Fin digitCount) (κ : Coord) (pos : Fin coordinateBitCount) (x : Block) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind ((outcomePoints o).fixedIn (.gadget d κ pos) x) ≤ 0 := by
  refine le_trans (off_const_le scalar source input (fun p => p.fixedIn (.gadget d κ pos) x) False
    fun first tape o member hit => ?_) (le_of_eq (ind_neg id))
  obtain ⟨y, found⟩ := Option.ne_none_iff_exists'.mp hit
  obtain ⟨lane, _, c, s, small, e, _, h, iEq, _⟩ :=
    off_fixed source input first tape o member _ _ y found
  rw [hotIndexNat_eq _ _ _ _ _ (step_lt_chunkBits small) (entry_lt_chunkBits small e)] at iEq
  cases iEq

/-- **Off the curve, a hash key has mass `≤ 1/2^128`**: it is a system-A limb input at a one-hot
label (fold-label entropy), or never stored. -/
theorem offHash_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (k : BaseField) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind ((outcomePoints o).hashIn k) ≤ delta := by
  cases cellEq : cellOf k with
  | none =>
    refine le_trans (off_const_le scalar source input (fun p => p.hashIn k) False
      fun first tape o member hit => ?_) (le_trans (le_of_eq (ind_neg id)) zero_le)
    obtain ⟨v, found⟩ := Option.ne_none_iff_exists'.mp hit
    obtain ⟨lane, _, c, s, limb, keyEq⟩ := off_hash source input first tape o member k v found
    rw [keyEq, cellOf_cellInput] at cellEq
    cases cellEq
  | some cell =>
    obtain ⟨label, same⟩ := cellOf_spec cellEq
    by_cases curve : cell.1.lane = .curveX ∨ cell.1.lane = .curveY
    · refine le_trans (off_event_le scalar source input (fun p => p.hashIn k)
        (fun first tape => delta) fun first tape => ?_)
        (le_of_eq (by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, PMF.tsum_coe,
          PMF.tsum_coe, one_mul, one_mul]))
      rw [runFillFlag_eq_runRefill (restoredBits source input) _ _
        (designedOffM_free _ _ _ first) LazyOracle.empty noRecord ∅, tsum_map_mul]
      refine le_trans (tsum_mul_le_of_support _ _ (optWeight fun state => ind (offLevel
        source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) state) cell.1.lane cell.1.chunk
          (chunkWidth cell.1.chunk) cell.1.switch = label)) fun o member => ?_)
        (designedOff_level_le _ _ _ first tape _ curve _ _ (two_le_chunkWidth _) le_rfl _ _)
      rcases o with _ | o
      · exact zero_le
      · refine ind_mono fun hit => ?_
        obtain ⟨v, found⟩ := Option.ne_none_iff_exists'.mp hit
        obtain ⟨lane, _, c, s, limb, keyEq⟩ := off_hash source input first tape o
          (by unfold offRun; exact member) k v found
        have pair := cellInput_injective (a₁ := (cell, label))
          (a₂ := (maskCell lane c s limb, _)) (same.trans keyEq)
        simp only [Prod.mk.injEq] at pair
        obtain ⟨rfl, rfl⟩ := pair
        rfl
    · refine le_trans (off_const_le scalar source input (fun p => p.hashIn k) False
        fun first tape o member hit => ?_) (le_trans (le_of_eq (ind_neg id)) zero_le)
      obtain ⟨v, found⟩ := Option.ne_none_iff_exists'.mp hit
      obtain ⟨lane, laneCurve, c, s, limb, keyEq⟩ :=
        off_hash source input first tape o member k v found
      have pair := cellInput_injective (a₁ := (cell, label))
        (a₂ := (maskCell lane c s limb, _)) (same.trans keyEq)
      simp only [Prod.mk.injEq] at pair
      obtain ⟨rfl, _⟩ := pair
      exact curve laneCurve

end Bounds

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
