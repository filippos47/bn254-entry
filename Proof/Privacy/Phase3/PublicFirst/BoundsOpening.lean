/-
**Phase 3, P1m — (B1) tools: `HW`'s opening and `M'`'s on-curve shadow, along an answer function.**

* `mem_opening` — the questions of `openingQueriesM` along `ans`: system A's two lanes (at the
  input's MAC labels), the bridge hash at `bridgeInput (tOf ans)`, the whitening pads at `kOf ans`,
  system B's two lanes (at the labels whitened by `wPadsOf ans`).
* `mem_shadow_fixed`, `mem_shadow_hash` — the fixed-key and hash questions of the shadow `shadowOnM`
  along `ans`: system A's lanes again, the bridge hash, system B's lanes (whitened by the evaluator's
  pads `ePadsOf ans`, the same whitening: `whitenMac_ePads`), and, fixed-key only, the gadget at the
  transformed labels.
* `lane_hash_mem` — a lane's hash questions are the limbs of an inactive switch of some chunk at
  its one-hot label (the chunk fold's output); `evalLaneM_fresh`, `evalLaneM_inCells` — along every
  path of a lane its consumed cells are distinct (one hash question per (chunk, inactive switch,
  limb)) and lie in the lane's cells. Both at any chunk width.
* `opening_fresh`, `opening_described` — **the opening run, described** (`runRefill_describe`).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsPath

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM whitePadsM noRecord)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request AllQ EncAt queriesAlong
  queriesAlong_bind queriesAlong_pure queriesAlong_vector consumedCell cellOf cellOf_cellInput
  cellOf_spec cellInput maskCell evalLaneM_allQ whitePadsM_allQ padM_allQ runRefill)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The programs, named -/

section Programs

variable [FieldCertificate] (table : Public) (bits : BitInput)

/-- System A's `x` lane. -/
abbrev curveXM (mac : InputMac) : Programs.M (Fin curveElementCountX → BaseField) :=
  Programs.evalLaneM .curveX table.curveXHot
    (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x)

/-- System A's `y` lane. -/
abbrev curveYM (mac : InputMac) : Programs.M (Fin curveElementCountY → BaseField) :=
  Programs.evalLaneM .curveY table.curveYHot
    (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y)

/-- System B's `x` lane, at some labels. -/
abbrev pointXM (mac : InputMac) : Programs.M (Fin pointElementCountX → BaseField) :=
  Programs.evalLaneM .pointX table.pointXHot
    (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x)

/-- System B's `y` lane, at some labels. -/
abbrev pointYM (mac : InputMac) : Programs.M (Fin pointElementCountY → BaseField) :=
  Programs.evalLaneM .pointY table.pointYHot
    (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y)

/-- The bridge value along `ans` (its hash input is `bridgeInput (tOf …)`). -/
abbrev tOf (mac : InputMac) (ans : (request : Request) → request.Answer) : BaseField :=
  CurveMembership.evaluate table.curve bits.toAffine
    (Pipeline.curveValues (FreeQuery.eval ans (curveXM table bits mac))
      (FreeQuery.eval ans (curveYM table bits mac)))

/-- The whitening keys along `ans`. -/
abbrev kOf (mac : InputMac) (ans : (request : Request) → request.Answer) : Block × Block :=
  ans (.hash (bridgeInput (tOf table bits mac ans)))

/-- The opening's whitening pads along `ans`. -/
abbrev wPadsOf (mac : InputMac) (ans : (request : Request) → request.Answer) :
    EncPRF.Coordinate → Fin coordinateBitCount → Block × Block :=
  FreeQuery.eval ans (whitePadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩)

/-- The evaluator's pads along `ans`. -/
abbrev ePadsOf (mac : InputMac) (ans : (request : Request) → request.Answer) :
    EncPRF.Coordinate → Fin coordinateBitCount → Block × Block :=
  FreeQuery.eval ans (Programs.evalPadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩
    bits)

theorem openingQueriesM_eq (mac : InputMac) :
    openingQueriesM table bits mac =
      curveXM table bits mac >>= fun curveX => curveYM table bits mac >>= fun curveY =>
        Programs.askHash (bridgeInput (CurveMembership.evaluate table.curve bits.toAffine
          (Pipeline.curveValues curveX curveY))) >>= fun hashed =>
          whitePadsM ⟨hashed.1, hashed.2⟩ >>= fun pads =>
            pointXM table bits (Programs.whitenMacOf pads mac) >>= fun pointX =>
              pointYM table bits (Programs.whitenMacOf pads mac) >>= fun pointY =>
                pure (pointX, pointY) := rfl

theorem queriesAlong_askHash (ans : (request : Request) → request.Answer) (input : BaseField) :
    queriesAlong ans (Programs.askHash input) = [.hash input] := rfl

theorem eval_askHash (ans : (request : Request) → request.Answer) (input : BaseField) :
    FreeQuery.eval ans (Programs.askHash input) = ans (.hash input) := rfl

/-- **The questions of the opening.** -/
theorem mem_opening (mac : InputMac) (ans : (request : Request) → request.Answer) (r : Request)
    (member : r ∈ queriesAlong ans (openingQueriesM table bits mac)) :
    r ∈ queriesAlong ans (curveXM table bits mac) ∨ r ∈ queriesAlong ans (curveYM table bits mac) ∨
      r = .hash (bridgeInput (tOf table bits mac ans)) ∨
      r ∈ queriesAlong ans (whitePadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩) ∨
      r ∈ queriesAlong ans (pointXM table bits
        (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) ∨
      r ∈ queriesAlong ans (pointYM table bits
        (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) := by
  rw [openingQueriesM_eq] at member
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, queriesAlong_askHash,
    List.mem_append, List.mem_singleton, eval_askHash] at member
  rcases member with a | b | c | d | e | f
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · exact Or.inr (Or.inr (Or.inl c))
  · exact Or.inr (Or.inr (Or.inr (Or.inl d)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr f))))

/-- The whitening pad of a position, from the opening's pads. -/
theorem whitePads_fst (keys : WhiteningKeys) (ans : (request : Request) → request.Answer)
    (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) :
    (FreeQuery.eval ans (whitePadsM keys) coordinate index).1 =
      FreeQuery.eval ans (Programs.padM keys coordinate index false) := by
  cases coordinate <;>
    simp only [whitePadsM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
      Vector.get_ofFn]

/-- The whitening pad of a position, from the evaluator's pads. -/
theorem evalPads_fst (keys : WhiteningKeys) (ans : (request : Request) → request.Answer)
    (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) :
    (FreeQuery.eval ans (Programs.evalPadsM keys bits) coordinate index).1 =
      FreeQuery.eval ans (Programs.padM keys coordinate index false) := by
  cases coordinate <;>
  · simp only [Programs.evalPadsM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
      Vector.get_ofFn]
    split <;> simp only [FreeQuery.eval_bind, FreeQuery.eval_pure]

/-- The two paddings whiten alike: both read only the bit-`false` pads. -/
theorem whitenMac_ePads (mac : InputMac) (ans : (request : Request) → request.Answer) :
    Programs.whitenMacOf (ePadsOf table bits mac ans) mac =
      Programs.whitenMacOf (wPadsOf table bits mac ans) mac := by
  unfold Programs.whitenMacOf
  simp only [ePadsOf, wPadsOf, evalPads_fst, whitePads_fst]

end Programs

section Shadow

variable [FieldCertificate] [GroupCertificate] (table : Public) (bits : BitInput)

theorem onCurveM_eq (mac : InputMac) :
    Programs.onCurveM table bits mac =
      curveXM table bits mac >>= fun curveX => curveYM table bits mac >>= fun curveY =>
        Programs.askHash (bridgeInput (CurveMembership.evaluate table.curve bits.toAffine
          (Pipeline.curveValues curveX curveY))) >>= fun hashed =>
          Programs.evalPadsM ⟨hashed.1, hashed.2⟩ bits >>= fun pads =>
            pointXM table bits (Programs.whitenMacOf pads mac) >>= fun pointX =>
              pointYM table bits (Programs.whitenMacOf pads mac) >>= fun pointY =>
                Programs.masksM bits.toAffine (Programs.transformMacOf pads mac) >>= fun masks =>
                  pure (some (Garbling.decodeResult
                    { point := bits.toAffine
                      pointMacs := FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable table)
                        (Pipeline.digitValues pointX pointY) bits.toAffine
                      exceptionDigits :=
                        Programs.unlockDigits (Pipeline.pointTable table) bits.toAffine masks false
                      tripleDigits :=
                        Programs.unlockDigits (Pipeline.pointTable table) bits.toAffine masks true
                    })) := rfl

theorem evalPadsM_encAt (keys : WhiteningKeys) : AllQ EncAt (Programs.evalPadsM keys bits) := by
  unfold Programs.evalPadsM
  dsimp only
  exact (AllQ.vector fun _ => (padM_allQ keys _ _ _).bind fun _ =>
      AllQ.ite ((padM_allQ keys _ _ _).bind fun _ => .pure _) (.pure _)).bind fun _ =>
    (AllQ.vector fun _ => (padM_allQ keys _ _ _).bind fun _ =>
      AllQ.ite ((padM_allQ keys _ _ _).bind fun _ => .pure _) (.pure _)).bind fun _ => .pure _

theorem queriesAlong_curvePrefixM (mac : InputMac) (ans : (request : Request) → request.Answer) :
    queriesAlong ans (curvePrefixM table bits mac) =
      queriesAlong ans (curveXM table bits mac) ++ (queriesAlong ans (curveYM table bits mac) ++
        [.hash (bridgeInput (tOf table bits mac ans))]) := by
  unfold curvePrefixM
  rw [queriesAlong_bind, queriesAlong_bind, queriesAlong_askHash]

theorem eval_curvePrefixM (mac : InputMac) (ans : (request : Request) → request.Answer) :
    FreeQuery.eval ans (curvePrefixM table bits mac) = kOf table bits mac ans := by
  unfold curvePrefixM
  rw [FreeQuery.eval_bind, FreeQuery.eval_bind, eval_askHash]

theorem queriesAlong_onCurveM (mac : InputMac) (ans : (request : Request) → request.Answer) :
    queriesAlong ans (Programs.onCurveM table bits mac) =
      queriesAlong ans (curveXM table bits mac) ++ (queriesAlong ans (curveYM table bits mac) ++
        ([.hash (bridgeInput (tOf table bits mac ans))] ++
          (queriesAlong ans (Programs.evalPadsM ⟨(kOf table bits mac ans).1,
              (kOf table bits mac ans).2⟩ bits) ++
            (queriesAlong ans (pointXM table bits
                (Programs.whitenMacOf (ePadsOf table bits mac ans) mac)) ++
              (queriesAlong ans (pointYM table bits
                  (Programs.whitenMacOf (ePadsOf table bits mac ans) mac)) ++
                queriesAlong ans (Programs.masksM bits.toAffine
                  (Programs.transformMacOf (ePadsOf table bits mac ans) mac))))))) := by
  rw [onCurveM_eq]
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, queriesAlong_askHash]
  rfl

theorem queriesAlong_shadowOnM (mac : InputMac) (ans : (request : Request) → request.Answer) :
    queriesAlong ans (shadowOnM table bits mac) =
      queriesAlong ans (curvePrefixM table bits mac) ++
        (queriesAlong ans (truePadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩) ++
          queriesAlong ans (Programs.onCurveM table bits mac)) := by
  unfold shadowOnM
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, eval_curvePrefixM]

theorem truePadsM_encAt (keys : WhiteningKeys) : AllQ EncAt (truePadsM keys) :=
  (AllQ.vector fun _ => padM_allQ _ _ _ _).bind fun _ =>
    (AllQ.vector fun _ => padM_allQ _ _ _ _).bind fun _ => .pure _

theorem not_encAt_fixed {i : FixedIndex} {x : Block} :
    ¬ EncAt (.fixedForward i x : Request) := fun h => h

theorem not_encAt_hash {k : BaseField} : ¬ EncAt (.hash k : Request) := fun h => h

/-- **The fixed-key questions of the shadow.** -/
theorem mem_shadow_fixed (mac : InputMac) (ans : (request : Request) → request.Answer)
    (i : FixedIndex) (x : Block)
    (member : .fixedForward i x ∈ queriesAlong ans (shadowOnM table bits mac)) :
    .fixedForward i x ∈ queriesAlong ans (curveXM table bits mac) ∨
      .fixedForward i x ∈ queriesAlong ans (curveYM table bits mac) ∨
      .fixedForward i x ∈ queriesAlong ans (pointXM table bits
        (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) ∨
      .fixedForward i x ∈ queriesAlong ans (pointYM table bits
        (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) ∨
      .fixedForward i x ∈ queriesAlong ans (Programs.masksM
        bits.toAffine (Programs.transformMacOf (ePadsOf table bits mac ans) mac)) := by
  rw [queriesAlong_shadowOnM, queriesAlong_curvePrefixM, queriesAlong_onCurveM,
    whitenMac_ePads] at member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (a | b | c) | d | a | b | c | d | e | f | g
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · cases c
  · exact absurd (mem_queriesAlong_allQ ans (truePadsM_encAt _) _ d) not_encAt_fixed
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · cases c
  · exact absurd (mem_queriesAlong_allQ ans (evalPadsM_encAt bits _) _ d) not_encAt_fixed
  · exact Or.inr (Or.inr (Or.inl e))
  · exact Or.inr (Or.inr (Or.inr (Or.inl f)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr g)))

/-- A gadget question at the given labels (at any bit's index). -/
def GadgetQ (mac : InputMac) (r : Request) : Prop :=
  ∃ (d : Fin digitCount) (κ : EncPRF.Coordinate) (pos : Fin coordinateBitCount) (bit : Bool),
    r = .fixedForward (.gadget d (Pipeline.gadgetCoord κ) pos bit)
      (Pipeline.macLabels mac (Pipeline.gadgetCoord κ) pos)

theorem gadgetDigestM_gadgetQ (mac : InputMac) (d : Fin digitCount) (κ : EncPRF.Coordinate)
    (bits : CoordinateBits) (labels : CoordinateMac)
    (same : ∀ pos, labels.get pos = Pipeline.macLabels mac (Pipeline.gadgetCoord κ) pos) :
    AllQ (GadgetQ mac) (Programs.gadgetDigestM d κ bits labels) :=
  (AllQ.vector fun pos => AllQ.bind (.query _ _ ⟨d, κ, pos, _, by rw [same]⟩ fun _ => .pure _)
    fun _ => .pure _).bind fun _ => .pure _

theorem masksM_gadgetQ (input : AffineInput) (mac : InputMac) :
    AllQ (GadgetQ mac) (Programs.masksM input mac) :=
  AllQ.vector fun d =>
    ((gadgetDigestM_gadgetQ mac d .x _ mac.x fun _ => rfl).bind fun _ =>
      (gadgetDigestM_gadgetQ mac d .y _ mac.y fun _ => rfl).bind fun _ => .pure _).bind
        fun _ => .pure _

/-- **The hash questions of the shadow** are the bridge input and the lanes' own hash questions
(system B's at the opening's whitening). -/
theorem mem_shadow_hash (mac : InputMac) (ans : (request : Request) → request.Answer)
    (k : BaseField) (member : .hash k ∈ queriesAlong ans (shadowOnM table bits mac)) :
    k = bridgeInput (tOf table bits mac ans) ∨
      .hash k ∈ queriesAlong ans (curveXM table bits mac) ∨
      .hash k ∈ queriesAlong ans (curveYM table bits mac) ∨
      .hash k ∈ queriesAlong ans (pointXM table bits
        (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) ∨
      .hash k ∈ queriesAlong ans (pointYM table bits
        (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) := by
  rw [queriesAlong_shadowOnM, queriesAlong_curvePrefixM, queriesAlong_onCurveM,
    whitenMac_ePads] at member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (a | b | c) | d | a | b | c | d | e | f | g
  · exact Or.inr (Or.inl a)
  · exact Or.inr (Or.inr (Or.inl b))
  · exact Or.inl (PublicQuery.hash.inj c)
  · exact absurd (mem_queriesAlong_allQ ans (truePadsM_encAt _) _ d) not_encAt_hash
  · exact Or.inr (Or.inl a)
  · exact Or.inr (Or.inr (Or.inl b))
  · exact Or.inl (PublicQuery.hash.inj c)
  · exact absurd (mem_queriesAlong_allQ ans (evalPadsM_encAt bits _) _ d) not_encAt_hash
  · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr f)))
  · obtain ⟨_, _, _, _, same⟩ := mem_queriesAlong_allQ ans (masksM_gadgetQ _ _) _ g
    cases same

end Shadow

/-! ### The lanes' cells, and the opening, fresh -/

section Fresh

/-- The cells of one lane. -/
def laneCells (lane : Lane) : Set Cell := {cell | cell.1.lane = lane}

theorem consumedCell_none_of_encAt {bits : BitInput} {r : Request} (inside : EncAt r) :
    consumedCell bits r = none := by
  cases r with
  | encForward _ _ => rfl
  | fixedForward _ _ => exact inside.elim
  | fixedInverse _ _ => exact inside.elim
  | encInverse _ _ => exact inside.elim
  | hash _ => exact inside.elim

theorem inCells_of_none {bits : BitInput} {S : Set Cell} {r : Request}
    (none : consumedCell bits r = none) : InCells bits S r := fun i hi => by
  rw [none] at hi
  cases hi

/-- A consumed cell is the cell of its input. -/
theorem consumedCell_hash {bits : BitInput} {input : BaseField} {cell : Cell}
    (consumed : consumedCell bits (.hash input) = some cell) : cellOf input = some cell := by
  classical
  simp only [consumedCell] at consumed
  split_ifs at consumed
  exact consumed

/-- The bridge input consumes no cell. -/
theorem consumedCell_bridge (bits : BitInput) (t : BaseField) :
    consumedCell bits (.hash (bridgeInput t)) = none := by
  cases consumed : consumedCell bits (.hash (bridgeInput t)) with
  | none => rfl
  | some cell =>
    obtain ⟨label, same⟩ := cellOf_spec (consumedCell_hash consumed)
    exact absurd same.symm (bridgeInput_ne_scaleInput t _ _ _ _ _)

/-- **A lane's consumed cells are its own cells.** -/
theorem evalLaneM_inCells [FieldCertificate] (bits : BitInput) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    AllQ (InCells bits (laneCells lane)) (Programs.evalLaneM lane joins scale word labels) :=
  (evalLaneM_allQ lane joins scale word labels).mono fun r inside cell consumed => by
    obtain ⟨c, inside⟩ := inside
    cases r with
    | hash input =>
      rcases inside with fixed | ⟨cell', label, laneEq, _, rfl⟩
      · exact fixed.elim
      · cases Option.some.inj ((consumedCell_hash consumed).symm.trans (cellOf_cellInput _ _))
        exact laneEq
    | _ => cases consumed

/-- The cell of a switch-mask question. -/
theorem consumedCell_scaleInput {bits : BitInput} {lane : Lane} {c : Fin chunkCount}
    {switch : Fin (2 ^ chunkWidth c)} {limb : Fin (limbCount lane)} {label : Block} {cell : Cell}
    (consumed : consumedCell bits (.hash (scaleInput lane c switch.val limb.val label)) = some cell) :
    cell = ⟨⟨lane, c, switch⟩, limb⟩ :=
  Option.some.inj ((consumedCell_hash consumed).symm.trans
    (cellOf_cellInput ⟨⟨lane, c, switch⟩, limb⟩ label))

/-- **Along every path of a lane, the consumed cells are distinct** (one hash question per
(chunk, inactive switch, limb)), at any chunk width. -/
theorem evalLaneM_fresh [FieldCertificate] (bits : BitInput) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    Fresh bits ∅ (Programs.evalLaneM lane joins scale word labels) := by
  -- the fold consumes nothing
  have foldNone : ∀ (c : Fin chunkCount) (value : ℕ) (bitLabel join : ℕ → Block) (w : ℕ),
      AllQ (fun r => consumedCell bits r = none)
        (Programs.evalFoldM lane c value bitLabel join w) := fun c value bitLabel join w =>
    (Kriterion.ArgoMAC.Phase3.Lazy.evalFoldM_allQ lane c value bitLabel join w).mono
      fun r inside => by
        cases r with
        | fixedForward _ _ => rfl
        | _ => exact inside.elim
  -- one switch: one question per limb, at its own cell
  have switchFresh : ∀ (c : Fin chunkCount) (switch : Fin (2 ^ chunkWidth c)) (label : Block),
      Fresh bits ∅ (Programs.switchMaskM lane c switch.val label) ∧
        AllQ (InCells bits {cell | cell.1 = ⟨lane, c, switch⟩})
          (Programs.switchMaskM lane c switch.val label) := by
    intro c switch label
    have limbIn : ∀ limb : Fin (limbCount lane),
        AllQ (InCells bits {cell | cell = ⟨⟨lane, c, switch⟩, limb⟩})
          (Programs.askHash (scaleInput lane c switch.val limb.val label)) := fun limb =>
      .query _ _ (fun cell consumed => consumedCell_scaleInput consumed) fun _ => .pure _
    refine ⟨Fresh.bind (S := {cell | cell.1 = ⟨lane, c, switch⟩})
      (Fresh.vector (fun limb => {cell | cell = ⟨⟨lane, c, switch⟩, limb⟩})
        (fun limb => .query _ _ _ (fun _ _ => Set.notMem_empty _) fun _ => .pure _ _) limbIn
        (fun limb limb' different cell inside inside' => different (by
          rw [Set.mem_ofPred_eq] at inside inside'
          rw [inside] at inside'
          exact (Sigma.mk.inj_iff.mp inside').2.eq)) ∅ fun _ _ _ outside => outside)
      (AllQ.vector fun limb => (limbIn limb).mono fun r inside cell consumed => by
        have same : cell = _ := inside cell consumed
        subst same
        rfl)
      fun _ => .pure _ _, ?_⟩
    exact (AllQ.vector fun limb => (limbIn limb).mono fun r inside cell consumed => by
      have same : cell = _ := inside cell consumed
      subst same
      rfl).bind fun _ => .pure _
  -- one chunk: the fold, then one switch-mask vector per inactive switch
  have chunkFresh : ∀ c : Fin chunkCount,
      Fresh bits ∅ (Programs.evalChunkM lane joins scale word labels c) ∧
        AllQ (InCells bits {cell | cell.1.lane = lane ∧ cell.1.chunk = c})
          (Programs.evalChunkM lane joins scale word labels c) := by
    intro c
    have masksIn : ∀ switch : Fin (2 ^ chunkWidth c), ∀ hot : HotLabels (chunkWidth c),
        AllQ (InCells bits {cell | cell.1 = ⟨lane, c, switch⟩})
          (if switch = chunkOf word c then pure (Vector.ofFn fun _ => 0)
            else Programs.switchMaskM lane c switch.val (hot switch)) := by
      intro switch hot
      split
      · exact .pure _
      · exact (switchFresh c switch _).2
    have masksFresh : ∀ hot : HotLabels (chunkWidth c),
        Fresh bits ∅ (Programs.evalMasksM lane c (chunkWidth c) hot (chunkOf word c)) ∧
          AllQ (InCells bits {cell | cell.1.lane = lane ∧ cell.1.chunk = c})
            (Programs.evalMasksM lane c (chunkWidth c) hot (chunkOf word c)) := by
      intro hot
      unfold Programs.evalMasksM
      have each : ∀ switch : Fin (2 ^ chunkWidth c),
          Fresh bits ∅ (if switch = chunkOf word c then pure (Vector.ofFn fun _ => 0)
            else Programs.switchMaskM lane c switch.val (hot switch)) := fun switch =>
        Fresh.ite (.pure _ _) (switchFresh c switch _).1
      refine ⟨Fresh.bind (S := {cell | cell.1.lane = lane ∧ cell.1.chunk = c})
        (Fresh.vector (fun switch => {cell | cell.1 = ⟨lane, c, switch⟩}) each (masksIn · hot)
          (fun switch switch' different cell inside inside' => different (by
            rw [Set.mem_ofPred_eq] at inside inside'
            rw [inside] at inside'
            exact (VectorSite.mk.inj inside').2.2.eq)) ∅ fun _ _ _ outside => outside)
        (AllQ.vector fun switch => (masksIn switch hot).mono fun r inside cell consumed => by
          have same := inside cell consumed
          rw [Set.mem_ofPred_eq] at same
          exact ⟨by rw [same], by rw [same]⟩) fun _ => .pure _ _, ?_⟩
      exact (AllQ.vector fun switch => (masksIn switch hot).mono fun r inside cell consumed => by
        have same := inside cell consumed
        rw [Set.mem_ofPred_eq] at same
        exact ⟨by rw [same], by rw [same]⟩).bind fun _ => .pure _
    refine ⟨?_, ?_⟩
    · exact Fresh.bind (S := ∅) (Fresh.of_none (foldNone _ _ _ _ _) _)
        ((foldNone _ _ _ _ _).mono fun _ none => inCells_of_none none) fun hot =>
          Fresh.bind (S := {cell | cell.1.lane = lane ∧ cell.1.chunk = c})
            ((masksFresh hot).1.mono fun _ inside => inside.elim (fun h => h.elim) fun h => h.elim)
            (masksFresh hot).2 fun _ => .pure _ _
    · exact ((foldNone _ _ _ _ _).mono fun _ none => inCells_of_none none).bind fun hot =>
        (masksFresh hot).2.bind fun _ => .pure _
  unfold Programs.evalLaneM
  exact Fresh.bind (S := laneCells lane)
    (Fresh.vector (fun c => {cell | cell.1.lane = lane ∧ cell.1.chunk = c})
      (fun c => (chunkFresh c).1) (fun c => (chunkFresh c).2)
      (fun c c' different cell inside inside' => different (inside.2.symm.trans inside'.2))
      ∅ fun _ _ _ outside => outside)
    (AllQ.vector fun c => (chunkFresh c).2.mono fun r inside cell consumed =>
      (inside cell consumed).1) fun _ => .pure _ _

/-- **A lane's hash questions**: at a chunk `c`, the limbs of an inactive switch at its one-hot
label (the fold's output along `ans`), at any chunk width. -/
theorem lane_hash_mem [FieldCertificate] (ans : (request : Request) → request.Answer) (lane : Lane)
    (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (k : BaseField)
    (member : .hash k ∈ queriesAlong ans (Programs.evalLaneM lane joins scale word labels)) :
    ∃ (c : Fin chunkCount) (switch : Fin (2 ^ chunkWidth c)) (limb : Fin (limbCount lane)),
      switch ≠ chunkOf word c ∧
        k = cellInput (maskCell lane c switch limb)
          (FreeQuery.eval ans (Programs.evalFoldM lane c (chunkValue word c).toNat
            (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c)) (chunkWidth c)) switch) := by
  unfold Programs.evalLaneM at member
  rw [queriesAlong_bind, queriesAlong_pure, List.append_nil, queriesAlong_vector] at member
  obtain ⟨c, _, inner⟩ := List.mem_flatMap.mp member
  change .hash k ∈ queriesAlong ans (Programs.evalFoldM lane c (chunkValue word c).toNat
      (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c)) (chunkWidth c) >>= fun hot =>
    Programs.evalMasksM lane c (chunkWidth c) hot (chunkOf word c) >>= fun masks =>
      pure (Programs.evalScaleOf (chunkWidth c) masks (chunkOf word c) (scale c))) at inner
  rw [queriesAlong_bind, queriesAlong_bind, queriesAlong_pure, List.append_nil] at inner
  rcases List.mem_append.mp inner with fold | masks
  · exact absurd (mem_queriesAlong_allQ ans
      (Kriterion.ArgoMAC.Phase3.Lazy.evalFoldM_allQ lane c _ _ _ _) _ fold) id
  · obtain ⟨switch, inactive, limb, same⟩ :=
      Kriterion.ArgoMAC.Phase3.Lazy.mem_queriesAlong_evalMasksM ans lane c _ _ _ masks
    exact ⟨c, switch, limb, inactive, PublicQuery.hash.inj same⟩

variable [FieldCertificate]

theorem laneCells_ne {lane lane' : Lane} (different : lane ≠ lane') {cell : Cell}
    (inside : cell ∈ laneCells lane) : cell ∉ laneCells lane' :=
  fun inside' => different (inside.symm.trans inside')

theorem lane_fresh_avoid (bits : BitInput) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (U : Set Cell)
    (avoid : ∀ cell ∈ laneCells lane, cell ∉ U) :
    Fresh bits U (Programs.evalLaneM lane joins scale word labels) :=
  ((evalLaneM_fresh bits lane joins scale word labels).union_disjoint
    (evalLaneM_inCells bits lane joins scale word labels) avoid).mono fun _ member => Or.inr member

/-- **Along every path of the opening, the consumed cells are distinct.** -/
theorem opening_fresh (table : Public) (bits : BitInput) (mac : InputMac) :
    Fresh bits ∅ (openingQueriesM table bits mac) := by
  have hashNone : ∀ t : BaseField, AllQ (fun r => consumedCell bits r = none)
      (Programs.askHash (bridgeInput t)) := fun t =>
    .query _ _ (consumedCell_bridge bits t) fun _ => .pure _
  have padsNone : ∀ keys : WhiteningKeys, AllQ (fun r => consumedCell bits r = none)
      (whitePadsM keys) := fun keys =>
    (whitePadsM_allQ keys).mono fun _ inside => consumedCell_none_of_encAt inside
  rw [openingQueriesM_eq]
  refine Fresh.bind (S := laneCells .curveX) (evalLaneM_fresh bits _ _ _ _ _)
    (evalLaneM_inCells bits _ _ _ _ _) fun _ => ?_
  refine Fresh.bind (S := laneCells .curveY)
    (lane_fresh_avoid bits _ _ _ _ _ _ fun cell inside outside => ?_)
    (evalLaneM_inCells bits _ _ _ _ _) fun _ => ?_
  · rcases outside with outside | outside
    · exact outside
    · exact laneCells_ne (by decide) inside outside
  refine Fresh.bind (S := ∅) (Fresh.of_none (hashNone _) _)
    ((hashNone _).mono fun _ none => inCells_of_none none) fun _ => ?_
  refine Fresh.bind (S := ∅) (Fresh.of_none (padsNone _) _)
    ((padsNone _).mono fun _ none => inCells_of_none none) fun _ => ?_
  refine Fresh.bind (S := laneCells .pointX)
    (lane_fresh_avoid bits _ _ _ _ _ _ fun cell inside outside => ?_)
    (evalLaneM_inCells bits _ _ _ _ _) fun _ => ?_
  · rcases outside with (((outside | outside) | outside) | outside) | outside
    · exact outside
    · exact laneCells_ne (by decide) inside outside
    · exact laneCells_ne (by decide) inside outside
    · exact outside
    · exact outside
  refine Fresh.bind (S := laneCells .pointY)
    (lane_fresh_avoid bits _ _ _ _ _ _ fun cell inside outside => ?_)
    (evalLaneM_inCells bits _ _ _ _ _) fun _ => .pure _ _
  rcases outside with ((((outside | outside) | outside) | outside) | outside) | outside
  · exact outside
  · exact laneCells_ne (by decide) inside outside
  · exact laneCells_ne (by decide) inside outside
  · exact outside
  · exact outside
  · exact laneCells_ne (by decide) inside outside

variable [GroupCertificate]

/-- **The opening run, described.** -/
theorem opening_described (source : Stage1Source) (input : AffineInput) (tape : Tape)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)
    (member : some ran ∈ (runRefill (restoredBits source input) (fun cell => PMF.pure (tape cell))
      (openingQueriesM source.publicValue (restoredBits source input) (restoredMac source input))
      LazyOracle.empty noRecord ∅).support) :
    Described (restoredBits source input) tape
      (openingQueriesM source.publicValue (restoredBits source input) (restoredMac source input))
      LazyOracle.empty noRecord ran :=
  runRefill_describe (restoredBits source input) tape _
    (openingQueriesM_forwardOnly _ _ _) ∅ (opening_fresh _ _ _) LazyOracle.empty noRecord ∅
    (fun _ _ => ⟨fun h => h, fun _ => rfl⟩) ran member

end Fresh

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
