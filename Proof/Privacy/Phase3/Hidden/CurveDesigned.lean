/-
**Phase 3, P1h — off the curve, the designed entries are the curve lanes' and ignore the hidden sites.**

Off the curve `designedRule` keeps only curve-lane gates and the hash limbs of inactive curve-lane
switches. So:

* `designedEntries_offCurve`: the designed entries are the designed part of the two curve lanes'
  garbler transcripts (the bridge hash is not designed, the pads are EncPRF, the point lanes and the
  gadget ask only non-designed questions — `laneM_laneOnly`, `gadgetM_gadgetOnly`);
* `curveDesigned_congr`: the designed part of a curve lane's transcript is the same on two tapes
  with the same input keys and fixed-key oracle whose hash tables agree at every scale
  input of a curve lane's non-hidden site under its garbler label: the lane's questions do not
  depend on its hash answers, and a designed entry is never at a hidden site (`sim_laneM_offH`).
-/

import Proof.Privacy.Phase3.Hidden.CurveFamily

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open scoped ENNReal

noncomputable section

/-! ### The lane of a question -/

/-- The lane a fixed-key index belongs to (`none` for the gadget). -/
def indexLane : FixedIndex → Option Lane
  | .hot ℓ _ _ _ _ => some ℓ
  | .gadget _ _ _ => none

/-- A question of lane `ℓ`: a fold gate of `ℓ`, or a hash limb of a switch of `ℓ`. -/
def LaneQ (ℓ : Lane) : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward index _ => indexLane index = some ℓ
  | .hash key => ∃ slot : LimbSite, ∃ label : Block, labelInput slot label = key ∧ slot.1.lane = ℓ
  | _ => False

/-- A fixed-key forward question at a gadget index. -/
def GadgetQ : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward (.gadget _ _ _) _ => True
  | _ => False

section LaneOnly

variable [FieldCertificate] [GroupCertificate]

theorem garbleFoldM_laneOnly (lane : Lane) (chunk : Fin chunkCount) (delta : Block)
    (zeroLabel : Nat → Block) :
    ∀ steps, QueryOnly (LaneQ lane) (Programs.garbleFoldM lane chunk delta zeroLabel steps)
  | 0 => QueryOnly.pure' _
  | steps + 1 => by
      refine QueryOnly.bind (garbleFoldM_laneOnly lane chunk delta zeroLabel steps) fun previous =>
        QueryOnly.bind ?_ fun _ => QueryOnly.pure' _
      unfold Programs.garbleStepM
      split
      · exact QueryOnly.pure' _
      · exact QueryOnly.bind (QueryOnly.vector _ fun _ =>
          QueryOnly.bind (hashM_ask _ _ rfl) fun _ => QueryOnly.bind (hashM_ask _ _ rfl) fun _ =>
            QueryOnly.pure' _) fun _ => QueryOnly.pure' _

theorem laneM_laneOnly (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block) :
    QueryOnly (LaneQ lane) (Programs.laneM lane delta bitKey) :=
  QueryOnly.bind (QueryOnly.pi _ fun c =>
    QueryOnly.bind (QueryOnly.bind (garbleFoldM_laneOnly _ _ _ _ _) fun _ => QueryOnly.pure' _)
      fun _ => QueryOnly.bind (QueryOnly.vector _ fun switch =>
        QueryOnly.bind (QueryOnly.vector _ fun limb => QueryOnly.ask _
          ⟨⟨⟨lane, c, switch⟩, limb⟩, _, rfl, rfl⟩) fun _ => QueryOnly.pure' _)
        fun _ => QueryOnly.pure' _) fun _ => QueryOnly.pure' _

end LaneOnly

theorem gadgetM_gadgetOnly [FieldCertificate] [GroupCertificate] (keys : FieldMacToECMac.OutputKeys)
    (inputKey : InputMacKey) (pads : FieldMacToECMac.ExceptionPad) :
    QueryOnly GadgetQ (Programs.gadgetM keys inputKey pads) := by
  have digest : ∀ output coordinate mac,
      QueryOnly GadgetQ (Programs.gadgetDigestM output coordinate mac) :=
    fun _ _ _ =>
      QueryOnly.bind (QueryOnly.vector _ fun _ => hashM_ask _ _ trivial) fun _ => QueryOnly.pure' _
  refine QueryOnly.vector _ fun output => ?_
  unfold Programs.garbleEntryM
  split
  · exact QueryOnly.pure' _
  · exact QueryOnly.bind (QueryOnly.bind (digest _ _ _) fun _ => QueryOnly.bind (digest _ _ _)
      fun _ => QueryOnly.pure' _) fun _ => QueryOnly.pure' _

/-- A transcript all of whose questions a predicate rejects filters to nothing. -/
theorem filter_nil_of_only {α : Type} {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}
    {P : FreeQuery Programs.Spec α} (only : QueryOnly S P)
    (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (keep : Entry FixedIndex EncPRF.PermutationIndex → Bool)
    (reject : ∀ e : Entry FixedIndex EncPRF.PermutationIndex, S e.1 → keep e = false) :
    (Hidden.transcriptOf ans P).filter keep = [] :=
  List.filter_eq_nil_iff.mpr fun e member => by simp [reject e (only.mem ans e member)]

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- The designed-entry filter. -/
def designedKeep (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (e : Entry FixedIndex EncPRF.PermutationIndex) : Bool :=
  !e.IsEnc && designedRule scalar tape input e

/-- **The designed part of the curve lanes' transcripts.** -/
def curveDesigned (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput) :
    List (Entry FixedIndex EncPRF.PermutationIndex) :=
  (Hidden.transcriptOf (publicAnswer tape.2) (Programs.laneM .curveX (tape.1.inputDelta .x)
      (Pipeline.bitKeyOf tape.1.inputMacKey .x))).filter (designedKeep scalar tape input) ++
    (Hidden.transcriptOf (publicAnswer tape.2) (Programs.laneM .curveY (tape.1.inputDelta .y)
      (Pipeline.bitKeyOf tape.1.inputMacKey .y))).filter (designedKeep scalar tape input)

theorem keep_point (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (invalid : validate input = false) (ℓ : Lane) (point : laneIsCurve ℓ = false)
    (e : Entry FixedIndex EncPRF.PermutationIndex) (lane : LaneQ ℓ e.1) :
    designedKeep scalar tape input e = false := by
  obtain ⟨request, answer⟩ := e
  cases request with
  | fixedForward index x =>
      cases index with
      | hot ℓ' k fold r half =>
          simp only [LaneQ, indexLane, Option.some.injEq] at lane
          subst lane
          simp [designedKeep, designedRule, designedIndex, point, invalid, Entry.IsEnc]
      | gadget o κ position => simp [LaneQ, indexLane] at lane
  | hash key =>
      obtain ⟨slot, label, rfl, same⟩ := lane
      have notDesigned : designedHash input (labelInput slot label) = false := by
        rw [designedHash_labelInput]
        simp [designedSite, same, point, invalid]
      simp [designedKeep, designedRule, notDesigned, Entry.IsEnc]
  | _ => exact lane.elim

theorem keep_gadget (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (invalid : validate input = false) (e : Entry FixedIndex EncPRF.PermutationIndex)
    (gadget : GadgetQ e.1) : designedKeep scalar tape input e = false := by
  obtain ⟨request, answer⟩ := e
  cases request with
  | fixedForward index x =>
      cases index with
      | gadget o κ position => simp [designedKeep, designedRule, designedIndex, invalid, Entry.IsEnc]
      | _ => exact gadget.elim
  | _ => exact gadget.elim

theorem keep_enc (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (e : Entry FixedIndex EncPRF.PermutationIndex) (enc : IsEncForward e.1) :
    designedKeep scalar tape input e = false := by
  simp [designedKeep, isEnc_of_encForward e enc]

/-- **Off the curve, the designed entries are the curve lanes'.** -/
theorem designedEntries_offCurve (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (invalid : validate input = false) :
    designedEntries designedRule parameter scalar tape input = curveDesigned scalar tape input := by
  rw [designedEntries_eq, garblerTranscript_eq]
  show (Hidden.transcriptOf (publicAnswer tape.2) (Programs.garbleM scalar tape.1)).filter
    (designedKeep scalar tape input) = _
  unfold Programs.garbleM
  simp only [transcriptOf_bind, List.filter_append]
  have hashNil : ∀ value, (Hidden.transcriptOf (publicAnswer tape.2)
      (Programs.askHash (bridgeInput value))).filter (designedKeep scalar tape input) = [] :=
    fun value => by
      show [(⟨.hash (bridgeInput value), publicAnswer tape.2 (.hash (bridgeInput value))⟩ :
        Entry FixedIndex EncPRF.PermutationIndex)].filter _ = []
      have notDesigned : designedHash input (bridgeInput value) = false := by
        rw [designedHash_bridgeInput, invalid]
      simp [designedKeep, designedRule, notDesigned, Entry.IsEnc]
  have padsNil : ∀ keys, (Hidden.transcriptOf (publicAnswer tape.2) (Programs.padsM keys)).filter
      (designedKeep scalar tape input) = [] := fun keys =>
    filter_nil_of_only (padsM_encOnly keys) _ _ (keep_enc scalar tape input)
  have pointNil : ∀ ℓ delta bitKey, laneIsCurve ℓ = false →
      (Hidden.transcriptOf (publicAnswer tape.2) (Programs.laneM ℓ delta bitKey)).filter
        (designedKeep scalar tape input) = [] := fun ℓ delta bitKey point =>
    filter_nil_of_only (laneM_laneOnly ℓ delta bitKey) _ _
      (keep_point scalar tape input invalid ℓ point)
  have gadgetNil : ∀ keys inputKey pads,
      (Hidden.transcriptOf (publicAnswer tape.2) (Programs.gadgetM keys inputKey pads)).filter
        (designedKeep scalar tape input) = [] := fun keys inputKey pads =>
    filter_nil_of_only (gadgetM_gadgetOnly keys inputKey pads) _ _
      (keep_gadget scalar tape input invalid)
  have pureNil : ∀ {β : Type} (value : β), (Hidden.transcriptOf (publicAnswer tape.2)
      (Pure.pure value : FreeQuery Programs.Spec β)).filter (designedKeep scalar tape input) = [] :=
    fun _ => rfl
  rw [hashNil, padsNil, pointNil .pointX _ _ rfl, pointNil .pointY _ _ rfl, gadgetNil, pureNil]
  simp only [List.nil_append, List.append_nil]
  rfl

/-! ### The hidden sites do not reach the designed entries -/

/-- A question at a hidden site: a hash limb of a hidden curve switch. -/
def AtH (input : AffineInput) : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .hash key => ∃ slot : LimbSite, ∃ label : Block, labelInput slot label = key ∧
      IsHidden input slot.1
  | _ => False

/-- Two transcripts with the same questions and the same answers off the hidden sites. -/
def OffHRel (input : AffineInput) (e e' : Entry FixedIndex EncPRF.PermutationIndex) : Prop :=
  e.1 = e'.1 ∧ (¬ AtH input e.1 → e = e')

theorem offHRel_refl (input : AffineInput) (e : Entry FixedIndex EncPRF.PermutationIndex) :
    OffHRel input e e :=
  ⟨rfl, fun _ => rfl⟩

theorem forall₂_refl_offH (input : AffineInput) :
    ∀ l : List (Entry FixedIndex EncPRF.PermutationIndex), List.Forall₂ (OffHRel input) l l
  | [] => List.Forall₂.nil
  | e :: l => List.Forall₂.cons (offHRel_refl input e) (forall₂_refl_offH input l)

/-- A hot-index question. -/
def HotQ : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward (.hot _ _ _ _ _) _ => True
  | _ => False

theorem garbleFoldM_hotOnly (lane : Lane) (chunk : Fin chunkCount) (delta : Block)
    (zeroLabel : Nat → Block) :
    ∀ steps, QueryOnly HotQ (Programs.garbleFoldM lane chunk delta zeroLabel steps)
  | 0 => QueryOnly.pure' _
  | steps + 1 => by
      refine QueryOnly.bind (garbleFoldM_hotOnly lane chunk delta zeroLabel steps) fun previous =>
        QueryOnly.bind ?_ fun _ => QueryOnly.pure' _
      unfold Programs.garbleStepM
      split
      · exact QueryOnly.pure' _
      · exact QueryOnly.bind (QueryOnly.vector _ fun _ =>
          QueryOnly.bind (hashM_ask _ _ trivial) fun _ => QueryOnly.bind (hashM_ask _ _ trivial)
            fun _ => QueryOnly.pure' _) fun _ => QueryOnly.pure' _

/-- **One lane on two oracles with the same fixed-key oracle whose hash agrees at every scale
input of a non-hidden site of the lane, under its garbler label.** -/
theorem sim_laneM_offH (input : AffineInput) (O O' : Oracle) (fixed : O'.1 = O.1) (lane : Lane)
    (delta : Block) (bitKey : Fin PlanB.coordinateBits → Block × Block)
    (agree : ∀ (c : Fin chunkCount) (j : Fin (2 ^ chunkWidth c)) (limb : Fin (limbCount lane)),
      ¬ IsHidden input ⟨lane, c, j⟩ →
        O'.2.2 (scaleInput lane c j.val limb.val ((garbleChunk O.1 lane delta bitKey c).1 j)) =
          O.2.2 (scaleInput lane c j.val limb.val ((garbleChunk O.1 lane delta bitKey c).1 j))) :
    Sim (publicAnswer O) (publicAnswer O') (OffHRel input) (fun _ _ => True)
      (Programs.laneM lane delta bitKey) (Programs.laneM lane delta bitKey) := by
  have hotAgree : ∀ request, HotQ request → publicAnswer O' request = publicAnswer O request := by
    intro request hot
    cases request with
    | fixedForward index x =>
        cases index with
        | hot ℓ c f e h =>
            show O'.1.permutation _ x = O.1.permutation _ x
            rw [fixed]
        | _ => exact hot.elim
    | _ => exact hot.elim
  unfold Programs.laneM
  refine Sim.bind (R := fun _ _ => True) ?_ fun _ _ _ => Sim.pure' trivial
  refine Sim.mono (Sim.pi chunkCount (R := fun _ _ _ => True) _ _ fun c => ?_) fun _ _ _ => trivial
  unfold Programs.chunkTablesM
  have chunkSame := (QueryOnly.bind (garbleFoldM_hotOnly lane c delta
    (labelAt fun position => (chunkKey bitKey c position).1) (chunkWidth c)) fun folded =>
      QueryOnly.pure' (S := HotQ) (folded.1, Vector.ofFn fun slot : Fin (chunkWidth c - 1) =>
        folded.2 (slot.val + 1))).agree O O' hotAgree
  refine Sim.bind (R := fun chunk chunk' => chunk = garbleChunk O.1 lane delta bitKey c ∧
    chunk' = chunk) ⟨?_, ?_, ?_⟩ fun chunk chunk' same => ?_
  · show List.Forall₂ _ (Hidden.transcriptOf _ (Programs.garbleChunkM lane delta bitKey c))
      (Hidden.transcriptOf _ (Programs.garbleChunkM lane delta bitKey c))
    have := chunkSame.1
    unfold Programs.garbleChunkM
    rw [this]
    exact forall₂_refl_offH input _
  · exact Programs.eval_garbleChunkM O lane delta bitKey c
  · unfold Programs.garbleChunkM
    exact chunkSame.2
  · obtain ⟨rfl, rfl⟩ := same
    refine Sim.bind (R := fun _ _ => True) (Sim.mono (Sim.vector _ (R := fun _ _ _ => True) _ _
      fun switch => ?_) fun _ _ _ => trivial) fun _ _ _ => Sim.pure' trivial
    unfold Programs.switchMaskM
    refine Sim.bind (R := fun _ _ => True) (Sim.mono (Sim.vector _ (R := fun _ _ _ => True) _ _
      fun limb => ?_) fun _ _ _ => trivial) fun _ _ _ => Sim.pure' trivial
    unfold Programs.askHash
    refine Sim.ask _ _ (fun _ _ => True) ⟨rfl, fun notH => ?_⟩ trivial
    have notHidden : ¬ IsHidden input ⟨lane, c, switch⟩ :=
      fun hidden => notH ⟨⟨⟨lane, c, switch⟩, limb⟩, _, rfl, hidden⟩
    have same : publicAnswer O' (PublicQuery.hash (FixedIndex := FixedIndex)
        (EncIndex := EncPRF.PermutationIndex)
          (scaleInput lane c switch.val limb.val ((garbleChunk O.1 lane delta bitKey c).1 switch)))
              =
        publicAnswer O (.hash
          (scaleInput lane c switch.val limb.val ((garbleChunk O.1 lane delta bitKey c).1
              switch))) := by
      simp only [publicAnswer]
      exact agree c switch limb notHidden
    rw [same]

/-- Two related transcripts keep the same entries under a filter that never keeps a hidden-site
entry and reads only the question. -/
theorem filter_offH (input : AffineInput) (keep : Entry FixedIndex EncPRF.PermutationIndex → Bool)
    (reads : ∀ e e' : Entry FixedIndex EncPRF.PermutationIndex, e.1 = e'.1 → keep e = keep e')
    (never : ∀ e, keep e = true → ¬ AtH input e.1) :
    ∀ {l l' : List (Entry FixedIndex EncPRF.PermutationIndex)}, List.Forall₂ (OffHRel input) l l' →
      l.filter keep = l'.filter keep
  | [], [], List.Forall₂.nil => rfl
  | e :: l, e' :: l', List.Forall₂.cons head rest => by
      rw [List.filter_cons, List.filter_cons, filter_offH input keep reads never rest,
        ← reads e e' head.1]
      by_cases k : keep e = true
      · rw [if_pos k, if_pos k, head.2 (never e k)]
      · rw [if_neg k, if_neg k]

theorem designedKeep_reads (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (e e' : Entry FixedIndex EncPRF.PermutationIndex) (same : e.1 = e'.1) :
    designedKeep scalar tape input e = designedKeep scalar tape input e' := by
  obtain ⟨q, a⟩ := e
  obtain ⟨q', a'⟩ := e'
  simp only at same
  subst same
  cases q <;> rfl

theorem designedKeep_never (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (e : Entry FixedIndex EncPRF.PermutationIndex) (keep : designedKeep scalar tape input e = true) :
    ¬ AtH input e.1 := by
  obtain ⟨request, answer⟩ := e
  cases request with
  | hash key =>
      rintro ⟨slot, label, rfl, hidden⟩
      have designed : designedHash input (labelInput slot label) = true := by
        simpa [designedKeep, designedRule, Entry.IsEnc] using keep
      rw [designedHash_labelInput] at designed
      simp only [designedSite, Bool.and_eq_true, decide_eq_true_eq] at designed
      exact designed.1 (Fin.ext hidden.2)
  | _ => exact id

/-- **The designed part of the curve lanes ignores the hidden sites, the bridge coins and the hash
off the curve lanes' non-hidden limbs.** -/
theorem curveDesigned_congr (scalar : NonZeroScalar) (tape tape' : Coins × Oracle)
    (input : AffineInput) (delta : tape'.1.inputDelta = tape.1.inputDelta)
    (key : tape'.1.inputMacKey = tape.1.inputMacKey)
    (fixed : tape'.2.1 = tape.2.1)
    (agree : ∀ slot : LimbSite, laneIsCurve slot.1.lane = true → ¬ IsHidden input slot.1 →
      tape'.2.2.2 (labelInput slot (garblerLabelOf tape slot.1)) =
        tape.2.2.2 (labelInput slot (garblerLabelOf tape slot.1))) :
    curveDesigned scalar tape' input = curveDesigned scalar tape input := by
  have rule : ∀ (ℓ : Lane) (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block),
      (Hidden.transcriptOf (publicAnswer tape'.2) (Programs.laneM ℓ delta bitKey)).filter
          (designedKeep scalar tape' input) =
        (Hidden.transcriptOf (publicAnswer tape'.2) (Programs.laneM ℓ delta bitKey)).filter
          (designedKeep scalar tape input) := by
    intro ℓ delta bitKey
    refine List.filter_congr fun e member => ?_
    have lane := (laneM_laneOnly ℓ delta bitKey).mem _ e member
    obtain ⟨request, answer⟩ := e
    cases request with
    | fixedForward index x =>
        cases index with
        | gadget o κ position => simp [LaneQ, indexLane] at lane
        | _ => rfl
    | hash key => rfl
    | _ => exact lane.elim
  unfold curveDesigned
  rw [delta, key, rule, rule]
  have laneX := (sim_laneM_offH input tape.2 tape'.2 fixed .curveX (tape.1.inputDelta .x)
    (Pipeline.bitKeyOf tape.1.inputMacKey .x)
    fun c j limb notHidden => agree ⟨⟨.curveX, c, j⟩, limb⟩ rfl notHidden).1
  have laneY := (sim_laneM_offH input tape.2 tape'.2 fixed .curveY (tape.1.inputDelta .y)
    (Pipeline.bitKeyOf tape.1.inputMacKey .y)
    fun c j limb notHidden => agree ⟨⟨.curveY, c, j⟩, limb⟩ rfl notHidden).1
  rw [filter_offH input _ (designedKeep_reads scalar tape input) (designedKeep_never scalar tape
      input)
      laneX,
    filter_offH input _ (designedKeep_reads scalar tape input) (designedKeep_never scalar tape
        input)
      laneY]

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
