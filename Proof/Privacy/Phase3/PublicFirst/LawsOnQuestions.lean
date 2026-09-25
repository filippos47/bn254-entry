/-
**Phase 3, P1p — the evaluator's questions before the gadget and at the gadget.**
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnUpper

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion public_step)
open Kriterion.ArgoMAC.Phase3.Lazy (LState AllQ)
open scoped ENNReal

noncomputable section

/-! ### 4. The evaluator's questions: before the gadget, and the gadget -/

section Questions

variable [FieldCertificate] [GroupCertificate]

/-- **The evaluator before its gadget**: the prefix, the pads and system B. -/
def preM (table : Public) (bits : BitInput) (mac : InputMac) :
    Programs.M ((EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) ×
      (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) :=
  curvePrefixM table bits mac >>= fun hashed =>
    Programs.evalPadsM ⟨hashed.1, hashed.2⟩ bits >>= fun pads =>
      Programs.evalLaneM .pointX table.pointXHot
          (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
          (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)
        >>= fun pointX =>
      Programs.evalLaneM .pointY table.pointYHot
          (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
          (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
        >>= fun pointY => pure (pads, pointX, pointY)

/-- **The evaluator's gadget**, after `preM`. -/
def gadgetPart (table : Public) (bits : BitInput) (mac : InputMac)
    (r : (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) ×
      (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) :
    Programs.M (Option (Option Point)) :=
  Programs.masksM bits.toAffine (Programs.transformMacOf r.1 mac) >>= fun masks =>
  pure (some (Garbling.decodeResult
    { point := bits.toAffine
      pointMacs := FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable table)
        (Pipeline.digitValues r.2.1 r.2.2) bits.toAffine
      exceptionDigits := Programs.unlockDigits (Pipeline.pointTable table) bits.toAffine masks false
      tripleDigits := Programs.unlockDigits (Pipeline.pointTable table) bits.toAffine masks true }))

open Kriterion.ArgoMAC.Phase3.Lazy (fq_bind_assoc fq_pure_bind) in
theorem onCurveM_split (table : Public) (bits : BitInput) (mac : InputMac) :
    Programs.onCurveM table bits mac = preM table bits mac >>= gadgetPart table bits mac := by
  have tail : Programs.onCurveM table bits mac =
      (curvePrefixM table bits mac >>= fun hashed =>
        Programs.evalPadsM ⟨hashed.1, hashed.2⟩ bits >>= fun pads =>
          Programs.evalLaneM .pointX table.pointXHot
              (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
              (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)
            >>= fun pointX =>
          Programs.evalLaneM .pointY table.pointYHot
              (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
              (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
            >>= fun pointY => gadgetPart table bits mac (pads, pointX, pointY)) := by
    unfold curvePrefixM
    simp only [fq_bind_assoc]
    rfl
  rw [tail]
  unfold preM
  simp only [fq_bind_assoc, fq_pure_bind]

/-- A question at no gadget index. -/
def NotGadget (q : PublicQuery FixedIndex EncPRF.PermutationIndex) : Prop :=
  ∀ (o : Fin digitCount) (κ : Coord) (p : Fin PlanB.coordinateBits) (bit : Bool) (x : Block),
    q ≠ .fixedForward (.gadget o κ p bit) x

theorem notGadget_laneAt (lane : Lane) (c : Fin chunkCount)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (inside : Kriterion.ArgoMAC.Phase3.Lazy.LaneAt lane c q) : NotGadget q := by
  intro o κ p bit x same
  subst same
  rcases inside with fixed | hash
  · exact fixed
  · exact hash

/-- A lane of the evaluator asks only questions of its own chunks. -/
theorem evalLaneM_laneAt (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    AllQ (fun r => ∃ c, Kriterion.ArgoMAC.Phase3.Lazy.LaneAt lane c r)
      (Programs.evalLaneM lane joins scale bits labels) :=
  (Kriterion.ArgoMAC.Phase3.Lazy.AllQ.vector fun c =>
    (Kriterion.ArgoMAC.Phase3.Lazy.evalChunkM_allQ lane joins scale bits labels c).mono
      fun _ inside => ⟨c, inside⟩).bind fun _ => .pure _

theorem notGadget_laneM (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    Hidden.QueryOnly NotGadget (Programs.evalLaneM lane joins scale bits labels) :=
  queryOnly_of_allQ ((evalLaneM_laneAt lane joins scale bits labels).mono
    fun r ⟨c, inside⟩ => notGadget_laneAt lane c r inside)

theorem notGadget_prefix (table : Public) (bits : BitInput) (mac : InputMac) :
    Hidden.QueryOnly NotGadget (curvePrefixM table bits mac) := by
  unfold curvePrefixM
  exact Hidden.QueryOnly.bind (notGadget_laneM _ _ _ _ _) fun _ =>
    Hidden.QueryOnly.bind (notGadget_laneM _ _ _ _ _) fun _ =>
      Hidden.QueryOnly.ask _ fun o κ p bit x same => by cases same

theorem notGadget_preM (table : Public) (bits : BitInput) (mac : InputMac) :
    Hidden.QueryOnly NotGadget (preM table bits mac) := by
  unfold preM
  refine Hidden.QueryOnly.bind (notGadget_prefix _ _ _) fun hashed =>
    Hidden.QueryOnly.bind (queryOnly_mono (Guess.evalPadsM_encOnly _ _) ?_) fun _ =>
      Hidden.QueryOnly.bind (notGadget_laneM _ _ _ _ _) fun _ =>
        Hidden.QueryOnly.bind (notGadget_laneM _ _ _ _ _) fun _ => Hidden.QueryOnly.pure' _
  rintro q ⟨c, i, b, rfl⟩ o κ p bit x same
  cases same

/-- The pads ask each pad question at the first whitening key. -/
theorem padsM_form (keys : WhiteningKeys) :
    Hidden.QueryOnly (fun q => ∃ (c : EncPRF.Coordinate) (i : Fin coordinateBitCount) (b : Bool),
      q = .encForward (c, i) (encodeBit b ^^^ keys.first)) (Programs.padsM keys) := by
  have pad : ∀ c i b, Hidden.QueryOnly (fun q => ∃ (c : EncPRF.Coordinate)
      (i : Fin coordinateBitCount) (b : Bool), q = .encForward (c, i) (encodeBit b ^^^ keys.first))
      (Programs.padM keys c i b) := fun c i b =>
    Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ ⟨c, i, b, rfl⟩) fun _ => Hidden.QueryOnly.pure' _
  unfold Programs.padsM
  exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => Hidden.QueryOnly.bind (pad _ _ _)
      fun _ => Hidden.QueryOnly.bind (pad _ _ _) fun _ => Hidden.QueryOnly.pure' _) fun _ =>
    Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => Hidden.QueryOnly.bind (pad _ _ _)
      fun _ => Hidden.QueryOnly.bind (pad _ _ _) fun _ => Hidden.QueryOnly.pure' _) fun _ =>
      Hidden.QueryOnly.pure' _

theorem asks_truePadsM (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (keys : WhiteningKeys) (c : EncPRF.Coordinate) (i : Fin coordinateBitCount) :
    Asks ans (truePadsM keys) (.encForward (c, i) (encodeBit true ^^^ keys.first)) := by
  unfold truePadsM
  cases c
  · exact Asks.bind_left (Asks.vector _ i (Asks.bind_left (Asks.ask' _)))
  · exact Asks.bind_right (Asks.bind_left (Asks.vector _ i (Asks.bind_left (Asks.ask' _))))

theorem asks_evalPadsM_false (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (keys : WhiteningKeys) (bits : BitInput) (c : EncPRF.Coordinate) (i : Fin coordinateBitCount) :
    Asks ans (Programs.evalPadsM keys bits) (.encForward (c, i) (encodeBit false ^^^ keys.first)) := by
  unfold Programs.evalPadsM
  cases c
  · exact Asks.bind_left (Asks.vector _ i (Asks.bind_left (Asks.bind_left (Asks.ask' _))))
  · exact Asks.bind_right (Asks.bind_left (Asks.vector _ i (Asks.bind_left (Asks.bind_left
      (Asks.ask' _)))))

theorem asks_bind_cases {α β : Type}
    {ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer}
    {P : FreeQuery Programs.Spec α} {f : α → FreeQuery Programs.Spec β}
    {q : PublicQuery FixedIndex EncPRF.PermutationIndex} (asks : Asks ans (P >>= f) q) :
    Asks ans P q ∨ Asks ans (f (P.eval ans)) q := by
  unfold Asks at *
  rw [Hidden.transcriptOf_bind, List.map_append] at asks
  exact List.mem_append.mp asks

end Questions

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
