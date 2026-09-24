/-
**Phase 3, P1m — (B1) fold-label entropy on the opening.**

The four lanes as one family (`laneJoins`, `laneScale`, `laneWord`, `laneLabels`: system A at the
input's MAC labels, system B at the labels whitened by the opening's pads `wPadsOf`), and:

* `opening_laneSplit` — every lane runs inside `HW`'s opening `openingQueriesM` as one of its parts
  (`LaneSplit`): the questions before it (the lanes before it, the bridge hash, the pads) fix its
  labels, and nothing else asks its fold indices;
* **`opening_level_le`** — **fold-label entropy on the opening**: on the opening's refill run from
  the empty oracle, every label of level `2 ≤ s ≤ chunkWidth c` of every chunk of every lane (along
  the run's answers, `openLevel`) hits any point with mass `≤ 1/2^128`.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedProc

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM whitePadsM noRecord)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Tape Request AllQ EncAt IndexAt LaneAt runRefill
  queriesAlong queriesAlong_bind queriesAlong_pure evalLaneM_allQ whitePadsM_allQ padM_allQ)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The lanes as one family -/

section Family

variable [FieldCertificate] (table : Public) (bits : BitInput)

/-- The joins of a lane. -/
def laneJoins : Lane → Vector Block foldStepCount
  | .curveX => table.curveXHot
  | .curveY => table.curveYHot
  | .pointX => table.pointXHot
  | .pointY => table.pointYHot

/-- The scale readers of a lane. -/
def laneScale : (lane : Lane) → Fin chunkCount → Fin (laneCount lane) → BaseField
  | .curveX => fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk))
  | .curveY => fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk))
  | .pointX => fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk))
  | .pointY => fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk))

/-- The cleartext word of a lane. -/
def laneWord : Lane → BitVec coordinateBitCount
  | .curveX => Pipeline.coordBits bits .x
  | .curveY => Pipeline.coordBits bits .y
  | .pointX => Pipeline.coordBits bits .x
  | .pointY => Pipeline.coordBits bits .y

/-- The labels of a lane: the MAC labels (system A) or the labels whitened by `pads` (system B). -/
def laneLabels (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    Lane → Fin coordinateBitCount → Block
  | .curveX => Pipeline.macLabels mac .x
  | .curveY => Pipeline.macLabels mac .y
  | .pointX => Pipeline.macLabels (Programs.whitenMacOf pads mac) .x
  | .pointY => Pipeline.macLabels (Programs.whitenMacOf pads mac) .y

/-- **A level label of the opening**, along `ans`: the labels of system B are whitened by the
opening's pads along `ans`. -/
abbrev openLevel (mac : InputMac) (ans : (request : Request) → request.Answer) (lane : Lane)
    (c : Fin chunkCount) (s : ℕ) : Fin (2 ^ s) → Block :=
  laneFoldLevel ans lane (laneJoins table lane) (laneWord bits lane)
    (laneLabels mac (wPadsOf table bits mac ans) lane) c s

end Family

/-! ### Questions away from a lane -/

section Away

theorem awayFrom_of_encAt {lane : Lane} {q : Request} (inside : EncAt q) : AwayFrom lane q := by
  cases q with
  | fixedForward _ _ => exact inside.elim
  | _ => trivial

/-- Another lane's questions are away from a lane. -/
theorem awayFrom_of_lane [FieldCertificate] {lane lane' : Lane} (different : lane' ≠ lane)
    (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane') → BaseField) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (ans : (request : Request) → request.Answer)
    (q : Request)
    (member : q ∈ queriesAlong ans (Programs.evalLaneM lane' joins scale word labels)) :
    AwayFrom lane q := by
  obtain ⟨c, inside⟩ := mem_queriesAlong_allQ ans (evalLaneM_allQ lane' joins scale word labels) q
    member
  cases q with
  | fixedForward i _ =>
    rcases inside with fixed | hash
    · intro c' at'
      cases i with
      | hot l cc f e h => exact different (fixed.1.symm.trans at'.1)
      | gadget _ _ _ => exact at'.elim
    · exact hash.elim
  | _ => trivial

end Away

/-! ### The opening -/

section Opening

variable [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac)

theorem queriesAlong_opening (ans : (request : Request) → request.Answer) :
    queriesAlong ans (openingQueriesM table bits mac) =
      queriesAlong ans (curveXM table bits mac) ++ (queriesAlong ans (curveYM table bits mac) ++
        ([.hash (bridgeInput (tOf table bits mac ans))] ++
          (queriesAlong ans (whitePadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩) ++
            (queriesAlong ans (pointXM table bits
                (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) ++
              queriesAlong ans (pointYM table bits
                (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)))))) := by
  rw [openingQueriesM_eq]
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, queriesAlong_askHash,
    eval_askHash]

/-- **The opening's pads are read off the questions before system B.** -/
theorem wPadsOf_congr (ans ans' : (request : Request) → request.Answer)
    (agree : ∀ q ∈ queriesAlong ans (curveXM table bits mac) ++
      (queriesAlong ans (curveYM table bits mac) ++
        ([.hash (bridgeInput (tOf table bits mac ans))] ++
          queriesAlong ans (whitePadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩))),
      ans' q = ans q) :
    wPadsOf table bits mac ans' = wPadsOf table bits mac ans := by
  have xSame := (queriesAlong_congr ans ans' (curveXM table bits mac) fun q member =>
    agree q (List.mem_append_left _ member)).2
  have ySame := (queriesAlong_congr ans ans' (curveYM table bits mac) fun q member =>
    agree q (List.mem_append_right _ (List.mem_append_left _ member))).2
  have tSame : tOf table bits mac ans' = tOf table bits mac ans := by
    unfold tOf
    rw [xSame, ySame]
  have kSame : kOf table bits mac ans' = kOf table bits mac ans := by
    show ans' (.hash (bridgeInput (tOf table bits mac ans'))) = _
    rw [tSame]
    exact agree _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ List.mem_cons_self)))
  show FreeQuery.eval ans' (whitePadsM ⟨(kOf table bits mac ans').1,
      (kOf table bits mac ans').2⟩) = _
  rw [kSame]
  exact (queriesAlong_congr ans ans' _ fun q member => agree q (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _ member)))).2

/-- **Every lane runs inside the opening as one of its parts.** -/
theorem opening_laneSplit (lane : Lane) :
    LaneSplit (openingQueriesM table bits mac) lane (laneJoins table lane)
      (laneScale table lane) (laneWord bits lane)
      (fun ans => laneLabels mac (wPadsOf table bits mac ans) lane) := by
  intro ans
  have padsAway : ∀ q ∈ queriesAlong ans (whitePadsM ⟨(kOf table bits mac ans).1,
      (kOf table bits mac ans).2⟩), AwayFrom lane q := fun q member =>
    awayFrom_of_encAt (mem_queriesAlong_allQ ans (whitePadsM_allQ _) q member)
  have path := queriesAlong_opening table bits mac ans
  cases lane with
  | curveX =>
    refine ⟨[], queriesAlong ans (curveYM table bits mac) ++
      ([.hash (bridgeInput (tOf table bits mac ans))] ++
        (queriesAlong ans (whitePadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩) ++
          (queriesAlong ans (pointXM table bits
              (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) ++
            queriesAlong ans (pointYM table bits
              (Programs.whitenMacOf (wPadsOf table bits mac ans) mac))))), ?_, ?_, ?_, ?_⟩
    · show _ = [] ++ queriesAlong ans (curveXM table bits mac) ++ _
      rw [path, List.nil_append]
    · intro q member
      cases member
    · intro q member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with y | rfl | pads | x | y
      · exact awayFrom_of_lane (by decide) _ _ _ _ ans q y
      · trivial
      · exact padsAway q pads
      · exact awayFrom_of_lane (by decide) _ _ _ _ ans q x
      · exact awayFrom_of_lane (by decide) _ _ _ _ ans q y
    · intro ans' _
      show Pipeline.macLabels mac .x = Pipeline.macLabels mac .x
      rfl
  | curveY =>
    refine ⟨queriesAlong ans (curveXM table bits mac),
      [.hash (bridgeInput (tOf table bits mac ans))] ++
        (queriesAlong ans (whitePadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩) ++
          (queriesAlong ans (pointXM table bits
              (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) ++
            queriesAlong ans (pointYM table bits
              (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)))), ?_, ?_, ?_, ?_⟩
    · show _ = queriesAlong ans (curveXM table bits mac) ++
        queriesAlong ans (curveYM table bits mac) ++ _
      rw [path, List.append_assoc]
    · exact fun q member => awayFrom_of_lane (by decide) _ _ _ _ ans q member
    · intro q member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with rfl | pads | x | y
      · trivial
      · exact padsAway q pads
      · exact awayFrom_of_lane (by decide) _ _ _ _ ans q x
      · exact awayFrom_of_lane (by decide) _ _ _ _ ans q y
    · intro ans' _
      show Pipeline.macLabels mac .y = Pipeline.macLabels mac .y
      rfl
  | pointX =>
    refine ⟨queriesAlong ans (curveXM table bits mac) ++
      (queriesAlong ans (curveYM table bits mac) ++
        ([.hash (bridgeInput (tOf table bits mac ans))] ++
          queriesAlong ans (whitePadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩))),
      queriesAlong ans (pointYM table bits (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)),
      ?_, ?_, ?_, ?_⟩
    · show _ = _ ++ queriesAlong ans (pointXM table bits
          (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) ++ _
      rw [path]
      simp only [List.append_assoc]
    · intro q member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with x | y | rfl | pads
      · exact awayFrom_of_lane (by decide) _ _ _ _ ans q x
      · exact awayFrom_of_lane (by decide) _ _ _ _ ans q y
      · trivial
      · exact padsAway q pads
    · exact fun q member => awayFrom_of_lane (by decide) _ _ _ _ ans q member
    · intro ans' agree
      show Pipeline.macLabels (Programs.whitenMacOf (wPadsOf table bits mac ans') mac) .x = _
      rw [wPadsOf_congr table bits mac ans ans' agree]
      rfl
  | pointY =>
    refine ⟨queriesAlong ans (curveXM table bits mac) ++
      (queriesAlong ans (curveYM table bits mac) ++
        ([.hash (bridgeInput (tOf table bits mac ans))] ++
          (queriesAlong ans (whitePadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩) ++
            queriesAlong ans (pointXM table bits
              (Programs.whitenMacOf (wPadsOf table bits mac ans) mac))))), [], ?_, ?_, ?_, ?_⟩
    · show _ = _ ++ queriesAlong ans (pointYM table bits
          (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) ++ []
      rw [path]
      simp only [List.append_assoc, List.append_nil]
    · intro q member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with x | y | rfl | pads | x'
      · exact awayFrom_of_lane (by decide) _ _ _ _ ans q x
      · exact awayFrom_of_lane (by decide) _ _ _ _ ans q y
      · trivial
      · exact padsAway q pads
      · exact awayFrom_of_lane (by decide) _ _ _ _ ans q x'
    · intro q member
      cases member
    · intro ans' agree
      have agree' : ∀ q ∈ queriesAlong ans (curveXM table bits mac) ++
          (queriesAlong ans (curveYM table bits mac) ++
            ([.hash (bridgeInput (tOf table bits mac ans))] ++
              queriesAlong ans (whitePadsM ⟨(kOf table bits mac ans).1,
                (kOf table bits mac ans).2⟩))), ans' q = ans q := by
        intro q member
        refine agree q ?_
        simp only [List.mem_append] at member ⊢
        rcases member with x | y | h | pads
        · exact Or.inl x
        · exact Or.inr (Or.inl y)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl pads)))
      show Pipeline.macLabels (Programs.whitenMacOf (wPadsOf table bits mac ans') mac) .y = _
      rw [wPadsOf_congr table bits mac ans ans' agree']
      rfl

variable [GroupCertificate]

/-- **Fold-label entropy on the opening**: every label of level `2 ≤ t + 1 ≤ chunkWidth c` of every
lane, along the opening's answers, hits any point with mass `≤ 1/2^128`. -/
theorem opening_level_le (source : Stage1Source) (input : AffineInput) (tape : Tape) (lane : Lane)
    (c : Fin chunkCount) (t : ℕ) (one : 1 ≤ t) (small : t < chunkWidth c) (n : Fin (2 ^ (t + 1)))
    (L : Block) :
    ∑' ran, openingRun source input tape ran *
      optWeight (fun state => ind (openLevel source.publicValue (restoredBits source input)
        (restoredMac source input) (refillAns (restoredBits source input) state) lane c (t + 1) n =
          L)) ran ≤ delta := by
  unfold openingRun
  exact runRefill_level_le (restoredBits source input) tape _
    (openingQueriesM_forwardOnly _ _ _) (opening_fresh _ _ _) lane _ _ _ _
    (opening_laneSplit _ _ _ lane) c t one small n L

end Opening

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
