/-
**Phase 3, P1f — the shape of the garbler's questions.**

`GarblerAsk scalar coins`: every question the garbler asks on coins `coins` is a hash question (the
bridge input or a switch-mask limb), an EncPRF forward query, or a fixed-key forward query at

* a fold gate of a paid step `1 ≤ n < b_c` of its chunk, at a parent `r < 2 ^ n` (step `0` is
  free; chunk `0` has one paid step, every other chunk three),
* a gadget position of a digit with an exceptional input (`digitEndomorphismBase ≠ none`).

`garblerTranscript_ask`: every garbler transcript entry has this shape.
-/

import Proof.Privacy.Phase3.Hidden.Views
import Proof.Privacy.Phase3.Hidden.QueryOnly

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden

noncomputable section

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- **The shape of a garbler question.** -/
def GarblerAsk (scalar : NonZeroScalar) (coins : Coins) :
    PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward (.hot _ chunk fold entry _) _ =>
      1 ≤ fold.val ∧ fold.val < chunkWidth chunk ∧ entry.val < 2 ^ fold.val
  | .fixedForward (.gadget o _ _) _ =>
      (digitEndomorphismBase (digitKey scalar coins.offsets o).digit).isSome = true
  | .encForward _ _ => True
  | .hash _ => True
  | _ => False

theorem garblerAsk_hot (scalar : NonZeroScalar) (coins : Coins) (lane : Lane)
    (chunk : Fin chunkCount) (n entry : Nat) (half : Bool) (x : Block) (one : 1 ≤ n)
    (small : n < chunkWidth chunk) (entrySmall : entry < 2 ^ n) :
    GarblerAsk scalar coins (.fixedForward (hotIndexNat lane chunk n entry half) x) := by
  obtain ⟨fold, e, foldEq, entryEq, same⟩ := hotIndexNat_of_lt lane chunk n entry half small
      entrySmall
  rw [same]
  exact ⟨foldEq ▸ one, foldEq ▸ small, foldEq ▸ entryEq ▸ entrySmall⟩

theorem garbleFoldM_ask (scalar : NonZeroScalar) (coins : Coins) (lane : Lane)
    (chunk : Fin chunkCount) (delta : Block) (zeroLabel : Nat → Block) :
    ∀ steps, steps ≤ chunkWidth chunk →
      QueryOnly (GarblerAsk scalar coins) (Programs.garbleFoldM lane chunk delta zeroLabel steps)
  | 0, _ => QueryOnly.pure' _
  | steps + 1, small => by
      refine QueryOnly.bind (garbleFoldM_ask scalar coins lane chunk delta zeroLabel steps
        (by omega)) fun previous => QueryOnly.bind ?_ fun _ => QueryOnly.pure' _
      unfold Programs.garbleStepM
      split
      · exact QueryOnly.pure' _
      · rename_i nonzero
        refine QueryOnly.bind (QueryOnly.vector _ fun entry => ?_) fun _ => QueryOnly.pure' _
        exact QueryOnly.bind (QueryOnly.bind (QueryOnly.ask _
            (garblerAsk_hot scalar coins lane chunk steps entry.val false _ (by omega) (by omega)
              entry.isLt)) fun _ => QueryOnly.pure' _)
          fun _ => QueryOnly.bind (QueryOnly.bind (QueryOnly.ask _
            (garblerAsk_hot scalar coins lane chunk steps entry.val true _ (by omega) (by omega)
              entry.isLt)) fun _ => QueryOnly.pure' _) fun _ => QueryOnly.pure' _

theorem hashM_ask {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop} (index : FixedIndex)
    (label : Block) (holds : S (.fixedForward index label)) : QueryOnly S (Programs.hashM index label) :=
  QueryOnly.bind (QueryOnly.ask _ holds) fun _ => QueryOnly.pure' _

theorem laneM_ask (scalar : NonZeroScalar) (coins : Coins) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block) :
    QueryOnly (GarblerAsk scalar coins) (Programs.laneM lane delta bitKey) := by
  refine QueryOnly.bind (QueryOnly.pi _ fun c => ?_) fun _ => QueryOnly.pure' _
  refine QueryOnly.bind (QueryOnly.bind (garbleFoldM_ask scalar coins _ _ _ _ _ le_rfl)
    fun _ => QueryOnly.pure' _) fun _ => ?_
  refine QueryOnly.bind (QueryOnly.vector _ fun switch => ?_) fun _ => QueryOnly.pure' _
  exact QueryOnly.bind (QueryOnly.vector _ fun _ => QueryOnly.ask _ trivial) fun _ =>
    QueryOnly.pure' _

theorem gadgetM_ask (scalar : NonZeroScalar) (coins : Coins) (inputKey : InputMacKey)
    (pads : FieldMacToECMac.ExceptionPad) :
    QueryOnly (GarblerAsk scalar coins)
      (Programs.gadgetM (FieldMacToECMac.outputKeys construction scalar.value coins.offsets) inputKey pads) := by
  refine QueryOnly.vector _ fun output => ?_
  unfold Programs.garbleEntryM
  split
  · exact QueryOnly.pure' _
  · rename_i phi found
    have digit : (digitEndomorphismBase (digitKey scalar coins.offsets output).digit).isSome = true := by
      show (digitEndomorphismBase ((FieldMacToECMac.outputKeys construction scalar.value
        coins.offsets).get output).digit).isSome = true
      rw [found]
      rfl
    have digest : ∀ coordinate mac, QueryOnly (GarblerAsk scalar coins)
        (Programs.gadgetDigestM output coordinate mac) := fun coordinate mac =>
      QueryOnly.bind (QueryOnly.vector _ fun index => hashM_ask _ _ digit) fun _ => QueryOnly.pure' _
    exact QueryOnly.bind (QueryOnly.bind (digest _ _) fun _ => QueryOnly.bind (digest _ _) fun _ =>
      QueryOnly.pure' _) fun _ => QueryOnly.pure' _

/-- **The garbler asks only questions of the garbler's shape.** -/
theorem garbleM_ask (scalar : NonZeroScalar) (coins : Coins) :
    QueryOnly (GarblerAsk scalar coins) (Programs.garbleM scalar coins) := by
  unfold Programs.garbleM
  refine QueryOnly.bind (QueryOnly.ask _ trivial) fun hashed => ?_
  refine QueryOnly.bind ((padsM_encOnly _).imp fun q enc => ?_) fun pads => ?_
  · cases q with
    | encForward _ _ => trivial
    | _ => exact enc.elim
  refine QueryOnly.bind (laneM_ask scalar coins .curveX _ _) fun _ => ?_
  refine QueryOnly.bind (laneM_ask scalar coins .curveY _ _) fun _ => ?_
  refine QueryOnly.bind (laneM_ask scalar coins .pointX _ _) fun _ => ?_
  refine QueryOnly.bind (laneM_ask scalar coins .pointY _ _) fun _ => ?_
  exact QueryOnly.bind (gadgetM_ask scalar coins _ _) fun _ => QueryOnly.pure' _

/-- **Every garbler entry has the garbler's shape.** -/
theorem garblerTranscript_ask (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    ∀ entry ∈ garblerTranscript scalar tape, GarblerAsk scalar tape.1 entry.1 := by
  rw [garblerTranscript_eq]
  exact (garbleM_ask scalar tape.1).mem _

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
