/-
**Phase 3, P1f — stage 1's bridge input, on the (rest, vectors) coordinates.**

The stage-1 view factors through `Φ tape = (restOf tape, maskOf tape)`: the published value is
`publishedOf` of it (`published_eq`: lane tables from the fold gates and the switch-mask vectors,
gadget from the gadget permutations) and the EncPRF entries are the pads' transcript, a function of
the rest (`encEntries_eq`). Under the swapped tape `Φ` is uniform × uniform (`swapped_restMasks`,
from `MaskSwap.swappedTape_garblerMasks`): the rest is the coins, the fixed-key and EncPRF oracles
and the hash off the scale range, the vectors are every garbler switch-mask vector.
-/

import Proof.Privacy.Phase3.Hidden.StageOne
import Proof.Privacy.Phase3.Hidden.QueryOnly

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open scoped ENNReal

noncomputable section

/-- The oracle a rest determines: its fixed-key and EncPRF oracles, and its hash with the scale
range blank. -/
def restOracle (rest : RestTape TapeRest) : Oracle :=
  (rest.1.2.1, rest.1.2.2, hashOf rest.2 blankScale)

/-- The keys of the garbler's lanes are those of the rest of the tape. -/
theorem restKeys_restOf (tape : Coins × Oracle) : restKeys (restOf tape) = laneKeys tape := by
  unfold restKeys laneKeys restOf
  rw [garblerKeys_hashOf _ _ blankScale (scaleTableOf tape.2.2.2), hashOf_tables]

/-- The bridge input's hash is read off the rest of the table. -/
theorem hash_bridgeInput_blank (other : OtherTable) (scale : ScaleTable) (key : BaseField) :
    hashOf other blankScale (bridgeInput key) = hashOf other scale (bridgeInput key) := by
  rw [hashOf_bridgeInput, hashOf_bridgeInput]

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- **Under the swapped tape, the rest and the vectors are uniform and independent.** -/
theorem swapped_restMasks :
    swappedChallengeTape.map (fun tape => (restOf tape, maskOf tape)) =
      productPMF (restLaw restUniform) (PMF.uniformOfFintype MaskVectors) := by
  unfold swappedChallengeTape
  rw [PMF.map_comp]
  refine Eq.trans ?_ (swappedTape_garblerMasks restUniform (fun rest : TapeRest => rest.2.1)
    fun tape => garblerKeys tape.1 (hashOf tape.2 blankScale))
  refine congrArg (fun observe => PMF.map observe
    (swappedTape restUniform garblerLabels)) (funext fun tape => ?_)
  obtain ⟨rest, hash⟩ := tape
  show ((rest, otherTableOf hash), garblerMask rest.2.1 hash (garblerKeys rest hash).1
      (garblerKeys rest hash).2) = _
  have keys : garblerKeys rest hash = garblerKeys rest (hashOf (otherTableOf hash) blankScale) := by
    conv_lhs => rw [← hashOf_tables hash]
    exact garblerKeys_hashOf rest _ _ _
  rw [keys]

/-! ### The EncPRF entries are the pads' transcript -/

theorem isEnc_of_plain (entry : Entry FixedIndex EncPRF.PermutationIndex)
    (plain : IsPlain entry.1) : entry.IsEnc = false := by
  obtain ⟨request, answer⟩ := entry
  cases request <;> first | rfl | exact plain.elim

theorem isEnc_of_encForward (entry : Entry FixedIndex EncPRF.PermutationIndex)
    (enc : IsEncForward entry.1) : entry.IsEnc = true := by
  obtain ⟨request, answer⟩ := entry
  cases request <;> first | rfl | exact enc.elim

/-- The pads' transcript on the rest's oracle. -/
def encOf (rest : RestTape TapeRest) : List (Entry FixedIndex EncPRF.PermutationIndex) :=
  Hidden.transcriptOf (publicAnswer (restOracle rest))
    (Programs.padsM ⟨(hashOf rest.2 blankScale (bridgeInput rest.1.1.bridgeKey)).1,
      (hashOf rest.2 blankScale (bridgeInput rest.1.1.bridgeKey)).2⟩)

theorem filter_all {α : Type} (P : α → Bool) (l : List α) (all : ∀ a ∈ l, P a = true) :
    l.filter P = l := List.filter_eq_self.mpr all

theorem filter_none {α : Type} (P : α → Bool) (l : List α) (none' : ∀ a ∈ l, P a = false) :
    l.filter P = [] := List.filter_eq_nil_iff.mpr fun a member => by simp [none' a member]

/-- The EncPRF part of a hash-then-pads-then-plain program is the pads' transcript. -/
theorem enc_split {β : Type} (t : BaseField) (O : Oracle)
    (R : Block × Block → Programs.Pads → FreeQuery Programs.Spec β)
    (only : ∀ h p, QueryOnly IsPlain (R h p)) :
    (Hidden.transcriptOf (publicAnswer O) (Programs.askHash t >>= fun h =>
        Programs.padsM ⟨h.1, h.2⟩ >>= fun p => R h p)).filter Entry.IsEnc =
      Hidden.transcriptOf (publicAnswer O) (Programs.padsM ⟨(O.2.2 t).1, (O.2.2 t).2⟩) := by
  rw [transcriptOf_bind, transcriptOf_bind]
  have hashHead : Hidden.transcriptOf (publicAnswer O) (Programs.askHash t) =
      [⟨.hash t, publicAnswer O (.hash t)⟩] := rfl
  have keys : FreeQuery.eval (publicAnswer O) (Programs.askHash t) = O.2.2 t := rfl
  rw [hashHead, keys, List.filter_append, List.filter_append,
    filter_none _ [_] (fun a member => by rcases List.mem_singleton.mp member with rfl; rfl),
    filter_all _ _ fun a member => isEnc_of_encForward a ((padsM_encOnly _).mem _ a member),
    filter_none _ _ fun a member => isEnc_of_plain a ((only _ _).mem _ a member),
    List.nil_append, List.append_nil]

/-- **The EncPRF entries are a function of the rest.** -/
theorem encEntries_eq (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    encEntries scalar tape = encOf (restOf tape) := by
  unfold encEntries
  rw [garblerTranscript_eq]
  unfold Programs.garbleM
  refine (enc_split (bridgeInput tape.1.bridgeKey) tape.2 _ fun _ _ => ?_).trans ?_
  · exact QueryOnly.bind (laneM_plainOnly _ _ _) fun _ => QueryOnly.bind (laneM_plainOnly _ _ _)
      fun _ => QueryOnly.bind (laneM_plainOnly _ _ _) fun _ =>
        QueryOnly.bind (laneM_plainOnly _ _ _) fun _ =>
          QueryOnly.bind (gadgetM_plainOnly _ _ _) fun _ => QueryOnly.pure' _
  · have keys : hashOf (restOf tape).2 blankScale (bridgeInput (restOf tape).1.1.bridgeKey) =
        tape.2.2.2 (bridgeInput tape.1.bridgeKey) := by
      show hashOf (otherTableOf tape.2.2.2) blankScale (bridgeInput tape.1.bridgeKey) = _
      rw [hash_bridgeInput_blank _ (scaleTableOf tape.2.2.2), hashOf_tables]
    unfold encOf
    rw [keys]
    have same : ∀ request : PublicQuery FixedIndex EncPRF.PermutationIndex, IsEncForward request →
        publicAnswer (restOracle (restOf tape)) request = publicAnswer tape.2 request := by
      intro request enc
      cases request with
      | encForward index input => rfl
      | _ => exact enc.elim
    have agreed := (padsM_encOnly ⟨(tape.2.2.2 (bridgeInput tape.1.bridgeKey)).1,
      (tape.2.2.2 (bridgeInput tape.1.bridgeKey)).2⟩).agree tape.2 (restOracle (restOf tape)) same
    exact agreed.1.symm

/-! ### The published value is a function of the rest and the vectors -/

/-- One lane's tables from the rest and the vectors. -/
def tablesOf (rest : RestTape TapeRest) (masks : MaskVectors) (ℓ : Lane) :
    Programs.LaneTables (laneCount ℓ) where
  hot c := garbleChunk rest.1.2.1 ℓ ((restKeys rest).1 ℓ) ((restKeys rest).2 ℓ) c
  masks c switch := masks ⟨ℓ, c, switch⟩

/-- **The published value, from the rest and the vectors.** -/
def publishedOf (scalar : NonZeroScalar) (z : RestTape TapeRest × MaskVectors) : Public :=
  Programs.assemble (FieldMacToECMac.outputKeys construction scalar.value z.1.1.1.offsets)
    z.1.1.1.pointRandomness z.1.1.1.bridgeKey z.1.1.1.curveMask
    (tablesOf z.1 z.2 .curveX) (tablesOf z.1 z.2 .curveY) (tablesOf z.1 z.2 .pointX)
    (tablesOf z.1 z.2 .pointY)
    (Vector.ofFn fun output => FieldMacToECMac.garbleEntry
      (Pipeline.gadgetPermutations z.1.1.2.1) output
      ((FieldMacToECMac.outputKeys construction scalar.value z.1.1.1.offsets).get output)
      (EncPRF.transformKey z.1.1.2.2 (EncPRF.whiteningKeys (hashOf z.1.2 blankScale)
        z.1.1.1.bridgeKey) z.1.1.1.inputMacKey) (z.1.1.1.exceptionPad.get output))

theorem laneTables_eq (tape : Coins × Oracle) (lane : Lane) :
    Programs.laneTables tape.2.1 tape.2.2.2 lane ((laneKeys tape).1 lane) ((laneKeys tape).2 lane) =
      tablesOf (restOf tape) (maskOf tape) lane := by
  unfold Programs.laneTables tablesOf
  rw [restKeys_restOf]
  rfl

/-- **The published value is `publishedOf` of the rest and the vectors.** -/
theorem published_eq (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    (Scheme.scheme.garble parameter scalar tape).1 = publishedOf scalar (restOf tape, maskOf tape) := by
  obtain ⟨coins, oracle⟩ := tape
  rw [← garble_eval parameter scalar coins oracle, Programs.eval_garbleM, ← Programs.assemble_real]
  unfold publishedOf
  have cx : Programs.laneTables oracle.1 oracle.2.2 .curveX (coins.inputDelta .x)
      (Pipeline.bitKeyOf coins.inputMacKey .x) = tablesOf (restOf (coins, oracle))
        (maskOf (coins, oracle)) .curveX := laneTables_eq (coins, oracle) .curveX
  have cy : Programs.laneTables oracle.1 oracle.2.2 .curveY (coins.inputDelta .y)
      (Pipeline.bitKeyOf coins.inputMacKey .y) = tablesOf (restOf (coins, oracle))
        (maskOf (coins, oracle)) .curveY := laneTables_eq (coins, oracle) .curveY
  have px : Programs.laneTables oracle.1 oracle.2.2 .pointX (coins.inputDelta .x)
      (Pipeline.bitKeyOf (Pipeline.whitenedKey oracle.2.1 oracle.2.2 coins.bridgeKey
        coins.inputMacKey) .x) = tablesOf (restOf (coins, oracle)) (maskOf (coins, oracle))
            .pointX :=
    laneTables_eq (coins, oracle) .pointX
  have py : Programs.laneTables oracle.1 oracle.2.2 .pointY (coins.inputDelta .y)
      (Pipeline.bitKeyOf (Pipeline.whitenedKey oracle.2.1 oracle.2.2 coins.bridgeKey
        coins.inputMacKey) .y) = tablesOf (restOf (coins, oracle)) (maskOf (coins, oracle))
            .pointY :=
    laneTables_eq (coins, oracle) .pointY
  have white : EncPRF.whiteningKeys (hashOf (restOf (coins, oracle)).2 blankScale)
      (restOf (coins, oracle)).1.1.bridgeKey = EncPRF.whiteningKeys oracle.2.2 coins.bridgeKey := by
    unfold EncPRF.whiteningKeys
    show (⟨(hashOf (otherTableOf oracle.2.2) blankScale (bridgeInput coins.bridgeKey)).1,
      (hashOf (otherTableOf oracle.2.2) blankScale (bridgeInput coins.bridgeKey)).2⟩ :
        WhiteningKeys) = _
    rw [hash_bridgeInput_blank _ (scaleTableOf oracle.2.2), hashOf_tables]
  rw [← cx, ← cy, ← px, ← py, white]
  rfl

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
