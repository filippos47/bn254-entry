/-
**Phase 3, P1f — programs that ask only one kind of question.**

`QueryOnly S P`: every question `P` asks, on every path, satisfies `S`. Closed under `pure`, `bind`,
`FreeQuery.vector` and `FreeQuery.pi`. Its transcript entries satisfy `S` (`QueryOnly.mem`), and two
oracles agreeing on `S` run it identically (`QueryOnly.agree`). The garbler's lanes (fold gates and
switch-mask hash limbs) and gadget ask only plain -- fixed-key forward or hash -- questions, its
pads only EncPRF questions (`laneM_plainOnly`, `gadgetM_plainOnly`, `padsM_encOnly`).
-/

import Proof.Privacy.Phase3.Hidden.TapeShift

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)

noncomputable section

/-- Every question of every path satisfies `S`. -/
inductive QueryOnly (S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop) {α : Type} :
    FreeQuery Programs.Spec α → Prop
  | pure (value : α) : QueryOnly S (.pure value)
  | query (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (next : request.Answer → FreeQuery Programs.Spec α)
      (holds : S request) (rest : ∀ answer, QueryOnly S (next answer)) : QueryOnly S (.query request next)

namespace QueryOnly

variable {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop} {α β : Type}

theorem pure' (value : α) : QueryOnly S (Pure.pure value : FreeQuery Programs.Spec α) := .pure value

theorem bind {P : FreeQuery Programs.Spec α} {f : α → FreeQuery Programs.Spec β}
    (first : QueryOnly S P) (rest : ∀ a, QueryOnly S (f a)) : QueryOnly S (P >>= f) := by
  induction first with
  | pure value => exact rest value
  | query request next holds _ ih => exact .query request _ holds ih

theorem ask (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (holds : S request) :
    QueryOnly S (FreeQuery.ask (spec := Programs.Spec) request) :=
  .query request _ holds fun answer => .pure answer

theorem vector : ∀ (count : Nat) {P : Fin count → FreeQuery Programs.Spec α},
    (∀ index, QueryOnly S (P index)) → QueryOnly S (FreeQuery.vector count P)
  | 0, _, _ => pure' _
  | count + 1, _, each => bind (vector count fun index => each index.castSucc) fun _ =>
      bind (each (Fin.last count)) fun _ => pure' _

theorem pi : ∀ (count : Nat) {γ : Fin count → Type} {P : (index : Fin count) → FreeQuery Programs.Spec (γ index)},
    (∀ index, QueryOnly S (P index)) → QueryOnly S (FreeQuery.pi count P)
  | 0, _, _, _ => pure' _
  | count + 1, _, _, each => bind (each 0) fun _ =>
      bind (pi count fun index => each index.succ) fun _ => pure' _

/-- Every transcript entry's question satisfies `S`. -/
theorem mem {P : FreeQuery Programs.Spec α} (only : QueryOnly S P)
    (answer : ∀ query : PublicQuery FixedIndex EncPRF.PermutationIndex, query.Answer) :
    ∀ entry ∈ transcriptOf answer P, S entry.1 := by
  induction only with
  | pure value => intro entry member; cases member
  | query request next holds _ ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact holds
      · exact ih _ entry member

/-- A weaker predicate. -/
theorem imp {S' : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop} {P : FreeQuery
    Programs.Spec α}
    (only : QueryOnly S P) (weaker : ∀ q, S q → S' q) : QueryOnly S' P := by
  induction only with
  | pure value => exact .pure value
  | query request next holds _ ih => exact .query request next (weaker _ holds) ih

/-- Two oracles agreeing on `S` run the program identically. -/
theorem agree {P : FreeQuery Programs.Spec α} (only : QueryOnly S P) (first second : Oracle)
    (same : ∀ request, S request → publicAnswer second request = publicAnswer first request) :
    transcriptOf (publicAnswer second) P = transcriptOf (publicAnswer first) P ∧
      P.eval (publicAnswer second) = P.eval (publicAnswer first) :=
  transcriptOf_of_agrees P first second fun entry member => by
    rw [same entry.1 (only.mem _ entry member)]
    exact (transcriptOf_agrees first P entry member)

end QueryOnly

/-- A plain question: a fixed-key forward question or a hash question. -/
def IsPlain : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward _ _ => True
  | .hash _ => True
  | _ => False

/-- An EncPRF forward question. -/
def IsEncForward : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .encForward _ _ => True
  | _ => False

theorem hashM_plainOnly (index : FixedIndex) (label : Block) :
    QueryOnly IsPlain (Programs.hashM index label) :=
  QueryOnly.bind (QueryOnly.ask _ trivial) fun _ => QueryOnly.pure' _

theorem garbleFoldM_plainOnly (lane : Lane) (chunk : Fin chunkCount) (delta : Block)
    (zeroLabel : Nat → Block) : ∀ steps,
    QueryOnly IsPlain (Programs.garbleFoldM lane chunk delta zeroLabel steps)
  | 0 => QueryOnly.pure' _
  | steps + 1 => by
      refine QueryOnly.bind (garbleFoldM_plainOnly lane chunk delta zeroLabel steps) fun previous =>
        QueryOnly.bind ?_ fun _ => QueryOnly.pure' _
      unfold Programs.garbleStepM
      split
      · exact QueryOnly.pure' _
      · exact QueryOnly.bind (QueryOnly.vector _ fun _ =>
          QueryOnly.bind (hashM_plainOnly _ _) fun _ => QueryOnly.bind (hashM_plainOnly _ _) fun _
              =>
            QueryOnly.pure' _) fun _ => QueryOnly.pure' _

theorem switchMaskM_plainOnly (lane : Lane) (chunk : Fin chunkCount) (switch : Nat) (label :
    Block) :
    QueryOnly IsPlain (Programs.switchMaskM lane chunk switch label) :=
  QueryOnly.bind (QueryOnly.vector _ fun _ => QueryOnly.ask _ trivial) fun _ => QueryOnly.pure' _

/-- A lane's switch mask asks only that switch's limbs at its label. -/
theorem switchMaskM_only (lane : Lane) (chunk : Fin chunkCount) (switch : Nat) (label : Block) :
    QueryOnly (fun q => ∃ limb : Fin (limbCount lane),
        q = .hash (scaleInput lane chunk switch limb.val label))
      (Programs.switchMaskM lane chunk switch label) :=
  QueryOnly.bind (QueryOnly.vector _ fun limb => QueryOnly.ask _ ⟨limb, rfl⟩)
    fun _ => QueryOnly.pure' _

theorem laneM_plainOnly (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block) :
    QueryOnly IsPlain (Programs.laneM lane delta bitKey) :=
  QueryOnly.bind (QueryOnly.pi _ fun _ =>
    QueryOnly.bind (QueryOnly.bind (garbleFoldM_plainOnly _ _ _ _ _) fun _ => QueryOnly.pure' _)
      fun _ => QueryOnly.bind (QueryOnly.vector _ fun _ => switchMaskM_plainOnly _ _ _ _)
        fun _ => QueryOnly.pure' _) fun _ => QueryOnly.pure' _

theorem gadgetM_plainOnly [FieldCertificate] [GroupCertificate] (keys : FieldMacToECMac.OutputKeys)
    (inputKey : InputMacKey) (pads : FieldMacToECMac.ExceptionPad) :
    QueryOnly IsPlain (Programs.gadgetM keys inputKey pads) := by
  have digest : ∀ output coordinate mac,
      QueryOnly IsPlain (Programs.gadgetDigestM output coordinate mac) := fun _ _ _ =>
    QueryOnly.bind (QueryOnly.vector _ fun _ => hashM_plainOnly _ _) fun _ => QueryOnly.pure' _
  refine QueryOnly.vector _ fun output => ?_
  unfold Programs.garbleEntryM
  split
  · exact QueryOnly.pure' _
  · exact QueryOnly.bind (QueryOnly.bind (digest _ _ _) fun _ => QueryOnly.bind (digest _ _ _) fun _ =>
      QueryOnly.pure' _) fun _ => QueryOnly.pure' _

theorem padsM_encOnly (keys : WhiteningKeys) : QueryOnly IsEncForward (Programs.padsM keys) := by
  have pad : ∀ coordinate index bit, QueryOnly IsEncForward (Programs.padM keys coordinate index bit) :=
    fun _ _ _ => QueryOnly.bind (QueryOnly.ask _ trivial) fun _ => QueryOnly.pure' _
  exact QueryOnly.bind (QueryOnly.vector _ fun _ => QueryOnly.bind (pad _ _ _) fun _ =>
      QueryOnly.bind (pad _ _ _) fun _ => QueryOnly.pure' _) fun _ =>
    QueryOnly.bind (QueryOnly.vector _ fun _ => QueryOnly.bind (pad _ _ _) fun _ =>
      QueryOnly.bind (pad _ _ _) fun _ => QueryOnly.pure' _) fun _ => QueryOnly.pure' _

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
