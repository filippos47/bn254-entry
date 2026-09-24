/-
**Phase 3, P1o — the coincidence guess, part 1: what the reach asks.**

`CoincidenceGuess` (`LiftGuess.lean`) bounds, at a fixed input `u`, the mass of `Coincide u`: the
reach (the full evaluator `Programs.onCurveM` on `u`'s labels, run on the tape) asks a garbler
question the designed rule hides. This file pins down **every** question of the reach, as a pure
function of the tape (`AsksOnly`, `laneAsks`, `onCurveM_asks`):

* each lane asks, in every chunk and at every paid fold level `n < b_c`, the two halves of every
  gate **off** the level's active parent, at its level-`n` labels, and the `limbCount ℓ` hash
  limbs of every switch **off** the active one, at its one-hot (level-`b_c`) labels (`LaneAsk`);
* the bridge hash at `bridgeInput t_eval`, `t_eval = t + mask·(x³ + 3 − y²)` (`reach_hashArg`: the
  evaluator's curve values are the garbler's, `Pipeline.curveValues_garble`);
* EncPRF questions (the pads);
* every gadget position of every digit, at the transformed label of `u`'s bit.

It then shows that a coincidence is one of **the coincidence events** (`coincide_events`):

* **a label event** `Hit ℓ c m r` per lane, chunk, level `m + 1 ≤ b_c` and entry `r` of that level:
  the reach's level-`(m+1)` label at `r` is the garbler's, and — at level `1` — the lane is a point
  lane, the input is off the curve and the reach's bridge input is not the garbler's; at a level
  `m + 1 ≥ 2`, the reach's label at the routed parent `gateEntry v m r` of level `m` is **not** the
  garbler's (else that parent is an earlier coincidence: `label_events`, by induction on the level).
  A coincidence at a fold gate `(n, r)` is a label event at level `n`, one at a switch `j` a label
  event at level `b_c`;
* **a gadget event off the curve** per position and bit (`GadgetOff`), **a gadget collision on the
  curve** per position (`GadgetOn`);
* **the bridge event** (`BridgeHit`): off the curve the reach's bridge input `bridgeInput t_eval`
  is the garbler's `bridgeInput t` (`t_eval ≠ t`, but `bridgeInput` is `2`-to-`1`).
-/

import Proof.Privacy.Phase3.PublicFirst.LiftHop
import Proof.Privacy.Phase3.Hidden

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.Guess

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.Phase3.Hidden (transcriptOf QueryOnly)

noncomputable section

/-! ### 1. Every question of a program, on given answers -/

/-- Every question `P` asks on the answers `ans` satisfies `S`. -/
def AsksOnly {α : Type} (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop) (P : FreeQuery Programs.Spec α) :
    Prop :=
  ∀ entry ∈ transcriptOf ans P, S entry.1

namespace AsksOnly

variable {α β : Type} {ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer}
  {S S' : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}

theorem pure' (value : α) : AsksOnly ans S (Pure.pure value : FreeQuery Programs.Spec α) := by
  intro entry member
  cases member

theorem bind {P : FreeQuery Programs.Spec α} {f : α → FreeQuery Programs.Spec β}
    (first : AsksOnly ans S P) (rest : AsksOnly ans S (f (P.eval ans))) :
    AsksOnly ans S (P >>= f) := by
  intro entry member
  rw [Hidden.transcriptOf_bind] at member
  rcases List.mem_append.mp member with inFirst | inRest
  · exact first entry inFirst
  · exact rest entry inRest

theorem bind_eq {P : FreeQuery Programs.Spec α} {f : α → FreeQuery Programs.Spec β} (value : α)
    (first : AsksOnly ans S P) (evalEq : P.eval ans = value) (rest : AsksOnly ans S (f value)) :
    AsksOnly ans S (P >>= f) := by
  subst evalEq
  exact bind first rest

theorem mono {P : FreeQuery Programs.Spec α} (only : AsksOnly ans S P)
    (weaker : ∀ q, S q → S' q) : AsksOnly ans S' P :=
  fun entry member => weaker _ (only entry member)

theorem of_queryOnly {P : FreeQuery Programs.Spec α} (only : QueryOnly S P) : AsksOnly ans S P :=
  only.mem ans

theorem vector : ∀ (count : Nat) {P : Fin count → FreeQuery Programs.Spec α},
    (∀ index, AsksOnly ans S (P index)) → AsksOnly ans S (FreeQuery.vector count P)
  | 0, _, _ => pure' _
  | count + 1, P, each => by
      show AsksOnly ans S (FreeQuery.vector count (fun index => P index.castSucc) >>= fun values =>
          P (Fin.last count) >>= fun value => Pure.pure (values.push value))
      exact bind (vector count fun index => each index.castSucc)
        (bind (each (Fin.last count)) (pure' _))

end AsksOnly

/-! ### 2. One lane of the evaluator -/

variable [FieldCertificate] [GroupCertificate]

/-- **A question of one lane of the evaluator**: in some chunk, a half of a fold gate at a paid
level `n < b_c` off the level's active parent, at its level-`n` label; or a hash limb of a switch
off the active one, at its one-hot label. -/
def LaneAsk (O : PermutationOracle FixedIndex Block) (lane : Lane)
    (joins : Vector Block foldStepCount)
    (bits : BitVec PlanB.coordinateBits) (labels : Fin PlanB.coordinateBits → Block)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex) : Prop :=
  ∃ c : Fin chunkCount,
    (∃ (n : Nat) (r : Fin (2 ^ n)) (half : Bool), n < chunkWidth c ∧
      r ≠ activeAt (chunkValue bits c).toNat n ∧
      q = .fixedForward (hotIndexNat lane c n r.val half)
        (evalFold O lane c (chunkValue bits c).toNat (labelAt (chunkLabels labels c))
          (joinAt (hotSlice joins c)) n r)) ∨
    (∃ (j : Fin (2 ^ chunkWidth c)) (limb : Fin (limbCount lane)), j ≠ chunkOf bits c ∧
      q = .hash (scaleInput lane c j.val limb.val
        (evalFold O lane c (chunkValue bits c).toNat (labelAt (chunkLabels labels c))
          (joinAt (hotSlice joins c)) (chunkWidth c) j)))

/-- The fold asks each gate off the active parent of its level, at the level's label. -/
theorem evalFoldM_asks (O : Oracle) (lane : Lane) (c : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) : ∀ steps,
    AsksOnly (publicAnswer O)
      (fun q => ∃ (n : Nat) (r : Fin (2 ^ n)) (half : Bool), n < steps ∧ r ≠ activeAt value n ∧
        q = .fixedForward (hotIndexNat lane c n r.val half)
          (evalFold O.1 lane c value bitLabel join n r))
      (Programs.evalFoldM lane c value bitLabel join steps)
  | 0 => AsksOnly.pure' _
  | steps + 1 => by
      show AsksOnly _ _ (Programs.evalFoldM lane c value bitLabel join steps >>= fun previous =>
        Programs.evalStepM lane c steps (bitLabel steps) (join steps) (activeAt value steps)
          previous >>= fun right => Pure.pure (extendLevel steps previous right))
      refine AsksOnly.bind_eq _ ((evalFoldM_asks O lane c value bitLabel join steps).mono
        fun q ⟨n, r, half, small, off, eq⟩ => ⟨n, r, half, by omega, off, eq⟩)
        (Programs.eval_evalFoldM O lane c value bitLabel join steps) ?_
      refine AsksOnly.bind ?_ (AsksOnly.pure' _)
      unfold Programs.evalStepM
      refine AsksOnly.bind (AsksOnly.vector _ fun entry => ?_) (AsksOnly.pure' _)
      by_cases same : entry = activeAt value steps
      · rw [if_pos same]
        exact AsksOnly.pure' _
      · rw [if_neg same]
        refine AsksOnly.of_queryOnly ?_
        unfold Programs.foldMaskM
        refine QueryOnly.bind (hashM_ask _ _ ⟨steps, entry, false, by omega, same, rfl⟩)
          fun _ => QueryOnly.bind (hashM_ask _ _ ⟨steps, entry, true, by omega, same, rfl⟩)
            fun _ => QueryOnly.pure' _

/-- **Every question of one lane of the evaluator** is a `LaneAsk`. -/
theorem laneAsks (O : Oracle) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (bits : BitVec PlanB.coordinateBits) (labels : Fin PlanB.coordinateBits → Block) :
    AsksOnly (publicAnswer O) (LaneAsk O.1 lane joins bits labels)
      (Programs.evalLaneM lane joins scale bits labels) := by
  unfold Programs.evalLaneM
  refine AsksOnly.bind (AsksOnly.vector _ fun c => ?_) (AsksOnly.pure' _)
  unfold Programs.evalChunkM
  refine AsksOnly.bind_eq _ ((evalFoldM_asks O lane c (chunkValue bits c).toNat
      (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c)) (chunkWidth c)).mono ?_)
    (Programs.eval_evalFoldM O lane c _ _ _ (chunkWidth c)) ?_
  · rintro q ⟨n, r, half, small, off, rfl⟩
    exact ⟨c, Or.inl ⟨n, r, half, small, off, rfl⟩⟩
  · refine AsksOnly.bind ?_ (AsksOnly.pure' _)
    unfold Programs.evalMasksM
    refine AsksOnly.bind (AsksOnly.vector _ fun switch => ?_) (AsksOnly.pure' _)
    by_cases same : switch = chunkOf bits c
    · rw [if_pos same]
      exact AsksOnly.pure' _
    · rw [if_neg same]
      refine (AsksOnly.of_queryOnly (Hidden.switchMaskM_only lane c switch.val _)).mono ?_
      rintro q ⟨limb, rfl⟩
      exact ⟨c, Or.inr ⟨switch, limb, same, rfl⟩⟩

/-! ### 3. The whole reach -/

/-- The evaluator's pads ask only EncPRF questions, at their first whitening key. -/
theorem evalPadsM_encOnly (keys : WhiteningKeys) (bits : BitInput) :
    QueryOnly (fun q => ∃ (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount)
      (bit : Bool), q = .encForward (coordinate, index) (encodeBit bit ^^^ keys.first))
      (Programs.evalPadsM keys bits) := by
  have pad : ∀ coordinate index bit,
      QueryOnly (fun q => ∃ (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount)
        (bit : Bool), q = .encForward (coordinate, index) (encodeBit bit ^^^ keys.first))
        (Programs.padM keys coordinate index bit) :=
    fun coordinate index bit =>
      QueryOnly.bind (QueryOnly.ask _ ⟨coordinate, index, bit, rfl⟩) fun _ => QueryOnly.pure' _
  have row : ∀ (which : EncPRF.Coordinate) (word : BitVec coordinateBitCount)
      (index : Fin coordinateBitCount),
      QueryOnly (fun q => ∃ (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount)
        (bit : Bool), q = .encForward (coordinate, index) (encodeBit bit ^^^ keys.first))
        (Programs.padM keys which index false >>= fun zero =>
        if word.getLsb index then
          Programs.padM keys which index true >>= fun one => Pure.pure (zero, one)
        else Pure.pure (zero, zero)) := by
    intro which word index
    refine QueryOnly.bind (pad _ _ _) fun _ => ?_
    split
    · exact QueryOnly.bind (pad _ _ _) fun _ => QueryOnly.pure' _
    · exact QueryOnly.pure' _
  exact QueryOnly.bind (QueryOnly.vector _ fun index => row .x bits.xBits index) fun _ =>
    QueryOnly.bind (QueryOnly.vector _ fun index => row .y bits.yBits index) fun _ =>
      QueryOnly.pure' _

/-- The gadget asks every position of every digit at the given label. -/
theorem unlockM_asks (table : FieldMacToECMac.Table) (input : AffineInput) (mac : InputMac) :
    QueryOnly (fun q => ∃ (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits),
        q = .fixedForward (.gadget o κ position) (macAt mac κ position))
      (Programs.unlockM table input mac) := by
  unfold Programs.unlockM
  refine QueryOnly.vector _ fun o => QueryOnly.bind ?_ fun _ => QueryOnly.pure' _
  unfold Programs.gadgetMaskM Programs.gadgetDigestM
  exact QueryOnly.bind (QueryOnly.bind (QueryOnly.vector _ fun index =>
      hashM_ask _ _ ⟨o, .x, index, rfl⟩) fun _ => QueryOnly.pure' _) fun _ =>
    QueryOnly.bind (QueryOnly.bind (QueryOnly.vector _ fun index =>
      hashM_ask _ _ ⟨o, .y, index, rfl⟩) fun _ => QueryOnly.pure' _) fun _ =>
        QueryOnly.pure' _

/-- The reach's curve value (its bridge question is at `bridgeInput` of it). -/
def reachHashArg (O : Oracle) (table : Public) (bits : BitInput) (mac : InputMac) : BaseField :=
  CurveMembership.evaluate table.curve bits.toAffine
    (Pipeline.curveValues (Pipeline.curveXValues O.1 O.2.2 table bits mac)
      (Pipeline.curveYValues O.1 O.2.2 table bits mac))

/-- The reach's pads, keyed by its own bridge hash. -/
def reachPads (O : Oracle) (table : Public) (bits : BitInput) (mac : InputMac) :
    EncPRF.Coordinate → Fin coordinateBitCount → Block × Block :=
  Programs.realEvalPads O.2.1
    ⟨(O.2.2 (bridgeInput (reachHashArg O table bits mac))).1,
      (O.2.2 (bridgeInput (reachHashArg O table bits mac))).2⟩ bits

/-- An EncPRF question of the reach: a pad at its own first whitening key. -/
def ReachEnc (O : Oracle) (table : Public) (bits : BitInput) (mac : InputMac)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex) : Prop :=
  ∃ (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) (bit : Bool),
    q = .encForward (coordinate, index)
      (encodeBit bit ^^^ (O.2.2 (bridgeInput (reachHashArg O table bits mac))).1)

/-- **A question of the reach.** -/
def ReachAsk (O : Oracle) (table : Public) (bits : BitInput) (mac : InputMac)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex) : Prop :=
  LaneAsk O.1 .curveX table.curveXHot (Pipeline.coordBits bits .x)
    (Pipeline.macLabels mac .x) q ∨
  LaneAsk O.1 .curveY table.curveYHot (Pipeline.coordBits bits .y)
    (Pipeline.macLabels mac .y) q ∨
  q = .hash (bridgeInput (reachHashArg O table bits mac)) ∨ ReachEnc O table bits mac q ∨
  LaneAsk O.1 .pointX table.pointXHot (Pipeline.coordBits bits .x)
    (Pipeline.macLabels (Programs.whitenMacOf (reachPads O table bits mac) mac) .x) q ∨
  LaneAsk O.1 .pointY table.pointYHot (Pipeline.coordBits bits .y)
    (Pipeline.macLabels (Programs.whitenMacOf (reachPads O table bits mac) mac) .y) q ∨
  ∃ (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits),
    q = .fixedForward (.gadget o κ position)
      (macAt (Programs.transformMacOf (reachPads O table bits mac) mac) κ position)

/-- **Every question of the reach is a `ReachAsk`.** -/
theorem onCurveM_asks (O : Oracle) (table : Public) (bits : BitInput) (mac : InputMac) :
    AsksOnly (publicAnswer O) (ReachAsk O table bits mac) (Programs.onCurveM table bits mac) := by
  unfold Programs.onCurveM
  refine AsksOnly.bind_eq (Pipeline.curveXValues O.1 O.2.2 table bits mac)
    ((laneAsks O .curveX _ _ _ _).mono fun q h => Or.inl h)
    (Programs.eval_evalLaneM _ _ _ _ _ _) ?_
  refine AsksOnly.bind_eq (Pipeline.curveYValues O.1 O.2.2 table bits mac)
    ((laneAsks O .curveY _ _ _ _).mono fun q h => Or.inr (Or.inl h))
    (Programs.eval_evalLaneM _ _ _ _ _ _) ?_
  refine AsksOnly.bind_eq (O.2.2 (bridgeInput (reachHashArg O table bits mac)))
    (fun entry member => ?_) (Programs.eval_askHash _ _) ?_
  · rcases List.mem_singleton.mp member with rfl
    exact Or.inr (Or.inr (Or.inl rfl))
  refine AsksOnly.bind_eq (reachPads O table bits mac)
    ((AsksOnly.of_queryOnly (evalPadsM_encOnly _ _)).mono
      fun q h => Or.inr (Or.inr (Or.inr (Or.inl h))))
    (Programs.eval_evalPadsM _ _ _) ?_
  refine AsksOnly.bind ((laneAsks O .pointX _ _ _ _).mono
    fun q h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) ?_
  refine AsksOnly.bind ((laneAsks O .pointY _ _ _ _).mono
    fun q h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) ?_
  refine AsksOnly.bind ((AsksOnly.of_queryOnly (unlockM_asks _ _ _)).mono
    fun q h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))) (AsksOnly.pure' _)

/-! ### 4. The reach on a tape, as a pure function of the tape -/

/-- The curve value the reach computes at `u`: `t + mask · (x³ + 3 − y²)`. -/
def evalKey (coins : Coins) (input : AffineInput) : BaseField :=
  coins.bridgeKey + coins.curveMask.value * curveGap input

/-- **The reach's curve value is `t + mask·(x³ + 3 − y²)`**: the evaluator's curve values are the
garbler's (`Pipeline.curveValues_garble`), whatever the input. -/
theorem reach_hashArg (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) :
    reachHashArg tape.2 (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
      (tape.1.inputMacKey.encode (BitInput.ofAffine input)) = evalKey tape.1 input := by
  unfold reachHashArg
  rw [garble_table, Pipeline.curveValues_garble _ _ _ _ _ _ _ _ _ _ _ _ (coins_correlated tape.1)
    (delivers tape.2.1 tape.2.2.2) input, BitInput.toAffineOfAffine]
  exact CurveMembership.evaluateEncoded _ _ _ _ _ input

/-- On the curve the reach's curve value is the bridge key. -/
theorem evalKey_eq (coins : Coins) (input : AffineInput) (valid : validate input = true) :
    evalKey coins input = coins.bridgeKey := by
  have gap : curveGap input = 0 := by
    have onCurve := (validate_eq_true_iff input).mp valid
    unfold OnCurve at onCurve
    unfold curveGap
    linear_combination -onCurve
  unfold evalKey
  rw [gap, mul_zero, add_zero]

/-- The encoded labels of `u` on a tape. -/
def macOf (tape : Coins × Oracle) (input : AffineInput) : InputMac :=
  tape.1.inputMacKey.encode (BitInput.ofAffine input)

/-- **The reach's pads on a tape**: the EncPRF pads keyed by `hash(bridgeInput t_eval)`. -/
def padsOf (tape : Coins × Oracle) (input : AffineInput) :
    EncPRF.Coordinate → Fin coordinateBitCount → Block × Block :=
  Programs.realEvalPads tape.2.2.1
    ⟨(tape.2.2.2 (bridgeInput (evalKey tape.1 input))).1,
      (tape.2.2.2 (bridgeInput (evalKey tape.1 input))).2⟩
    (BitInput.ofAffine input)

theorem reachPads_eq (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) :
    reachPads tape.2 (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
      (macOf tape input) = padsOf tape input := by
  unfold reachPads padsOf macOf
  rw [reach_hashArg]

/-- A lane's published fold joins. -/
def lanePub (table : Public) : Lane → Vector Block foldStepCount
  | .curveX => table.curveXHot
  | .curveY => table.curveYHot
  | .pointX => table.pointXHot
  | .pointY => table.pointYHot

/-- The labels the reach holds in each lane: raw for system A, whitened by its own pads for
system B. -/
def laneLabels (tape : Coins × Oracle) (input : AffineInput) :
    Lane → Fin PlanB.coordinateBits → Block
  | .curveX => Pipeline.macLabels (macOf tape input) .x
  | .curveY => Pipeline.macLabels (macOf tape input) .y
  | .pointX => Pipeline.macLabels (Programs.whitenMacOf (padsOf tape input) (macOf tape input)) .x
  | .pointY => Pipeline.macLabels (Programs.whitenMacOf (padsOf tape input) (macOf tape input)) .y

/-- The input's chunk value, as a number. -/
abbrev chunkNat (input : AffineInput) (lane : Lane) (c : Fin chunkCount) : Nat :=
  (chunkValue (inputBits input lane.coord) c).toNat

/-- The reach's labels at level `n` of a chunk's fold. -/
def reachFold (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (n : Nat) : Fin (2 ^ n) → Block :=
  evalFold tape.2.1 lane c (chunkNat input lane c)
    (labelAt (chunkLabels (laneLabels tape input lane) c))
    (joinAt (hotSlice (lanePub (Scheme.scheme.garble parameter scalar tape).1 lane) c)) n

/-- The garbler's labels at level `n` of a chunk's fold. -/
def garbFold (tape : Coins × Oracle) (lane : Lane) (c : Fin chunkCount) (n : Nat) :
    Fin (2 ^ n) → Block :=
  (garbleFold tape.2.1 lane c ((Hidden.laneKeys tape).1 lane)
    (labelAt fun p => (chunkKey ((Hidden.laneKeys tape).2 lane) c p).1) n).1

/-- One label pair of a key. -/
def keyAt (key : InputMacKey) : Coord → Fin PlanB.coordinateBits → BitAdaptor.Key
  | .x, position => key.x.get position
  | .y, position => key.y.get position

/-- The garbler's transformed label of a gadget position, at a bit. -/
def glabel (tape : Coins × Oracle) (κ : Coord) (position : Fin PlanB.coordinateBits) (bit : Bool) :
    Block :=
  BitAdaptor.encode (keyAt (EncPRF.transformKey tape.2.2.1
    (EncPRF.whiteningKeys tape.2.2.2 tape.1.bridgeKey) tape.1.inputMacKey) κ position) bit

/-- The reach's transformed label of a gadget position. -/
def reachGadget (tape : Coins × Oracle) (input : AffineInput) (κ : Coord)
    (position : Fin PlanB.coordinateBits) : Block :=
  macAt (Programs.transformMacOf (padsOf tape input) (macOf tape input)) κ position

/-! ### 5. The coincidence events -/

/-- **The routed parent** of entry `r` of level `m + 1` at level `m ≥ 1`: its own parent
`r mod 2^m`, or — if that is the active one — its sibling `(r mod 2^m) xor 1`. Transposing its
first gate half moves the reach's label at `r` (`LawsGuessFamily.evalFold_trans`). -/
def gateEntry (value m : Nat) (r : Nat) : Fin (2 ^ m) :=
  ⟨(if r % 2 ^ m = value % 2 ^ m then r % 2 ^ m ^^^ 1 else r % 2 ^ m) % 2 ^ m,
    Nat.mod_lt _ (Nat.two_pow_pos m)⟩

/-- The routed parent is off the active parent. -/
theorem gateEntry_ne (value m r : Nat) (one : 1 ≤ m) :
    (gateEntry value m r).val ≠ value % 2 ^ m := by
  have small : r % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
  have oneSmall : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
  unfold gateEntry
  dsimp only
  split
  · rename_i active
    rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow small oneSmall), ← active]
    intro same
    have cancel := congrArg (fun x => r % 2 ^ m ^^^ x) same
    simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at cancel
    exact absurd cancel (by decide)
  · rename_i inactive
    rw [Nat.mod_eq_of_lt small]
    exact inactive

/-- The routed parent is the target's parent, or the target's parent is active. -/
theorem gateEntry_routed (value m r : Nat) :
    (gateEntry value m r).val = r % 2 ^ m ∨ r % 2 ^ m = value % 2 ^ m := by
  unfold gateEntry
  dsimp only
  split
  · exact Or.inr ‹_›
  · exact Or.inl (Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos m)))

/-- **A label event** at level `m + 1` and entry `r` of `(lane, c)`: the reach's label there is
the garbler's; at level `1` the lane is a point lane, the input off the curve and the reach's
bridge input not the garbler's; at a higher level the reach's label at the routed parent is not
the garbler's. -/
def Hit (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) (m : Fin (chunkWidth c)) (r : Fin (2 ^ (m.val + 1))) :
    Prop :=
  reachFold parameter scalar tape input lane c (m.val + 1) r =
      garbFold tape lane c (m.val + 1) r ∧
    if m.val = 0 then
      Hidden.laneIsPoint lane = true ∧ validate input = false ∧
        bridgeInput (evalKey tape.1 input) ≠ bridgeInput tape.1.bridgeKey
    else
      reachFold parameter scalar tape input lane c m.val
          (gateEntry (chunkNat input lane c) m.val r.val) ≠
        garbFold tape lane c m.val (gateEntry (chunkNat input lane c) m.val r.val)

/-- **A gadget event off the curve**: the reach's gadget label of a position is the garbler's at
a bit, with the reach's bridge input not the garbler's. -/
def GadgetOff (tape : Coins × Oracle) (input : AffineInput) (κ : Coord)
    (position : Fin PlanB.coordinateBits) (bit : Bool) : Prop :=
  validate input = false ∧ bridgeInput (evalKey tape.1 input) ≠ bridgeInput tape.1.bridgeKey ∧
    reachGadget tape input κ position = glabel tape κ position bit

/-- **A gadget collision on the curve**: the two transformed labels of a position collide. -/
def GadgetOn (tape : Coins × Oracle) (κ : Coord) (position : Fin PlanB.coordinateBits) : Prop :=
  glabel tape κ position false = glabel tape κ position true

/-- **The bridge event**: off the curve the reach's bridge input is the garbler's. -/
def BridgeHit (tape : Coins × Oracle) (input : AffineInput) : Prop :=
  validate input = false ∧ bridgeInput (evalKey tape.1 input) = bridgeInput tape.1.bridgeKey

/-! ### 6. The gadget labels -/

theorem vget_ofFn {α : Type} (f : Fin coordinateBitCount → α)
    (position : Fin PlanB.coordinateBits) : (Vector.ofFn f).get position = f position :=
  Vector.get_ofFn f position

theorem encodeCoordinate_get (key : CoordinateMacKey) (bits : BitVec coordinateBitCount)
    (position : Fin coordinateBitCount) :
    (encodeCoordinate key bits).get position =
      BitAdaptor.encode (key.get position) (bits.getLsb position) := by
  simp only [encodeCoordinate, Vector.get_ofFn]
  rfl

/-- The garbler's gadget label of a digit with an exceptional input is the transformed label at
its exceptional bit. -/
theorem gadgetLabel_eq (scalar : NonZeroScalar) (tape : Coins × Oracle) (o : Fin digitCount)
    (κ : Coord) (position : Fin PlanB.coordinateBits)
    (some : (digitEndomorphismBase (Hidden.digitKey scalar tape.1.offsets o).digit).isSome =
      true) :
    Hidden.gadgetLabel scalar tape o κ position =
      glabel tape κ position (Hidden.exceptionalBit scalar tape.1.offsets o κ position) := by
  obtain ⟨phi, found⟩ := Option.isSome_iff_exists.mp some
  unfold Hidden.gadgetLabel Hidden.exceptionalBit
  rw [found]
  cases κ
  · exact encodeCoordinate_get _ _ _
  · exact encodeCoordinate_get _ _ _

/-- **On the curve the reach's gadget label is the garbler's at `u`'s bit.** -/
theorem reachGadget_onCurve (tape : Coins × Oracle) (input : AffineInput)
    (valid : validate input = true) (κ : Coord) (position : Fin PlanB.coordinateBits) :
    reachGadget tape input κ position =
      glabel tape κ position ((inputBits input κ).getLsb position) := by
  have key := evalKey_eq tape.1 input valid
  unfold reachGadget padsOf glabel
  rw [key]
  cases κ
  · simp only [macAt, Programs.transformMacOf, Programs.realEvalPads, keyAt, macOf,
      EncPRF.transformKey, EncPRF.transformCoordinateKey, InputMacKey.encode]
    rw [vget_ofFn, vget_ofFn]
    simp only [encodeCoordinate, Vector.getElem_ofFn]
    show encrypt (EncPRF.evenMansourPad _ _
          (EncPRF.Counter.mk .x position ((coordinateBits input.x).getLsb position)))
        (BitAdaptor.encode _ ((coordinateBits input.x).getLsb position)) =
      BitAdaptor.encode _ ((coordinateBits input.x).getLsb position)
    generalize (coordinateBits input.x).getLsb position = b
    cases b <;> rfl
  · simp only [macAt, Programs.transformMacOf, Programs.realEvalPads, keyAt, macOf,
      EncPRF.transformKey, EncPRF.transformCoordinateKey, InputMacKey.encode]
    rw [vget_ofFn, vget_ofFn]
    simp only [encodeCoordinate, Vector.getElem_ofFn]
    show encrypt (EncPRF.evenMansourPad _ _
          (EncPRF.Counter.mk .y position ((coordinateBits input.y).getLsb position)))
        (BitAdaptor.encode _ ((coordinateBits input.y).getLsb position)) =
      BitAdaptor.encode _ ((coordinateBits input.y).getLsb position)
    generalize (coordinateBits input.y).getLsb position = b
    cases b <;> rfl

/-! ### 7. A coincidence is one of the events -/

/-- A coincidence is a non-EncPRF garbler entry the reach asks and the designed rule hides. -/
theorem coincide_entry (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (hit : Coincide parameter scalar tape input) :
    ∃ e ∈ garblerTranscript scalar tape, e.IsEnc = false ∧
      e.1 ∈ (transcriptOf (publicAnswer tape.2)
        (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1
          (BitInput.ofAffine input) (macOf tape input))).map Sigma.fst ∧
      designedRule scalar tape input e = false := by
  by_contra none
  apply hit
  unfold visibleInstall designedInstall visibleEntries
  refine List.filter_congr fun e member => ?_
  cases enc : e.IsEnc
  · cases d : designedRule scalar tape input e
    · have notReached : e.1 ∉ (reachTranscript (Scheme.scheme.garble parameter scalar tape).1 input
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input) tape).map
            Sigma.fst := by
        intro reached
        rw [reach_eq] at reached
        exact none ⟨e, member, enc, reached, d⟩
      simp [notReached]
    · have asks := designed_asks parameter scalar tape input e member d
      unfold Asks at asks
      have reached : e.1 ∈ (reachTranscript (Scheme.scheme.garble parameter scalar tape).1 input
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input) tape).map
            Sigma.fst := by
        rw [reach_eq]
        exact asks
      simp [reached]
  · simp

theorem laneIsPoint_of_curve (lane : Lane) (curve : laneIsCurve lane = false) :
    Hidden.laneIsPoint lane = true := by
  cases lane <;> simp_all [laneIsCurve, Hidden.laneIsPoint]

/-- **A label coincidence is a label event**, by induction on the level: at level `1` it is the
event itself; at a higher level either the routed parent's label is not the garbler's (the event)
or it is, which is a coincidence one level down. -/
theorem label_events (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (lane : Lane) (c : Fin chunkCount)
    (point : Hidden.laneIsPoint lane = true) (invalid : validate input = false)
    (bridge : bridgeInput (evalKey tape.1 input) ≠ bridgeInput tape.1.bridgeKey) :
    ∀ n, n ≤ chunkWidth c → ∀ r : Fin (2 ^ n), r.val ≠ chunkNat input lane c % 2 ^ n →
      reachFold parameter scalar tape input lane c n r = garbFold tape lane c n r →
      ∃ (m : Fin (chunkWidth c)) (r' : Fin (2 ^ (m.val + 1))),
        Hit parameter scalar tape input lane c m r'
  | 0, _, r, off, _ => absurd (by have := r.isLt; simp at this; omega) off
  | m + 1, small, r, off, same => by
      by_cases zero : m = 0
      · subst zero
        exact ⟨⟨0, by omega⟩, r, same, by rw [if_pos rfl]; exact ⟨point, invalid, bridge⟩⟩
      · let r' := gateEntry (chunkNat input lane c) m r.val
        by_cases parent : reachFold parameter scalar tape input lane c m r' =
            garbFold tape lane c m r'
        · exact label_events parameter scalar tape input lane c point invalid bridge m (by omega)
            r' (gateEntry_ne _ m r.val (by omega)) parent
        · exact ⟨⟨m, by omega⟩, r, same, by rw [if_neg zero]; exact parent⟩

/-- The garbler's point at a fold gate is its level label. -/
theorem garblerPointOf_hot (scalar : NonZeroScalar) (tape : Coins × Oracle) (lane : Lane)
    (c : Fin chunkCount) (n r : Nat) (half : Bool) (small : n < chunkBits)
    (entry : r < 2 ^ n) (bound : 2 ^ n ≤ 2 ^ chunkBits) :
    Hidden.garblerPointOf scalar tape (.hot lane c ⟨n, small⟩ ⟨r, lt_of_lt_of_le entry bound⟩ half)
      = garbFold tape lane c n ⟨r, entry⟩ := by
  show (garbleFold tape.2.1 lane c _ _ n).1 ⟨r % 2 ^ n, _⟩ = _
  simp only [Nat.mod_eq_of_lt entry]
  rfl

/-- The garbler's label at a vector site is its one-hot level label. -/
theorem garblerLabelOf_site (tape : Coins × Oracle) (site : VectorSite) :
    Hidden.garblerLabelOf tape site =
      garbFold tape site.lane site.chunk (chunkWidth site.chunk) site.switch := rfl

/-- **A hidden garbler entry a lane of the reach asks is a label coincidence**: off the curve, in
a point lane, at an entry off the level's active parent. -/
theorem lane_coincidence (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (lane : Lane) (e : Entry FixedIndex EncPRF.PermutationIndex)
    (member : e ∈ garblerTranscript scalar tape)
    (ask : LaneAsk tape.2.1 lane (lanePub (Scheme.scheme.garble parameter scalar tape).1 lane)
      (inputBits input lane.coord) (laneLabels tape input lane) e.1)
    (hidden : designedRule scalar tape input e = false) :
    Hidden.laneIsPoint lane = true ∧ validate input = false ∧ ∃ c n, ∃ _ : n ≤ chunkWidth c,
      ∃ r : Fin (2 ^ n), r.val ≠ chunkNat input lane c % 2 ^ n ∧
        reachFold parameter scalar tape input lane c n r = garbFold tape lane c n r := by
  have good := garblerTranscript_good scalar tape e member
  have value : ∀ c, chunkNat input lane c = (chunkOf (inputBits input lane.coord) c).val :=
    fun c => chunkValue_toNat _ _
  obtain ⟨request, answer⟩ := e
  obtain ⟨c, ⟨n, r, half, small, off, eq⟩ | ⟨j, limb, off, eq⟩⟩ := ask
  · -- a fold gate
    cases eq
    have nSmall : n < chunkBits := lt_of_lt_of_le small (chunkWidth_le c)
    have bound : 2 ^ n ≤ 2 ^ chunkBits := Nat.pow_le_pow_right (by omega) nSmall.le
    have entrySmall : r.val < 2 ^ chunkBits := lt_of_lt_of_le r.isLt bound
    have offNat : r.val ≠ chunkNat input lane c % 2 ^ n := fun same => off (Fin.ext same)
    have point : reachFold parameter scalar tape input lane c n r =
        Hidden.garblerPointOf scalar tape (hotIndexNat lane c n r.val half) := good
    rw [hotIndexNat_eq lane c n r.val half nSmall entrySmall,
      garblerPointOf_hot scalar tape lane c n r.val half nSmall r.isLt bound] at point
    rw [hotIndexNat_eq lane c n r.val half nSmall entrySmall] at hidden
    have shown : (decide (r.val ≠ (chunkOf (inputBits input lane.coord) c).val % 2 ^ n) &&
        (laneIsCurve lane || validate input)) = false := hidden
    rw [← value, decide_eq_true offNat, Bool.true_and, Bool.or_eq_false_iff] at shown
    exact ⟨laneIsPoint_of_curve lane shown.1, shown.2, c, n, small.le, r, offNat, point⟩
  · -- a hash limb of a switch
    cases eq
    rcases (good : _ ∨ _) with bridgeEq | ⟨slot, scaleEq⟩
    · exact absurd bridgeEq.symm (bridgeInput_ne_scaleInput _ _ _ _ _ _)
    · obtain ⟨⟨ℓ, k, s⟩, i⟩ := slot
      obtain ⟨rfl, rfl, switchEq, limbEq, labelEq⟩ := scaleInput_injective
        (Pipeline.switch_lt_twoPowChunkBits c j) (Pipeline.switch_lt_twoPowChunkBits k s)
        (lt_trans limb.isLt (limbCount_lt _)) (lt_trans i.isLt (limbCount_lt _)) scaleEq
      obtain rfl : j = s := Fin.ext switchEq
      have offNat : j.val ≠ chunkNat input lane c % 2 ^ chunkWidth c := by
        rw [value, Nat.mod_eq_of_lt (chunkOf (inputBits input lane.coord) c).isLt]
        exact fun same => off (Fin.ext same)
      have shown : designedSite input ⟨lane, c, j⟩ = false := by
        rw [← designedHash_labelInput input ⟨⟨lane, c, j⟩, limb⟩
          (reachFold parameter scalar tape input lane c (chunkWidth c) j)]
        exact hidden
      simp only [designedSite, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_not,
        Bool.or_eq_false_iff] at shown
      rcases shown with active | ⟨curve, invalid⟩
      · exact absurd active off
      · exact ⟨laneIsPoint_of_curve lane curve, invalid, c, chunkWidth c, le_rfl, j, offNat,
          labelEq.trans (garblerLabelOf_site tape ⟨lane, c, j⟩)⟩

/-- **Every coincidence is one of the events.** -/
theorem coincide_events (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (hit : Coincide parameter scalar tape input) :
    (∃ lane c m r, Hit parameter scalar tape input lane c m r) ∨
    (∃ κ position bit, GadgetOff tape input κ position bit) ∨
    (∃ κ position, GadgetOn tape κ position) ∨ BridgeHit tape input := by
  obtain ⟨e, member, notEnc, reached, notDesigned⟩ := coincide_entry parameter scalar tape input hit
  obtain ⟨entry, entryMember, entryEq⟩ := List.mem_map.mp reached
  have ask := onCurveM_asks tape.2 _ _ _ entry entryMember
  rw [entryEq] at ask
  have good := garblerTranscript_good scalar tape e member
  have shape := garblerTranscript_ask scalar tape e member
  have pads := reachPads_eq parameter scalar tape input
  have hashArg : reachHashArg tape.2 (Scheme.scheme.garble parameter scalar tape).1
      (BitInput.ofAffine input) (macOf tape input) = evalKey tape.1 input :=
    reach_hashArg parameter scalar tape input
  unfold ReachAsk at ask
  rw [pads, hashArg] at ask
  have laneCase : ∀ lane : Lane,
      LaneAsk tape.2.1 lane (lanePub (Scheme.scheme.garble parameter scalar tape).1 lane)
        (inputBits input lane.coord) (laneLabels tape input lane) e.1 →
      (∃ lane c m r, Hit parameter scalar tape input lane c m r) ∨
      (∃ κ position bit, GadgetOff tape input κ position bit) ∨
      (∃ κ position, GadgetOn tape κ position) ∨ BridgeHit tape input := by
    intro lane laneAsk
    obtain ⟨point, invalid, c, n, small, r, off, same⟩ :=
      lane_coincidence parameter scalar tape input lane e member laneAsk notDesigned
    by_cases bridge : bridgeInput (evalKey tape.1 input) = bridgeInput tape.1.bridgeKey
    · exact Or.inr (Or.inr (Or.inr ⟨invalid, bridge⟩))
    · obtain ⟨m, r', event⟩ :=
        label_events parameter scalar tape input lane c point invalid bridge n small r off same
      exact Or.inl ⟨lane, c, m, r', event⟩
  rcases ask with a | a | a | a | a | a | a
  · exact laneCase .curveX a
  · exact laneCase .curveY a
  · -- the bridge question
    obtain ⟨request, answer⟩ := e
    cases a
    rcases (good : _ ∨ _) with bridgeEq | ⟨slot, scaleEq⟩
    · have invalid : validate input = false := by
        have keep : designedHash input (bridgeInput (evalKey tape.1 input)) = false := notDesigned
        rwa [bridgeEq, designedHash_bridgeInput] at keep
      exact Or.inr (Or.inr (Or.inr ⟨invalid, bridgeEq⟩))
    · exact absurd scaleEq (bridgeInput_ne_scaleInput _ _ _ _ _ _)
  · obtain ⟨_, _, _, eq⟩ := a
    obtain ⟨request, answer⟩ := e
    cases eq
    simp [Entry.IsEnc] at notEnc
  · exact laneCase .pointX a
  · exact laneCase .pointY a
  · obtain ⟨o, κ, position, eq⟩ := a
    obtain ⟨request, answer⟩ := e
    cases eq
    have isGood : reachGadget tape input κ position = Hidden.gadgetLabel scalar tape o κ position :=
      good
    have some : (digitEndomorphismBase (Hidden.digitKey scalar tape.1.offsets o).digit).isSome =
        true := shape
    have isGood' : reachGadget tape input κ position =
        glabel tape κ position (Hidden.exceptionalBit scalar tape.1.offsets o κ position) :=
      isGood.trans (gadgetLabel_eq scalar tape o κ position some)
    have shown : designedIndex scalar tape input (.gadget o κ position) =
        (validate input && decide ((inputBits input κ).getLsb position =
          Hidden.exceptionalBit scalar tape.1.offsets o κ position)) := rfl
    have hidden : designedIndex scalar tape input (.gadget o κ position) = false := notDesigned
    rw [shown] at hidden
    cases valid : validate input
    · by_cases bridge : bridgeInput (evalKey tape.1 input) = bridgeInput tape.1.bridgeKey
      · exact Or.inr (Or.inr (Or.inr ⟨valid, bridge⟩))
      · exact Or.inr (Or.inl ⟨κ, position, _, valid, bridge, isGood'⟩)
    · rw [valid, Bool.true_and, decide_eq_false_iff_not] at hidden
      have onCurve := reachGadget_onCurve tape input valid κ position
      rw [onCurve] at isGood'
      refine Or.inr (Or.inr (Or.inl ⟨κ, position, ?_⟩))
      unfold GadgetOn
      revert isGood' hidden
      cases (inputBits input κ).getLsb position <;>
        cases Hidden.exceptionalBit scalar tape.1.offsets o κ position <;> simp_all

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.Guess
