/-
**Phase 3, P1i — the shadow of `M'` (on the curve), and the generalised exceptional event.**

On the curve, `G1U`'s stage-2 state holds the garbler's EncPRF entries (both pads of every
position) and the garbler's entries the evaluator's own evaluation (`reachTranscript`, i.e.
`Programs.onCurveM`) asks. `HW`'s opening (`openingQueriesM`) asks all of these but the 508
bit-`true` pads and the gadget. The on-curve shadow asks exactly the rest, in a fixed order:

1. `curvePrefixM` — system A and the bridge hash again (every answer is stored by the opening, so
   the re-run reads the opening's keys `(k₁, k₂) = hash(t)`);
2. `truePadsM` — the 508 bit-`true` pads `π_{κ,i}(1 ⊕ k₁)` (fresh);
3. `Programs.onCurveM` — the whole evaluator (stored but for the gadget: its questions at the
   evaluator's transformed labels are fresh; those at a position where the garbler asks the same
   label mirror the garbler's visible gadget entries, the others are discardable fresh pairs).

The **reveal flag** is the generalised exceptional event (root `PublicFirst` §4): some nonzero digit
`o` whose exceptional input agrees with the input `u` at every position `i` where the two pads do
not collide, `pad₀(i) ⊕ pad₁(i) ≠ Δ_κ` (at a colliding position the two gadget labels coincide).
The pads are read from the
final private state at the keys the evaluator's prefix reads there (`prefixKeysOn`), and the
free-XOR offsets `Δ` are the shadow's coin (`HW`'s Lamport key has none).

The off-curve part is left a parameter (`OffShadow`); the designed one is `LiftTV.designedOff`.
-/

import Proof.Privacy.Phase3.PublicFirst.FlagBound
import Proof.Privacy.Phase3.Lazy.Program

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM whitePadsM)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record)
open scoped ENNReal

noncomputable section

/-! ### The on-curve shadow's questions -/

section Programs

variable [FieldCertificate]

/-- **The evaluator's prefix**: system A's two lanes and the bridge hash at `bridgeInput t`
(`openingQueriesM`'s and `Programs.onCurveM`'s first three stages). -/
def curvePrefixM (table : Public) (bits : BitInput) (mac : InputMac) : Programs.M (Block × Block) :=
  Programs.evalLaneM .curveX table.curveXHot
      (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x) >>= fun curveX =>
    Programs.evalLaneM .curveY table.curveYHot
        (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
        (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y) >>= fun curveY =>
      Programs.askHash (bridgeInput (CurveMembership.evaluate table.curve bits.toAffine
        (Pipeline.curveValues curveX curveY)))

/-- **The 508 bit-`true` pads.** -/
def truePadsM (keys : WhiteningKeys) : Programs.M Unit :=
  FreeQuery.vector coordinateBitCount (fun index => Programs.padM keys .x index true) >>= fun _ =>
    FreeQuery.vector coordinateBitCount (fun index => Programs.padM keys .y index true) >>= fun _ =>
      pure ()

/-- **The on-curve shadow's questions**: the prefix again, the bit-`true` pads, the evaluator. -/
def shadowOnM [GroupCertificate] (table : Public) (bits : BitInput) (mac : InputMac) :
    Programs.M Unit :=
  curvePrefixM table bits mac >>= fun hashed =>
    truePadsM ⟨hashed.1, hashed.2⟩ >>= fun _ =>
      Programs.onCurveM table bits mac >>= fun _ => pure ()

end Programs

/-! ### Reading a state -/

section Read

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A state's answer to a question: its stored answer, or `0` where it has none. -/
def answerOf (state : LState) : (request : PublicQuery FixedIndex EncPRF.PermutationIndex) →
    request.Answer
  | .fixedForward index input =>
      (LazyOracle.lookup (.fixedForward index input) state).getD (show Block from 0)
  | .fixedInverse index output =>
      (LazyOracle.lookup (.fixedInverse index output) state).getD (show Block from 0)
  | .encForward index input =>
      (LazyOracle.lookup (.encForward index input) state).getD (show Block from 0)
  | .encInverse index output =>
      (LazyOracle.lookup (.encInverse index output) state).getD (show Block from 0)
  | .hash input => (LazyOracle.lookup (.hash input) state).getD (show Block × Block from (0, 0))

/-- **The keys the evaluator's prefix reads from a state.** -/
def prefixKeysOn [FieldCertificate] (state : LState) (table : Public) (bits : BitInput)
    (mac : InputMac) : Block × Block :=
  FreeQuery.eval (answerOf state) (curvePrefixM table bits mac)

/-- The two pads' xor at a position, read from a state at the whitening key `k₁` (`none` if either
pad is not stored). The second key `k₂` cancels. -/
def padXor (state : LState) (coordinate : EncPRF.Coordinate) (position : Fin coordinateBitCount)
    (first : Block) : Option Block :=
  (lk (state.enc (coordinate, position)) (encodeBit false ^^^ first).toFin).bind fun zero =>
    (lk (state.enc (coordinate, position)) (encodeBit true ^^^ first).toFin).map fun one =>
      BitVec.ofFin zero ^^^ BitVec.ofFin one

end Read

/-! ### The generalised exceptional event -/

section Reveal

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- An input's bit at a (coordinate, position). -/
def inputBit (bits : BitInput) : EncPRF.Coordinate → Fin coordinateBitCount → Bool
  | .x, position => bits.xBits.getLsb position
  | .y, position => bits.yBits.getLsb position

/-- The output key of digit `o`. -/
def outputKeyOf (scalar : NonZeroScalar) (offsets : FieldMacToECMac.SuccessfulOffsets)
    (o : Fin digitCount) : FieldMacToECMac.OutputKey :=
  (FieldMacToECMac.outputKeys construction scalar.value offsets).get o

/-- **Digit `o` reveals at `u` off the collisions**: it is a nonzero digit, and its exceptional
input agrees with `u` at every position whose two pads do not differ by `Δ`. -/
def RevealsAt (scalar : NonZeroScalar) (offsets : FieldMacToECMac.SuccessfulOffsets)
    (bits : BitInput) (collide : EncPRF.Coordinate → Fin coordinateBitCount → Prop)
    (o : Fin digitCount) : Prop :=
  ∃ phi, digitEndomorphismBase (outputKeyOf scalar offsets o).digit = some phi ∧
    ∀ coordinate position,
      inputBit (BitInput.ofAffine (Exception.exceptionalInput phi
          (outputKeyOf scalar offsets o).offset.coordinates)) coordinate position
        = inputBit bits coordinate position ∨ collide coordinate position

/-- **The on-curve reveal flag**: some digit reveals, with the collisions read from the final
private state (the pads at the prefix's key) and the shadow's offsets `Δ`. -/
def revealOnPred (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (coins : Coins) (delta : EncPRF.Coordinate → Block) (state : LState) : Prop :=
  let restored := Lamport.restore input (sourceLabels source input)
  let keys := prefixKeysOn state source.publicValue restored.input restored.inputMac
  ∃ o, RevealsAt scalar coins.offsets restored.input
    (fun coordinate position => padXor state coordinate position keys.1 = some (delta coordinate)) o

end Reveal

/-! ### The shadow -/

/-- **The off-curve part of a shadow** (the open part of (A)). -/
structure OffShadow where
  /-- Its coins. -/
  Coin : Type
  /-- Their law. -/
  law : PMF Coin
  /-- Its questions. -/
  offCurve : Stage1Source → AffineInput → Coin → FreeQuery Programs.Spec Unit
  /-- Its reveal flag. -/
  revealOff : Stage1Source → AffineInput → Coin → LState → Prop

/-- The uniform offsets `Δ` of the two coordinates. -/
def deltaLaw : PMF (EncPRF.Coordinate → Block) := PMF.uniformOfFintype _

section Shadow

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **The shadow of `M'`**: on the curve, the prefix again, the bit-`true` pads and the evaluator,
flagged at the generalised exceptional event; off the curve, `off`. -/
def planBShadow (scalar : NonZeroScalar) (off : OffShadow) : Shadow where
  Coin := (EncPRF.Coordinate → Block) × off.Coin
  law := deltaLaw.bind fun delta => off.law.map fun coin => (delta, coin)
  onCurve source input _ _ _ :=
    let restored := Lamport.restore input (sourceLabels source input)
    shadowOnM source.publicValue restored.input restored.inputMac
  offCurve source input coin := off.offCurve source input coin.2
  revealOn source input coins coin state := revealOnPred scalar source input coins coin.1 state
  revealOff source input coin state := off.revealOff source input coin.2 state

end Shadow

/-! ### The prefix is the opening's and the evaluator's prefix -/

section Prefix

variable [FieldCertificate]

open Kriterion.ArgoMAC.Phase3.Lazy (fq_bind_assoc)

/-- **`HW`'s opening starts with the prefix.** -/
theorem openingQueriesM_eq_prefix (table : Public) (bits : BitInput) (mac : InputMac) :
    openingQueriesM table bits mac = curvePrefixM table bits mac >>= fun hashed =>
      whitePadsM ⟨hashed.1, hashed.2⟩ >>= fun pads =>
        Programs.evalLaneM .pointX table.pointXHot
            (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
            (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)
          >>= fun pointX =>
        Programs.evalLaneM .pointY table.pointYHot
            (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
            (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
          >>= fun pointY =>
        pure (pointX, pointY) := by
  unfold openingQueriesM curvePrefixM
  simp only [fq_bind_assoc]

end Prefix

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
