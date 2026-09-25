/-
**Phase 3, P1f — the designed-visibility rule `designedRule`.**

`designedRule scalar tape u entry` keeps a reached garbler entry iff its **index** is one the
evaluator is meant to hold at `u` — decided by the index and `u` alone, never by the entry's
input (the entry's input carrying a coincidence is exactly what made `D = true` false). For a hash
entry the index is the vector site its key names, never its label:

| index | designed at `u` |
|---|---|
| fold gate `(ℓ, c, step, r, half)` | `r ≠` the active parent `chunk_c(u) mod 2^step`, and (`ℓ` a curve lane, or `u` on the curve) |
| scale input of `(ℓ, c, j)` (any limb, label) | `j ≠ chunk_c(u)`, and as for fold gates |
| gadget `(o, κ, pos, b)` | `u` on the curve, and `u`'s bit at `(κ, pos)` is `b` |
| hash off the scale range (the bridge input) | `u` on the curve |
| EncPRF | never (`visibleEntries` has none) |

**No additive constant.** The coincidence views of P1c's trap (a reach that happens to equal a
hidden garbler point, e.g. a gadget point at a differing position when `Δ = pad₀ ⊕ pad₁`) are at
non-designed indices, so the designed view never contains them: such a coincidence is a stage-2
*touch* of a hidden entry by the adversary's own query, charged per query inside `L1`'s
`3/2^128` (the hidden point is `Δ`-uniform given the designed view). `GameUntilBad`'s error is
per-query only, and none is needed. `G1U` dominates the designed flagged law at this rule as at
every rule (`TwoStage.lateInstalled_ge`: `designedEntries ⊆ visibleEntries` by `List.filter`).

`stageOneGuess` (real): `StageOneGuess` at L1's constant. `hidden_of_stageTwo`: hop (1) from the one
remaining statement, `StageTwoGuess designedRule`.

The hidden hash entries at `u` are therefore the `limbCount ℓ` scale inputs of every active switch
(they carry the hidden active label), off the curve every scale input of system B, and, off the
curve, the bridge input.
-/

import Proof.Privacy.Phase3.Hidden.BridgeFamily

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden

noncomputable section

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- The input's bits on one coordinate. -/
def inputBits (input : AffineInput) : Coord → BitVec PlanB.coordinateBits
  | .x => coordinateBits input.x
  | .y => coordinateBits input.y

/-- A curve lane (system A). -/
def laneIsCurve : Lane → Bool
  | .curveX | .curveY => true
  | _ => false

/-- **The designed indices at an input.** -/
def designedIndex (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput) :
    FixedIndex → Bool
  | .hot ℓ c fold entry _ =>
      decide (entry.val ≠ (chunkOf (inputBits input ℓ.coord) c).val % 2 ^ fold.val) &&
        (laneIsCurve ℓ || validate input)
  | .gadget _ κ position bit =>
      validate input && decide ((inputBits input κ).getLsb position = bit)

/-- **The designed vector sites at an input**: the inactive switches, of a curve lane or on the
curve. -/
def designedSite (input : AffineInput) (site : VectorSite) : Bool :=
  decide (site.switch ≠ chunkOf (inputBits input site.lane.coord) site.chunk) &&
    (laneIsCurve site.lane || validate input)

open Classical in
/-- **The designed hash keys at an input**: a scale input of a designed site (whatever its limb
and label); off the scale range (the bridge input), on the curve. -/
def designedHash (input : AffineInput) (key : BaseField) : Bool :=
  if key.val < scaleRange then
    decide (∃ slot : LimbSite, ∃ label : Block, labelInput slot label = key ∧
      designedSite input slot.1 = true)
  else validate input

/-- **The designed-visibility rule.** -/
def designedRule : Designed := fun scalar tape input entry =>
  match entry.1 with
  | .fixedForward index _ | .fixedInverse index _ => designedIndex scalar tape input index
  | .hash key => designedHash input key
  | _ => false

/-- A scale input is designed exactly when its site is, whatever its label. -/
theorem designedHash_labelInput (input : AffineInput) (slot : LimbSite) (label : Block) :
    designedHash input (labelInput slot label) = designedSite input slot.1 := by
  unfold designedHash
  rw [if_pos (labelInput_val_lt slot label)]
  by_cases d : designedSite input slot.1 = true
  · rw [d]
    exact decide_eq_true ⟨slot, label, rfl, d⟩
  · rw [Bool.not_eq_true] at d
    rw [d]
    refine decide_eq_false fun ⟨slot', label', same, d'⟩ => ?_
    obtain ⟨rfl, rfl⟩ := labelInput_inj same
    rw [d] at d'
    cases d'

/-- The bridge input is designed exactly on the curve. -/
theorem designedHash_bridgeInput (input : AffineInput) (t : BaseField) :
    designedHash input (bridgeInput t) = validate input := by
  unfold designedHash
  rw [if_neg (bridgeInput_not_lt t)]

/-- Relabelling keeps every key's designation. -/
theorem designedHash_relabel (input : AffineInput) (shift : VectorSite → Block) (key : BaseField) :
    designedHash input (relabel shift key) = designedHash input key := by
  by_cases hit : ∃ slot label, labelInput slot label = key
  · obtain ⟨slot, label, rfl⟩ := hit
    rw [relabel_labelInput, designedHash_labelInput, designedHash_labelInput]
  · simp only [not_exists] at hit
    rw [relabel_of_not shift key hit]

end Instances

/-- **`StageOneGuess` at L1's constant, real.** -/
theorem stageOneGuess : StageOneGuess (ENNReal.ofReal hiddenCharge) :=
  stageOneGuess_of_bridge stageOneBridgeGuess

/-- **Hop (1) from the stage-2 guess at `designedRule` alone.** -/
theorem hidden_of_stageTwo (two : StageTwoGuess designedRule (ENNReal.ofReal hiddenCharge)) :
    Kriterion.ArgoMAC.Phase3.Glue.GameUntilBad maskSwappedHybrid hiddenDeletedHybrid
      fun first second => Kriterion.ArgoMAC.Phase3.Glue.hiddenPointError (first + second) :=
  hidden_of_guess designedRule stageOneGuess two

end

end Kriterion.ArgoMAC.Security.Phase3
