/-
**Phase 3, P4 — `I^U`: the ideal game with every derived switch-mask vector programmed uniform.**

`I` (`Glue.idealHybrid`) answers the simulator's honest evaluation from the shared lazy oracle
(`Glue.runIntercept`): a fresh hash query at a scale input is a uniform answer, stored. `I^U`
differs in exactly one place. At the start of the opening it draws a **mask tape** -- one hash
answer per (vector site, limb), the `5,584` switch-mask vectors iid uniform on `F_p^n` and the tape
uniform on the `sampleLane` fibre of `masksOf` (`uniformMaskTape`; the fibre kernel of P1's
`G0 → G0U` swap) -- and a non-designated hash query at a scale input is answered from the tape when
it is the **first stage-2 touch of its cell at a fresh input** (`consumeCell`): the simulator
*programs* `input ↦ tape cell`. A hash program needs only a fresh input
(`LazyOracle.program (.hash _)`), and a cell is consumed only at an input the lazy table does not
hold, so the program always succeeds. Every other query -- a touched cell, a stored input (the
cached answer is returned, as in `I`), the bridge hash `bridgeInput t` (outside the scale range),
the fold and the gadget (fixed-key), EncPRF -- goes to the lazy oracle exactly as in `I`.

A cell (`Cell = MaskSwap.LimbSite`) is a vector site `(lane, chunk, switch)` and one of its
`limbCount lane` limbs; its hash inputs are `cellInput cell label = scaleInput lane chunk switch
limb label`, pairwise distinct over (cell, label) (`cellInput_injective`, from
`PlanB.scaleInput_injective`). It is stated for an arbitrary query computation, so no fact about the
evaluator's query order is used anywhere in the `I^U → I` bound.

The runner `runRefill` takes the per-cell law as a parameter `draw`: `I^U` reads the tape
(`draw = pure ∘ tape`), and the proof's intermediate game draws a fresh uniform answer per consumed
cell (`draw = uniform`), which is `I` itself (`StepBound.runRefill_uniform_eq`).
-/

import Proof.Privacy.Phase3.GameSwap

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.Phase3 (VectorSite LimbSite MaskVectors masksOf masksOf_surjective
  fibreLaw)
open scoped ENNReal

noncomputable section

/-! ### Cells, tapes and the lazy state

Every definition below takes the index types' `DecidableEq` instances as arguments (as
`Glue.runIntercept` does), so that at the `Solution` instances (`Classical.decEq`, via
`atSolution`) the refill game and `I` use the same instances; the derived global instances are
never used. -/

section Definitions

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A switch-mask vector site and one of its hash limbs. -/
abbrev Cell := LimbSite

/-- One hash answer per cell. -/
abbrev Tape := Cell → Block × Block

/-- The lazy oracle state of Plan B. -/
abbrev LState := LazyOracle.State FixedIndex EncPRF.PermutationIndex

/-- The designated labels recorded by the intercepting run, one per limb. -/
abbrev Record := DesignatedRecord

/-- A Plan B public query. -/
abbrev Request := PublicQuery FixedIndex EncPRF.PermutationIndex

/-- The hash input of a cell at a label: `scaleInput lane chunk switch limb label`. -/
def cellInput (cell : Cell) (label : Block) : BaseField :=
  scaleInput cell.1.lane cell.1.chunk cell.1.switch.val cell.2.val label

/-- **The cell inputs are pairwise distinct over (cell, label)** (`scaleInput_injective`: the
switch is below `2 ^ chunkBits` and the limb below `512`). -/
theorem cellInput_injective :
    Function.Injective fun pair : Cell × Block => cellInput pair.1 pair.2 := by
  rintro ⟨⟨⟨lane, chunk, switch⟩, limb⟩, label⟩ ⟨⟨⟨lane', chunk', switch'⟩, limb'⟩, label'⟩ same
  simp only [cellInput] at same
  have widthBound : ∀ c : Fin chunkCount, 2 ^ chunkWidth c ≤ 2 ^ chunkBits := fun c =>
    Nat.pow_le_pow_right (by norm_num) (chunkWidth_le c)
  obtain ⟨rfl, rfl, switchEq, limbEq, rfl⟩ := scaleInput_injective
    (lt_of_lt_of_le switch.isLt (widthBound _)) (lt_of_lt_of_le switch'.isLt (widthBound _))
    (lt_trans limb.isLt (limbCount_lt _)) (lt_trans limb'.isLt (limbCount_lt _)) same
  obtain rfl : switch = switch' := Fin.ext switchEq
  obtain rfl : limb = limb' := Fin.ext limbEq
  rfl

open Classical in
/-- The cell of a hash input, if it is a cell input (`cellInput_injective`). -/
def cellOf (input : BaseField) : Option Cell :=
  if h : ∃ cell : Cell, ∃ label, cellInput cell label = input then some (Classical.choose h)
  else none

theorem cellOf_spec {input : BaseField} {cell : Cell} (found : cellOf input = some cell) :
    ∃ label, cellInput cell label = input := by
  unfold cellOf at found
  split at found
  · rename_i h
    cases found
    exact Classical.choose_spec h
  · cases found

theorem cellOf_cellInput (cell : Cell) (label : Block) :
    cellOf (cellInput cell label) = some cell := by
  have exists_cell : ∃ other : Cell, ∃ label', cellInput other label' = cellInput cell label :=
    ⟨cell, label, rfl⟩
  unfold cellOf
  rw [dif_pos exists_cell]
  obtain ⟨label', same⟩ := Classical.choose_spec exists_cell
  exact congrArg some (congrArg Prod.fst (cellInput_injective (a₁ := (_, label'))
    (a₂ := (cell, label)) same))

/-- The cell a request touches: a hash query at a cell input. -/
def touchedCell : Request → Option Cell
  | .fixedForward _ _ => none
  | .fixedInverse _ _ => none
  | .encForward _ _ => none
  | .encInverse _ _ => none
  | .hash input => cellOf input

/-- The touched cells after a request. -/
def touch (request : Request) (touched : Set Cell) : Set Cell :=
  {cell | cell ∈ touched ∨ touchedCell request = some cell}

theorem subset_touch (request : Request) (touched : Set Cell) :
    touched ⊆ touch request touched := fun _ member => Or.inl member

open Classical in
/-- **The consuming rule, at a hash input.** A cell input whose cell no stage-2 query has touched
yet, at an input the lazy table does not hold, reads the tape cell. -/
def consumeHash (touched : Set Cell) (oracle : LState) (input : BaseField) : Option Cell :=
  match cellOf input with
  | some cell => if cell ∈ touched ∨ oracle.hash.lookup input ≠ none then none else some cell
  | none => none

/-- **The consuming rule.** Only hash queries are consumed (`consumeHash`). -/
def consumeCell (touched : Set Cell) (oracle : LState) : Request → Option Cell
  | .fixedForward _ _ => none
  | .fixedInverse _ _ => none
  | .encForward _ _ => none
  | .encInverse _ _ => none
  | .hash input => consumeHash touched oracle input

/-- What a consuming request looks like. -/
theorem consumeCell_spec {touched : Set Cell} {oracle : LState} {request : Request}
    {cell : Cell} (consumed : consumeCell touched oracle request = some cell) :
    ∃ input, request = .hash input ∧ cell ∉ touched ∧ oracle.hash.lookup input = none ∧
      cellOf input = some cell := by
  cases request with
  | fixedForward _ _ => cases consumed
  | fixedInverse _ _ => cases consumed
  | encForward _ _ => cases consumed
  | encInverse _ _ => cases consumed
  | hash input =>
      change consumeHash touched oracle input = some cell at consumed
      unfold consumeHash at consumed
      split at consumed
      · rename_i found
        split_ifs at consumed with used
        cases consumed
        exact ⟨input, rfl, fun member => used (Or.inl member),
          not_not.mp fun stored => used (Or.inr stored), found⟩
      · cases consumed

/-- A consumed cell is touched afterwards. -/
theorem mem_touch_of_consumeCell {touched : Set Cell} {oracle : LState} {request : Request}
    {cell : Cell} (consumed : consumeCell touched oracle request = some cell) :
    cell ∈ touch request touched := by
  obtain ⟨input, rfl, _, _, found⟩ := consumeCell_spec consumed
  exact Or.inr found

/-- The answer a consumed cell gives: the tape's hash answer. (Only hash queries are ever
consumed.) -/
def refillAnswer : (request : Request) → Block × Block → request.Answer
  | .fixedForward _ _, value => value.1
  | .fixedInverse _ _, value => value.1
  | .encForward _ _, value => value.1
  | .encInverse _ _, value => value.1
  | .hash _, value => value

/-! ### The refill runner -/

/-- **The `I^U` runner.** Designated queries are intercepted exactly as in `Glue.runIntercept`; a
consuming query (`consumeCell`) programs `input ↦ value` with `value` drawn from `draw cell`, and a
failed program aborts (it never fails: a consumed input is fresh); every other query goes to the
lazy oracle. -/
def runRefill (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type} :
    FreeQuery Programs.Spec α → LState → Record → Set Cell → PMF (Option (α × LState × Record))
  | .pure value, oracle, record, _ => PMF.pure (some (value, oracle, record))
  | .query request next, oracle, record, touched =>
      match interceptAnswer bits request with
      | some answer => runRefill bits draw (next answer) oracle (recordAfter bits request record)
          touched
      | none => match consumeCell touched oracle request with
        | some cell => (draw cell).bind fun value =>
            match LazyOracle.program request (refillAnswer request value) oracle with
            | none => PMF.pure none
            | some updated => runRefill bits draw (next (refillAnswer request value)) updated
                record (touch request touched)
        | none => (LazyOracle.query request oracle).bind fun answer =>
            runRefill bits draw (next answer.1) answer.2 record (touch request touched)

/-- **The `I^U` mask tape**: the `5,584` switch-mask vectors iid uniform on `F_p^n`, then the tape
uniformly among those that produce them -- each vector's limbs a uniform `sampleLane`-preimage of a
uniform vector, independently across vectors. -/
def uniformMaskTape : PMF Tape :=
  (PMF.uniformOfFintype MaskVectors).bind
    (fibreLaw (masksOf VectorSite.lane) (masksOf_surjective VectorSite.lane))

/-- The `I^U` run of a query computation: the tape, then the refill runner reading it. -/
def refillRun {α : Type} (bits : BitInput) (computation : FreeQuery Programs.Spec α)
    (oracle : LState) : PMF (Option (α × LState × Record)) :=
  uniformMaskTape.bind fun tape =>
    runRefill bits (fun cell => PMF.pure (tape cell)) computation oracle noRecord ∅

/-! ### `I^U` -/

/-- The opening after its honest run (`Glue.opening`, steps 2–5): the tail, the lifts, the
designated vector's free coordinates and collector solve, its `452` hash answers
(`Glue.openingLimbs`), the `452` programs. -/
def openingCont [FieldCertificate] [GroupCertificate] (samplers : Samplers) (table : Public)
    (input : AffineInput) (labels : LamportSignature) (target : Point)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record) : PMF (Option LState) :=
  let restored := Lamport.restore input labels
  (openingLimbs samplers table restored.input target ran.1.1 ran.1.2).bind fun answers =>
    match answers with
    | none => PMF.pure none
    | some answers => PMF.pure (programAll (programRequests restored.input ran.2.2 answers) ran.2.1)

/-- `Glue.opening` is its honest run followed by `openingCont`. -/
theorem opening_eq [FieldCertificate] [GroupCertificate] (samplers : Samplers) (table : Public)
    (input : AffineInput) (labels : LamportSignature) (target : Point) (oracle : LState) :
    opening samplers table input labels target oracle =
      (runIntercept (Lamport.restore input labels).input
          (openingQueriesM table (Lamport.restore input labels).input
            (Lamport.restore input labels).inputMac) oracle noRecord).bind
        (openingCont samplers table input labels target) := rfl

/-- **The `I^U` opening**: the refill run in place of the intercepting run; an abort of the run
aborts the opening. -/
def refillOpening [FieldCertificate] [GroupCertificate] (samplers : Samplers) (table : Public)
    (input : AffineInput) (labels : LamportSignature) (target : Point) (oracle : LState) :
    PMF (Option LState) :=
  let restored := Lamport.restore input labels
  (refillRun restored.input (openingQueriesM table restored.input restored.inputMac) oracle).bind
    fun ran => match ran with
    | none => PMF.pure none
    | some ran => openingCont samplers table input labels target ran

/-- The `I^U` stage 2: as `planBAbstractSimulator`, with the refill opening. -/
def refillStage2 [FieldCertificate] [GroupCertificate] (samplers : Samplers)
    (source : Stage1Source) (input : AffineInput) (output : Option Point) (oracle : LState) :
    PMF (Option (LamportSignature × LState)) :=
  let labels := Lamport.selectedLabels (source.key.encode (BitInput.ofAffine input))
  match output with
  | none => PMF.pure (some (labels, oracle))
  | some target => (refillOpening samplers source.publicValue input labels target oracle).map
      (Option.map fun updated => (labels, updated))

/-- **The `I^U` abstract simulator**: `planBAbstractSimulator` with the refill stage 2. -/
def refillSimulator [FieldCertificate] [GroupCertificate] (samplers : Samplers) :
    LazyAbstractSimulator FixedIndex EncPRF.PermutationIndex Public :=
  { planBAbstractSimulator samplers with stage2 := refillStage2 samplers }

end Definitions

/-- **`I^U` as a chain game** (the `Hybrids.idealUniform` field): the abstract ideal game of the
refill simulator with the exact samplers. -/
def idealUniformHybrid : HybridGame := fun adversary parameter scalar =>
  abstractIdealGame Scheme.scheme (refillSimulator idealSamplers) adversary parameter scalar ()

end

end Kriterion.ArgoMAC.Phase3.Lazy
