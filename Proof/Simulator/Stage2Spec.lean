/-
**Stage 2, the interface of the opening** (the one open premise of `Stage2Law`).

The valid arm is `Replay.program`, then `Opening.program`, then the label emission.
`Opening.program` is the oracle-free part `openingFree` (the tail points, Horner and the head
clamp, the `91` randomiser pairs, the lifts, the `91` non-collectors, the collector solve and the
preimage sampler) followed by the `362` programs and a register clear. This file states what the
oracle-free part must do:

* `OpeningPre`: what it may read, as left by the prefix and the replay -- the request cells, the
  row constants, the two point lanes' (designated-free) accumulators and `κ`;
* the abstract counterpart is P3's `openingLimbs`, the part of the opening between the replay and
  `programAll` (tail, lift, free coordinates, collector solve, preimage), for the extracted table
  and the replay's lanes;
* `OpeningLaw`: the law of `openingFree.memSem`, read through `openView` (the `724` half cells the
  programs read, the cells `tmpJStar` and `E*`, the labels and the response stack), is the law of
  `openingLimbs`, read through `blocksView` (the drawn limbs' halves, the other four unchanged).

Everything else of `Stage2Law` (prefix, replay, programs, emission, the invalid arm) is proved
from `OpeningLaw` in `Stage2Valid.lean`.
-/

import Proof.Simulator.ReplayBase

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-- **The oracle-free part of the opening**: `Opening.program` without its `362` programs and
the final register clear. -/
def openingFree : Prog :=
  Prog.seqList [Opening.tail, Opening.horner, Opening.lambdas, Opening.lifts,
    Opening.nonCollectors, Opening.solve, Opening.preimage]

/-- The half cells the programs read: `halfCell i`, `i < 2 · 362`. -/
def halfCell (half : Nat) : Nat := BigInt.halfBase samplerBase BigInt.samplerLimbs + half

/-- Half `i` of `362` limbs: the low block of limb `⌊i / 2⌋` at even `i`, the high block at odd
`i` (the order the programs read, `Opening.programOne`). -/
def limbHalf (limbs : DesignatedLimbs) (half : Fin (2 * limbCount .pointX)) : Block :=
  if half.val % 2 = 0 then (limbs ⟨half.val / 2, by have := half.isLt; omega⟩).1
  else (limbs ⟨half.val / 2, by have := half.isLt; omega⟩).2

section Spec

variable [FieldCertificate]

/-- The output cells the head clamp reads, `(tag₀, Q.x, Q.y)`: `(0, 0, 0)` for `O`. -/
def outputWords : Point → Word × Word × Word
  | .zero => (bitWord false, word 0, word 0)
  | .some (x := x) (y := y) _ => (bitWord true, fieldWord x, fieldWord y)

/-- **What the oracle-free opening may assume** about the memory it starts from (registers and
every other cell arbitrary). `bits = BitInput.ofAffine input` is the selected input. -/
structure OpeningPre (source : Stage1Source) (input : AffineInput) (target : Point)
    (pointX : Fin pointElementCountX → BaseField) (pointY : Fin pointElementCountY → BaseField)
    (memory : Memory) : Prop where
  /-- `u.x` and `u.y`. -/
  reqXCell : memory.ram (word reqX) = fieldWord input.x
  reqYCell : memory.ram (word reqY) = fieldWord input.y
  /-- `tag₀`, `Q.x`, `Q.y` of the output `Q = f_k(u)`. -/
  outputCells : (memory.ram (word reqTag0), memory.ram (word reqQX), memory.ram (word reqQY)) =
    outputWords target
  /-- The row constants of every digit, in wire (cell) order (`rowField`: `xC0, xC1, xC2, xC4,
  yC0, yC2, yC4, yC5, zC0, zC1`). -/
  rowCells : ∀ (digit : Fin digitCount) (slot : Nat), slot < 10 →
    memory.ram (word (Opening.rowCell digit.val slot)) = fieldWord (rowField (source.rows.get digit) slot)
  /-- The `pointX` lane's (designated-free) values, slots `0 .. 363`. -/
  accXCells : ∀ element : Fin pointElementCountX,
    memory.ram (word (accBase + element.val)) = fieldWord (pointX element)
  /-- The `pointY` lane's values, slots `367 .. 639`. -/
  accYCells : ∀ element : Fin pointElementCountY,
    memory.ram (word (accBase + 367 + element.val)) = fieldWord (pointY element)
  /-- `κ = ι(j*) − ι(α₀)`. -/
  kappaCell : memory.ram (word tmpKappa) = fieldWord (kappa (BitInput.ofAffine input))

end Spec

/-- What the programs and the label emission read after the oracle-free opening. -/
abbrev OpenView :=
  (Fin (2 * limbCount .pointX) → Word) × Word × Word × Vector Block 508 × List Bool

/-- The machine's view: the `724` half cells, `tmpJStar`, `E*`, the labels, the response stack. -/
def openView (memory : Memory) : OpenView :=
  (fun half => memory.ram (word (halfCell half.val)), memory.ram (word tmpJStar),
    memory.ram (word designatedLabel), labelVector memory.ram, memory.bits 3)

/-- The abstract view: the drawn limbs' halves, the other cells as they were. -/
def blocksView (memory : Memory) (limbs : DesignatedLimbs) : OpenView :=
  (fun half => blockWord (limbHalf limbs half), memory.ram (word tmpJStar),
    memory.ram (word designatedLabel), labelVector memory.ram, memory.bits 3)

/-- **The opening law**: from every memory satisfying `OpeningPre`, the oracle-free opening's
law, read through `openView`, is `openingLimbs` of the machine's samplers, read through
`blocksView`. -/
def OpeningLaw : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (source : Stage1Source) (input : AffineInput)
    (target : Point) (pointX : Fin pointElementCountX → BaseField)
    (pointY : Fin pointElementCountY → BaseField) (memory : Memory),
    OpeningPre source input target pointX pointY memory →
      (openingFree.memSem memory).map (Option.map openView) =
        (openingLimbs boundedSamplers source.publicValue (BitInput.ofAffine input) target pointX
          pointY).map (Option.map (blocksView memory))

end

end Kriterion.ArgoMAC.PlanB.SimMachine
