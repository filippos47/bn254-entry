/-
Stage 2 of the Plan B simulator: the common prefix (parse, select the `508` labels from the
stage-1 key), then one of two arms chosen by the output tag:

* `invalid` (`f_k u = none`): emit the labels. No oracle instruction.
* `valid`: the replay of the honest queries (`Replay.program`), the opening with its `362`
  hash programs (`Opening.program`), then emit the labels.
-/

import Construction.Simulator.Opening
import Construction.Simulator.Request

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine Blocks Prog

namespace Stage2

variable (ordF : FixedIndex → Nat) (ordE : EncPRF.PermutationIndex → Nat)

/-- The arm for an undefined output. -/
def invalid : Prog := Request.emitLabels

/-- The arm for a defined output. -/
def valid : Prog :=
  seqList [Replay.program ordF ordE, Opening.program, Request.emitLabels]

theorem size_invalid : invalid.size = labelCount * (2 + 3 * 128) := Request.size_emitLabels
theorem cost_invalid : invalid.cost = labelCount * (2 + 3 * 128) := Request.cost_emitLabels

theorem size_valid : (valid ordF ordE).size =
    Replay.programSize + Opening.programSize + labelCount * (2 + 3 * 128) := by
  unfold valid
  rw [seqList, seqList, seqList, seqList, Prog.size_seq, Prog.size_seq, Prog.size_seq,
    Replay.size_program, Opening.size_program, Request.size_emitLabels]
  rfl

theorem cost_valid : (valid ordF ordE).cost =
    Replay.programCost + Opening.programCost + labelCount * (2 + 3 * 128) := by
  unfold valid
  rw [seqList, seqList, seqList, seqList, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq,
    Replay.cost_program, Opening.cost_program, Request.cost_emitLabels]
  rfl

end Stage2

end Kriterion.ArgoMAC.PlanB.SimMachine
