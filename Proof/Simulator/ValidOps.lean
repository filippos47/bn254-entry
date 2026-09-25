/-
**The valid arm's oracle operations** (`valid_ops`): every operation of `Stage2.valid` satisfies
`ValidOracle` — fixed-key forward queries (`query 0`, the fold), EncPRF forward queries
(`query 2`, the whitening pads), hash queries (`query 4`, the scale limbs and the bridge) and hash
programs (`program 4`, the `362` designated limbs), all on the fixed operand registers; no lookup.

The big-integer blocks are oracle-free: digit extraction is plain (`plain_digitsOf`,
`IsPlain.noOracle`) and the preimage sampler draws coins only (`noOracle_preimageSampler`).
Straight-line blocks are split operation by operation (`ops_split`).
-/

import Proof.Simulator.BigIntSampler

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine Blocks

/-- An oracle-free block satisfies `ValidOracle`. -/
theorem validOps_of_noOracle {program : Prog} (free : program.NoOracle) :
    program.OpsSatisfy ValidOracle :=
  opsSatisfy_of_noOracle validOracle_plain program free

/-- Split a block into its operations and discharge each one: a plain operation by computation,
an oracle operation by its fixed shape, an unrolled `rep` body by body, a static `if` by cases. -/
macro "ops_split" : tactic => `(tactic| repeat' (first
  | exact trivial
  | rfl
  | decide
  | refine ⟨?_, ?_⟩
  | refine opsSatisfy_rep _ _ fun _ _ => ?_
  | split))

section Valid

variable (ordF : PlanB.FixedIndex → Nat) (ordE : EncPRF.PermutationIndex → Nat)

theorem replay_digitsOf (base count digits digitBase : Nat) :
    (BigInt.digitsOf base count digits digitBase).OpsSatisfy ValidOracle :=
  validOps_of_noOracle (BigInt.plain_digitsOf base count digits digitBase).noOracle

theorem replay_switchStep (spec : Replay.LaneSpec) (designated : Bool) (chunk switch : Nat) :
    (Replay.switchStep spec designated chunk switch).OpsSatisfy ValidOracle := by
  unfold Replay.switchStep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, replay_digitsOf _ _ _ _, ?_, trivial⟩ <;> ops_split

theorem replay_chunkBody (spec : Replay.LaneSpec) (designated : Bool) (chunk : Nat) :
    (Replay.chunkBody ordF spec designated chunk).OpsSatisfy ValidOracle := by
  unfold Replay.chunkBody
  refine ⟨?_, opsSatisfy_rep _ _ fun _ _ => ?_, ?_,
    opsSatisfy_rep _ _ fun _ _ => replay_switchStep _ _ _ _, ?_, ?_, trivial⟩
  · unfold Replay.chunkPrefix; ops_split
  · unfold Replay.foldStep Replay.foldEntry Replay.foldGate Replay.foldPair Replay.absorbEntry
      Replay.extendEntry
    ops_split
  · cases designated
    · trivial
    · unfold Replay.designatedPart Replay.designatedPrefix; ops_split
  · ops_split
  · unfold Replay.joinTerm; ops_split

theorem replay_ops : (Replay.program ordF ordE).OpsSatisfy ValidOracle := by
  unfold Replay.program Replay.lane Replay.designatedLane
  have lane (spec : Replay.LaneSpec) (designated : Bool) :
      (Prog.seq (Replay.chunkBody ordF spec designated 0) (Prog.rep (chunkCount - 1) fun chunk =>
        Replay.chunkBody ordF spec false (chunk + 1))).OpsSatisfy ValidOracle :=
    ⟨replay_chunkBody ordF _ _ _, opsSatisfy_rep _ _ fun _ _ => replay_chunkBody ordF _ _ _⟩
  refine ⟨?_, lane _ _, lane _ _, ?_, ?_, lane _ _, lane _ _⟩
  · unfold Replay.initAcc; ops_split
  · unfold Replay.bridge; ops_split
  · unfold Replay.whiten Replay.whitenOne; ops_split

theorem opening_ops : Opening.program.OpsSatisfy ValidOracle := by
  unfold Opening.program
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    validOps_of_noOracle (BigInt.noOracle_preimageSampler _ _ _ _ _), ?_,
    validOps_of_noOracle (noOracle_zeroRegs _), trivial⟩
  · unfold Opening.tail Opening.tailOne Opening.storeCurvePoint Opening.testCurveX
      Opening.curveRoot Opening.sqrtRound
    ops_split
  · unfold Opening.horner Opening.clearP Opening.hornerStep Opening.head Opening.betaMul
      Opening.copyPoint Opening.betaRound Opening.loadPoint Opening.storePoint
    ops_split
  · unfold Opening.lambdas Opening.lambdaOne; ops_split
  · unfold Opening.lifts Opening.liftOne Opening.loadPoint; ops_split
  · unfold Opening.nonCollectors Opening.nonCollectorOne Opening.storeNonCollector; ops_split
  · unfold Opening.solve Opening.solveDigit Opening.addScaled Opening.addCell Opening.finishTarget
      Opening.finishScaled
    ops_split
  · unfold Opening.programs Opening.programOne; ops_split

/-- **The valid arm issues only the four allowed oracle shapes.** -/
theorem valid_ops : (Stage2.valid ordF ordE).OpsSatisfy ValidOracle := by
  unfold Stage2.valid
  exact ⟨replay_ops ordF ordE, opening_ops,
    validOps_of_noOracle (noOracle_rep _ _ fun _ _ => noOracle_emitWord _ _), trivial⟩

end Valid

end Kriterion.ArgoMAC.PlanB.SimMachine
