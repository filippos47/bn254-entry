/-
The design of the Plan B simulator machine: its exact instruction counts, and the
cost bound `code size + stage-1 fuel + stage-2 fuel ≤ 2 ^ 60` (in fact `< 2 ^ 35.8`).

The register / RAM / stack layout is `Construction/Simulator/Layout.lean`. The counts below are
closed formulas; the machine modules prove that their `Prog.size` / `Prog.cost` equal them
(`Construction/Simulator.lean`), so the numbers here are the machine's, not estimates.

**Static cost.** Every `Prog` has one cost on every non-aborting path (`ite` pads its cheaper
arm), so the fuels below are exact: a stage that does not abort halts after exactly its fuel.
The only data-dependent branch without padding is the top-level output-tag dispatch of stage 2,
whose fuel is the larger (valid) arm.

**Top-level code layout** (slot `0 .. size`):

| slots | contents |
|---|---|
| `0, 1` | pop the two protocol tag bits (`[f, f]` stage 1, `[f, t]` stage 2) |
| `2 ..` | stage 1, then `halt` |
| next | stage-2 prefix (parse, select labels), then `branch rFlag` |
| next | invalid arm (emit labels), then `halt` |
| next | valid arm (replay, opening, emit labels), then `halt` |
| last | reject `halt` |

**Where the charge goes** (`totalCost = 48,384,145,715 ≈ 2 ^ 35.49`): stage 1's `34,295`
bounded-rejection field cells and its big-integer serializer (`≈ 2.85 · 10 ^ 10` in code and
fuel), the replay's digit extraction of every switch mask vector (`1,588` vectors per lane,
`≈ 1.90 · 10 ^ 10`), and the opening's preimage sampler (`≈ 5.4 · 10 ^ 8`).
-/

import Construction.Simulator.Layout
import Construction.Simulator.Replay
import Construction.Simulator.Opening

namespace Kriterion.ArgoMAC.PlanB.SimMachine

namespace Design

/-! ### Oracle instruction counts -/

/-- Fixed-key fold queries of one lane: chunk `0` asks `2` (one step, one inactive entry), each
of the `48` width-`5` chunks `2 + 6 + 14 + 30 = 52`, each of the `3` width-`4` chunks
`2 + 6 + 14 = 22`. -/
def laneFoldQueries : Nat := 2 + 48 * 52 + 3 * 22

/-- Hash queries of one lane with `k` limbs per vector: `k` for each of the `3` inactive switches
of chunk `0`, the `31` of each width-`5` chunk and the `15` of each width-`4` chunk, `1536 k` in
all. -/
def laneHashQueries (limbs : Nat) : Nat := 3 * limbs + 48 * (31 * limbs) + 3 * (15 * limbs)

/-- All queries of one lane: the honest evaluator's `laneEvalBudget`,
`(2 + 3k) + 48 (52 + 31k) + 3 (22 + 15k)`. -/
def laneQueries (limbs : Nat) : Nat := laneFoldQueries + laneHashQueries limbs

/-- Stage 2's lane queries: the replay's fixed-key fold queries and scale hash queries of systems
A and B (`k = 4, 3, 362, 272`), less the `362` designated limbs of lane `pointX` (which the
opening programs instead); `laneReplayQueries_split` separates the two kinds. -/
def laneReplayQueries : Nat :=
  laneQueries 4 + laneQueries 3 + laneQueries 362 - 362 + laneQueries 272

/-- The replay's fixed-key fold queries. -/
def foldQueries : Nat := 4 * laneFoldQueries

/-- The replay's scale hash queries: every inactive vector's limbs but the designated ones. -/
def hashQueries : Nat :=
  laneHashQueries 4 + laneHashQueries 3 + laneHashQueries 362 - 362 + laneHashQueries 272

/-- Stage 2's oracle queries: systems A and B, one bridge hash, `508` EncPRF pads. -/
def stage2Queries : Nat := laneReplayQueries + 1 + 508

/-- Stage 2's programs: the `362` designated hash limbs. -/
def stage2Programs : Nat := limbCount .pointX

theorem laneQueries_eq (limbs : Nat) : laneQueries limbs = 2564 + 1536 * limbs := by
  unfold laneQueries laneFoldQueries laneHashQueries
  omega

/-- The lane queries split into the fold's fixed-key queries and the scale hash queries. -/
theorem laneReplayQueries_split : laneReplayQueries = foldQueries + hashQueries := by
  unfold laneReplayQueries foldQueries hashQueries laneQueries laneHashQueries
  omega

theorem foldQueries_eq : foldQueries = 10256 := by
  unfold foldQueries laneFoldQueries
  norm_num

theorem hashQueries_eq : hashQueries = 984214 := by
  unfold hashQueries laneHashQueries
  norm_num

theorem laneReplayQueries_eq : laneReplayQueries = 994470 := by
  rw [laneReplayQueries_split, foldQueries_eq, hashQueries_eq]

theorem stage2Queries_eq : stage2Queries = 994979 := by
  unfold stage2Queries
  rw [laneReplayQueries_eq]

theorem stage2Programs_eq : stage2Programs = 362 := rfl

/-- The honest evaluator's `1,042,077` queries are the machine's `994,979` plus the `362`
designated limbs, which it programs instead, the `508` bit-`true` pads it may ask, and the
`46,228` gadget hashes (`508` per digit: one mask per digit unlocks both exceptional slots),
which the opening does not need. -/
theorem evaluator_queries : stage2Queries + stage2Programs + 508 + 46228 = 1042077 := by
  rw [stage2Queries_eq, stage2Programs_eq]

/-! ### Instruction counts -/

/-- The serializer: `2 + 3 · width` per emitted word; each chunk word is built by the big-integer
Horner encoder over the `903`-limb scratch, emitted as `636 · 256` bits, and its scratch cleared;
the curve-and-rows word likewise, emitted as `902 · 256 + 120` bits. -/
def serializeCount : Nat :=
  52 * (4 + BigInt.macPassesCost serialLimbCount 642 + (2 + 3 * topLimbBits) +
    (chunkLimbCount - 1) * (2 + 3 * 256) + (1 + serialLimbCount * 2)) +
    hotBlockCount * (2 + 3 * 128) +
    ((2 + 3 * 4) + exceptionByteCount * (2 + 3 * 3)) +
    (4 + BigInt.macPassesCost serialLimbCount (curveCellCount + rowCellCount) +
      (2 + 3 * fieldsTopLimbBits) + (fieldsLimbCount - 1) * (2 + 3 * 256) +
      (1 + serialLimbCount * 2))

/-- Stage 1: code slots and fuel. -/
def stage1Size : Nat :=
  fieldCellCount * 457231 + exceptionByteCount * 27 + hotBlockCount * 902 +
    keyBlockCount * 902 + serializeCount + 16
def stage1Cost : Nat :=
  fieldCellCount * 327180 + exceptionByteCount * 21 + hotBlockCount * 646 +
    keyBlockCount * 646 + serializeCount + 16

/-- The stage-2 prefix (parse, select labels, tag sum). -/
def prefixSize : Nat := 9692 + (labelCount * 11 + 4) + 5
def prefixCost : Nat := 5109 + (labelCount * 11 + 4) + 5

/-- The invalid arm: emit the labels. -/
def invalidSize : Nat := labelCount * (2 + 3 * 128)

/-- The replay (`Replay.programSize`, `Replay.programCost`). -/
def replaySize : Nat := Replay.programSize
def replayCost : Nat := Replay.programCost

/-- The opening (`Opening.programSize`, `Opening.programCost`). -/
def openingSize : Nat := Opening.programSize
def openingCost : Nat := Opening.programCost

/-- The valid arm. -/
def validSize : Nat := replaySize + openingSize + labelCount * (2 + 3 * 128)
def validCost : Nat := replayCost + openingCost + labelCount * (2 + 3 * 128)

/-! ### The top-level layout -/

def stage1Base : Nat := 2
def stage1Halt : Nat := stage1Base + stage1Size
def stage2Base : Nat := stage1Halt + 1
def branchAt : Nat := stage2Base + prefixSize
def invalidBase : Nat := branchAt + 1
def invalidHalt : Nat := invalidBase + invalidSize
def validBase : Nat := invalidHalt + 1
def validHalt : Nat := validBase + validSize
def rejectAt : Nat := validHalt + 1

/-- The code table has `size + 1` slots. -/
def size : Nat := rejectAt

/-- Stage 1: two pops, stage 1, halt. -/
def firstFuel : Nat := 2 + stage1Cost + 1

/-- Stage 2: two pops, the prefix, the branch, the valid arm (the costlier one), halt. -/
def secondFuel : Nat := 2 + prefixCost + 1 + validCost + 1

/-- **The simulator's charge**, `size + 1 + firstFuel + secondFuel`. -/
def totalCost : Nat := size + 1 + firstFuel + secondFuel

/-! The closed formulas are unfolded (never rewritten by their equation lemmas) and evaluated
by `norm_num`; every term is a sum or product of numerals below `2 ^ 36`. -/

theorem stage1Size_eq : stage1Size = 16483270400 := by
  unfold stage1Size serializeCount fieldCellCount curveCellCount rowCellCount scaleCellCount
    exceptionByteCount hotBlockCount keyBlockCount BigInt.macPassesCost BigInt.macPassCost
    serialLimbCount chunkLimbCount topLimbBits fieldsLimbCount fieldsTopLimbBits
  norm_num

theorem stage1Cost_eq : stage1Cost = 12022697859 := by
  unfold stage1Cost serializeCount fieldCellCount curveCellCount rowCellCount scaleCellCount
    exceptionByteCount hotBlockCount keyBlockCount BigInt.macPassesCost BigInt.macPassCost
    serialLimbCount chunkLimbCount topLimbBits fieldsLimbCount fieldsTopLimbBits
  norm_num

theorem replaySize_eq : replaySize = 9518946919 := by
  unfold replaySize Replay.programSize Replay.laneSize Replay.chunkSize Replay.foldSize
    Replay.switchSize BigInt.digitsOfCost BigInt.digitStepCost
  norm_num

theorem replayCost_eq : replayCost = 9510713367 := by
  unfold replayCost Replay.programCost Replay.laneCost Replay.chunkCost Replay.foldCost
    Replay.switchCost BigInt.digitsOfCost BigInt.digitStepCost
  norm_num

theorem openingSize_eq : openingSize = 449262537 := by
  unfold openingSize Opening.programSize BigInt.preimageSamplerSize BigInt.tAttemptSize
    BigInt.useKeptCost BigInt.macPassesCost BigInt.macPassCost BigInt.samplerLimbs
    BigInt.samplerDigits BigInt.samplerAttempts BigInt.hiWidth
  norm_num

theorem openingCost_eq : openingCost = 398640360 := by
  unfold openingCost Opening.programCost BigInt.preimageSamplerCost BigInt.tAttemptCost
    BigInt.useKeptCost BigInt.macPassesCost BigInt.macPassCost BigInt.samplerLimbs
    BigInt.samplerDigits BigInt.samplerAttempts BigInt.hiWidth
  norm_num

theorem validSize_eq : validSize = 9968405544 := by
  unfold validSize labelCount
  rw [replaySize_eq, openingSize_eq]

theorem validCost_eq : validCost = 9909549815 := by
  unfold validCost labelCount
  rw [replayCost_eq, openingCost_eq]

theorem size_eq : size = 26451887327 := by
  unfold size rejectAt validHalt validBase invalidHalt invalidBase branchAt stage2Base stage1Halt
    stage1Base
  rw [stage1Size_eq, validSize_eq]
  unfold prefixSize invalidSize labelCount
  norm_num

theorem firstFuel_eq : firstFuel = 12022697862 := by
  unfold firstFuel
  rw [stage1Cost_eq]

theorem secondFuel_eq : secondFuel = 9909560525 := by
  unfold secondFuel
  rw [validCost_eq]
  unfold prefixCost labelCount
  norm_num

/-- **The exact charge** of the machine. -/
theorem totalCost_eq : totalCost = 48384145715 := by
  unfold totalCost
  rw [size_eq, firstFuel_eq, secondFuel_eq]

/-- **The cost bound**: `size + 1 + firstFuel + secondFuel ≤ 2 ^ 60`. -/
theorem totalCost_le : totalCost ≤ 2 ^ 60 := by
  rw [totalCost_eq]; norm_num

/-- The code table's address bound. -/
theorem size_lt : size < 2 ^ 256 := by rw [size_eq]; norm_num

end Design

end Kriterion.ArgoMAC.PlanB.SimMachine
