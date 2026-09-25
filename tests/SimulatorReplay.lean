import Construction.Simulator
import Construction.OraclePrograms
import Construction.ArgoMAC.Seed

/-!
T9b checks: the stage-2 machine code of the simulator, run by a small executable interpreter
(`exec`) whose oracle instructions are answered by the seeded benchmark tape
(`Seed.randomness 0x5eed`: fixed-key and EncPRF permutations are shifts by derived blocks, the
hash is `Seed`'s hash), against the construction's honest evaluator on the same tape.

* `laneCheck lane`: a whole system-A lane (`Replay.lane`, 56 chunks of widths `2`, `5` and `4`,
  and `1,396` digit extractions) on random joins, scale cells, bits and labels: the accumulators
  equal `evalCoord` and the evaluator program's result, and the machine's query sequence is exactly
  `Programs.evalLaneM`'s (kind, index code, input), in order.
* `designatedCheck`: the designated chunk code (`Replay.chunkBody … true 0`) on lane `curveX` and
  on the real lane `pointX` (four full-size switch steps, `k = 452`, `n = 455`): the machine skips
  exactly the `limbCount` limbs of `j* = α ⊕ 1` from the evaluator's chunk-`0` queries, its
  accumulators miss exactly `κ · Y_{j*}`, and it records `j*`, `E*` and `κ`.
* `bridgeCheck`: the bridge asks `bridgeInput t` (both branches: `t ≥ 2 ^ 150` and a small `t`).
* `programsCheck`: the `452` hash programs are `scaleInput pointX 0 j* i E* ↦` the halves.
* `solveCheck`: the opening's collector solve of one digit (`Opening.solveDigit`) on random row
  constants `gX, gY, gZ`, accumulators, targets and `κ = ±1`: once `κ · Y*[c]` is added at the three
  collectors (`rowX_x9`, `rowY_cubic`, `rowZ_x9`), the digit's rows `Biquadratic.evaluateX/Y/Z`
  hit the targets exactly; the `Y` collector's coefficient is `x²`.

Whole pointX/pointY lanes are the same code at `k = 452, 272` (`≈ 10 ^ 10` instructions), beyond
an interpreter; their chunk `0` is checked at full size, and the big-integer routines on their own
in `tests/BigInt.lean`.

Run: `lake env lean tests/SimulatorReplay.lean`.
-/

namespace Kriterion.ArgoMAC.PlanB.SimMachine.ReplayTest

open Cryptography Cryptography.BoundedMachine BN254

/-! ### The tape -/

def seed : BitVec 256 := 0x5eed

/-- The tape's fixed-key permutation of index code `code` (`Seed.randomness`). -/
def fixedAt (code : Nat) (input : Block) : Block := input + Seed.block seed (2_000_000 + code)
/-- The tape's EncPRF permutation of index code `code`. -/
def encAt (code : Nat) (input : Block) : Block := input + Seed.block seed (40_000 + code)
/-- The tape's hash. -/
def hashAt (value : BaseField) : Block × Block :=
  (Seed.block seed (100_000 + 2 * Seed.hashWord seed value),
    Seed.block seed (100_000 + 2 * Seed.hashWord seed value + 1))

def fixedOracle : PermutationOracle FixedIndex Block :=
  ⟨fun index => Seed.shift (Seed.block seed (2_000_000 + Seed.fixedKeyCode index))⟩
def encOracle : PermutationOracle EncPRF.PermutationIndex Block :=
  ⟨fun index => Seed.shift (Seed.block seed (40_000 + Seed.encPRFCode index))⟩
def tapeOracle : PublicOracle FixedIndex EncPRF.PermutationIndex := (fixedOracle, encOracle, hashAt)

/-- One oracle event: kind, index code (`0` for the hash), input (a block, or a field element). -/
abbrev Event := Nat × Nat × Nat

def eventOf : PublicQuery FixedIndex EncPRF.PermutationIndex → Event
  | .fixedForward index input => (0, Seed.fixedKeyCode index, input.toNat)
  | .fixedInverse index output => (1, Seed.fixedKeyCode index, output.toNat)
  | .encForward index input => (2, Seed.encPRFCode index, input.toNat)
  | .encInverse index output => (3, Seed.encPRFCode index, output.toNat)
  | .hash input => (4, 0, input.val)

/-- Run an evaluator program on the tape, logging its questions. -/
def runLog {α : Type} : FreeQuery Programs.Spec α → Array Event → α × Array Event
  | .pure value, log => (value, log)
  | .query request next, log =>
      runLog (next (publicAnswer tapeOracle request)) (log.push (eventOf request))

/-! ### The interpreter -/

structure St where
  regs : Array Word := Array.replicate 16 0
  ram : Std.HashMap Nat Word := {}
  bitStacks : Array (List Bool) := Array.replicate 4 []
  log : Array Event := #[]
  programmed : Array Event := #[]

def St.get (s : St) (r : Register) : Word := s.regs.getD r.val 0
def St.put (s : St) (r : Register) (v : Word) : St := { s with regs := s.regs.set! r.val v }
def St.read (s : St) (address : Nat) : Word := s.ram.getD address 0
def St.write (s : St) (address : Nat) (value : Word) : St :=
  { s with ram := s.ram.insert address value }

def execOp (s : St) : Op → Option St
  | .constant target value => some (s.put target value)
  | .arith operation target left right =>
      some (s.put target (operation.eval (s.get left) (s.get right)))
  | .load target address => some (s.put target (s.read (s.get address).toNat))
  | .store address source => some (s.write (s.get address).toNat (s.get source))
  | .push stack bit => some { s with bitStacks := s.bitStacks.modify stack.val (bit :: ·) }
  | .pushBit stack source =>
      some { s with bitStacks := s.bitStacks.modify stack.val ((s.get source).getLsbD 0 :: ·) }
  | .coin _ | .pointAdd .. | .lookup .. => none
  | .query kind index input first second =>
      let code := (s.get index).toNat
      let raw := (s.get input).toNat
      if kind.val = 0 then
        let answer := fixedAt code (BitVec.ofNat 128 raw)
        some (({ s with log := s.log.push (0, code, raw % 2 ^ 128) }.put first
          (BitVec.ofNat 256 answer.toNat)).put second 0)
      else if kind.val = 2 then
        let answer := encAt code (BitVec.ofNat 128 raw)
        some (({ s with log := s.log.push (2, code, raw % 2 ^ 128) }.put first
          (BitVec.ofNat 256 answer.toNat)).put second 0)
      else if kind.val = 4 then
        let answer := hashAt (raw : BaseField)
        some (({ s with log := s.log.push (4, 0, (raw : BaseField).val) }.put first
          (BitVec.ofNat 256 answer.1.toNat)).put second (BitVec.ofNat 256 answer.2.toNat))
      else none
  | .program kind _ input first second =>
      if kind.val = 4 then
        some { s with programmed := s.programmed.push (((s.get input).toNat : BaseField).val,
          (s.get first).toNat % 2 ^ 128, (s.get second).toNat % 2 ^ 128) }
      else none

/-- The machine's semantics on one memory, oracle instructions answered by the tape. -/
def exec : Prog → St → Option St
  | .op operation, s => execOp s operation
  | .popBit stack target, s => match s.bitStacks.getD stack.val [] with
    | [] => some (s.put target 2)
    | bit :: rest => some ({ s with bitStacks := s.bitStacks.set! stack.val rest }.put target
        (if bit then 1 else 0))
  | .skip _, s => some s
  | .abort _, _ => none
  | .seq first second, s => (exec first s).bind (exec second)
  | .ite source whenSet whenClear, s =>
      if s.get source = 0 then exec whenClear s else exec whenSet s

def ordF : FixedIndex → Nat := Seed.fixedKeyCode
def ordE : EncPRF.PermutationIndex → Nat := Seed.encPRFCode

/-! ### A random lane input -/

def bits : BitVec 254 :=
  BitVec.ofNat 254 ((Seed.block seed 77).toNat + 2 ^ 128 * (Seed.block seed 78).toNat)
def labels : Fin 254 → Block := fun i => Seed.block seed (5_000 + i.val)
def joins : Vector Block foldStepCount := Vector.ofFn fun i => Seed.block seed (6_000 + i.val)
def scale (lane : Lane) : Fin chunkCount → Fin (laneCount lane) → BaseField :=
  fun c e => Seed.field seed (7_000 + 8 * c.val + e.val)

/-- The stage-1 cells a lane reads, in the machine's layout. -/
def laneMemory (spec : Replay.LaneSpec) : St := Id.run do
  let mut s : St := {}
  s := s.write spec.coordinate (BitVec.ofNat 256 bits.toNat)
  for i in List.range 254 do
    s := s.write (spec.labels + i) (BitVec.ofNat 256 (labels ⟨i % 254, by omega⟩).toNat)
  for i in List.range foldStepCount do
    s := s.write (hotBase + foldStepCount * spec.hotRow + i)
      (BitVec.ofNat 256 (joins.get ⟨i % foldStepCount, Nat.mod_lt _ (by decide)⟩).toNat)
  for c in List.range chunkCount do
    for e in List.range spec.count do
      if h : e < laneCount spec.lane then
        s := s.write (scaleCellBase + elementCount * c + spec.slot + e)
          (BitVec.ofNat 256
            (scale spec.lane ⟨c % chunkCount, Nat.mod_lt _ (by decide)⟩ ⟨e, h⟩).val)
  return s

/-- The accumulators of a lane. -/
def accOf (spec : Replay.LaneSpec) (s : St) : List Nat :=
  (List.range spec.count).map fun e => (s.read (accBase + spec.slot + e)).toNat

/-! ### Checks -/

/-- A whole lane: accumulators and the query sequence against the evaluator. -/
def laneCheck (spec : Replay.LaneSpec) : Bool × Nat × Nat :=
  match exec (.seq Replay.initAcc (Replay.lane ordF spec)) (laneMemory spec) with
  | none => (false, 0, 0)
  | some s =>
      let (value, log) :=
        runLog (Programs.evalLaneM spec.lane joins (scale spec.lane) bits labels) #[]
      let expected := (List.finRange (laneCount spec.lane)).map fun e =>
        (evalCoord fixedOracle hashAt spec.lane joins (scale spec.lane) bits labels e).val
      let program := (List.finRange (laneCount spec.lane)).map fun e => (value e).val
      (accOf spec s == expected && program == expected && s.log == log, s.log.size, log.size)

/-- The designated chunk code (`Replay.chunkBody … true 0`) on the lane of `spec`, chunk `0`. -/
def designatedCheck (spec : Replay.LaneSpec) : Bool × Nat × Nat :=
  let lane := spec.lane
  let c0 : Fin chunkCount := ⟨0, by decide⟩
  match exec (.seq Replay.initAcc (Replay.chunkBody ordF spec true 0)) (laneMemory spec) with
  | none => (false, 0, 0)
  | some s =>
      let alpha := chunkOf bits c0
      let jStar := alpha.val ^^^ 1
      let hot := evalHot fixedOracle lane c0 (chunkWidth c0) (hotSlice joins c0)
        (chunkLabels labels c0) (chunkValue bits c0)
      let eStar := hot ⟨jStar % 4, Nat.mod_lt _ (by decide)⟩
      let kappa : BaseField := (jStar : BaseField) - (alpha.val : BaseField)
      let skipped := (List.range (limbCount lane)).map fun i =>
        ((4 : Nat), (0 : Nat), (scaleInput lane c0 jStar i eStar).val)
      let (_, log) := runLog (Programs.evalChunkM lane joins (scale lane) bits labels c0) #[]
      let kept := log.toList.filter fun event => !(skipped.contains event)
      let removed := log.size - kept.length
      let yStar := switchMask hashAt lane c0 jStar eStar
      let expected := (List.finRange (laneCount lane)).map fun e =>
        (evalScale hashAt lane c0 (chunkWidth c0) hot alpha (scale lane c0) e - kappa * yStar e).val
      (accOf spec s == expected && s.log.toList == kept && removed == limbCount lane &&
          (s.read tmpJStar).toNat == jStar && (s.read designatedLabel).toNat == eStar.toNat &&
          (s.read tmpKappa).toNat == kappa.val,
        s.log.size, log.size)

/-- The bridge input: `t` from the request, the curve cells and the curve accumulators. -/
def bridgeCheck (x y c0 c1 c2 : BaseField) (curveX : Fin 3 → BaseField)
    (curveY : Fin 2 → BaseField) : Bool × Bool :=
  let s0 : St := Id.run do
    let mut s : St := {}
    s := (s.write reqX (BitVec.ofNat 256 x.val)).write reqY (BitVec.ofNat 256 y.val)
    s := ((s.write fieldBase (BitVec.ofNat 256 c0.val)).write (fieldBase + 1)
      (BitVec.ofNat 256 c1.val)).write (fieldBase + 2) (BitVec.ofNat 256 c2.val)
    for i in List.range 3 do
      s := s.write (accBase + 455 + i)
        (BitVec.ofNat 256 (curveX ⟨i % 3, Nat.mod_lt _ (by decide)⟩).val)
    for i in List.range 2 do
      s := s.write (accBase + 731 + i)
        (BitVec.ofNat 256 (curveY ⟨i % 2, Nat.mod_lt _ (by decide)⟩).val)
    return s
  match exec Replay.bridge s0 with
  | none => (false, false)
  | some s =>
      let t := CurveMembership.evaluate (c0, c1, c2) ⟨x, y⟩ (Pipeline.curveValues curveX curveY)
      let answer := hashAt (bridgeInput t)
      (s.log == #[(4, 0, (bridgeInput t).val)] &&
          (s.read tmpK1).toNat == answer.1.toNat && (s.read tmpK2).toNat == answer.2.toNat,
        decide (t.val < scaleRange))

/-- The `452` programs against `scaleInput pointX 0 j* i E*` and the halves. -/
def programsCheck (jStar : Nat) : Bool :=
  let eStar : Block := Seed.block seed 999
  let half (t : Nat) : Nat := (Seed.block seed (10_000 + t)).toNat
  let s0 : St := Id.run do
    let mut s : St := {}
    s := (s.write tmpJStar (BitVec.ofNat 256 jStar)).write designatedLabel
      (BitVec.ofNat 256 eStar.toNat)
    for t in List.range (2 * 452) do
      s := s.write (BigInt.halfBase samplerBase BigInt.samplerLimbs + t) (BitVec.ofNat 256 (half t))
    return s
  match exec Opening.programs s0 with
  | none => false
  | some s =>
      s.log.size == 0 && s.programmed.toList == (List.range 452).map fun i =>
        ((scaleInput .pointX ⟨0, by decide⟩ jStar i eStar).val, half (2 * i), half (2 * i + 1))

/-- The opening's solve of digit `digit` at the input `(x, y)` and `κ`, against the row algebra. -/
def solveCheck (digit : Nat) (x y kappa : BaseField) : Bool :=
  let word (value : BaseField) : Word := BitVec.ofNat 256 value.val
  let gamma (k : Nat) : BaseField := Seed.field seed (30_000 + 3 * digit + k)
  let xAcc (slot : Nat) : BaseField := Seed.field seed (31_000 + 4 * digit + slot)
  let yAcc (slot : Nat) : BaseField := Seed.field seed (32_000 + 3 * digit + slot)
  let target (row : Nat) : BaseField := Seed.field seed (33_000 + 3 * digit + row)
  let s0 : St := Id.run do
    let mut s : St := {}
    s := ((s.write reqX (word x)).write reqY (word y)).write tmpKappa (word kappa)
    for k in List.range 3 do
      s := s.write (Opening.rowCell digit k) (word (gamma k))
    for slot in List.range 4 do
      s := s.write (Opening.xCell (4 * digit + slot)) (word (xAcc slot))
    for slot in List.range 3 do
      s := s.write (Opening.yCell (3 * digit + slot)) (word (yAcc slot))
    for row in List.range 3 do
      s := s.write (openRow digit + row) (word (target row))
    return s
  match exec (Opening.solveDigit digit) s0 with
  | none => false
  | some s =>
      let star (slot : Nat) : BaseField := ((s.read (designatedCell (4 * digit + slot))).toNat : BaseField)
      let values : Biquadratic.Values := fun element => match element with
        | .inl .rowX_x7 => xAcc 0
        | .inl .rowX_x9 => xAcc 1 + kappa * star 1
        | .inl .rowY_cubic => xAcc 2 + kappa * star 2
        | .inl .rowZ_x9 => xAcc 3 + kappa * star 3
        | .inr .rowX_y10 => yAcc 0
        | .inr .rowY_y8 => yAcc 1
        | .inr .rowY_y10 => yAcc 2
      let input : AffineInput := ⟨x, y⟩
      s.log.size == 0 &&
        Biquadratic.evaluateX ⟨gamma 0, gamma 1, gamma 2⟩ input values == target 0 &&
        Biquadratic.evaluateY ⟨gamma 0, gamma 1, gamma 2⟩ input values == target 1 &&
        Biquadratic.evaluateZ ⟨gamma 0, gamma 1, gamma 2⟩ values == target 2

#eval laneCheck Replay.curveXSpec
#eval laneCheck Replay.curveYSpec
#eval designatedCheck Replay.curveXSpec
#eval designatedCheck Replay.pointXSpec
#eval bridgeCheck (Seed.field seed 1) (Seed.field seed 2) (Seed.field seed 3) (Seed.field seed 4)
  (Seed.field seed 5) (fun i => Seed.field seed (10 + i.val))
  (fun i => Seed.field seed (20 + i.val))
#eval bridgeCheck 0 0 0 0 0 (fun i => if i.val = 2 then 12345 else 0) (fun _ => 0)
#eval (programsCheck 0, programsCheck 1, programsCheck 2, programsCheck 3)
#eval (solveCheck 0 (Seed.field seed 40) (Seed.field seed 41) 1,
  solveCheck 57 (Seed.field seed 42) (Seed.field seed 43) (-1),
  solveCheck 90 1 2 1)

end Kriterion.ArgoMAC.PlanB.SimMachine.ReplayTest
