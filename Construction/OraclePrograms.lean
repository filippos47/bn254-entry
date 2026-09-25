/-
This file writes the Plan B garbler and evaluator as query programs.

The pinned library (`aaf2789`) requires `garbleProgram`/`evaluateProgram`: programs that read the
public oracle only through query instructions, whose type index bounds the number of queries on
every path, and which equal `Scheme.scheme` for every complete oracle.

The pure Plan B definitions recompute oracle values freely -- `offsets`, `scaleJoins` and
`evalCoord` rerun the whole `bin-to-hot` fold for every element -- so they are not programs. The
programs below ask every *distinct* question once and keep the answer in a table:

* the fold of one (lane, chunk) is run level by level; level `j ≥ 1` asks both halves of each of
  its `2 ^ j` gates (the evaluator skips its active entry, whose value it recovers from the join);
* one switch's mask vector is asked once -- its `limbCount lane` hash limbs (`362`, `272`, `4`, `3`
  for `pointX`, `pointY`, `curveX`, `curveY`), turned into the lane's `laneCount lane` base-`p`
  digits by `sampleLane` and kept as a `Vector` -- and read by the offsets, the aggregate and (on
  the evaluator side) the recovery of the active switch, whose own limbs the evaluator never asks;
* the bridge key `t` is hashed once, at `bridgeInput t`, the input `EncPRF.whiteningKeys` reads;
* the whitening pad of a position is the bit-`false` EncPRF pad, asked once;
* the gadget asks `508` labels per digit on the evaluator side (one digest unlocks both exceptional
  slots); the garbler asks both labels of every position of a nonzero digit once (`1,016` per
  digit, `gadgetPairsM`) and reads the digests of both exceptional inputs from them.

Each table has a *real* counterpart built from the oracle (`laneTables`, `realPads`, ...), the
table-driven assembly on the real tables is the pure definition by `rfl`, and each program's
`eval` is its real table. The query bounds are exact up to the gadget of a zero digit, which
asks nothing. Per lane, with `k = limbCount lane` and the chunk widths
`[2, 5 × 48, 4 × 3]`, garbling asks `(4 + 4k) + 48 (60 + 32k) + 3 (28 + 16k) = 2,968 + 1,588k`
and evaluation `(2 + 3k) + 48 (52 + 31k) + 3 (22 + 15k) = 2,564 + 1,536k`
(`laneGarbleBudget_closed`, `laneEvalBudget_closed`); in total garbling asks at most `1,123,253`
and evaluation at most `1,042,077` (`garbleBudget_eq`, `evaluateBudget_eq`).
-/

import Construction.QueryMonad
import Construction.Scheme

namespace Kriterion.ArgoMAC.Programs

open BN254 Cryptography
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Scheme (Oracle Coins)
open FreeQuery (Bounded)

/-- The public query interface. -/
abbrev Spec := publicOracleSpec FixedIndex EncPRF.PermutationIndex

/-- A Plan B query computation. -/
abbrev M := FreeQuery Spec

/-! ## Questions

The three kinds of question the programs ask, each at its answer's plain type. -/

/-- Ask a fixed-key permutation in the forward direction. -/
def askFixed (index : FixedIndex) (input : Block) : M Block :=
  FreeQuery.ask (spec := Spec) (.fixedForward index input)

/-- Ask an EncPRF permutation in the forward direction. -/
def askEnc (index : EncPRF.PermutationIndex) (input : Block) : M Block :=
  FreeQuery.ask (spec := Spec) (.encForward index input)

/-- Ask the field hash. -/
def askHash (input : BaseField) : M (Block × Block) :=
  FreeQuery.ask (spec := Spec) (.hash input)

@[simp] theorem eval_askFixed (oracle : Oracle) (index : FixedIndex) (input : Block) :
    (askFixed index input).eval (publicAnswer oracle) = oracle.1.permutation index input := rfl

@[simp] theorem eval_askEnc (oracle : Oracle) (index : EncPRF.PermutationIndex) (input : Block) :
    (askEnc index input).eval (publicAnswer oracle) = oracle.2.1.permutation index input := rfl

@[simp] theorem eval_askHash (oracle : Oracle) (input : BaseField) :
    (askHash input).eval (publicAnswer oracle) = oracle.2.2 input := rfl

theorem bounded_askFixed (index : FixedIndex) (input : Block) : (askFixed index input).Bounded 1 :=
  Bounded.ask _

theorem bounded_askEnc (index : EncPRF.PermutationIndex) (input : Block) :
    (askEnc index input).Bounded 1 :=
  Bounded.ask _

theorem bounded_askHash (input : BaseField) : (askHash input).Bounded 1 :=
  Bounded.ask _

/-! ## Gates -/

/-- One Davies--Meyer fixed-key hash `pi_index(label) xor label`, asked once. -/
def hashM (index : FixedIndex) (label : Block) : M Block :=
  askFixed index label >>= fun image => pure (image ^^^ label)

theorem eval_hashM (oracle : Oracle) (index : FixedIndex) (label : Block) :
    (hashM index label).eval (publicAnswer oracle) = hash oracle.1 index label := rfl

theorem bounded_hashM (index : FixedIndex) (label : Block) : (hashM index label).Bounded 1 :=
  Bounded.bind (bounded_askFixed _ _) fun _ => Bounded.pure' _ 0

/-- The two-image fold-step material of one `bin-to-hot` gate. -/
def foldMaskM (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat) (label : Block) :
    M Block :=
  hashM (hotIndexNat lane chunk step entry false) label >>= fun first =>
    hashM (hotIndexNat lane chunk step entry true) label >>= fun second =>
      pure (first ^^^ second)

theorem eval_foldMaskM (oracle : Oracle) (lane : Lane) (chunk : Fin chunkCount)
    (step entry : Nat) (label : Block) :
    (foldMaskM lane chunk step entry label).eval (publicAnswer oracle) =
      foldMask oracle.1 lane chunk step entry label := rfl

theorem bounded_foldMaskM (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat)
    (label : Block) : (foldMaskM lane chunk step entry label).Bounded 2 :=
  Bounded.bind (bounded_hashM _ _) fun _ =>
    Bounded.bind (bounded_hashM _ _) fun _ => Bounded.pure' _ 0

/-! ## Garbling: the `bin-to-hot` fold -/

/-- The garbler's step material at one level. -/
def garbleStepM (lane : Lane) (chunk : Fin chunkCount) (step : Nat) (zeroLabel : Block)
    (parent : Fin (2 ^ step) → Block) : M (Fin (2 ^ step) → Block) :=
  if step = 0 then pure fun _ => zeroLabel
  else
    FreeQuery.vector (2 ^ step) (fun entry => foldMaskM lane chunk step entry.val (parent entry))
      >>= fun masks => pure masks.get

theorem eval_garbleStepM (oracle : Oracle) (lane : Lane) (chunk : Fin chunkCount) (step : Nat)
    (zeroLabel : Block) (parent : Fin (2 ^ step) → Block) :
    (garbleStepM lane chunk step zeroLabel parent).eval (publicAnswer oracle) =
      garbleStep oracle.1 lane chunk step zeroLabel parent := by
  funext entry
  by_cases zero : step = 0
  · rw [garbleStepM, if_pos zero]
    simp only [garbleStep, if_pos zero, FreeQuery.eval_pure]
  · rw [garbleStepM, if_neg zero]
    simp only [garbleStep, if_neg zero, FreeQuery.eval_bind, FreeQuery.eval_pure,
      FreeQuery.eval_vector, Vector.get_ofFn, eval_foldMaskM]

/-- The garbler's queries at level `step`: none at the free level `0`. -/
def stepGarbleBudget (step : Nat) : Nat := if step = 0 then 0 else 2 ^ step * 2

theorem bounded_garbleStepM (lane : Lane) (chunk : Fin chunkCount) (step : Nat)
    (zeroLabel : Block) (parent : Fin (2 ^ step) → Block) :
    (garbleStepM lane chunk step zeroLabel parent).Bounded (stepGarbleBudget step) := by
  unfold garbleStepM
  refine Bounded.ite (fun _ => Bounded.pure' _ _) fun zero => ?_
  refine (Bounded.bind (Bounded.vector_const fun entry =>
    bounded_foldMaskM lane chunk step entry.val (parent entry)) fun _ =>
      Bounded.pure' _ 0).of_eq ?_
  simp [stepGarbleBudget, zero]

/-- The garbler's fold, level by level. -/
def garbleFoldM (lane : Lane) (chunk : Fin chunkCount) (delta : Block) (zeroLabel : Nat → Block) :
    (steps : Nat) → M ((Fin (2 ^ steps) → Block) × (Nat → Block))
  | 0 => pure (fun _ => delta, fun _ => 0)
  | steps + 1 =>
      garbleFoldM lane chunk delta zeroLabel steps >>= fun previous =>
        garbleStepM lane chunk steps (zeroLabel steps) previous.1 >>= fun right =>
          pure (extendLevel steps previous.1 right,
            fun step => if step = steps then stepJoin steps (zeroLabel steps) right
              else previous.2 step)

theorem eval_garbleFoldM (oracle : Oracle) (lane : Lane) (chunk : Fin chunkCount)
    (delta : Block) (zeroLabel : Nat → Block) (steps : Nat) :
    (garbleFoldM lane chunk delta zeroLabel steps).eval (publicAnswer oracle) =
      garbleFold oracle.1 lane chunk delta zeroLabel steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [garbleFoldM, garbleFold, FreeQuery.eval_bind, FreeQuery.eval_pure, ih,
        eval_garbleStepM]

/-- The garbler's fold queries over `steps` levels. -/
def hotGarbleBudget : Nat → Nat
  | 0 => 0
  | steps + 1 => hotGarbleBudget steps + stepGarbleBudget steps

theorem bounded_garbleFoldM (lane : Lane) (chunk : Fin chunkCount) (delta : Block)
    (zeroLabel : Nat → Block) (steps : Nat) :
    (garbleFoldM lane chunk delta zeroLabel steps).Bounded (hotGarbleBudget steps) := by
  induction steps with
  | zero => exact Bounded.pure' _ _
  | succ steps ih =>
      exact (Bounded.bind ih fun previous =>
        Bounded.bind (bounded_garbleStepM lane chunk steps (zeroLabel steps) previous.1) fun _ =>
          Bounded.pure' _ 0).of_eq (by simp [hotGarbleBudget])

/-- **`bin-to-hot`, garbler side**, for chunk `c` of one lane. -/
def garbleChunkM (lane : Lane) (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block)
    (c : Fin chunkCount) : M (HotLabels (chunkWidth c) × Vector Block (chunkWidth c - 1)) :=
  garbleFoldM lane c delta (labelAt fun position => (chunkKey bitKey c position).1) (chunkWidth c)
    >>= fun folded =>
      pure (folded.1, Vector.ofFn fun slot : Fin (chunkWidth c - 1) => folded.2 (slot.val + 1))

theorem eval_garbleChunkM (oracle : Oracle) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) (c : Fin chunkCount) :
    (garbleChunkM lane delta bitKey c).eval (publicAnswer oracle) =
      garbleChunk oracle.1 lane delta bitKey c := by
  simp only [garbleChunkM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_garbleFoldM]
  rfl

theorem bounded_garbleChunkM (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) (c : Fin chunkCount) :
    (garbleChunkM lane delta bitKey c).Bounded (hotGarbleBudget (chunkWidth c)) :=
  (Bounded.bind (bounded_garbleFoldM _ _ _ _ _) fun _ => Bounded.pure' _ 0).of_eq (by simp)

/-! ## The `scale-hot` switch masks -/

/-- `(Vector.ofFn f).get` is `f`, as a function. -/
theorem vector_get_ofFn {α : Type} {count : Nat} (f : Fin count → α) :
    (Vector.ofFn f).get = f :=
  funext (Vector.get_ofFn f)

/-- One switch's mask vector: the switch's `limbCount lane` hash limbs, each asked once at its
scale input under the switch's one-hot label, read as the `laneCount lane` little-endian base-`p`
digits of their number (`sampleLane`). The vector is computed once, here; every reader indexes
it. -/
def switchMaskM (lane : Lane) (chunk : Fin chunkCount) (switch : Nat) (label : Block) :
    M (Vector BaseField (laneCount lane)) :=
  FreeQuery.vector (limbCount lane)
      (fun limb => askHash (scaleInput lane chunk switch limb.val label)) >>= fun limbs =>
    pure (Vector.ofFn (sampleLane (laneCount lane) (limbCount lane) limbs.get))

theorem eval_switchMaskM (oracle : Oracle) (lane : Lane) (chunk : Fin chunkCount)
    (switch : Nat) (label : Block) :
    (switchMaskM lane chunk switch label).eval (publicAnswer oracle) =
      Vector.ofFn (switchMask oracle.2.2 lane chunk switch label) := by
  simp only [switchMaskM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    eval_askHash, vector_get_ofFn]
  rfl

/-- A switch asks exactly its `limbCount lane` hash limbs. -/
theorem bounded_switchMaskM (lane : Lane) (chunk : Fin chunkCount) (switch : Nat)
    (label : Block) : (switchMaskM lane chunk switch label).Bounded (limbCount lane) :=
  (Bounded.bind (Bounded.vector_const fun _ => bounded_askHash _) fun _ =>
    Bounded.pure' _ 0).of_eq (by rw [Nat.mul_one, Nat.add_zero])

/-! ## One lane of the garbler -/

/-- Everything one lane's garbling reads from the oracle: each chunk's fold (one-hot labels and
published fold joins) and each chunk's switch-mask vectors. The program's tables (`laneM`) read
every mask out of the switch's stored `Vector`. -/
structure LaneTables (count : Nat) where
  hot : (c : Fin chunkCount) → HotLabels (chunkWidth c) × Vector Block (chunkWidth c - 1)
  masks : (c : Fin chunkCount) → Fin (2 ^ chunkWidth c) → Fin count → BaseField

/-- The lane tables of a real oracle. -/
def laneTables (fixed : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle)
    (lane : Lane) (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block) :
    LaneTables (laneCount lane) where
  hot c := garbleChunk fixed lane delta bitKey c
  masks c switch :=
    switchMask hashOracle lane c switch.val ((garbleChunk fixed lane delta bitKey c).1 switch)

namespace LaneTables

variable {count : Nat}

/-- The lane's published fold joins, read from its tables. -/
def hotJoins (tables : LaneTables count) : Vector Block foldStepCount :=
  flattenHot fun c position =>
    if inRange : position < chunkWidth c - 1 then (tables.hot c).2.get ⟨position, inRange⟩ else 0

/-- The lane's element offsets `O[e]`, read from its tables. -/
def offsets (tables : LaneTables count) : Fin count → BaseField :=
  fun element => ∑ c : Fin chunkCount, ∑ switch : Fin (2 ^ chunkWidth c),
    iota _ switch * tables.masks c switch element

/-- The lane's published `scale-hot` joins, read from its tables. -/
def scaleJoins (tables : LaneTables count) (slopes : Fin count → BaseField) :
    Fin chunkCount → Fin count → BaseField :=
  fun c element => (∑ switch : Fin (2 ^ chunkWidth c), tables.masks c switch element)
    + chunkScalar slopes c element

end LaneTables

theorem laneTables_hotJoins (fixed : PermutationOracle FixedIndex Block)
    (hashOracle : EncPRF.HashOracle) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) :
    (laneTables fixed hashOracle lane delta bitKey).hotJoins = hotJoins fixed lane delta bitKey :=
  rfl

theorem laneTables_offsets (fixed : PermutationOracle FixedIndex Block)
    (hashOracle : EncPRF.HashOracle) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) :
    (laneTables fixed hashOracle lane delta bitKey).offsets =
      offsets fixed hashOracle lane delta bitKey := rfl

theorem laneTables_scaleJoins (fixed : PermutationOracle FixedIndex Block)
    (hashOracle : EncPRF.HashOracle) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block)
    (slopes : Fin (laneCount lane) → BaseField) :
    (laneTables fixed hashOracle lane delta bitKey).scaleJoins slopes =
      scaleJoins fixed hashOracle lane delta bitKey slopes := rfl

/-- One chunk's tables: the fold, then the mask vector of each of the `2 ^ b_c` switches. -/
def chunkTablesM (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) (c : Fin chunkCount) :
    M ((HotLabels (chunkWidth c) × Vector Block (chunkWidth c - 1)) ×
      Vector (Vector BaseField (laneCount lane)) (2 ^ chunkWidth c)) :=
  garbleChunkM lane delta bitKey c >>= fun chunk =>
    FreeQuery.vector (2 ^ chunkWidth c)
        (fun switch => switchMaskM lane c switch.val (chunk.1 switch)) >>= fun masks =>
      pure (chunk, masks)

/-- One lane's tables. Every mask is read out of its switch's stored vector. -/
def laneM (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) : M (LaneTables (laneCount lane)) :=
  FreeQuery.pi chunkCount (chunkTablesM lane delta bitKey) >>= fun tables =>
    pure { hot := fun c => (tables c).1, masks := fun c switch => ((tables c).2.get switch).get }

theorem eval_laneM (oracle : Oracle) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) :
    (laneM lane delta bitKey).eval (publicAnswer oracle) =
      laneTables oracle.1 oracle.2.2 lane delta bitKey := by
  simp only [laneM, chunkTablesM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_pi,
    FreeQuery.eval_vector, eval_garbleChunkM, eval_switchMaskM, Vector.get_ofFn, vector_get_ofFn]
  rfl

/-- One lane's garbling queries: per chunk, the fold and `limbCount lane` hash limbs for each of
the chunk's `2 ^ b_c` switches. -/
def laneGarbleBudget (lane : Lane) : Nat :=
  ∑ c : Fin chunkCount, (hotGarbleBudget (chunkWidth c) + 2 ^ chunkWidth c * limbCount lane)

theorem bounded_chunkTablesM (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) (c : Fin chunkCount) :
    (chunkTablesM lane delta bitKey c).Bounded
      (hotGarbleBudget (chunkWidth c) + 2 ^ chunkWidth c * limbCount lane) := by
  unfold chunkTablesM
  exact (Bounded.bind (bounded_garbleChunkM lane delta bitKey c) fun chunk =>
    Bounded.bind (Bounded.vector_const fun switch =>
      bounded_switchMaskM lane c switch.val (chunk.1 switch)) fun _ =>
        Bounded.pure' _ 0).of_eq (by rw [Nat.add_zero])

theorem bounded_laneM (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) :
    (laneM lane delta bitKey).Bounded (laneGarbleBudget lane) := by
  unfold laneM
  exact (Bounded.bind (Bounded.pi fun c => bounded_chunkTablesM lane delta bitKey c)
    fun _ => Bounded.pure' _ 0).of_eq (by rw [Nat.add_zero]; rfl)

/-! ## The EncPRF pads -/

/-- The Even--Mansour pad of one (coordinate, position, bit), asked once. -/
def padM (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) : M Block :=
  askEnc (coordinate, index) (encodeBit bit ^^^ keys.first) >>= fun image =>
    pure (image ^^^ keys.second)

theorem eval_padM (oracle : Oracle) (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    (padM keys coordinate index bit).eval (publicAnswer oracle) =
      EncPRF.evenMansourPad oracle.2.1 keys { coordinate, index, bit } := rfl

theorem bounded_padM (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) : (padM keys coordinate index bit).Bounded 1 :=
  Bounded.bind (bounded_askEnc _ _) fun _ => Bounded.pure' _ 0

/-- A table of EncPRF pads, one per (coordinate, position, bit). -/
abbrev Pads := EncPRF.Coordinate → Fin coordinateBitCount → Bool → Block

/-- The pads of a real oracle. -/
def realPads (encOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) : Pads :=
  fun coordinate index bit => EncPRF.evenMansourPad encOracle keys { coordinate, index, bit }

/-- The garbler asks both pads of every position. -/
def padsM (keys : WhiteningKeys) : M Pads :=
  let row (coordinate : EncPRF.Coordinate) :=
    FreeQuery.vector coordinateBitCount fun index =>
      padM keys coordinate index false >>= fun zero =>
        padM keys coordinate index true >>= fun one => pure (zero, one)
  row .x >>= fun xs => row .y >>= fun ys =>
    pure fun coordinate index bit =>
      let pair := match coordinate with
        | .x => xs.get index
        | .y => ys.get index
      if bit then pair.2 else pair.1

theorem eval_padsM (oracle : Oracle) (keys : WhiteningKeys) :
    (padsM keys).eval (publicAnswer oracle) = realPads oracle.2.1 keys := by
  funext coordinate index bit
  cases coordinate <;> cases bit <;>
    simp only [padsM, realPads, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
      Vector.get_ofFn, eval_padM, Bool.false_eq_true, if_false, if_true]

theorem bounded_padsM (keys : WhiteningKeys) : (padsM keys).Bounded 1016 :=
  (Bounded.bind (Bounded.vector_const fun _ =>
    Bounded.bind (bounded_padM _ _ _ _) fun _ => Bounded.bind (bounded_padM _ _ _ _) fun _ =>
      Bounded.pure' _ 0) fun _ =>
    Bounded.bind (Bounded.vector_const fun _ =>
      Bounded.bind (bounded_padM _ _ _ _) fun _ => Bounded.bind (bounded_padM _ _ _ _) fun _ =>
        Bounded.pure' _ 0) fun _ => Bounded.pure' _ 0).of_eq (by norm_num)

/-- The whitened label pairs, from a pad table. -/
def whitenKeyOf (pads : Pads) (key : InputMacKey) : InputMacKey :=
  let coordinate (which : EncPRF.Coordinate) (source : CoordinateMacKey) : CoordinateMacKey :=
    Vector.ofFn fun index =>
      let label := source[index.val]
      { falseLabel := encrypt (pads which index false) label.falseLabel
        trueLabel := encrypt (pads which index false) label.trueLabel }
  { x := coordinate .x key.x, y := coordinate .y key.y }

/-- The bit-dependent transformed label pairs, from a pad table. -/
def transformKeyOf (pads : Pads) (key : InputMacKey) : InputMacKey :=
  let coordinate (which : EncPRF.Coordinate) (source : CoordinateMacKey) : CoordinateMacKey :=
    Vector.ofFn fun index =>
      let label := source[index.val]
      { falseLabel := encrypt (pads which index false) label.falseLabel
        trueLabel := encrypt (pads which index true) label.trueLabel }
  { x := coordinate .x key.x, y := coordinate .y key.y }

theorem whitenKeyOf_realPads (encOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (key : InputMacKey) :
    whitenKeyOf (realPads encOracle keys) key = EncPRF.whitenKey encOracle keys key := rfl

theorem transformKeyOf_realPads (encOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (key : InputMacKey) :
    transformKeyOf (realPads encOracle keys) key = EncPRF.transformKey encOracle keys key := rfl

/-! ## The exception gadget -/

/-- The digest of one coordinate's labels: one fixed-key hash per label, through the permutation
of the label's position and bit, XOR-folded. -/
def gadgetDigestM (output : Fin FieldMacToECMac.outputMacCount) (coordinate : EncPRF.Coordinate)
    (bits : CoordinateBits) (mac : CoordinateMac) : M Block :=
  FreeQuery.vector coordinateBitCount (fun index =>
    hashM (.gadget output (Pipeline.gadgetCoord coordinate) index (bits.getLsb index))
      (mac.get index)) >>= fun values =>
      pure (Fin.foldl coordinateBitCount (fun acc index => acc ^^^ values.get index) 0)

theorem eval_gadgetDigestM (oracle : Oracle) (output : Fin FieldMacToECMac.outputMacCount)
    (coordinate : EncPRF.Coordinate) (bits : CoordinateBits) (mac : CoordinateMac) :
    (gadgetDigestM output coordinate bits mac).eval (publicAnswer oracle) =
      FieldMacToECMac.gadgetDigest (Pipeline.gadgetPermutations oracle.1 output coordinate)
        bits mac := by
  simp only [gadgetDigestM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    Vector.get_ofFn, eval_hashM]
  rfl

theorem bounded_gadgetDigestM (output : Fin FieldMacToECMac.outputMacCount)
    (coordinate : EncPRF.Coordinate) (bits : CoordinateBits) (mac : CoordinateMac) :
    (gadgetDigestM output coordinate bits mac).Bounded 254 :=
  (Bounded.bind (Bounded.vector_const fun _ => bounded_hashM _ _) fun _ =>
    Bounded.pure' _ 0).of_eq (by norm_num)

/-- The gadget mask byte of one digit at one input, over the input's 508 selected labels. -/
def gadgetMaskM (output : Fin FieldMacToECMac.outputMacCount) (input : AffineInput)
    (mac : InputMac) : M (BitVec 8) :=
  gadgetDigestM output .x (Kriterion.ArgoMAC.coordinateBits input.x) mac.x >>= fun first =>
    gadgetDigestM output .y (Kriterion.ArgoMAC.coordinateBits input.y) mac.y >>= fun second =>
      pure (Exception.lowByte (first ^^^ second))

theorem eval_gadgetMaskM (oracle : Oracle) (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (mac : InputMac) :
    (gadgetMaskM output input mac).eval (publicAnswer oracle) =
      FieldMacToECMac.gadgetMask (Pipeline.gadgetPermutations oracle.1) output input mac := by
  simp only [gadgetMaskM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_gadgetDigestM]
  rfl

theorem bounded_gadgetMaskM (output : Fin FieldMacToECMac.outputMacCount) (input : AffineInput)
    (mac : InputMac) : (gadgetMaskM output input mac).Bounded 508 :=
  Bounded.bind (bounded_gadgetDigestM _ _ _ _) fun _ =>
    Bounded.bind (bounded_gadgetDigestM _ _ _ _) fun _ => Bounded.pure' _ 0

/-- Both hashes of every position of one coordinate: at the label of bit `false`, then at the
label of bit `true`. A digest at any bits reads one of them per position (`pairsDigest`), so the
garbler reads both exceptional inputs of a digit from one run and asks every gadget index once. -/
def gadgetPairsM (output : Fin FieldMacToECMac.outputMacCount) (coordinate : EncPRF.Coordinate)
    (key : CoordinateMacKey) : M (Vector (Block × Block) coordinateBitCount) :=
  FreeQuery.vector coordinateBitCount fun index =>
    hashM (.gadget output (Pipeline.gadgetCoord coordinate) index false)
        (BitAdaptor.encode key[index.val] false) >>= fun zero =>
      hashM (.gadget output (Pipeline.gadgetCoord coordinate) index true)
          (BitAdaptor.encode key[index.val] true) >>= fun one =>
        pure (zero, one)

/-- A coordinate's digest at some bits, read from both hashes of every position. -/
def pairsDigest (pairs : Vector (Block × Block) coordinateBitCount) (bits : CoordinateBits) :
    Block :=
  Fin.foldl coordinateBitCount
    (fun acc index => acc ^^^ if bits.getLsb index then (pairs.get index).2 else (pairs.get index).1)
    0

/-- An input's mask byte, read from both coordinates' hashes. -/
def pairsMask (xPairs yPairs : Vector (Block × Block) coordinateBitCount) (input : AffineInput) :
    BitVec 8 :=
  Exception.lowByte (pairsDigest xPairs (Kriterion.ArgoMAC.coordinateBits input.x) ^^^
    pairsDigest yPairs (Kriterion.ArgoMAC.coordinateBits input.y))

theorem eval_gadgetPairsM (oracle : Oracle) (output : Fin FieldMacToECMac.outputMacCount)
    (coordinate : EncPRF.Coordinate) (key : CoordinateMacKey) :
    (gadgetPairsM output coordinate key).eval (publicAnswer oracle) =
      Vector.ofFn fun index =>
        (hash oracle.1 (.gadget output (Pipeline.gadgetCoord coordinate) index false)
            (BitAdaptor.encode key[index.val] false),
          hash oracle.1 (.gadget output (Pipeline.gadgetCoord coordinate) index true)
            (BitAdaptor.encode key[index.val] true)) := by
  simp only [gadgetPairsM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    eval_hashM]
  rfl

/-- Reading the hashes at the bits is the digest of the bits' labels. -/
theorem pairsDigest_eval (oracle : Oracle) (output : Fin FieldMacToECMac.outputMacCount)
    (coordinate : EncPRF.Coordinate) (key : CoordinateMacKey) (bits : CoordinateBits) :
    pairsDigest ((gadgetPairsM output coordinate key).eval (publicAnswer oracle)) bits =
      FieldMacToECMac.gadgetDigest (Pipeline.gadgetPermutations oracle.1 output coordinate) bits
        (encodeCoordinate key bits) := by
  rw [eval_gadgetPairsM]
  unfold pairsDigest FieldMacToECMac.gadgetDigest
  refine congrArg (fun step => Fin.foldl coordinateBitCount step (0 : Block))
    (funext fun acc => funext fun index => ?_)
  simp only [Vector.get_ofFn, encodeCoordinate]
  split
  · rename_i bitTrue
    rw [bitTrue]
    exact congrArg (fun pair : Block × Block => acc ^^^ pair.2) (Vector.get_ofFn _ index)
  · rename_i bitFalse
    rw [Bool.not_eq_true] at bitFalse
    rw [bitFalse]
    exact congrArg (fun pair : Block × Block => acc ^^^ pair.1) (Vector.get_ofFn _ index)

theorem bounded_gadgetPairsM (output : Fin FieldMacToECMac.outputMacCount)
    (coordinate : EncPRF.Coordinate) (key : CoordinateMacKey) :
    (gadgetPairsM output coordinate key).Bounded 508 :=
  (Bounded.vector_const fun _ => Bounded.bind (bounded_hashM _ _) fun _ =>
    Bounded.bind (bounded_hashM _ _) fun _ => Bounded.pure' _ 0).of_eq (by norm_num)

/-- The garbler's gadget entry of one digit: a zero digit publishes its pad and asks nothing; a
nonzero digit asks both hashes of every position, then writes its doubling slot and its sign-zero
slot. -/
def garbleEntryM (output : Fin FieldMacToECMac.outputMacCount) (key : FieldMacToECMac.OutputKey)
    (inputKey : InputMacKey) (pad : Exception.Entry) : M Exception.Entry :=
  match digitEndomorphismBase key.digit with
  | none => pure pad
  | some phi =>
      gadgetPairsM output .x inputKey.x >>= fun xPairs =>
        gadgetPairsM output .y inputKey.y >>= fun yPairs =>
          pure (Exception.writeEntry
            (Exception.writeEntry pad
              (Exception.slotOf false (Exception.exceptionalInput phi key.offset.coordinates))
              (pairsMask xPairs yPairs (Exception.exceptionalInput phi key.offset.coordinates) ^^^
                Exception.digitCode key.digit))
            (Exception.slotOf true (Exception.tripleInput phi key.offset.coordinates))
            (pairsMask xPairs yPairs (Exception.tripleInput phi key.offset.coordinates) ^^^
              Exception.digitCode key.digit))

/-- Reading an input's mask from the hashes is the mask of its labels. -/
theorem pairsMask_eval (oracle : Oracle) (output : Fin FieldMacToECMac.outputMacCount)
    (inputKey : InputMacKey) (input : AffineInput) :
    pairsMask ((gadgetPairsM output .x inputKey.x).eval (publicAnswer oracle))
        ((gadgetPairsM output .y inputKey.y).eval (publicAnswer oracle)) input =
      FieldMacToECMac.gadgetMask (Pipeline.gadgetPermutations oracle.1) output input
        (inputKey.encodeAffine input) := by
  unfold pairsMask FieldMacToECMac.gadgetMask
  rw [pairsDigest_eval, pairsDigest_eval]
  rfl

theorem eval_garbleEntryM (oracle : Oracle) (output : Fin FieldMacToECMac.outputMacCount)
    (key : FieldMacToECMac.OutputKey) (inputKey : InputMacKey) (pad : Exception.Entry) :
    (garbleEntryM output key inputKey pad).eval (publicAnswer oracle) =
      FieldMacToECMac.garbleEntry (Pipeline.gadgetPermutations oracle.1) output key inputKey pad := by
  unfold garbleEntryM FieldMacToECMac.garbleEntry
  cases digitEndomorphismBase key.digit with
  | none => rfl
  | some phi =>
      simp only [FreeQuery.eval_bind, FreeQuery.eval_pure, pairsMask_eval,
        FieldMacToECMac.writeCase]

theorem bounded_garbleEntryM (output : Fin FieldMacToECMac.outputMacCount)
    (key : FieldMacToECMac.OutputKey) (inputKey : InputMacKey) (pad : Exception.Entry) :
    (garbleEntryM output key inputKey pad).Bounded 1016 := by
  unfold garbleEntryM
  cases digitEndomorphismBase key.digit with
  | none => exact Bounded.pure' _ _
  | some phi =>
      exact Bounded.bind (bounded_gadgetPairsM _ _ _) fun _ =>
        Bounded.bind (bounded_gadgetPairsM _ _ _) fun _ => Bounded.pure' _ 0

/-- All 91 gadget entries. -/
def gadgetM (keys : FieldMacToECMac.OutputKeys) (inputKey : InputMacKey)
    (pads : FieldMacToECMac.ExceptionPad) : M (Vector Exception.Entry FieldMacToECMac.outputMacCount) :=
  FreeQuery.vector FieldMacToECMac.outputMacCount fun output =>
    garbleEntryM output (keys.get output) inputKey (pads.get output)

theorem eval_gadgetM (oracle : Oracle) (keys : FieldMacToECMac.OutputKeys)
    (inputKey : InputMacKey) (pads : FieldMacToECMac.ExceptionPad) :
    (gadgetM keys inputKey pads).eval (publicAnswer oracle) =
      Vector.ofFn fun output => FieldMacToECMac.garbleEntry (Pipeline.gadgetPermutations oracle.1)
        output (keys.get output) inputKey (pads.get output) := by
  simp only [gadgetM, FreeQuery.eval_vector, eval_garbleEntryM]

theorem bounded_gadgetM (keys : FieldMacToECMac.OutputKeys) (inputKey : InputMacKey)
    (pads : FieldMacToECMac.ExceptionPad) :
    (gadgetM keys inputKey pads).Bounded (FieldMacToECMac.outputMacCount * 1016) :=
  Bounded.vector_const fun _ => bounded_garbleEntryM _ _ _ _

/-! ## The garbler -/

/-- The published value, assembled from the four lanes' tables and the gadget entries. On the
real tables this is `Pipeline.garble` (`assemble_laneTables`). -/
def assemble (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (bridgeKey : BaseField)
    (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
    (curveX : LaneTables curveElementCountX) (curveY : LaneTables curveElementCountY)
    (pointX : LaneTables pointElementCountX) (pointY : LaneTables pointElementCountY)
    (gadget : Vector Exception.Entry FieldMacToECMac.outputMacCount) : Public :=
  let curveK := Pipeline.curveValues curveX.offsets curveY.offsets
  let curveSlopes := CurveMembership.slopes curveR1 curveR2 curveK
  let digitK : FieldMacToECMac.DigitValues :=
    fun digit => Pipeline.digitValues pointX.offsets pointY.offsets digit
  let rows := FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness
  let pointSlopes : Fin digitCount → Biquadratic.Values := fun digit =>
    Biquadratic.slopes (rows.get digit) (digitK digit)
  { curve := CurveMembership.garble bridgeKey curveMask.value curveR1 curveR2 curveK
    rows := Vector.ofFn fun index => FieldMacToECMac.garbleRow (rows.get index) (digitK index)
    exception := gadget
    curveXHot := curveX.hotJoins
    curveYHot := curveY.hotJoins
    pointXHot := pointX.hotJoins
    pointYHot := pointY.hotJoins
    scale := Vector.ofFn fun chunk => pack (Pipeline.assembleWord
      (pointX.scaleJoins (Pipeline.pointXAssemble pointSlopes) chunk)
      (curveX.scaleJoins (Pipeline.curveXAssemble curveSlopes) chunk)
      (pointY.scaleJoins (Pipeline.pointYAssemble pointSlopes) chunk)
      (curveY.scaleJoins (Pipeline.curveYAssemble curveSlopes) chunk)) }

/-- **On the real tables, the assembly is the Plan B garbler.** -/
theorem assemble_real (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (exceptionPad : FieldMacToECMac.ExceptionPad)
    (bridgeKey : BaseField) (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
    (oracle : Oracle) (delta : PlanB.Coord → Block) (key : InputMacKey) :
    assemble outputKeys pointRandomness bridgeKey curveMask curveR1 curveR2
        (laneTables oracle.1 oracle.2.2 .curveX (delta .x) (Pipeline.bitKeyOf key .x))
        (laneTables oracle.1 oracle.2.2 .curveY (delta .y) (Pipeline.bitKeyOf key .y))
        (laneTables oracle.1 oracle.2.2 .pointX (delta .x)
          (Pipeline.bitKeyOf (Pipeline.whitenedKey oracle.2.1 oracle.2.2 bridgeKey key) .x))
        (laneTables oracle.1 oracle.2.2 .pointY (delta .y)
          (Pipeline.bitKeyOf (Pipeline.whitenedKey oracle.2.1 oracle.2.2 bridgeKey key) .y))
        (Vector.ofFn fun output => FieldMacToECMac.garbleEntry
          (Pipeline.gadgetPermutations oracle.1) output (outputKeys.get output)
          (EncPRF.transformKey oracle.2.1 (EncPRF.whiteningKeys oracle.2.2 bridgeKey) key)
          (exceptionPad.get output)) =
      Pipeline.garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1 curveR2
        oracle.1 oracle.2.1 oracle.2.2 delta key := rfl

/-- **The garbling program**: the bridge-key hash (at `bridgeInput t`, the input
`EncPRF.whiteningKeys` reads), the EncPRF pads, the four lanes, the gadget. -/
def garbleM (scalar : NonZeroScalar) (coins : Coins) : M (Public × InputMacKey) :=
  let key := coins.inputMacKey
  let outputKeys := FieldMacToECMac.outputKeys construction scalar.value coins.offsets
  askHash (bridgeInput coins.bridgeKey) >>= fun hashed =>
    padsM ⟨hashed.1, hashed.2⟩ >>= fun pads =>
      laneM .curveX (coins.inputDelta .x) (Pipeline.bitKeyOf key .x) >>= fun curveX =>
      laneM .curveY (coins.inputDelta .y) (Pipeline.bitKeyOf key .y) >>= fun curveY =>
      laneM .pointX (coins.inputDelta .x)
          (Pipeline.bitKeyOf (whitenKeyOf pads key) .x) >>= fun pointX =>
      laneM .pointY (coins.inputDelta .y)
          (Pipeline.bitKeyOf (whitenKeyOf pads key) .y) >>= fun pointY =>
      gadgetM outputKeys (transformKeyOf pads key) coins.exceptionPad >>= fun gadget =>
        pure (assemble outputKeys coins.pointRandomness coins.bridgeKey coins.curveMask
          coins.curveR1 coins.curveR2 curveX curveY pointX pointY gadget, key)

theorem eval_garbleM (scalar : NonZeroScalar) (coins : Coins) (oracle : Oracle) :
    (garbleM scalar coins).eval (publicAnswer oracle) =
      (Pipeline.garble (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
        coins.pointRandomness coins.exceptionPad coins.bridgeKey coins.curveMask coins.curveR1
        coins.curveR2 oracle.1 oracle.2.1 oracle.2.2 coins.inputDelta coins.inputMacKey,
        coins.inputMacKey) := by
  simp only [garbleM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_askHash, eval_padsM,
    eval_laneM oracle .curveX, eval_laneM oracle .curveY, eval_laneM oracle .pointX,
    eval_laneM oracle .pointY, eval_gadgetM, whitenKeyOf_realPads, transformKeyOf_realPads]
  rw [← assemble_real]
  rfl

/-- The garbler's exact query budget, term by term. -/
def garbleBudget : Nat :=
  1 + (1016 + (laneGarbleBudget .curveX + (laneGarbleBudget .curveY +
    (laneGarbleBudget .pointX + (laneGarbleBudget .pointY +
      (FieldMacToECMac.outputMacCount * 1016 + 0))))))

theorem bounded_garbleM (scalar : NonZeroScalar) (coins : Coins) :
    (garbleM scalar coins).Bounded garbleBudget :=
  Bounded.bind (bounded_askHash _) fun _ =>
    Bounded.bind (bounded_padsM _) fun _ =>
      Bounded.bind (bounded_laneM _ _ _) fun _ =>
        Bounded.bind (bounded_laneM _ _ _) fun _ =>
          Bounded.bind (bounded_laneM _ _ _) fun _ =>
            Bounded.bind (bounded_laneM _ _ _) fun _ =>
              Bounded.bind (bounded_gadgetM _ _ _) fun _ => Bounded.pure' _ 0

/-! ## The evaluator -/

/-- The evaluator's step material at one level: every entry but the active one is hashed; the
active one is recovered from the published join. -/
def evalStepM (lane : Lane) (chunk : Fin chunkCount) (step : Nat) (bitLabel join : Block)
    (active : Fin (2 ^ step)) (parent : Fin (2 ^ step) → Block) : M (Fin (2 ^ step) → Block) :=
  FreeQuery.vector (2 ^ step) (fun entry =>
    if entry = active then pure 0 else foldMaskM lane chunk step entry.val (parent entry))
    >>= fun masks =>
      pure fun entry =>
        if entry = active then join ^^^ bitLabel ^^^ xorFoldExcept active masks.get
        else masks.get entry

/-- `xorFoldExcept` never reads the skipped entry. -/
theorem xorFoldExcept_congr {count : Nat} (skip : Fin count) (first second : Fin count → Block)
    (agree : ∀ entry, entry ≠ skip → first entry = second entry) :
    xorFoldExcept skip first = xorFoldExcept skip second := by
  unfold xorFoldExcept
  congr 1
  funext acc entry
  by_cases same : entry = skip
  · rw [if_pos same, if_pos same]
  · rw [if_neg same, if_neg same, agree entry same]

theorem eval_evalStepM (oracle : Oracle) (lane : Lane) (chunk : Fin chunkCount) (step : Nat)
    (bitLabel join : Block) (active : Fin (2 ^ step)) (parent : Fin (2 ^ step) → Block) :
    (evalStepM lane chunk step bitLabel join active parent).eval (publicAnswer oracle) =
      evalStep oracle.1 lane chunk step bitLabel join active parent := by
  funext entry
  simp only [evalStepM, evalStep, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_vector]
  by_cases same : entry = active
  · rw [if_pos same, if_pos same]
    congr 1
    apply xorFoldExcept_congr
    intro other different
    simp only [Vector.get_ofFn, if_neg different, eval_foldMaskM]
  · simp only [if_neg same, Vector.get_ofFn, eval_foldMaskM]

theorem bounded_evalStepM (lane : Lane) (chunk : Fin chunkCount) (step : Nat)
    (bitLabel join : Block) (active : Fin (2 ^ step)) (parent : Fin (2 ^ step) → Block) :
    (evalStepM lane chunk step bitLabel join active parent).Bounded ((2 ^ step - 1) * 2) :=
  (Bounded.bind (Bounded.vector (budget := fun entry => if entry = active then 0 else 2)
    fun entry => Bounded.ite (fun _ => Bounded.pure' _ _) fun different => by
      rw [if_neg different]
      exact bounded_foldMaskM _ _ _ _ _) fun _ => Bounded.pure' _ 0).of_eq (by
        rw [FreeQuery.sum_ite_skip, Nat.add_zero])

/-- The evaluator's fold, level by level. -/
def evalFoldM (lane : Lane) (chunk : Fin chunkCount) (value : Nat) (bitLabel join : Nat → Block) :
    (steps : Nat) → M (Fin (2 ^ steps) → Block)
  | 0 => pure fun _ => 0
  | steps + 1 =>
      evalFoldM lane chunk value bitLabel join steps >>= fun previous =>
        evalStepM lane chunk steps (bitLabel steps) (join steps) (activeAt value steps) previous
          >>= fun right => pure (extendLevel steps previous right)

theorem eval_evalFoldM (oracle : Oracle) (lane : Lane) (chunk : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) (steps : Nat) :
    (evalFoldM lane chunk value bitLabel join steps).eval (publicAnswer oracle) =
      evalFold oracle.1 lane chunk value bitLabel join steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [evalFoldM, evalFold, FreeQuery.eval_bind, FreeQuery.eval_pure, ih,
        eval_evalStepM]

/-- The evaluator's fold queries over `steps` levels. -/
def hotEvalBudget : Nat → Nat
  | 0 => 0
  | steps + 1 => hotEvalBudget steps + (2 ^ steps - 1) * 2

theorem bounded_evalFoldM (lane : Lane) (chunk : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) (steps : Nat) :
    (evalFoldM lane chunk value bitLabel join steps).Bounded (hotEvalBudget steps) := by
  induction steps with
  | zero => exact Bounded.pure' _ _
  | succ steps ih =>
      exact (Bounded.bind ih fun _ =>
        Bounded.bind (bounded_evalStepM _ _ _ _ _ _ _) fun _ =>
          Bounded.pure' _ 0).of_eq (by simp [hotEvalBudget])

/-- The evaluator's switch masks of one chunk: the mask vector of every switch but the active one,
each asked once and kept as a `Vector`. The active switch asks nothing -- none of its limbs is
touched -- and its slot holds zeros, which `evalScaleOf` never reads. -/
def evalMasksM (lane : Lane) (chunk : Fin chunkCount) (width : Nat) (hot : HotLabels width)
    (alpha : Fin (2 ^ width)) : M (Fin (2 ^ width) → Vector BaseField (laneCount lane)) :=
  FreeQuery.vector (2 ^ width) (fun switch =>
    if switch = alpha then pure (Vector.ofFn fun _ => 0)
    else switchMaskM lane chunk switch.val (hot switch)) >>= fun masks => pure masks.get

/-- The evaluator's free fold of one chunk, read from its stored switch mask vectors. -/
def evalScaleOf {count : Nat} (width : Nat) (masks : Fin (2 ^ width) → Vector BaseField count)
    (alpha : Fin (2 ^ width)) (join : Fin count → BaseField) : Fin count → BaseField :=
  fun element => ∑ switch : Fin (2 ^ width), iota _ switch *
    (if switch = alpha then
        join element - ∑ other ∈ Finset.univ.erase alpha, (masks other).get element
      else (masks switch).get element)

theorem evalScaleOf_evalMasksM (oracle : Oracle) (lane : Lane) (chunk : Fin chunkCount)
    (width : Nat) (hot : HotLabels width) (alpha : Fin (2 ^ width))
    (join : Fin (laneCount lane) → BaseField) :
    evalScaleOf width ((evalMasksM lane chunk width hot alpha).eval (publicAnswer oracle))
        alpha join =
      evalScale oracle.2.2 lane chunk width hot alpha join := by
  funext element
  simp only [evalScaleOf, evalScale, evalMasksM, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_vector, Vector.get_ofFn]
  refine Finset.sum_congr rfl fun switch _ => ?_
  by_cases same : switch = alpha
  · rw [if_pos same, if_pos same]
    congr 2
    refine Finset.sum_congr rfl fun other member => ?_
    rw [if_neg (Finset.ne_of_mem_erase member), eval_switchMaskM, Vector.get_ofFn]
  · rw [if_neg same, if_neg same, if_neg same, eval_switchMaskM, Vector.get_ofFn]

/-- The evaluator asks `limbCount lane` hash limbs for each of the `2 ^ width - 1` inactive
switches, and none for the active one. -/
theorem bounded_evalMasksM (lane : Lane) (chunk : Fin chunkCount) (width : Nat)
    (hot : HotLabels width) (alpha : Fin (2 ^ width)) :
    (evalMasksM lane chunk width hot alpha).Bounded ((2 ^ width - 1) * limbCount lane) :=
  (Bounded.bind (Bounded.vector (budget := fun switch => if switch = alpha then 0 else
      limbCount lane)
    fun switch => Bounded.ite (fun _ => Bounded.pure' _ _) fun different => by
      rw [if_neg different]
      exact bounded_switchMaskM _ _ _ _) fun _ => Bounded.pure' _ 0).of_eq (by
        rw [FreeQuery.sum_ite_skip, Nat.add_zero])

/-- **`Eval` for one lane**: per chunk, rebuild the one-hot labels, then fold them against the
chunk index; sum over the chunks. -/
def evalChunkM (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (c : Fin chunkCount) :
    M (Fin (laneCount lane) → BaseField) :=
  evalFoldM lane c (chunkValue bits c).toNat
      (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c)) (chunkWidth c) >>= fun hot =>
    evalMasksM lane c (chunkWidth c) hot (chunkOf bits c) >>= fun masks =>
      pure (evalScaleOf (chunkWidth c) masks (chunkOf bits c) (scale c))

def evalLaneM (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) : M (Fin (laneCount lane) → BaseField) :=
  FreeQuery.vector chunkCount (evalChunkM lane joins scale bits labels) >>= fun perChunk =>
    pure fun element => ∑ c : Fin chunkCount, perChunk.get c element

theorem eval_evalLaneM (oracle : Oracle) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    (evalLaneM lane joins scale bits labels).eval (publicAnswer oracle) =
      evalCoord oracle.1 oracle.2.2 lane joins scale bits labels := by
  funext element
  simp only [evalLaneM, evalChunkM, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_vector, Vector.get_ofFn, eval_evalFoldM, evalScaleOf_evalMasksM]
  rfl

/-- One lane's evaluation queries: per chunk, the fold and `limbCount lane` hash limbs for each of
the chunk's `2 ^ b_c - 1` inactive switches. -/
def laneEvalBudget (lane : Lane) : Nat :=
  ∑ c : Fin chunkCount, (hotEvalBudget (chunkWidth c) + (2 ^ chunkWidth c - 1) * limbCount lane)

theorem bounded_evalChunkM (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (c : Fin chunkCount) :
    (evalChunkM lane joins scale bits labels c).Bounded
      (hotEvalBudget (chunkWidth c) + (2 ^ chunkWidth c - 1) * limbCount lane) := by
  unfold evalChunkM
  exact (Bounded.bind (bounded_evalFoldM _ _ _ _ _ _) fun _ =>
    Bounded.bind (bounded_evalMasksM lane c _ _ _) fun _ => Bounded.pure' _ 0).of_eq
      (by rw [Nat.add_zero])

theorem bounded_evalLaneM (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    (evalLaneM lane joins scale bits labels).Bounded (laneEvalBudget lane) := by
  unfold evalLaneM
  exact (Bounded.bind (Bounded.vector fun c => bounded_evalChunkM lane joins scale bits labels c)
    fun _ => Bounded.pure' _ 0).of_eq (by rw [Nat.add_zero]; rfl)

/-- The evaluator's pads: per position, the whitening pad (bit `false`) and the pad of the held
bit, which is the same question when the bit is `false`. -/
def evalPadsM (keys : WhiteningKeys) (bits : BitInput) :
    M (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :=
  let row (which : EncPRF.Coordinate) (word : BitVec coordinateBitCount) :=
    FreeQuery.vector coordinateBitCount fun index =>
      padM keys which index false >>= fun zero =>
        if word.getLsb index then padM keys which index true >>= fun one => pure (zero, one)
        else pure (zero, zero)
  row .x bits.xBits >>= fun xs => row .y bits.yBits >>= fun ys =>
    pure fun which index => match which with
      | .x => xs.get index
      | .y => ys.get index

/-- The evaluator's pads of a real oracle. -/
def realEvalPads (encOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (bits : BitInput) :
    EncPRF.Coordinate → Fin coordinateBitCount → Block × Block :=
  fun which index =>
    (EncPRF.evenMansourPad encOracle keys { coordinate := which, index, bit := false },
      EncPRF.evenMansourPad encOracle keys
        { coordinate := which, index,
          bit := match which with
            | .x => bits.xBits.getLsb index
            | .y => bits.yBits.getLsb index })

theorem eval_evalPadsM (oracle : Oracle) (keys : WhiteningKeys) (bits : BitInput) :
    (evalPadsM keys bits).eval (publicAnswer oracle) = realEvalPads oracle.2.1 keys bits := by
  funext which index
  cases which
  · simp only [evalPadsM, realEvalPads, FreeQuery.eval_bind, FreeQuery.eval_pure,
      FreeQuery.eval_vector, Vector.get_ofFn]
    cases bit : bits.xBits.getLsb index
    · simp only [Bool.false_eq_true, if_false, FreeQuery.eval_pure, eval_padM]
    · simp only [if_true, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_padM]
  · simp only [evalPadsM, realEvalPads, FreeQuery.eval_bind, FreeQuery.eval_pure,
      FreeQuery.eval_vector, Vector.get_ofFn]
    cases bit : bits.yBits.getLsb index
    · simp only [Bool.false_eq_true, if_false, FreeQuery.eval_pure, eval_padM]
    · simp only [if_true, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_padM]

theorem bounded_evalPadsM (keys : WhiteningKeys) (bits : BitInput) :
    (evalPadsM keys bits).Bounded 1016 := by
  have row : ∀ (which : EncPRF.Coordinate) (word : BitVec coordinateBitCount)
      (index : Fin coordinateBitCount),
      (padM keys which index false >>= fun zero =>
        if word.getLsb index then padM keys which index true >>= fun one => pure (zero, one)
        else pure (zero, zero)).Bounded 2 := fun which word index =>
    Bounded.bind (bounded_padM _ _ _ _) fun _ =>
      Bounded.ite (fun _ => Bounded.bind (bounded_padM _ _ _ _) fun _ => Bounded.pure' _ 0)
        fun _ => Bounded.pure' _ _
  exact (Bounded.bind (Bounded.vector_const fun index => row .x bits.xBits index) fun _ =>
    Bounded.bind (Bounded.vector_const fun index => row .y bits.yBits index) fun _ =>
      Bounded.pure' _ 0).of_eq (by norm_num)

/-- The whitened selected labels, from the evaluator's pads. -/
def whitenMacOf (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (mac : InputMac) : InputMac := {
  x := Vector.ofFn fun index => encrypt (pads .x index).1 mac.x[index.val]
  y := Vector.ofFn fun index => encrypt (pads .y index).1 mac.y[index.val] }

/-- The transformed selected labels, from the evaluator's pads. -/
def transformMacOf (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (mac : InputMac) : InputMac := {
  x := Vector.ofFn fun index => encrypt (pads .x index).2 mac.x[index.val]
  y := Vector.ofFn fun index => encrypt (pads .y index).2 mac.y[index.val] }

theorem whitenMacOf_real (encOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (bits : BitInput) (mac : InputMac) :
    whitenMacOf (realEvalPads encOracle keys bits) mac = EncPRF.whitenMac encOracle keys mac := rfl

theorem transformMacOf_real (encOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (bits : BitInput) (mac : InputMac) :
    transformMacOf (realEvalPads encOracle keys bits) mac =
      EncPRF.transformMac encOracle keys bits mac := rfl

/-- The 91 gadget masks at the evaluator's own labels: one digest per digit, which unlocks both of
the digit's exceptional slots. -/
def masksM (input : AffineInput) (mac : InputMac) :
    M (Vector (BitVec 8) FieldMacToECMac.outputMacCount) :=
  FreeQuery.vector FieldMacToECMac.outputMacCount fun index =>
    gadgetMaskM index input mac >>= fun mask => pure mask

theorem eval_masksM (oracle : Oracle) (input : AffineInput) (mac : InputMac) :
    (masksM input mac).eval (publicAnswer oracle) =
      Vector.ofFn fun index =>
        FieldMacToECMac.gadgetMask (Pipeline.gadgetPermutations oracle.1) index input mac := by
  simp only [masksM, FreeQuery.eval_vector, FreeQuery.eval_bind, FreeQuery.eval_pure,
    eval_gadgetMaskM]

theorem bounded_masksM (input : AffineInput) (mac : InputMac) :
    (masksM input mac).Bounded (FieldMacToECMac.outputMacCount * (508 + 0)) :=
  Bounded.vector_const fun _ => Bounded.bind (bounded_gadgetMaskM _ _ _) fun _ => Bounded.pure' _ 0

/-- The digits one exceptional case unlocks, from the masks. -/
def unlockDigits (table : FieldMacToECMac.Table) (input : AffineInput)
    (masks : Vector (BitVec 8) FieldMacToECMac.outputMacCount) (triple : Bool) :
    Vector Digit FieldMacToECMac.outputMacCount :=
  Vector.ofFn fun index => Exception.unlock (masks.get index) (table.2.get index) triple input

section Evaluator

variable [FieldCertificate] [GroupCertificate]

/-- The on-curve branch of the evaluator: curve lanes, bridge key (hashed at `bridgeInput`, the
input `EncPRF.whiteningKeys` reads), EncPRF, point lanes, gadget. -/
def onCurveM (table : Public) (bits : BitInput) (mac : InputMac) : M (Option (Option Point)) :=
  evalLaneM .curveX table.curveXHot
      (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x) >>= fun curveX =>
    evalLaneM .curveY table.curveYHot
        (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
        (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y) >>= fun curveY =>
      askHash (bridgeInput (CurveMembership.evaluate table.curve bits.toAffine
          (Pipeline.curveValues curveX curveY))) >>= fun hashed =>
        evalPadsM ⟨hashed.1, hashed.2⟩ bits >>= fun pads =>
          evalLaneM .pointX table.pointXHot
              (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
              (Pipeline.coordBits bits .x) (Pipeline.macLabels (whitenMacOf pads mac) .x)
            >>= fun pointX =>
          evalLaneM .pointY table.pointYHot
              (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
              (Pipeline.coordBits bits .y) (Pipeline.macLabels (whitenMacOf pads mac) .y)
            >>= fun pointY =>
          masksM bits.toAffine (transformMacOf pads mac)
            >>= fun masks =>
          pure (some (Garbling.decodeResult
            { point := bits.toAffine
              pointMacs := FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable table)
                (Pipeline.digitValues pointX pointY) bits.toAffine
              exceptionDigits := unlockDigits (Pipeline.pointTable table) bits.toAffine masks false
              tripleDigits := unlockDigits (Pipeline.pointTable table) bits.toAffine masks true }))

/-- **The evaluation program.** An off-curve input is refused before any query. -/
def evaluateM (table : Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    M (Option (Option Point)) :=
  match decodePoint (Lamport.restore input labels).input.toAffine with
  | none => pure (some none)
  | some _ => onCurveM table (Lamport.restore input labels).input
      (Lamport.restore input labels).inputMac

theorem eval_onCurveM (oracle : Oracle) (table : Public) (bits : BitInput) (mac : InputMac)
    (point : Point) (decoded : decodePoint bits.toAffine = some point) :
    (onCurveM table bits mac).eval (publicAnswer oracle) =
      some ((Pipeline.evaluate oracle.1 oracle.2.1 oracle.2.2 table bits mac).bind
        Garbling.decodeResult) := by
  simp only [onCurveM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_askHash,
    eval_evalLaneM oracle .curveX, eval_evalLaneM oracle .curveY, eval_evalLaneM oracle .pointX,
    eval_evalLaneM oracle .pointY, eval_evalPadsM, eval_masksM, whitenMacOf_real,
    transformMacOf_real]
  simp only [Pipeline.evaluate, decoded, Option.bind_some, unlockDigits, Vector.get_ofFn]
  rfl

theorem eval_evaluateM (oracle : Oracle) (table : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    (evaluateM table input labels).eval (publicAnswer oracle) =
      Scheme.scheme.evaluate oracle table input labels := by
  unfold evaluateM
  split
  · rename_i decoded
    simp only [Scheme.scheme, Garbling.evaluate, Pipeline.evaluate, decoded, Option.bind_none,
      FreeQuery.eval_pure]
  · rename_i point decoded
    rw [eval_onCurveM oracle table _ _ point decoded]
    rfl

/-- The evaluator's exact query budget, term by term. -/
def evaluateBudget : Nat :=
  laneEvalBudget .curveX + (laneEvalBudget .curveY + (1 + (1016 +
    (laneEvalBudget .pointX + (laneEvalBudget .pointY +
      (FieldMacToECMac.outputMacCount * (508 + 0) + 0))))))

theorem bounded_evaluateM (table : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) : (evaluateM table input labels).Bounded evaluateBudget := by
  unfold evaluateM
  split
  · exact Bounded.pure' _ _
  · exact Bounded.bind (bounded_evalLaneM _ _ _ _ _) fun _ =>
      Bounded.bind (bounded_evalLaneM _ _ _ _ _) fun _ =>
        Bounded.bind (bounded_askHash _) fun _ =>
          Bounded.bind (bounded_evalPadsM _ _) fun _ =>
            Bounded.bind (bounded_evalLaneM _ _ _ _ _) fun _ =>
              Bounded.bind (bounded_evalLaneM _ _ _ _ _) fun _ =>
                Bounded.bind (bounded_masksM _ _) fun _ => Bounded.pure' _ 0

end Evaluator

/-! ## The budgets, evaluated -/

theorem hotGarbleBudget_two : hotGarbleBudget 2 = 4 := rfl

theorem hotGarbleBudget_four : hotGarbleBudget 4 = 28 := rfl

theorem hotGarbleBudget_five : hotGarbleBudget 5 = 60 := rfl

theorem hotEvalBudget_two : hotEvalBudget 2 = 2 := rfl

theorem hotEvalBudget_four : hotEvalBudget 4 = 22 := rfl

theorem hotEvalBudget_five : hotEvalBudget 5 = 52 := rfl

theorem laneGarbleBudget_eq (lane : Lane) :
    laneGarbleBudget lane =
      narrowChunkCount * (hotGarbleBudget narrowChunkBits + 2 ^ narrowChunkBits * limbCount lane)
        + wideChunkCount * (hotGarbleBudget chunkBits + 2 ^ chunkBits * limbCount lane)
        + (hotGarbleBudget firstChunkBits + 2 ^ firstChunkBits * limbCount lane) := by
  rw [laneGarbleBudget,
    sum_chunkWidth (fun width => hotGarbleBudget width + 2 ^ width * limbCount lane)]

theorem laneEvalBudget_eq (lane : Lane) :
    laneEvalBudget lane =
      narrowChunkCount * (hotEvalBudget narrowChunkBits
          + (2 ^ narrowChunkBits - 1) * limbCount lane)
        + wideChunkCount * (hotEvalBudget chunkBits + (2 ^ chunkBits - 1) * limbCount lane)
        + (hotEvalBudget firstChunkBits + (2 ^ firstChunkBits - 1) * limbCount lane) := by
  rw [laneEvalBudget,
    sum_chunkWidth (fun width => hotEvalBudget width + (2 ^ width - 1) * limbCount lane)]

/-- **One lane's garbling queries**, `k = limbCount lane`: the `2`-bit first chunk asks
`4 + 4k`, each of the `48` wide `5`-bit chunks `60 + 32k` and each of the `3` narrow `4`-bit
chunks `28 + 16k`, so `2,968 + 1,588k` in all. -/
theorem laneGarbleBudget_closed (lane : Lane) :
    laneGarbleBudget lane = 2968 + 1588 * limbCount lane := by
  rw [laneGarbleBudget_eq]
  simp only [narrowChunkCount, wideChunkCount, narrowChunkBits, chunkBits, firstChunkBits,
    hotGarbleBudget_two, hotGarbleBudget_four, hotGarbleBudget_five]
  omega

/-- **One lane's evaluation queries**, `k = limbCount lane`: the `2`-bit first chunk asks
`2 + 3k`, each of the `48` wide `5`-bit chunks `52 + 31k` and each of the `3` narrow `4`-bit
chunks `22 + 15k`, so `2,564 + 1,536k` in all. -/
theorem laneEvalBudget_closed (lane : Lane) :
    laneEvalBudget lane = 2564 + 1536 * limbCount lane := by
  rw [laneEvalBudget_eq]
  simp only [narrowChunkCount, wideChunkCount, narrowChunkBits, chunkBits, firstChunkBits,
    hotEvalBudget_two, hotEvalBudget_four, hotEvalBudget_five]
  omega

/-- **Garbling asks at most `1,123,253` questions**: `1` bridge hash, `1,016` EncPRF pads,
`11,872` fold hashes (`4 * 2,968`), `1,017,908` switch-mask hash limbs
(`1,588 * (4 + 3 + 362 + 272)`) and `92,456` gadget hashes (both labels of every position of
every digit). -/
theorem garbleBudget_eq : garbleBudget = 1123253 := by
  unfold garbleBudget
  rw [laneGarbleBudget_closed, laneGarbleBudget_closed, laneGarbleBudget_closed,
    laneGarbleBudget_closed]
  simp only [limbCount]
  norm_num

/-- **Evaluation asks `1,042,077` questions**: `10,256` fold hashes (`4 * 2,564`), `984,576`
switch-mask hash limbs (`1,536 * (4 + 3 + 362 + 272)`), `1` bridge hash, `≤ 1,016` EncPRF pads
and `46,228` gadget hashes. -/
theorem evaluateBudget_eq : evaluateBudget = 1042077 := by
  unfold evaluateBudget
  rw [laneEvalBudget_closed, laneEvalBudget_closed, laneEvalBudget_closed,
    laneEvalBudget_closed]
  simp only [limbCount]
  norm_num

/-! ## The indexed programs -/

variable [FieldCertificate] [GroupCertificate]

/-- The garbling query bound, which the program's type carries. -/
def garbleQueries : Nat := 1123253

/-- The evaluation query bound, which the program's type carries. -/
def evaluateQueries : Nat := 1042077

/-- **The garbling program**, at its exact budget. -/
def garbleProgram (_parameter : Nat) (scalar : NonZeroScalar) (coins : Coins) :
    QueryProgram Spec (Public × InputMacKey) garbleQueries :=
  FreeQuery.toProgram (garbleM scalar coins) garbleQueries
    ((bounded_garbleM scalar coins).of_eq garbleBudget_eq)

/-- **The evaluation program**, at its exact budget. -/
def evaluateProgram (table : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    QueryProgram Spec (Option (Option Point)) evaluateQueries :=
  FreeQuery.toProgram (evaluateM table input labels) evaluateQueries
    ((bounded_evaluateM table input labels).of_eq evaluateBudget_eq)

/-- **The garbling program is the scheme's garbler**, for every complete oracle. -/
theorem garbleProgram_correct (parameter : Nat) (scalar : NonZeroScalar) (coins : Coins)
    (oracle : Oracle) :
    (garbleProgram parameter scalar coins).eval (publicAnswer oracle) =
      Scheme.scheme.garble parameter scalar (coins, oracle) := by
  rw [garbleProgram, FreeQuery.eval_toProgram, eval_garbleM]
  rfl

/-- **The evaluation program is the scheme's evaluator**, for every complete oracle. -/
theorem evaluateProgram_correct (table : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) (oracle : Oracle) :
    (evaluateProgram table input labels).eval (publicAnswer oracle) =
      Scheme.scheme.evaluate oracle table input labels := by
  rw [evaluateProgram, FreeQuery.eval_toProgram, eval_evaluateM]

end Kriterion.ArgoMAC.Programs
