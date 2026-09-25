/-
Stage 2, part 1: the replay of the honest evaluator's queries (`Programs.evalLaneM`, design A1
§4 item 1).

For every lane and chunk `c` (width `w = chunkWidthNat c`: `2` for `c = 0`, `5` for the wide
chunks `1 .. 48`, `4` for the narrow chunks `49 .. 51`) the machine rebuilds the
chunk's one-hot labels exactly as `evalFoldM` does, then extracts every inactive switch's mask
vector from its hash limbs and accumulates the delivered value
`Σ_c [ι(α_c) · J_c[e] + Σ_{j ≠ α_c} (ι(j) − ι(α_c)) · Y_{c,j}[e]]`
(the algebraic form of `evalScaleOf`) in the `acc` region. System A (the curve lanes) runs on
the raw labels, then the bridge value `t = CurveMembership.evaluate`, one hash query at
`bridgeInput t`, and the `508` whitening pads (`encForward` at `k1`); system B (the point
lanes) runs on the whitened labels.

**The fold** (`foldStep`). Level `1` holds the chunk's bit-`0` label twice. Step `j = 1 .. w − 1`
has `2 ^ j` entries and the active one `a_j = α mod 2 ^ j`: every other entry asks its two
fixed-key halves (in entry order, the `false` half first, as `evalStepM`), the active entry's
material is recovered from the published join (`J_j ⊕ L_j ⊕` the others), and the level is
extended (`E_r ← E_r ⊕ M_r`, `E_{r + 2^j} ← M_r`). A width-`5` chunk asks `2 + 6 + 14 + 30 = 52`
fold queries, a width-`4` chunk `22`, and the width-`2` chunk `0` asks `2`.

**The switches** (`switchStep`). Switch `s` of a chunk asks its `limbCount lane` hash limbs
`scaleInput lane c s i E_s` (`i` in order) and packs them into the limb cells when it is
inactive; otherwise the limb cells are cleared. Either way the digits `Y = digitsOf` of the limb
cells are extracted and `acc[e] += (ι(s) − ι(α)) · Y[e]` for every element: a skipped switch
has zero limbs, hence zero digits, so it adds nothing. The limb cells are therefore always
written in the same step that reads them; what the extraction leaves behind is never read.

**The designated switch.** In lane `pointX`, chunk `0`, the switch `j* = α₀ ⊕ 1` is skipped as
well (the guard is `(s ⊕ α) >>> 1`): its `362` limbs `scaleInput pointX 0 j* i E*` are the
hash inputs stage 2 programs. The `pointX` accumulators therefore hold the sums without `j*`'s
vector. The label `E* = E_{0, j*}`, `j*` and `κ = ι(j*) − ι(α₀) = 1 − 2 · (α₀ mod 2)`
are recorded for the opening.

Every fixed-key index constant is `ord index`, where `ord` is the caller's ordinal function
(instantiated with `Fintype.equivFin`, which `queryFromRegisters` inverts); hash queries carry
their input only.
-/

import Construction.Simulator.BigInt
import Construction.PGS.Index

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine Blocks Prog

namespace Replay

/-- A chunk number as a `Fin chunkCount` (the identity below `52`). -/
def chunkFin (chunk : Nat) : Fin chunkCount := ⟨chunk % chunkCount, Nat.mod_lt _ chunkCount_pos⟩

/-- The fold index of step `step`, entry `entry`, half `half`. -/
def hotIdx (lane : Lane) (chunk step entry : Nat) (half : Bool) : FixedIndex :=
  hotIndexNat lane (chunkFin chunk) step entry half

/-- The EncPRF index of label position `position < 508`. -/
def encIdx (position : Nat) : EncPRF.PermutationIndex :=
  (if position < 254 then .x else .y, ⟨position % 254, Nat.mod_lt _ (by omega)⟩)

/-- The static description of one lane. -/
structure LaneSpec where
  lane : Lane
  /-- The coordinate's request cell. -/
  coordinate : Nat
  /-- The first label of the coordinate (raw or whitened region). -/
  labels : Nat
  /-- The slot of element `0` in the chunk word and in `acc`. -/
  slot : Nat
  /-- The lane's position among the four fold-join vectors. -/
  hotRow : Nat

/-- The number of elements `n = laneCount lane`: the length of one switch mask vector. -/
def LaneSpec.count (spec : LaneSpec) : Nat := laneCount spec.lane

/-- The number of hash limbs `k = limbCount lane` of one switch mask vector. -/
def LaneSpec.limbs (spec : LaneSpec) : Nat := limbCount spec.lane

def curveXSpec : LaneSpec := ⟨.curveX, reqX, labelBase, 364, 0⟩
def curveYSpec : LaneSpec := ⟨.curveY, reqY, labelBase + 254, 640, 1⟩
def pointXSpec : LaneSpec := ⟨.pointX, reqX, whiteBase, 0, 2⟩
def pointYSpec : LaneSpec := ⟨.pointY, reqY, whiteBase + 254, 367, 3⟩

/-- The label cell of bit `position` of chunk `chunk`. -/
def bitLabel (spec : LaneSpec) (chunk position : Nat) : Nat :=
  spec.labels + chunkOffset (chunkFin chunk) + position

/-- The published join of fold step `step ≥ 1` of chunk `chunk`: flat slot
`foldBase c + step − 1` of the lane's `foldStepCount` blocks. -/
def hotJoin (spec : LaneSpec) (chunk step : Nat) : Nat :=
  hotBase + foldStepCount * spec.hotRow + foldBase (chunkFin chunk) + (step - 1)

variable (ordF : FixedIndex → Nat) (ordE : EncPRF.PermutationIndex → Nat)

/-! ### The fold -/

/-- The two fixed-key halves of entry `entry` at step `step`: `M = hash₀(E) ⊕ hash₁(E)` into
the step-material cell (`foldMaskM`). -/
def foldPair (spec : LaneSpec) (chunk step entry : Nat) : Prog :=
  seqList [loadAt rInput (hotLabel entry),
    cst rIndex (ordF (hotIdx spec.lane chunk step entry false)),
    .op (.query 0 rIndex rInput rFirst rSecond), ar .xor rC rFirst rInput,
    cst rIndex (ordF (hotIdx spec.lane chunk step entry true)),
    .op (.query 0 rIndex rInput rFirst rSecond), ar .xor rFirst rFirst rInput,
    ar .xor rC rC rFirst, storeAt (stepMask entry) rC]

/-- The entry's two queries, run unless the guard `rA = entry ⊕ active` is zero. -/
def foldGate (spec : LaneSpec) (chunk step entry : Nat) : Prog :=
  .ite rA (foldPair ordF spec chunk step entry) (.skip 0)

/-- One entry of a fold step: queried unless it is the active entry. -/
def foldEntry (spec : LaneSpec) (chunk step entry : Nat) : Prog :=
  seqList [loadAt rA tmpActive, cst rB entry, ar .xor rA rA rB, foldGate ordF spec chunk step entry]

/-- One term of the active entry's recovery: `rC ⊕= M_entry` (the active cell holds `0`). -/
def absorbEntry (entry : Nat) : Prog := seqList [loadAt rD (stepMask entry), ar .xor rC rC rD]

/-- The extension of one entry: `E_{r + 2^j} ← M_r`, `E_r ← E_r ⊕ M_r`. -/
def extendEntry (step entry : Nat) : Prog :=
  seqList [loadAt rC (stepMask entry), storeAt (hotLabel (entry + 2 ^ step)) rC,
    loadAt rD (hotLabel entry), ar .xor rD rD rC, storeAt (hotLabel entry) rD]

/-- **Fold step `step ≥ 1`** (`evalStepM`, then `extendLevel`). -/
def foldStep (spec : LaneSpec) (chunk step : Nat) : Prog :=
  seqList [
    -- the active entry `α mod 2 ^ step`
    loadAt rA tmpAlpha, cst rB (2 ^ step - 1), ar .and rA rA rB, storeAt tmpActive rA,
    -- clear the step materials, then query every inactive entry
    cst rA 0, rep (2 ^ step) fun entry => storeAt (stepMask entry) rA,
    rep (2 ^ step) fun entry => foldEntry ordF spec chunk step entry,
    -- the active entry's material: `J ⊕ L ⊕ (⊕ of the others)`, the active cell being `0`
    loadAt rC (hotJoin spec chunk step), loadAt rD (bitLabel spec chunk step), ar .xor rC rC rD,
    rep (2 ^ step) absorbEntry,
    loadAt rA tmpActive, cst rB stepMaskBase, ar .add rA rA rB, .op (.store rA rC),
    -- the next level
    rep (2 ^ step) fun entry => extendEntry step entry]

/-- The chunk prefix: `α` (the chunk value), and level `1` of the fold (the bit-`0` label,
twice). -/
def chunkPrefix (spec : LaneSpec) (chunk : Nat) : Prog :=
  seqList [loadAt rA spec.coordinate, cst rB (chunkOffset (chunkFin chunk)),
    ar .shiftRight rA rA rB, cst rB (2 ^ chunkWidthNat chunk - 1), ar .and rA rA rB,
    storeAt tmpAlpha rA,
    loadAt rA (bitLabel spec chunk 0), storeAt (hotLabel 0) rA, storeAt (hotLabel 1) rA]

/-- The designated extras of `pointX` chunk `0`: `j* = α ⊕ 1`, `E* = E_{j*}` and
`κ = 1 − 2 · (α mod 2)`. -/
def designatedPrefix : Prog :=
  seqList [loadAt rA tmpAlpha, cst rB 1, ar .xor rA rA rB, storeAt tmpJStar rA,
    cst rB hotLabelBase, ar .add rA rA rB, .op (.load rC rA), storeAt designatedLabel rC,
    loadAt rA tmpAlpha, cst rB 1, ar .and rA rA rB, cst rC 1, ar .fieldAdd rA rA rA,
    ar .fieldSub rC rC rA, storeAt tmpKappa rC]

/-- The designated extras in the designated chunk, nothing elsewhere. -/
def designatedPart (designated : Bool) : Prog := if designated then designatedPrefix else .skip 0

/-! ### The switches -/

/-- Hash limb `limb` of switch `switch`, label in `rA`: the input
`E + 2 ^ 128 · scaleTag lane c s i` (`scaleInput`), one hash query, and the packed answer
`a.1 + 2 ^ 128 · a.2` into its limb cell. -/
def limbQuery (spec : LaneSpec) (chunk switch limb : Nat) : Prog :=
  seqList [cst rB (2 ^ 128 * scaleTag spec.lane chunk switch limb), ar .add rInput rA rB,
    .op (.query 4 rIndex rInput rFirst rSecond), BigInt.packLimb (vectorLimbBase + limb)]

/-- The `limbCount lane` hash limbs of switch `switch` (`switchMaskM`), at its label `E_s`. -/
def queryLimbs (spec : LaneSpec) (chunk switch : Nat) : Prog :=
  .seq (loadAt rA (hotLabel switch)) (rep spec.limbs fun limb => limbQuery spec chunk switch limb)

/-- A skipped switch: its limb cells are cleared. -/
def clearLimbs (spec : LaneSpec) : Prog :=
  .seq (cst rA 0) (rep spec.limbs fun limb => storeAt (vectorLimbBase + limb) rA)

/-- `acc[e] += R[rF] · Y[e]` for one element. -/
def accumulateOne (spec : LaneSpec) (element : Nat) : Prog :=
  seqList [loadAt rC (vectorDigitBase + element), ar .fieldMul rC rC rF,
    loadAt rD (accBase + spec.slot + element), ar .fieldAdd rD rD rC,
    storeAt (accBase + spec.slot + element) rD]

/-- The coefficient `ι(s) − ι(α)` (reloaded: digit extraction clobbers `R0 … R12`), then
every element. -/
def accumulate (spec : LaneSpec) (switch : Nat) : Prog :=
  seqList [loadAt rA tmpAlpha, cst rF switch, ar .fieldSub rF rF rA,
    rep spec.count fun element => accumulateOne spec element]

/-- The switch's limbs: queried if the guard `rA` is nonzero, cleared otherwise. -/
def limbGate (spec : LaneSpec) (chunk switch : Nat) : Prog :=
  .ite rA (queryLimbs spec chunk switch) (clearLimbs spec)

/-- **One switch.** The guard `(s ⊕ α) >>> shift` is zero exactly at the skipped switches: `α`,
and in the designated chunk (`shift = 1`) also `j* = α ⊕ 1`. -/
def switchStep (spec : LaneSpec) (designated : Bool) (chunk switch : Nat) : Prog :=
  seqList [loadAt rA tmpAlpha, cst rB switch, ar .xor rA rA rB,
    cst rB (if designated then 1 else 0), ar .shiftRight rA rA rB, limbGate spec chunk switch,
    BigInt.digitsOf vectorLimbBase spec.limbs spec.count vectorDigitBase,
    accumulate spec switch]

/-- The published-join term `acc[e] += ι(α) · J_c[e]` (`ι(α)` in `rF`). -/
def joinTerm (spec : LaneSpec) (chunk element : Nat) : Prog :=
  seqList [loadAt rC (scaleCellBase + elementCount * chunk + spec.slot + element),
    ar .fieldMul rC rC rF, loadAt rD (accBase + spec.slot + element), ar .fieldAdd rD rD rC,
    storeAt (accBase + spec.slot + element) rD]

/-- One chunk of one lane: the fold, the designated extras (lane `pointX`, chunk `0`), the
`2 ^ w` switches and the join term. -/
def chunkBody (spec : LaneSpec) (designated : Bool) (chunk : Nat) : Prog :=
  seqList [chunkPrefix spec chunk,
    rep (chunkWidthNat chunk - 1) (fun step => foldStep ordF spec chunk (step + 1)),
    designatedPart designated,
    rep (2 ^ chunkWidthNat chunk) (fun switch => switchStep spec designated chunk switch),
    loadAt rF tmpAlpha, rep spec.count fun element => joinTerm spec chunk element]

/-- One lane: its `52` chunks. -/
def lane (spec : LaneSpec) : Prog :=
  .seq (chunkBody ordF spec false 0)
    (rep (chunkCount - 1) fun chunk => chunkBody ordF spec false (chunk + 1))

/-- Lane `pointX`: chunk `0` is the designated one. -/
def designatedLane (spec : LaneSpec) : Prog :=
  .seq (chunkBody ordF spec true 0)
    (rep (chunkCount - 1) fun chunk => chunkBody ordF spec false (chunk + 1))

/-! ### System A's output, the bridge and the pads -/

/-- Zero the `642` accumulators. -/
def initAcc : Prog :=
  .seq (cst rA 0) (rep 642 fun index => storeAt (accBase + index) rA)

/-- The bridge value `t` of `CurveMembership.evaluate`, moved to `bridgeInput t` (`t + 2 ^ 150`
when `t < 2 ^ 150`), then the hash query; `k1`, `k2` are stored. -/
def bridge : Prog :=
  seqList [loadAt rA reqX, loadAt rB reqY, ar .fieldMul rC rA rA, loadAt rInput fieldBase,
    loadAt rAcc (accBase + 364), ar .fieldMul rAcc rAcc rC, ar .fieldAdd rInput rInput rAcc,
    loadAt rAcc (accBase + 640), ar .fieldMul rAcc rAcc rB, ar .fieldAdd rInput rInput rAcc,
    loadAt rAcc (accBase + 365), ar .fieldMul rAcc rAcc rA, ar .fieldAdd rInput rInput rAcc,
    loadAt rAcc (accBase + 641), ar .fieldAdd rInput rInput rAcc,
    loadAt rAcc (accBase + 366), ar .fieldAdd rInput rInput rAcc,
    cst rAcc scaleRange, ar .less rSel rInput rAcc, ar .mul rSel rSel rAcc,
    ar .add rInput rInput rSel,
    .op (.query 4 rIndex rInput rFirst rSecond), storeAt tmpK1 rFirst, storeAt tmpK2 rSecond]

/-- One whitened label: `W_i = (π_{enc i}(k1) ⊕ k2) ⊕ L_i`; `rInput = k1`, `rF = k2`. -/
def whitenOne (position : Nat) : Prog :=
  .seq (cst rIndex (ordE (encIdx position)))
    (.seq (.op (.query 2 rIndex rInput rFirst rSecond))
    (.seq (ar .xor rFirst rFirst rF)
    (.seq (loadAt rA (labelBase + position))
    (.seq (ar .xor rFirst rFirst rA) (storeAt (whiteBase + position) rFirst)))))

/-- The `508` whitened labels. -/
def whiten : Prog :=
  .seq (loadAt rInput tmpK1) (.seq (loadAt rF tmpK2) (rep labelCount fun position =>
    whitenOne ordE position))

/-- **The replay.** -/
def program : Prog :=
  .seq initAcc
    (.seq (lane ordF curveXSpec)
    (.seq (lane ordF curveYSpec)
    (.seq bridge
    (.seq (whiten ordE)
    (.seq (designatedLane ordF pointXSpec) (lane ordF pointYSpec))))))

/-! ### Sizes and costs -/

section Sizes

/-- The simp set for straight-line blocks. -/
macro "replay_size" : tactic => `(tactic| simp only [seqList, Prog.size_seq, Prog.cost_seq,
  size_cst, cost_cst, size_loadAt, cost_loadAt, size_storeAt, cost_storeAt, ar, Prog.size,
  Prog.cost, List.length_cons, List.length_nil])

theorem size_foldPair (spec : LaneSpec) (chunk step entry : Nat) :
    (foldPair ordF spec chunk step entry).size = 11 := by
  unfold foldPair; replay_size
theorem cost_foldPair (spec : LaneSpec) (chunk step entry : Nat) :
    (foldPair ordF spec chunk step entry).cost = 11 := by
  unfold foldPair; replay_size

theorem size_foldGate (spec : LaneSpec) (chunk step entry : Nat) :
    (foldGate ordF spec chunk step entry).size = 25 := by
  unfold foldGate
  rw [size_ite_of_le _ _ _ (by rw [cost_foldPair]; exact Nat.zero_le _), size_foldPair,
    cost_foldPair]
  rfl
theorem cost_foldGate (spec : LaneSpec) (chunk step entry : Nat) :
    (foldGate ordF spec chunk step entry).cost = 13 := by
  unfold foldGate
  rw [cost_ite_of_le _ _ _ (by rw [cost_foldPair]; exact Nat.zero_le _), cost_foldPair]

theorem size_foldEntry (spec : LaneSpec) (chunk step entry : Nat) :
    (foldEntry ordF spec chunk step entry).size = 29 := by
  unfold foldEntry; replay_size; rw [size_foldGate]
theorem cost_foldEntry (spec : LaneSpec) (chunk step entry : Nat) :
    (foldEntry ordF spec chunk step entry).cost = 17 := by
  unfold foldEntry; replay_size; rw [cost_foldGate]

theorem size_absorbEntry (entry : Nat) : (absorbEntry entry).size = 3 := by
  unfold absorbEntry; replay_size
theorem cost_absorbEntry (entry : Nat) : (absorbEntry entry).cost = 3 := by
  unfold absorbEntry; replay_size

theorem size_extendEntry (step entry : Nat) : (extendEntry step entry).size = 9 := by
  unfold extendEntry; replay_size
theorem cost_extendEntry (step entry : Nat) : (extendEntry step entry).cost = 9 := by
  unfold extendEntry; replay_size

theorem size_foldStep (spec : LaneSpec) (chunk step : Nat) :
    (foldStep ordF spec chunk step).size = 17 + 43 * 2 ^ step := by
  unfold foldStep; replay_size
  rw [size_rep _ _ _ fun _ _ => size_storeAt _ _,
    size_rep _ _ _ fun _ _ => size_foldEntry ordF _ _ _ _,
    size_rep _ _ _ fun _ _ => size_absorbEntry _, size_rep _ _ _ fun _ _ => size_extendEntry _ _]
  omega
theorem cost_foldStep (spec : LaneSpec) (chunk step : Nat) :
    (foldStep ordF spec chunk step).cost = 17 + 31 * 2 ^ step := by
  unfold foldStep; replay_size
  rw [cost_rep _ _ _ fun _ _ => cost_storeAt _ _,
    cost_rep _ _ _ fun _ _ => cost_foldEntry ordF _ _ _ _,
    cost_rep _ _ _ fun _ _ => cost_absorbEntry _, cost_rep _ _ _ fun _ _ => cost_extendEntry _ _]
  omega

/-- The fold of a chunk of width `w`: steps `1 .. w − 1`, step `j` over `2 ^ j` entries. -/
def foldSize (width : Nat) : Nat := 17 * (width - 1) + 43 * (2 ^ width - 2)
/-- The fold's cost. -/
def foldCost (width : Nat) : Nat := 17 * (width - 1) + 31 * (2 ^ width - 2)

theorem size_foldSteps (spec : LaneSpec) (chunk count : Nat) :
    (rep count fun step => foldStep ordF spec chunk (step + 1)).size =
      17 * count + 43 * (2 ^ (count + 1) - 2) := by
  induction count with
  | zero => rw [Prog.rep]; rfl
  | succ count ih =>
      rw [Prog.rep, Prog.size_seq, ih, size_foldStep]
      have grow : 2 ^ (count + 1 + 1) = 2 * 2 ^ (count + 1) := by rw [Nat.pow_succ]; ring
      have large : 2 ≤ 2 ^ (count + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (count + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
theorem cost_foldSteps (spec : LaneSpec) (chunk count : Nat) :
    (rep count fun step => foldStep ordF spec chunk (step + 1)).cost =
      17 * count + 31 * (2 ^ (count + 1) - 2) := by
  induction count with
  | zero => rw [Prog.rep]; rfl
  | succ count ih =>
      rw [Prog.rep, Prog.cost_seq, ih, cost_foldStep]
      have grow : 2 ^ (count + 1 + 1) = 2 * 2 ^ (count + 1) := by rw [Nat.pow_succ]; ring
      have large : 2 ≤ 2 ^ (count + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (count + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega

theorem size_chunkPrefix (spec : LaneSpec) (chunk : Nat) : (chunkPrefix spec chunk).size = 14 := by
  unfold chunkPrefix; replay_size
theorem cost_chunkPrefix (spec : LaneSpec) (chunk : Nat) : (chunkPrefix spec chunk).cost = 14 := by
  unfold chunkPrefix; replay_size

theorem size_designatedPrefix : designatedPrefix.size = 20 := by
  unfold designatedPrefix; replay_size
theorem cost_designatedPrefix : designatedPrefix.cost = 20 := by
  unfold designatedPrefix; replay_size

theorem size_designatedPart_true : (designatedPart true).size = 20 := size_designatedPrefix
theorem cost_designatedPart_true : (designatedPart true).cost = 20 := cost_designatedPrefix
theorem size_designatedPart_false : (designatedPart false).size = 0 := rfl
theorem cost_designatedPart_false : (designatedPart false).cost = 0 := rfl

theorem size_limbQuery (spec : LaneSpec) (chunk switch limb : Nat) :
    (limbQuery spec chunk switch limb).size = 8 := by
  unfold limbQuery; replay_size; rw [BigInt.size_packLimb]
theorem cost_limbQuery (spec : LaneSpec) (chunk switch limb : Nat) :
    (limbQuery spec chunk switch limb).cost = 8 := by
  unfold limbQuery; replay_size; rw [BigInt.cost_packLimb]

theorem size_queryLimbs (spec : LaneSpec) (chunk switch : Nat) :
    (queryLimbs spec chunk switch).size = 2 + 8 * spec.limbs := by
  unfold queryLimbs; replay_size; rw [size_rep _ _ _ fun _ _ => size_limbQuery _ _ _ _]; omega
theorem cost_queryLimbs (spec : LaneSpec) (chunk switch : Nat) :
    (queryLimbs spec chunk switch).cost = 2 + 8 * spec.limbs := by
  unfold queryLimbs; replay_size; rw [cost_rep _ _ _ fun _ _ => cost_limbQuery _ _ _ _]; omega

theorem size_clearLimbs (spec : LaneSpec) : (clearLimbs spec).size = 1 + 2 * spec.limbs := by
  unfold clearLimbs; replay_size; rw [size_rep _ _ _ fun _ _ => size_storeAt _ _]; omega
theorem cost_clearLimbs (spec : LaneSpec) : (clearLimbs spec).cost = 1 + 2 * spec.limbs := by
  unfold clearLimbs; replay_size; rw [cost_rep _ _ _ fun _ _ => cost_storeAt _ _]; omega

theorem size_accumulate (spec : LaneSpec) (switch : Nat) :
    (accumulate spec switch).size = 4 + 8 * spec.count := by
  unfold accumulate; replay_size
  rw [size_rep _ _ 8 fun _ _ => by unfold accumulateOne; replay_size]; omega
theorem cost_accumulate (spec : LaneSpec) (switch : Nat) :
    (accumulate spec switch).cost = 4 + 8 * spec.count := by
  unfold accumulate; replay_size
  rw [cost_rep _ _ 8 fun _ _ => by unfold accumulateOne; replay_size]; omega

theorem size_limbGate (spec : LaneSpec) (chunk switch : Nat) :
    (limbGate spec chunk switch).size = 7 + 16 * spec.limbs := by
  unfold limbGate
  rw [size_ite_of_le _ _ _ (by rw [cost_queryLimbs, cost_clearLimbs]; omega), size_queryLimbs,
    size_clearLimbs, cost_queryLimbs, cost_clearLimbs]
  omega
theorem cost_limbGate (spec : LaneSpec) (chunk switch : Nat) :
    (limbGate spec chunk switch).cost = 4 + 8 * spec.limbs := by
  unfold limbGate
  rw [cost_ite_of_le _ _ _ (by rw [cost_queryLimbs, cost_clearLimbs]; omega), cost_queryLimbs]
  omega

/-- One switch step's code size: guard `6`, the padded query-or-clear `7 + 16 k`, the digit
extraction and the accumulation `4 + 8 n`. -/
def switchSize (limbs count : Nat) : Nat :=
  17 + 16 * limbs + BigInt.digitsOfCost limbs count + 8 * count
/-- One switch step's cost. -/
def switchCost (limbs count : Nat) : Nat :=
  14 + 8 * limbs + BigInt.digitsOfCost limbs count + 8 * count

theorem size_switchStep (spec : LaneSpec) (designated : Bool) (chunk switch : Nat) :
    (switchStep spec designated chunk switch).size = switchSize spec.limbs spec.count := by
  unfold switchStep switchSize; replay_size
  rw [size_limbGate, BigInt.size_digitsOf, size_accumulate]
  omega
theorem cost_switchStep (spec : LaneSpec) (designated : Bool) (chunk switch : Nat) :
    (switchStep spec designated chunk switch).cost = switchCost spec.limbs spec.count := by
  unfold switchStep switchCost; replay_size
  rw [cost_limbGate, BigInt.cost_digitsOf, cost_accumulate]
  omega

theorem size_joinTerm (spec : LaneSpec) (chunk element : Nat) :
    (joinTerm spec chunk element).size = 8 := by
  unfold joinTerm; replay_size
theorem cost_joinTerm (spec : LaneSpec) (chunk element : Nat) :
    (joinTerm spec chunk element).cost = 8 := by
  unfold joinTerm; replay_size

/-- One plain chunk of width `w`: prefix, fold, `2 ^ w` switch steps, join term. -/
def chunkSize (width limbs count : Nat) : Nat :=
  14 + foldSize width + 2 ^ width * switchSize limbs count + 2 + 8 * count
/-- Its cost. -/
def chunkCost (width limbs count : Nat) : Nat :=
  14 + foldCost width + 2 ^ width * switchCost limbs count + 2 + 8 * count

theorem size_chunkBody (spec : LaneSpec) (designated : Bool) (chunk : Nat) :
    (chunkBody ordF spec designated chunk).size =
      (designatedPart designated).size + chunkSize (chunkWidthNat chunk) spec.limbs spec.count := by
  have wide : 1 ≤ chunkWidthNat chunk := chunkWidthNat_pos chunk
  unfold chunkBody chunkSize foldSize; replay_size
  rw [size_chunkPrefix, size_foldSteps, size_rep _ _ _ fun _ _ => size_switchStep _ _ _ _,
    size_rep _ _ _ fun _ _ => size_joinTerm _ _ _, Nat.sub_add_cancel wide]
  omega
theorem cost_chunkBody (spec : LaneSpec) (designated : Bool) (chunk : Nat) :
    (chunkBody ordF spec designated chunk).cost =
      (designatedPart designated).cost + chunkCost (chunkWidthNat chunk) spec.limbs spec.count := by
  have wide : 1 ≤ chunkWidthNat chunk := chunkWidthNat_pos chunk
  unfold chunkBody chunkCost foldCost; replay_size
  rw [cost_chunkPrefix, cost_foldSteps, cost_rep _ _ _ fun _ _ => cost_switchStep _ _ _ _,
    cost_rep _ _ _ fun _ _ => cost_joinTerm _ _ _, Nat.sub_add_cancel wide]
  omega

/-- A `rep` of bodies of varying size: the sum of their sizes. -/
theorem size_rep_sum (count : Nat) (body : Nat → Prog) :
    (Prog.rep count body).size = ∑ index ∈ Finset.range count, (body index).size := by
  induction count with
  | zero => simp [Prog.rep, Prog.size]
  | succ count ih => rw [Prog.rep, Prog.size_seq, ih, Finset.sum_range_succ]

/-- A `rep` of bodies of varying cost: the sum of their costs. -/
theorem cost_rep_sum (count : Nat) (body : Nat → Prog) :
    (Prog.rep count body).cost = ∑ index ∈ Finset.range count, (body index).cost := by
  induction count with
  | zero => simp [Prog.rep, Prog.cost]
  | succ count ih => rw [Prog.rep, Prog.cost_seq, ih, Finset.sum_range_succ]

/-- One lane: the width-`2` chunk `0`, `48` width-`5` chunks and `3` width-`4` chunks. -/
def laneSize (limbs count : Nat) : Nat :=
  chunkSize 2 limbs count + 48 * chunkSize 5 limbs count + 3 * chunkSize 4 limbs count
/-- Its cost. -/
def laneCost (limbs count : Nat) : Nat :=
  chunkCost 2 limbs count + 48 * chunkCost 5 limbs count + 3 * chunkCost 4 limbs count

/-- The chunks after chunk `0`, all plain: `48` wide and `3` narrow chunk sizes. -/
theorem size_laterChunks (spec : LaneSpec) :
    (Prog.rep (chunkCount - 1) fun chunk => chunkBody ordF spec false (chunk + 1)).size =
      48 * chunkSize 5 spec.limbs spec.count + 3 * chunkSize 4 spec.limbs spec.count := by
  have chunks : ∀ chunk ∈ Finset.range (chunkCount - 1),
      (chunkBody ordF spec false (chunk + 1)).size =
        chunkSize (chunkWidthNat (chunk + 1)) spec.limbs spec.count := by
    intro chunk _
    rw [size_chunkBody, size_designatedPart_false, Nat.zero_add]
  rw [size_rep_sum, Finset.sum_congr rfl chunks,
    sum_range_chunkWidthNat_succ (fun width => chunkSize width spec.limbs spec.count),
    show narrowChunkCount = 3 from rfl, show narrowChunkBits = 4 from rfl,
    show wideChunkCount = 48 from rfl, show chunkBits = 5 from rfl]
  omega
/-- Their cost. -/
theorem cost_laterChunks (spec : LaneSpec) :
    (Prog.rep (chunkCount - 1) fun chunk => chunkBody ordF spec false (chunk + 1)).cost =
      48 * chunkCost 5 spec.limbs spec.count + 3 * chunkCost 4 spec.limbs spec.count := by
  have chunks : ∀ chunk ∈ Finset.range (chunkCount - 1),
      (chunkBody ordF spec false (chunk + 1)).cost =
        chunkCost (chunkWidthNat (chunk + 1)) spec.limbs spec.count := by
    intro chunk _
    rw [cost_chunkBody, cost_designatedPart_false, Nat.zero_add]
  rw [cost_rep_sum, Finset.sum_congr rfl chunks,
    sum_range_chunkWidthNat_succ (fun width => chunkCost width spec.limbs spec.count),
    show narrowChunkCount = 3 from rfl, show narrowChunkBits = 4 from rfl,
    show wideChunkCount = 48 from rfl, show chunkBits = 5 from rfl]
  omega

theorem size_lane (spec : LaneSpec) : (lane ordF spec).size = laneSize spec.limbs spec.count := by
  unfold lane laneSize
  rw [Prog.size_seq, size_chunkBody, size_designatedPart_false, size_laterChunks,
    show chunkWidthNat 0 = 2 from rfl]
  omega
theorem cost_lane (spec : LaneSpec) : (lane ordF spec).cost = laneCost spec.limbs spec.count := by
  unfold lane laneCost
  rw [Prog.cost_seq, cost_chunkBody, cost_designatedPart_false, cost_laterChunks,
    show chunkWidthNat 0 = 2 from rfl]
  omega

theorem size_designatedLane (spec : LaneSpec) :
    (designatedLane ordF spec).size = 20 + laneSize spec.limbs spec.count := by
  unfold designatedLane laneSize
  rw [Prog.size_seq, size_chunkBody, size_designatedPart_true, size_laterChunks,
    show chunkWidthNat 0 = 2 from rfl]
  omega
theorem cost_designatedLane (spec : LaneSpec) :
    (designatedLane ordF spec).cost = 20 + laneCost spec.limbs spec.count := by
  unfold designatedLane laneCost
  rw [Prog.cost_seq, cost_chunkBody, cost_designatedPart_true, cost_laterChunks,
    show chunkWidthNat 0 = 2 from rfl]
  omega

theorem size_initAcc : initAcc.size = 1 + 642 * 2 := by
  simp only [initAcc, Prog.size_seq, size_cst]
  rw [size_rep _ _ _ fun _ _ => size_storeAt _ _]

theorem cost_initAcc : initAcc.cost = 1 + 642 * 2 := by
  simp only [initAcc, Prog.cost_seq, cost_cst]
  rw [cost_rep _ _ _ fun _ _ => cost_storeAt _ _]

theorem size_bridge : bridge.size = 34 := by unfold bridge; replay_size
theorem cost_bridge : bridge.cost = 34 := by unfold bridge; replay_size

theorem size_whiten : (whiten ordE).size = 4 + labelCount * 8 := by
  simp only [whiten, Prog.size_seq, size_loadAt]
  rw [size_rep _ _ 8 fun _ _ => by
    simp only [whitenOne, Prog.size_seq, size_cst, size_loadAt, size_storeAt, ar, Prog.size]]
  omega

theorem cost_whiten : (whiten ordE).cost = 4 + labelCount * 8 := by
  simp only [whiten, Prog.cost_seq, cost_loadAt]
  rw [cost_rep _ _ 8 fun _ _ => by
    simp only [whitenOne, Prog.cost_seq, cost_cst, cost_loadAt, cost_storeAt, ar, Prog.cost]]
  omega

/-- The replay's code size: system A (`k = 4`, `3`; `n = 3`, `2`), the bridge, the pads, and
system B (`k = 362`, `272`; `n = 364`, `273`). -/
def programSize : Nat :=
  (1 + 642 * 2) + laneSize 4 3 + laneSize 3 2 + 34 + (4 + 508 * 8) + (20 + laneSize 362 364) +
    laneSize 272 273

/-- The replay's cost. -/
def programCost : Nat :=
  (1 + 642 * 2) + laneCost 4 3 + laneCost 3 2 + 34 + (4 + 508 * 8) + (20 + laneCost 362 364) +
    laneCost 272 273

theorem size_program : (program ordF ordE).size = programSize := by
  simp only [program, Prog.size_seq, size_initAcc, size_lane, size_bridge, size_whiten,
    size_designatedLane]
  rfl

theorem cost_program : (program ordF ordE).cost = programCost := by
  simp only [program, Prog.cost_seq, cost_initAcc, cost_lane, cost_bridge, cost_whiten,
    cost_designatedLane]
  rfl

end Sizes

end Replay

end Kriterion.ArgoMAC.PlanB.SimMachine
