/-
**Machine big-integer routines** of the phase-4 batched hash-vector sampler (design A1 §4,
items 1, 4, 5; task T9a).

A lane's mask vector is the little-endian base-`p` digit vector of `V mod p^n`, where
`V = Σ_{i<k} limb_i · 2^(256 i)` and every limb is one hash answer `a.1 + 2^128 · a.2`. The
machine has no integer division, so every routine here uses only `add`, `sub`, `mul`, `and`,
`shiftRight`, `less` (all mod `2^256`) and `fieldMul`/`fieldAdd` (mod `p`):

* `packLimb`: `limb = a.1 + 2^128 · a.2` from the two answer registers, stored to RAM;
* `limbsToField`: `V mod p` by field Horner from the top limb
  (`acc ← fieldAdd (fieldMul acc (2^256 mod p)) limb_i`; `fieldAdd` reduces the raw limb);
* `exactDivP`: the limbs of `(V − r) / p` for `r = V mod p` by Hensel exact division
  (`q_i = (V_i − b_i) · p⁻¹ mod 2^256`, `b_{i+1} = ⌊q_i · p / 2^256⌋ + [V_i < b_i]`, `b_0 = r`),
  the high half from four `128`-bit half products (`mulHi`);
* `digitsOf`: `n` rounds of both, storing `Y_e = (V / p^e) mod p` at a digit cell;
* `macPasses`: the one big-integer Horner encoder, `E ← E · p + Y_e` from the top digit
  (multiply-accumulate with carries, no division): from the limbs of `E₀` it leaves those of
  `E₀ · p^n + Σ_e Y_e p^e`;
* `preimageSampler`: `R = 80` constant-time attempts, each drawing `t` from `326` fair coins
  (`70` high, `256` low), computing `V = t · p^455 + enc` on `453` limbs by `macPasses` from
  `E₀ = t` (so `enc` itself is never formed) and accepting iff the top limb is `0`, i.e.
  `V < 2^115712`; the first
  accepted `t` is kept, `V` is recomputed from it and its `452` limbs are split into the `128`-bit
  halves a hash `.program` takes.

Every routine is straight-line (`rep` unrolls; the sampler's only branch is the padded
`ite` on its flag), so its cost is a closed formula (`*_cost` below). The registers are `R0 …
R12` (the list `scratch`, which includes `R12 = rIndex`, the oracle index register);
`R13 … R15` (the oracle operands `rInput`, `rFirst`, `rSecond`) are never touched, except by
`packLimb`, which reads and clobbers the answer registers.
-/

import Construction.Simulator.Blocks

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine Blocks Prog

namespace BigInt

/-! ### Registers -/

/-- The Hensel borrow bit, the MAC low word; `rAcc` of the coin draws. -/
abbrev bBeta : Register := 0
/-- The constant `2^128 − 1`. -/
abbrev bMask : Register := 1
/-- The constant `128`. -/
abbrev bC128 : Register := 2
/-- Scratch; `rBit` of the coin draws. -/
abbrev bZ : Register := 3
/-- The constant `p mod 2^128`. -/
abbrev bP0 : Register := 5
/-- The constant `⌊p / 2^128⌋`. -/
abbrev bP1 : Register := 6
/-- The routine constant: `2^256 mod p` (Horner), `p⁻¹ mod 2^256` (Hensel), `p` (MAC). -/
abbrev bK : Register := 7
/-- The current limb. -/
abbrev bV : Register := 8
/-- The low half `q₀` of the `mulHi` operand, then half-product scratch. -/
abbrev bQ0 : Register := 9
/-- `mulHi` running sums; the MAC overflow bit; the keep test's scratch. -/
abbrev bX : Register := 10
/-- The high half of a product. -/
abbrev bY : Register := 11
/-- The Horner accumulator, the Hensel borrow, the MAC carry. -/
abbrev bCarry : Register := 12

/-- Every register a big-integer routine may write: `R0 … R12`. It includes the oracle index
register `R12 = rIndex` (`bCarry`), so a caller must reload `rIndex` (and any label or flag it
kept in `R0 … R12`) after a routine; `digitsOf` and `preimageSampler` end by zeroing all of it. -/
def scratch : List Register := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-! ### Constants -/

/-- `p⁻¹ mod 2^256` (`p · pinv ≡ 1 mod 2^256`, `BigIntArith.pinv_spec`). -/
def pinvNat : Nat := 4759646384140481320982610724935209484903937857060724391493050186936685796471

/-- The sampler's attempts: `R = 80`. -/
def samplerAttempts : Nat := 80
/-- The coins of the high draw word: `326 = 70 + 256` coins per attempt. -/
def hiWidth : Nat := 70
/-- The designated vector's digits: `n = 455`. -/
def samplerDigits : Nat := 455
/-- The sampler's working limbs: `K = 453` (`452` programmed, one overflow limb). -/
def samplerLimbs : Nat := 453

/-! ### Blocks -/

/-- Load the four `mulHi` constants. -/
def setup : Prog := seqList [cst bMask mask128, cst bC128 128, cst bP0 pLow, cst bP1 pHigh]

/-- `bY ← ⌊R[bV] · p / 2^256⌋` from the half products `q0 p0`, `q0 p1`, `q1 p0`, `q1 p1`
(`q = q0 + 2^128 q1`, `p = p0 + 2^128 p1`); clobbers `bV`, `bQ0`, `bX`, `bZ`. -/
def mulHi : Prog :=
  seqList [ar .and bQ0 bV bMask, ar .shiftRight bV bV bC128,
    ar .mul bX bQ0 bP0, ar .shiftRight bX bX bC128,
    ar .mul bY bQ0 bP1, ar .and bQ0 bY bMask, ar .add bX bX bQ0, ar .shiftRight bY bY bC128,
    ar .mul bQ0 bV bP0, ar .and bZ bQ0 bMask, ar .add bX bX bZ, ar .shiftRight bQ0 bQ0 bC128,
    ar .add bY bY bQ0, ar .shiftRight bX bX bC128, ar .add bY bY bX,
    ar .mul bZ bV bP1, ar .add bY bY bZ]

/-- `limb = a.1 + 2^128 · a.2` from the answer registers `rFirst`, `rSecond`, stored at
`address` (clobbers `rFirst`, `rSecond`, `rAddr`). -/
def packLimb (address : Nat) : Prog :=
  seqList [cst rAddr 128, ar .shiftLeft rSecond rSecond rAddr, ar .add rFirst rFirst rSecond,
    storeAt address rFirst]

/-- One field-Horner step on the limb at `address`: `acc ← acc · 2^256 + limb (mod p)`. -/
def hornerLimb (address : Nat) : Prog :=
  seqList [loadAt bV address, ar .fieldMul bCarry bCarry bK, ar .fieldAdd bCarry bCarry bV]

/-- `bCarry ← V mod p` for the `count` limbs of `V` at `base`, top limb first. -/
def limbsToField (base count : Nat) : Prog :=
  seqList [cst bK c256, cst bCarry 0, rep count fun j => hornerLimb (base + (count - 1 - j))]

/-- The first half of a Hensel step: the borrow bit `[V_i < b]` to `bBeta`, the quotient limb
`(V_i − b) · p⁻¹` to `bV` and to the limb's cell. -/
def henselPre (address : Nat) : Prog :=
  seqList [loadAt bV address, ar .less bBeta bV bCarry, ar .sub bV bV bCarry, ar .mul bV bV bK,
    storeAt address bV]

/-- One Hensel step on the limb at `address`, borrow in `bCarry`: the quotient limb replaces
the limb, the next borrow replaces the borrow. -/
def henselLimb (address : Nat) : Prog :=
  seqList [henselPre address, mulHi, ar .add bCarry bY bBeta]

/-- The limbs of `(V − r) / p`, in place, for `r` in `bCarry` (`r ≡ V mod p`, `r < p`). -/
def exactDivP (base count : Nat) : Prog :=
  seqList [cst bK pinvNat, rep count fun index => henselLimb (base + index)]

/-- One digit: `r = V mod p` to `cell`, then `V ← (V − r) / p`. -/
def digitStep (base count cell : Nat) : Prog :=
  seqList [limbsToField base count, storeAt cell bCarry, exactDivP base count]

/-- The digit loop: `Y_e = (V / p^e) mod p` to `digitBase + e`, `e < digits`; the limbs end
as those of `V / p^digits`. Expects the `setup` constants. -/
def digitLoop (base count digits digitBase : Nat) : Prog :=
  rep digits fun digit => digitStep base count (digitBase + digit)

/-- **Digit extraction** (A1 §4 item 1), with its own constants and scratch clearing. -/
def digitsOf (base count digits digitBase : Nat) : Prog :=
  seqList [setup, digitLoop base count digits digitBase, zeroRegs scratch]

/-- The first part of a multiply-accumulate limb: the limb to `bV`, its low product to `bBeta`. -/
def macPre (address : Nat) : Prog := seqList [loadAt bV address, ar .mul bBeta bV bK]

/-- The last part: the new limb `lo + carry`, and the new carry `hi + [overflow]`. -/
def macPost (address : Nat) : Prog :=
  seqList [ar .add bBeta bBeta bCarry, storeAt address bBeta, ar .less bX bBeta bCarry,
    ar .add bCarry bY bX]

/-- One multiply-accumulate limb: `(carry, E_j) ← E_j · p + carry`. -/
def macLimb (address : Nat) : Prog :=
  seqList [macPre address, mulHi, macPost address]

/-- One Horner pass `E ← E · p + Y` over `count` limbs, `Y` read from `cell`. -/
def macPass (base count cell : Nat) : Prog :=
  seqList [loadAt bCarry cell, rep count fun index => macLimb (base + index)]

/-- `digits` Horner passes, the top digit (`yBase + digits − 1`) first: the limbs of `E` become
those of `E · p^digits + Σ_e Y_e p^e`. Expects the `setup` constants. -/
def macPasses (base count digits yBase : Nat) : Prog :=
  seqList [cst bK pNat, rep digits fun step => macPass base count (yBase + (digits - 1 - step))]

/-! ### The preimage sampler (A1 §4 item 5) -/

/-! The sampler's cells, from one work base `a`: the flag, the kept draw (low, high), the
current draw (low, high), then the `count` working limbs, then the `2 (count − 1)` halves. The
draw cells and the working limbs are contiguous (`a + 3 … a + 4 + count`): an attempt writes
nothing else but the flag and the kept draw. -/

/-- The kept flag (`0`: nothing kept yet). -/
def flagCell (work : Nat) : Nat := work
/-- The kept draw's low word. -/
def keptLoCell (work : Nat) : Nat := work + 1
/-- The kept draw's high word. -/
def keptHiCell (work : Nat) : Nat := work + 2
/-- The current draw's low word. -/
def drawLoCell (work : Nat) : Nat := work + 3
/-- The current draw's high word. -/
def drawHiCell (work : Nat) : Nat := work + 4
/-- The first working limb. -/
def limbBase (work : Nat) : Nat := work + 5
/-- The first half word of the output (`2 (count − 1)` cells). -/
def halfBase (work count : Nat) : Nat := work + 5 + count

/-- The working limbs `← (lo, hi, 0, …, 0)`, read from two cells. -/
def initFrom (loCell hiCell base count : Nat) : Prog :=
  seqList [loadAt bV loCell, storeAt base bV, loadAt bV hiCell, storeAt (base + 1) bV, cst bV 0,
    rep (count - 2) fun index => storeAt (base + 2 + index) bV]

/-- The acceptance-and-selection bit `bZ = [flag = 0] ∧ [top limb = 0]`. -/
def keepTest (work count : Nat) : Prog :=
  seqList [loadAt bV (limbBase work + (count - 1)), cst bX 1, ar .less bBeta bV bX,
    loadAt bX (flagCell work), cst bY 1, ar .less bX bX bY, ar .and bZ bX bBeta]

/-- `RAM[kept] ← RAM[kept] + (RAM[draw] − RAM[kept]) · bZ`: the draw iff `bZ = 1`. -/
def selectCell (kept draw : Nat) : Prog :=
  seqList [loadAt bV kept, loadAt bY draw, ar .sub bY bY bV, ar .mul bY bY bZ, ar .add bV bV bY,
    storeAt kept bV]

/-- `flag ← flag + bZ`. -/
def flagStep (work : Nat) : Prog :=
  seqList [loadAt bX (flagCell work), ar .add bX bX bZ, storeAt (flagCell work) bX]

/-- Keep the draw iff nothing was kept and it is accepted. -/
def keepBlock (work count : Nat) : Prog :=
  seqList [keepTest work count, selectCell (keptLoCell work) (drawLoCell work),
    selectCell (keptHiCell work) (drawHiCell work), flagStep work]

/-- An attempt after its draws: `V = t · p^digits + enc`, then the keep block. -/
def attemptTail (work count digits yBase : Nat) : Prog :=
  seqList [setup, initFrom (drawLoCell work) (drawHiCell work) (limbBase work) count,
    macPasses (limbBase work) count digits yBase, keepBlock work count]

/-- One constant-time attempt: draw `t` (high word, then low word), compute
`V = t · p^digits + enc`, accept iff the top limb is `0`, keep `t` iff nothing was kept. -/
def tAttempt (work count digits yBase : Nat) : Prog :=
  seqList [sampleWord hiWidth, storeAt (drawHiCell work) rAcc,
    sampleWord 256, storeAt (drawLoCell work) rAcc, attemptTail work count digits yBase]

/-- Split the first `count` working limbs into `128`-bit halves: `halves + 2 i` gets
`V_i mod 2^128`, `halves + 2 i + 1` gets `V_i / 2^128`. -/
def splitHalves (base halves count : Nat) : Prog :=
  rep count fun index =>
    seqList [loadAt bV (base + index), ar .and bX bV bMask, storeAt (halves + 2 * index) bX,
      ar .shiftRight bX bV bC128, storeAt (halves + 2 * index + 1) bX]

/-- Zero the five sampler cells. -/
def clearCells (work : Nat) : Prog :=
  seqList [cst bV 0, storeAt (flagCell work) bV, storeAt (keptLoCell work) bV,
    storeAt (keptHiCell work) bV, storeAt (drawLoCell work) bV, storeAt (drawHiCell work) bV]

/-- On acceptance: recompute `V` from the kept `t`, split its low `count − 1` limbs. -/
def useKept (work count digits yBase : Nat) : Prog :=
  seqList [setup, initFrom (keptLoCell work) (keptHiCell work) (limbBase work) count,
    macPasses (limbBase work) count digits yBase,
    splitHalves (limbBase work) (halfBase work count) (count - 1), clearCells work]

/-- Empty the flag and the kept draw. -/
def initCells (work : Nat) : Prog :=
  seqList [cst bV 0, storeAt (flagCell work) bV, storeAt (keptLoCell work) bV,
    storeAt (keptHiCell work) bV]

/-- After the attempts: `useKept` if a draw was kept, else abort; then clear the scratch. -/
def finish (work count digits yBase : Nat) : Prog :=
  seqList [loadAt bV (flagCell work), .ite bV (useKept work count digits yBase) (.abort bBeta),
    zeroRegs scratch]

/-- **The preimage sampler**: `attempts` attempts, then `useKept` or an abort. -/
def preimageSampler (work count digits yBase attempts : Nat) : Prog :=
  seqList [initCells work, rep attempts fun _ => tAttempt work count digits yBase,
    finish work count digits yBase]

/-! ### Sizes and costs -/

section Sizes

/-- The simp set for straight-line blocks. -/
macro "big_size" : tactic => `(tactic| simp only [seqList, Prog.size_seq, Prog.cost_seq,
  size_cst, cost_cst, size_loadAt, cost_loadAt, size_storeAt, cost_storeAt, size_zeroRegs,
  cost_zeroRegs, ar, Prog.size, Prog.cost, List.length_cons, List.length_nil, scratch])

theorem size_setup : setup.size = 4 := by unfold setup; big_size
theorem cost_setup : setup.cost = 4 := by unfold setup; big_size
theorem size_mulHi : mulHi.size = 17 := by unfold mulHi; big_size
theorem cost_mulHi : mulHi.cost = 17 := by unfold mulHi; big_size
theorem size_packLimb (address : Nat) : (packLimb address).size = 5 := by unfold packLimb; big_size
theorem cost_packLimb (address : Nat) : (packLimb address).cost = 5 := by unfold packLimb; big_size

theorem size_hornerLimb (address : Nat) : (hornerLimb address).size = 4 := by
  unfold hornerLimb; big_size
theorem cost_hornerLimb (address : Nat) : (hornerLimb address).cost = 4 := by
  unfold hornerLimb; big_size

/-- `limbsToField`: `2 + 4 k`. -/
def limbsToFieldCost (count : Nat) : Nat := 2 + 4 * count

theorem size_limbsToField (base count : Nat) :
    (limbsToField base count).size = limbsToFieldCost count := by
  unfold limbsToField limbsToFieldCost; big_size
  rw [size_rep _ _ _ fun _ _ => size_hornerLimb _]; omega
theorem cost_limbsToField (base count : Nat) :
    (limbsToField base count).cost = limbsToFieldCost count := by
  unfold limbsToField limbsToFieldCost; big_size
  rw [cost_rep _ _ _ fun _ _ => cost_hornerLimb _]; omega

theorem size_henselLimb (address : Nat) : (henselLimb address).size = 25 := by
  unfold henselLimb henselPre; big_size; rw [size_mulHi]
theorem cost_henselLimb (address : Nat) : (henselLimb address).cost = 25 := by
  unfold henselLimb henselPre; big_size; rw [cost_mulHi]

/-- `exactDivP`: `1 + 25 k`. -/
def exactDivPCost (count : Nat) : Nat := 1 + 25 * count

theorem size_exactDivP (base count : Nat) : (exactDivP base count).size = exactDivPCost count := by
  unfold exactDivP exactDivPCost; big_size
  rw [size_rep _ _ _ fun _ _ => size_henselLimb _]; omega
theorem cost_exactDivP (base count : Nat) : (exactDivP base count).cost = exactDivPCost count := by
  unfold exactDivP exactDivPCost; big_size
  rw [cost_rep _ _ _ fun _ _ => cost_henselLimb _]; omega

/-- One digit: `5 + 29 k`. -/
def digitStepCost (count : Nat) : Nat := 5 + 29 * count

theorem size_digitStep (base count cell : Nat) :
    (digitStep base count cell).size = digitStepCost count := by
  unfold digitStep digitStepCost; big_size
  rw [size_limbsToField, size_exactDivP]; unfold limbsToFieldCost exactDivPCost; omega
theorem cost_digitStep (base count cell : Nat) :
    (digitStep base count cell).cost = digitStepCost count := by
  unfold digitStep digitStepCost; big_size
  rw [cost_limbsToField, cost_exactDivP]; unfold limbsToFieldCost exactDivPCost; omega

theorem size_digitLoop (base count digits digitBase : Nat) :
    (digitLoop base count digits digitBase).size = digits * digitStepCost count :=
  size_rep _ _ _ fun _ _ => size_digitStep _ _ _
theorem cost_digitLoop (base count digits digitBase : Nat) :
    (digitLoop base count digits digitBase).cost = digits * digitStepCost count :=
  cost_rep _ _ _ fun _ _ => cost_digitStep _ _ _

/-- **Digit extraction**: `17 + n (5 + 29 k)` (e.g. `k = 452`, `n = 455`: `5,966,432`). -/
def digitsOfCost (count digits : Nat) : Nat := 4 + digits * digitStepCost count + 13

theorem size_digitsOf (base count digits digitBase : Nat) :
    (digitsOf base count digits digitBase).size = digitsOfCost count digits := by
  unfold digitsOf digitsOfCost; big_size; rw [size_setup, size_digitLoop]; omega
theorem cost_digitsOf (base count digits digitBase : Nat) :
    (digitsOf base count digits digitBase).cost = digitsOfCost count digits := by
  unfold digitsOf digitsOfCost; big_size; rw [cost_setup, cost_digitLoop]; omega

theorem size_macLimb (address : Nat) : (macLimb address).size = 25 := by
  unfold macLimb macPre macPost; big_size; rw [size_mulHi]
theorem cost_macLimb (address : Nat) : (macLimb address).cost = 25 := by
  unfold macLimb macPre macPost; big_size; rw [cost_mulHi]

/-- One Horner pass: `2 + 25 K`. -/
def macPassCost (count : Nat) : Nat := 2 + 25 * count

theorem size_macPass (base count cell : Nat) : (macPass base count cell).size = macPassCost count := by
  unfold macPass macPassCost; big_size; rw [size_rep _ _ _ fun _ _ => size_macLimb _]; omega
theorem cost_macPass (base count cell : Nat) : (macPass base count cell).cost = macPassCost count := by
  unfold macPass macPassCost; big_size; rw [cost_rep _ _ _ fun _ _ => cost_macLimb _]; omega

/-- `n` Horner passes: `1 + n (2 + 25 K)`. -/
def macPassesCost (count digits : Nat) : Nat := 1 + digits * macPassCost count

theorem size_macPasses (base count digits yBase : Nat) :
    (macPasses base count digits yBase).size = macPassesCost count digits := by
  unfold macPasses macPassesCost; big_size; rw [size_rep _ _ _ fun _ _ => size_macPass _ _ _]; omega
theorem cost_macPasses (base count digits yBase : Nat) :
    (macPasses base count digits yBase).cost = macPassesCost count digits := by
  unfold macPasses macPassesCost; big_size; rw [cost_rep _ _ _ fun _ _ => cost_macPass _ _ _]; omega

theorem size_initFrom (loCell hiCell base count : Nat) :
    (initFrom loCell hiCell base count).size = 9 + 2 * (count - 2) := by
  unfold initFrom; big_size; rw [size_rep _ _ _ fun _ _ => size_storeAt _ _]; omega
theorem cost_initFrom (loCell hiCell base count : Nat) :
    (initFrom loCell hiCell base count).cost = 9 + 2 * (count - 2) := by
  unfold initFrom; big_size; rw [cost_rep _ _ _ fun _ _ => cost_storeAt _ _]; omega

theorem size_selectCell (kept draw : Nat) : (selectCell kept draw).size = 9 := by
  unfold selectCell; big_size
theorem cost_selectCell (kept draw : Nat) : (selectCell kept draw).cost = 9 := by
  unfold selectCell; big_size

/-- One attempt's code size (`sampleWord` pops take four slots, two instructions). -/
def tAttemptSize (count digits : Nat) : Nat :=
  (1 + 7 * hiWidth) + 2 + (1 + 7 * 256) + 2 + 4 + (9 + 2 * (count - 2)) +
    macPassesCost count digits + 4 + 5 + 9 + 9 + 5

/-- One attempt's cost. -/
def tAttemptCost (count digits : Nat) : Nat :=
  (1 + 5 * hiWidth) + 2 + (1 + 5 * 256) + 2 + 4 + (9 + 2 * (count - 2)) +
    macPassesCost count digits + 4 + 5 + 9 + 9 + 5

theorem size_tAttempt (work count digits yBase : Nat) :
    (tAttempt work count digits yBase).size = tAttemptSize count digits := by
  unfold tAttempt attemptTail keepBlock keepTest flagStep tAttemptSize; big_size
  rw [size_sampleWord, size_sampleWord, size_setup, size_initFrom, size_macPasses, size_selectCell,
    size_selectCell]; omega
theorem cost_tAttempt (work count digits yBase : Nat) :
    (tAttempt work count digits yBase).cost = tAttemptCost count digits := by
  unfold tAttempt attemptTail keepBlock keepTest flagStep tAttemptCost; big_size
  rw [cost_sampleWord, cost_sampleWord, cost_setup, cost_initFrom, cost_macPasses, cost_selectCell,
    cost_selectCell]; omega

theorem size_splitHalves (base halves count : Nat) : (splitHalves base halves count).size = 8 * count := by
  unfold splitHalves; rw [size_rep _ _ 8 fun _ _ => by big_size]; omega
theorem cost_splitHalves (base halves count : Nat) : (splitHalves base halves count).cost = 8 * count := by
  unfold splitHalves; rw [cost_rep _ _ 8 fun _ _ => by big_size]; omega

theorem size_clearCells (work : Nat) : (clearCells work).size = 11 := by unfold clearCells; big_size
theorem cost_clearCells (work : Nat) : (clearCells work).cost = 11 := by unfold clearCells; big_size

/-- The acceptance continuation: `4 + (9 + 2 (K − 2)) + passes + 8 (K − 1) + 11`. -/
def useKeptCost (count digits : Nat) : Nat :=
  4 + (9 + 2 * (count - 2)) + macPassesCost count digits + 8 * (count - 1) + 11

theorem size_useKept (work count digits yBase : Nat) :
    (useKept work count digits yBase).size = useKeptCost count digits := by
  unfold useKept useKeptCost; big_size
  rw [size_setup, size_initFrom, size_macPasses, size_splitHalves, size_clearCells]; omega
theorem cost_useKept (work count digits yBase : Nat) :
    (useKept work count digits yBase).cost = useKeptCost count digits := by
  unfold useKept useKeptCost; big_size
  rw [cost_setup, cost_initFrom, cost_macPasses, cost_splitHalves, cost_clearCells]; omega

/-- **The preimage sampler's code size.** -/
def preimageSamplerSize (count digits attempts : Nat) : Nat :=
  7 + attempts * tAttemptSize count digits + 2 +
    (3 + 2 * useKeptCost count digits) + 13

/-- **The preimage sampler's cost** (`K = 453`, `n = 455`, `R = 80`: about `4.18 · 10^8`). -/
def preimageSamplerCost (count digits attempts : Nat) : Nat :=
  7 + attempts * tAttemptCost count digits + 2 + (2 + useKeptCost count digits) + 13

theorem useKeptCost_pos (count digits : Nat) : 1 ≤ useKeptCost count digits := by
  unfold useKeptCost; omega

theorem size_preimageSampler (work count digits yBase attempts : Nat) :
    (preimageSampler work count digits yBase attempts).size =
      preimageSamplerSize count digits attempts := by
  unfold preimageSampler initCells finish preimageSamplerSize; big_size
  rw [size_rep _ _ _ fun _ _ => size_tAttempt _ _ _ _, size_useKept]
  simp only [Prog.padSet, Prog.padClear, Prog.cost, cost_useKept]
  have := useKeptCost_pos count digits
  omega
theorem cost_preimageSampler (work count digits yBase attempts : Nat) :
    (preimageSampler work count digits yBase attempts).cost =
      preimageSamplerCost count digits attempts := by
  unfold preimageSampler initCells finish preimageSamplerCost; big_size
  rw [cost_rep _ _ _ fun _ _ => cost_tAttempt _ _ _ _, cost_useKept]
  have := useKeptCost_pos count digits
  omega

end Sizes

end BigInt

end Kriterion.ArgoMAC.PlanB.SimMachine
