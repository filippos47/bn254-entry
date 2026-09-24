import Proof.Simulator.BigIntAccept

/-!
T9a checks: the axioms of every deliverable lemma, and executions of the machine big-integer
routines (through the point law `det`, which `memSem_det` identifies with the machine law) on
tiny instances, compared against `Nat` arithmetic.

Run: `lake env lean tests/BigInt.lean`.
-/

open Kriterion.ArgoMAC.PlanB.SimMachine Kriterion.ArgoMAC.PlanB.SimMachine.BigInt
open Kriterion.Cryptography.BoundedMachine

/-! ### Axioms -/

#print axioms preimageAccept_nat
#print axioms preimageComplete_nat
#print axioms memSem_det
#print axioms hiWord_eq
#print axioms hensel_step
#print axioms horner_step
#print axioms mac_step
#print axioms hornerValue_eq
#print axioms limb_limbSum
#print axioms det_packLimb
#print axioms det_mulHi
#print axioms det_limbsToField
#print axioms det_exactDivP
#print axioms det_digitLoop
#print axioms memSem_digitsOf
#print axioms det_macPasses
#print axioms tAttempt_law
#print axioms rep_tAttempt_law
#print axioms keepLaw_eq_rejectLaw
#print axioms memSem_preimageSampler
#print axioms memSem_preimageSampler_A1
#print axioms acceptTop_eq
#print axioms kept_below
#print axioms kept_uniform
#print axioms kept_off
#print axioms fibre_below
#print axioms accepted_iff_fibre
#print axioms rejectedCount_sampler
#print axioms samplerAbort_le
#print axioms cost_digitsOf
#print axioms cost_macPasses
#print axioms cost_preimageSampler

/-! ### Executions on tiny instances -/

/-- A memory holding the `count` limbs of `value` at `base` (and the extra cells `extra`). -/
def limbMemory (base count value : Nat) (extra : Nat → Option Nat := fun _ => none) : Memory :=
  { ram := fun address =>
      if base ≤ address.toNat ∧ address.toNat < base + count then
        word (limb value (address.toNat - base))
      else match extra address.toNat with
        | some cell => word cell
        | none => 0 }

/-- A 2-limb test value: `V = 2^500 + 1234567890123456789 · p + 42 < 2^512`. -/
def testValue : Nat := 2 ^ 500 + 1234567890123456789 * pNat + 42

/-- **Digit extraction** (`k = 2`, `n = 3`): the machine digits against `(V / p^e) mod p`, and
the remaining limbs against those of `V / p^3`. -/
def digitsCheck : Bool :=
  match det (digitsOf 100 2 3 200) (limbMemory 100 2 testValue) with
  | none => false
  | some final =>
      ((List.range 3).all fun e => (final.ram (word (200 + e))).toNat == testValue / pNat ^ e % pNat) &&
      ((List.range 2).all fun i => (final.ram (word (100 + i))).toNat == limb (testValue / pNat ^ 3) i)

#eval digitsCheck

/-- **Exact division alone** (`k = 2`): with `bCarry = V mod p`, the limbs of `V / p`. -/
def divisionCheck : Bool :=
  match det (Prog.seqList [setup, Blocks.cst bCarry (testValue % pNat), exactDivP 100 2])
      (limbMemory 100 2 testValue) with
  | none => false
  | some final =>
      (List.range 2).all fun i => (final.ram (word (100 + i))).toNat == limb (testValue / pNat) i

#eval divisionCheck

/-- **`V mod p` alone** (`k = 2`). -/
def fieldCheck : Bool :=
  match det (Prog.seqList [setup, limbsToField 100 2]) (limbMemory 100 2 testValue) with
  | none => false
  | some final => (final.registers bCarry).toNat == testValue % pNat

#eval fieldCheck

/-- Two test digits. -/
def testDigits : Nat → Nat
  | 0 => pNat - 1
  | 1 => 987654321987654321
  | _ => 0

/-- **Horner encoding** (`macPasses`, `n = 2` digits, `K = 2` limbs, from `E₀ = 0`): the limbs of
`Y₀ + Y₁ p`. -/
def encodeCheck : Bool :=
  match det (Prog.seqList [setup, macPasses 100 2 2 300])
      (limbMemory 100 2 0 fun address =>
        if address = 300 then some (testDigits 0) else if address = 301 then some (testDigits 1)
        else none) with
  | none => false
  | some final =>
      (List.range 2).all fun i =>
        (final.ram (word (100 + i))).toNat == limb (testDigits 0 + testDigits 1 * pNat) i

#eval encodeCheck

/-- **The sampler's acceptance continuation** (`K = 3` limbs, `n = 2` digits, kept
`t = 5 + 2^256 · 3`): the halves of `V = t · p^2 + Y₀ + Y₁ p` and the zeroed cells. -/
def useKeptCheck : Bool :=
  let t := 5 + 2 ^ 256 * 3
  let value := t * pNat ^ 2 + (testDigits 0 + testDigits 1 * pNat)
  let memory : Memory := { ram := fun address =>
    if address.toNat = keptLoCell 1000 then word 5
    else if address.toNat = keptHiCell 1000 then word 3
    else if address.toNat = 300 then word (testDigits 0)
    else if address.toNat = 301 then word (testDigits 1)
    else if address.toNat = flagCell 1000 then word 1 else 0 }
  match det (useKept 1000 3 2 300) memory with
  | none => false
  | some final =>
      ((List.range 4).all fun half =>
        (final.ram (word (halfBase 1000 3 + half))).toNat == halfValue value half) &&
      ((List.range 3).all fun i => (final.ram (word (limbBase 1000 + i))).toNat == limb value i) &&
      ((List.range 5).all fun cell => (final.ram (word (1000 + cell))).toNat == 0)

#eval useKeptCheck

/-- **One attempt's tail** (`K = 3`, `n = 2`): the draw `t = 5` gives `V = 5 p^2 + enc < 2^512`
(top limb `0`), so it is kept (flag `1`, kept `(5, 0)`); the draw `t = 2^69 · 2^256` gives
`V ≥ 2^512`, so nothing changes (flag and kept cells stay `0`). -/
def attemptCheck (lo hi : Nat) : Option (Nat × Nat × Nat) :=
  let memory : Memory := { ram := fun address =>
    if address.toNat = drawLoCell 1000 then word lo
    else if address.toNat = drawHiCell 1000 then word hi
    else if address.toNat = 300 then word (testDigits 0)
    else if address.toNat = 301 then word (testDigits 1) else 0 }
  (det (attemptTail 1000 3 2 300) memory).map fun final =>
    ((final.ram (word (flagCell 1000))).toNat, (final.ram (word (keptLoCell 1000))).toNat,
      (final.ram (word (keptHiCell 1000))).toNat)

/-- The machine's decision agrees with `acceptTop` on both draws. -/
def attemptAgrees : Bool :=
  attemptCheck 5 0 == some (1, 5, 0) && attemptCheck 0 (2 ^ 69) == some (0, 0, 0) &&
    acceptTop 3 2 (testDigits 0 + testDigits 1 * pNat) 5 &&
    !acceptTop 3 2 (testDigits 0 + testDigits 1 * pNat) (2 ^ 256 * 2 ^ 69)

#eval attemptCheck 5 0
#eval attemptCheck 0 (2 ^ 69)
#eval attemptAgrees
