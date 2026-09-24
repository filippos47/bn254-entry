/-
The fixed register, RAM and stack layout of the Plan B simulator machine, and the numeric
constants its code embeds. Every other machine module reads its addresses from here.

**Registers.** `R0`–`R5` are sampler / arithmetic scratch, `R6`–`R8` and `R9`–`R11` are the
two point registers of `pointAdd`, `R12`–`R15` are the fixed oracle operands (index, input,
first answer, second answer). The big-integer routines (`Construction/Simulator/BigInt.lean`)
write all of `R0`–`R12`, including the index register `R12`: the machine therefore loads
`rIndex` immediately before every fixed-key and EncPRF query, and its hash queries and hash
programs (kind `4`) never read it. No register value is live across a big-integer routine; the
replay reloads its operands (the chunk value, the switch label, the coefficient) from RAM.

**RAM.** Disjoint regions at `2 ^ 40 .. 2 ^ 53`. Stage 1 writes only `field`, `exception`,
`hot` and `key`; stage 2 reads those and writes the rest.

**Stacks.** Stack `0` is the protocol request, stack `1` the private coin stack (every coin is
pushed and immediately popped, so it is empty between instructions blocks), stack `3` the
protocol response. Stack `2` is unused.
-/

import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine

/-! ### Registers -/

/-- Sampler accumulator and general scratch. -/
abbrev rAcc : Register := 0
/-- The accepted candidate of a rejection sampler. -/
abbrev rOut : Register := 1
/-- The accepted flag of a rejection sampler; the stage-2 validity flag. -/
abbrev rFlag : Register := 2
/-- The coin bit and the acceptance test. -/
abbrev rBit : Register := 3
/-- Address scratch of every constant-address load and store. -/
abbrev rAddr : Register := 4
/-- Select scratch and the abort scratch. -/
abbrev rSel : Register := 5
/-- General-purpose registers outside the samplers. -/
abbrev rA : Register := 6
abbrev rB : Register := 7
abbrev rC : Register := 8
abbrev rD : Register := 9
abbrev rE : Register := 10
abbrev rF : Register := 11
/-- The first point register (`R6`, `R7`, `R8`). -/
abbrev pointP : PointRegisters := ⟨6, 7, 8⟩
/-- The second point register (`R9`, `R10`, `R11`). -/
abbrev pointQ : PointRegisters := ⟨9, 10, 11⟩
/-- The fixed oracle operands. -/
abbrev rIndex : Register := 12
abbrev rInput : Register := 13
abbrev rFirst : Register := 14
abbrev rSecond : Register := 15

/-! ### RAM regions -/

/-- The `42,052` public field cells, in `Wire.encoding` order: curve (3), rows (`91 · 11`),
scale (`56 · 733`). -/
def fieldBase : Nat := 2 ^ 40
/-- The `546` exception bytes. -/
def exceptionBase : Nat := 2 ^ 41
/-- The `4 · 198` fold joins: `curveX`, `curveY`, `pointX`, `pointY`, each the lane's
`foldStepCount = 198` blocks in flat slot order. -/
def hotBase : Nat := 2 ^ 42
/-- The parsed request: `u.x`, `u.y`, the two output tag bits, `Q.x`, `Q.y`. -/
def requestBase : Nat := 2 ^ 43
/-- The `508` raw labels sampled in stage 2. -/
def labelBase : Nat := 2 ^ 44
/-- The `508` EncPRF-whitened labels. -/
def whiteBase : Nat := 2 ^ 45
/-- The `733` delivered-value accumulators, in chunk-word slot order. -/
def accBase : Nat := 2 ^ 46
/-- The current chunk's fold: the level labels `E_0 .. E_31` at offsets `0 .. 31` (a chunk is at
most `5` bits wide), the step materials `M_0 .. M_15` at offsets `32 .. 47`, and the designated
label `E*` at offset `48`. -/
def hotLabelBase : Nat := 2 ^ 47
/-- Scalar temporaries (see `tmp*`). -/
def tmpBase : Nat := 2 ^ 48
/-- The opening: digit points, randomisers, lifted rows. -/
def openBase : Nat := 2 ^ 49
/-- The Lamport key: `keyBase + 2 i` is the false label of input bit `i`, `+ 1` the true one
(bits `0 .. 253` are `x`, `254 .. 507` are `y`). Sampled in stage 1. -/
def keyBase : Nat := 2 ^ 50
/-- The switch mask vector under digit extraction: its packed hash limbs (at most `452`) at
offsets `0 .. 511`. -/
def vectorLimbBase : Nat := 2 ^ 51
/-- Its base-`p` digits (at most `455`), above the limbs. -/
def vectorDigitBase : Nat := 2 ^ 51 + 512
/-- The work cells of the preimage sampler (`BigInt.preimageSampler`): the flag, the kept and the
current draw, `453` working limbs, then `2 · 452` halves. -/
def samplerBase : Nat := 2 ^ 52
/-- The designated vector `Y* ∈ F_p ^ 455` (lane `pointX`, chunk `0`, switch `j*`), one digit
per cell: the digit cells the preimage sampler encodes. -/
def designatedBase : Nat := 2 ^ 53

/-- The level label `E_entry` of the current chunk's fold. -/
def hotLabel (entry : Nat) : Nat := hotLabelBase + entry
/-- The first step-material cell. -/
def stepMaskBase : Nat := hotLabelBase + 32
/-- The step material `M_entry` of the current fold step. -/
def stepMask (entry : Nat) : Nat := stepMaskBase + entry
/-- The designated label `E* = E_{0, j*}` of lane `pointX`. -/
def designatedLabel : Nat := hotLabelBase + 48
/-- Coordinate `e` of the designated vector `Y*`. -/
def designatedCell (element : Nat) : Nat := designatedBase + element

/-- Field-cell counts. -/
def curveCellCount : Nat := 3
def rowCellCount : Nat := 91 * 11
def scaleCellCount : Nat := 56 * 733
def fieldCellCount : Nat := curveCellCount + rowCellCount + scaleCellCount
/-- The first scale cell. -/
def scaleCellBase : Nat := fieldBase + curveCellCount + rowCellCount
def exceptionByteCount : Nat := 91 * 6
def hotBlockCount : Nat := 4 * 198
def labelCount : Nat := 508
def keyBlockCount : Nat := 2 * 508

theorem fieldCellCount_eq : fieldCellCount = 42052 := by
  norm_num [fieldCellCount, curveCellCount, rowCellCount, scaleCellCount]

/-! ### Request cells -/

def reqX : Nat := requestBase
def reqY : Nat := requestBase + 1
def reqTag0 : Nat := requestBase + 2
def reqTag1 : Nat := requestBase + 3
def reqQX : Nat := requestBase + 4
def reqQY : Nat := requestBase + 5

/-! ### Temporaries -/

/-- The current chunk value `α` (its active switch). -/
def tmpAlpha : Nat := tmpBase
/-- The active entry `α mod 2 ^ j` of the current fold step `j`. -/
def tmpActive : Nat := tmpBase + 1
/-- The first whitening key `k1` (the bridge hash answer's first block). -/
def tmpK1 : Nat := tmpBase + 3
/-- The second whitening key `k2`. -/
def tmpK2 : Nat := tmpBase + 4
/-- `κ = ι(j*) − ι(α₀) = ±1`. -/
def tmpKappa : Nat := tmpBase + 5
/-- The designated switch `j* = α₀ ⊕ 1`. -/
def tmpJStar : Nat := tmpBase + 6

/-! ### Opening cells -/

/-- Digit point `d` (tag, x, y). -/
def openPoint (digit : Nat) : Nat := openBase + 3 * digit
/-- The lift randomiser of digit `d`. -/
def openLambda (digit : Nat) : Nat := openBase + 400 + digit
/-- The lifted row target `W_d` (X, Y, Z). -/
def openRow (digit : Nat) : Nat := openBase + 500 + 3 * digit

/-! ### Numeric constants -/

/-- The BN254 base-field modulus `p`. -/
def pNat : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583
/-- `2 ^ 256 mod p`, the weight of one hash limb in field Horner (`BigInt.limbsToField`). -/
def c256 : Nat := 2 ^ 256 % pNat
/-- The two 128-bit limbs of `p`. -/
def pLow : Nat := pNat % 2 ^ 128
def pHigh : Nat := pNat / 2 ^ 128
/-- The 128-bit mask. -/
def mask128 : Nat := 2 ^ 128 - 1

/-- `radix.val = (2 − ω).val`, the Horner radix `β` as a natural number (192 bits). -/
def betaNat : Nat := 4407920970296243842393367215006156084916469457145843978464

/-- `(p + 1) / 4`: since `p ≡ 3 (mod 4)`, `a ^ ((p + 1) / 4)` is a square root of every square
`a` (252 bits). -/
def sqrtExponent : Nat := 5472060717959818805561601436314318772174077789324455915672259473661306552146

/-- A word constant. -/
abbrev word (value : Nat) : Word := BitVec.ofNat 256 value

/-! ### Sampling parameters -/

/-- Every bounded rejection sampler makes this many constant-time attempts. -/
def attempts : Nat := 256
/-- Field cells, the designated vector's free coordinates and the randomisers are drawn from
254 coins per attempt. -/
def fieldWidth : Nat := 254

end Kriterion.ArgoMAC.PlanB.SimMachine
