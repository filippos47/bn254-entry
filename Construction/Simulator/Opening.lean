/-
Stage 2, part 2: the opening of a valid input to `Q = f_k(u)` (design note B §1.2–§2.2 and the
batched sampler's design A1 §4, items 2–5):

1. `tail`: `90` uniform finite curve points `D_d = (x, ±√(x³ + 3))`, `d = 1 .. 90`: `x` by
   bounded rejection over `254` coins, accepted when `x < p` and `x³ + 3` is a square (the
   candidate `(x³ + 3) ^ ((p + 1) / 4)` squares back; `p ≡ 3 mod 4`), then a fair sign — the
   construction's own offset law (P3's `coinOffsetsLaw`), with no group-order fact;
2. `horner`: `H = pointHorner β (D_1 … D_90)` by `P ← D_d + β · P` from `d = 90` down, with the
   constant multiple `β · P` unrolled over the `192` bits of `β`; the head clamp
   `D_0 = Q − β · H`, aborting when `β · H = O` (no clamped offset exists);
3. `lambdas`: `91` randomisers `λ_d ∈ [1, p)`;
4. `lifts`: `W_d = (λ² x', λ³ y', tag · λ)` with `x' = 1 + tag · (x − 1)`, i.e. `liftRow`;
5. `nonCollectors`: the designated vector `Y* ∈ F_p ^ 455` (lane `pointX`, chunk `0`, switch
   `j*`) — its `182` non-collector coordinates `5d`, `5d + 2` (`rowX_x7`, `rowY_mixed`) drawn
   uniform by bounded rejection over `254` coins, each added to its element's value,
   `acc[e] += κ · Y*[e]`;
6. `solve`: the running rows `X, Y, Z` of every digit on the accumulated values (which now hold
   the sampled non-collectors, and at each collector the running sum without `j*`) and
   `Y*[c] = κ · (W_d.c − row_c) / coef_c` at the three collectors `5d + 1`, `5d + 3`, `5d + 4`
   (`rowX_x9`, `rowY_cubic`, `rowZ_x9`), where `coef_c` is the collector's coefficient in its
   row: `1` for `X` and `Z`, `x²` for `Y` (`κ = ±1`, so `κ⁻¹ = κ`; `x ≠ 0` on the curve, because
   `3` is not a square);
7. `preimage`: `V = enc(Y*) + p ^ 455 · t` with `t` uniform on the fibre
   `{t : V < 2 ^ 115712}` (`BigInt.preimageSampler`, `80` constant-time attempts), split into
   the `2 · 452` halves `(V_i mod 2 ^ 128, V_i / 2 ^ 128)`;
8. `programs`: the `452` hash programs
   `scaleInput pointX 0 j* i E* ↦ (V_i mod 2 ^ 128, V_i / 2 ^ 128)`, `i = 0 .. 451`; the input's
   switch field is `j* · 2 ^ 137`, formed at run time from `j*`.
-/

import Construction.Simulator.Replay

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine Blocks Prog

namespace Opening

/-- Point register moves: `target ← source`, one coordinate at a time. -/
def copyPoint (target source : PointRegisters) : Prog :=
  seqList [ar .and target.tag source.tag source.tag, ar .and target.x source.x source.x,
    ar .and target.y source.y source.y]

/-- Load a stored point (tag, x, y) into a point register. -/
def loadPoint (target : PointRegisters) (address : Nat) : Prog :=
  seqList [loadAt target.tag address, loadAt target.x (address + 1), loadAt target.y (address + 2)]

/-- Store a point register. -/
def storePoint (address : Nat) (source : PointRegisters) : Prog :=
  seqList [storeAt address source.tag, storeAt (address + 1) source.x,
    storeAt (address + 2) source.y]

/-- `P ← O`. -/
def clearP : Prog := seqList [cst 6 0, cst 7 0, cst 8 0]

/-- One round of `s ← s² · a^bit` of the square-root exponentiation (`s` in `rB`, `a` in `rA`);
a one-instruction skip when the exponent bit is clear, so every round costs two. -/
def sqrtRound (bit : Nat) : Prog :=
  .seq (ar .fieldMul rB rB rB)
    (if sqrtExponent.testBit bit then ar .fieldMul rB rB rA else .skip 1)

/-- `rB ← (x³ + 3) ^ ((p + 1) / 4)` and `rA ← x³ + 3`, for `x` in register `source`
(clobbers `rAddr`). -/
def curveRoot (source : Register) : Prog :=
  seqList [ar .fieldMul rA source source, ar .fieldMul rA rA source, cst rAddr 3,
    ar .fieldAdd rA rA rAddr, cst rB 1, rep 252 fun round => sqrtRound (251 - round)]

/-- The acceptance test of the curve-point sampler, on `x = rAcc`: `x < p` and `x³ + 3` is a
square (the candidate root squares back to it). Sets `rBit`; clobbers `rAddr`, `rA` … `rD`. -/
def testCurveX : Prog :=
  seqList [cst rAddr pNat, ar .less rBit rAcc rAddr, curveRoot rAcc,
    ar .fieldMul rC rB rB, ar .xor rC rC rA, cst rD 1, ar .less rC rC rD,
    ar .and rBit rBit rC]

/-- One uniform finite point of the curve into the point cell of digit `d`: an accepted `x`
(in `rOut`), its root recomputed, and a fair sign. -/
def storeCurvePoint (digit : Nat) : Prog :=
  seqList [curveRoot rOut, coinBit rBit, cst rAcc 0, ar .fieldSub rC rAcc rB,
    ar .sub rC rC rB, ar .mul rC rC rBit, ar .add rC rC rB,
    cst rD 1, storeAt (openPoint digit) rD, storeAt (openPoint digit + 1) rOut,
    storeAt (openPoint digit + 2) rC]

/-- One tail digit `d ∈ 1 .. 90`: a uniform finite point (the construction's offset law). -/
def tailOne (digit : Nat) : Prog :=
  seqList [bounded fieldWidth testCurveX attempts (storeCurvePoint digit),
    zeroRegs [rAcc, rOut, rFlag, rBit, rAddr, rSel, rA, rB, rC, rD]]

/-- The `90` tail digits. -/
def tail : Prog := rep 90 fun index => tailOne (index + 1)

/-- One round of `P ← β · P` at bit `bit` of `β`: double, then add `Q` iff the bit is set (a
one-instruction skip otherwise, so every round costs two). -/
def betaRound (bit : Nat) : Prog :=
  .seq (.op (.pointAdd pointP pointP pointP))
    (if betaNat.testBit bit then .op (.pointAdd pointP pointP pointQ) else .skip 1)

/-- `P ← β · P` (clobbers `Q`). -/
def betaMul : Prog :=
  seqList [copyPoint pointQ pointP, clearP, rep 192 fun round => betaRound (191 - round)]

/-- One Horner step `P ← D_d + β · P`. -/
def hornerStep (digit : Nat) : Prog :=
  seqList [betaMul, loadPoint pointQ (openPoint digit), .op (.pointAdd pointP pointQ pointP)]

/-- The head clamp `D_0 = Q − β · H`, `H` in `P`; the tail is valid (the construction's clamped
offsets exist) only when `β · H ≠ O`, and the run aborts otherwise. -/
def head : Prog :=
  seqList [betaMul, .ite 6
    (seqList [cst rAcc 0, ar .fieldSub 8 rAcc 8, loadAt 9 reqTag0, loadAt 10 reqQX,
      loadAt 11 reqQY, .op (.pointAdd pointP pointQ pointP), storePoint (openPoint 0) pointP,
      zeroRegs [0, 4, 6, 7, 8, 9, 10, 11]])
    (.abort rSel)]

/-- `H`, then the head clamp. -/
def horner : Prog := seqList [clearP, rep 90 fun index => hornerStep (90 - index), head]

/-- One randomiser `λ_d ∈ [1, p)`. -/
def lambdaOne (digit : Nat) : Prog :=
  .seq (bounded fieldWidth (testPositiveBelow pNat) attempts (storeAt (openLambda digit) rOut))
    (zeroRegs samplerScratch)

def lambdas : Prog := rep 91 lambdaOne

/-- `W_d = liftRow D_d λ_d`. -/
def liftOne (digit : Nat) : Prog :=
  seqList [loadAt rA (openLambda digit), ar .fieldMul rB rA rA, ar .fieldMul rC rB rA,
    loadPoint ⟨rD, rE, rF⟩ (openPoint digit), cst rAcc 1,
    ar .fieldSub rE rE rAcc, ar .fieldMul rE rE rD, ar .fieldAdd rE rE rAcc,
    ar .fieldSub rF rF rAcc, ar .fieldMul rF rF rD, ar .fieldAdd rF rF rAcc,
    ar .fieldMul rE rE rB, ar .fieldMul rF rF rC, ar .fieldMul rD rD rA,
    storeAt (openRow digit) rE, storeAt (openRow digit + 1) rF, storeAt (openRow digit + 2) rD,
    zeroRegs [rAcc, rAddr, rA, rB, rC, rD, rE, rF]]

def lifts : Prog := rep 91 liftOne

/-- The row-constant cell `k` of digit `d`. -/
def rowCell (digit slot : Nat) : Nat := fieldBase + curveCellCount + 11 * digit + slot

/-- The accumulator cell of x-slot `s` and y-slot `s` of the point lanes. -/
def xCell (slot : Nat) : Nat := accBase + slot
def yCell (slot : Nat) : Nat := accBase + 458 + slot

/-- A uniform non-collector coordinate `Y*[e]` (in `rOut`): stored in its designated cell and
added to its element's value, `acc[e] += κ · Y*[e]`. -/
def storeNonCollector (element : Nat) : Prog :=
  seqList [storeAt (designatedCell element) rOut, loadAt rA tmpKappa, ar .fieldMul rA rA rOut,
    loadAt rB (xCell element), ar .fieldAdd rB rB rA, storeAt (xCell element) rB]

/-- One non-collector coordinate of the designated vector. -/
def nonCollectorOne (element : Nat) : Prog :=
  .seq (bounded fieldWidth (testBelow pNat) attempts (storeNonCollector element))
    (zeroRegs [rAcc, rOut, rFlag, rBit, rAddr, rSel, rA, rB])

/-- The `182` non-collector coordinates `5d`, `5d + 2` of the designated vector. -/
def nonCollectors : Prog :=
  rep 91 fun digit => .seq (nonCollectorOne (5 * digit)) (nonCollectorOne (5 * digit + 2))

/-- `rAcc += RAM[cell] · R[factor]`. -/
def addScaled (cell : Nat) (factor : Register) : Prog :=
  seqList [loadAt rSel cell, ar .fieldMul rSel rSel factor, ar .fieldAdd rAcc rAcc rSel]

/-- `rAcc += RAM[cell]`. -/
def addCell (cell : Nat) : Prog := seqList [loadAt rSel cell, ar .fieldAdd rAcc rAcc rSel]

/-- `RAM[target] = κ · (RAM[row] − rAcc)`. -/
def finishTarget (row target : Nat) : Prog :=
  seqList [loadAt rSel row, ar .fieldSub rSel rSel rAcc, ar .fieldMul rSel rSel rF,
    storeAt target rSel]

/-- `RAM[target] = κ · (RAM[row] − rAcc) · rC⁻¹`: the target of a collector whose coefficient in
its row is `rC = x²` (the `Y` row's `cubic`). -/
def finishScaled (row target : Nat) : Prog :=
  seqList [loadAt rSel row, ar .fieldSub rSel rSel rAcc, ar .fieldMul rSel rSel rF,
    ar .fieldInv rAcc rC rC, ar .fieldMul rSel rSel rAcc, storeAt target rSel]

/-- The three collector coordinates of digit `d` (rows in `evaluateX/Y/Z` order), each into its
designated cell. -/
def solveDigit (digit : Nat) : Prog :=
  seqList [loadAt rA reqX, loadAt rB reqY, ar .fieldMul rC rA rA, ar .fieldMul rD rB rB,
    ar .fieldMul rE rA rB, loadAt rF tmpKappa,
    -- X row: c0 + c1 x + c2 y + c4 x² + v[x7] x + v[x9] + v[y10]
    loadAt rAcc (rowCell digit 0), addScaled (rowCell digit 1) rA, addScaled (rowCell digit 2) rB,
    addScaled (rowCell digit 3) rC, addScaled (xCell (5 * digit)) rA,
    addCell (xCell (5 * digit + 1)), addCell (yCell (3 * digit)),
    finishTarget (openRow digit) (designatedCell (5 * digit + 1)),
    -- Y row: c0 + c2 y + c3 x y + c4 x² + c5 y² + v[mixed] y + v[cubic] x² + v[y8] y + v[y10];
    -- the collector `cubic` has coefficient x², so its target is κ · (W − Y) / x²
    loadAt rAcc (rowCell digit 4), addScaled (rowCell digit 5) rB, addScaled (rowCell digit 6) rE,
    addScaled (rowCell digit 7) rC, addScaled (rowCell digit 8) rD,
    addScaled (xCell (5 * digit + 2)) rB, addScaled (xCell (5 * digit + 3)) rC,
    addScaled (yCell (3 * digit + 1)) rB, addCell (yCell (3 * digit + 2)),
    finishScaled (openRow digit + 1) (designatedCell (5 * digit + 3)),
    -- Z row: c0 + c1 x + v[x9]
    loadAt rAcc (rowCell digit 9), addScaled (rowCell digit 10) rA, addCell (xCell (5 * digit + 4)),
    finishTarget (openRow digit + 2) (designatedCell (5 * digit + 4)),
    zeroRegs [rAcc, rAddr, rSel, rA, rB, rC, rD, rE, rF]]

def solve : Prog := rep 91 solveDigit

/-- The preimage of the designated vector: `V = enc(Y*) + p ^ 455 · t` on `453` working limbs,
then its low `452` limbs as `128`-bit halves. -/
def preimage : Prog :=
  BigInt.preimageSampler samplerBase BigInt.samplerLimbs BigInt.samplerDigits designatedBase
    BigInt.samplerAttempts

/-- Program `limb`: `hash (E* + 2 ^ 128 · scaleTag pointX 0 j* limb) := (V_limb mod 2 ^ 128,
V_limb / 2 ^ 128)`, the switch field `2 ^ 128 · 512 · j*` added at run time. -/
def programOne (limb : Nat) : Prog :=
  seqList [loadAt rFirst (BigInt.halfBase samplerBase BigInt.samplerLimbs + 2 * limb),
    loadAt rSecond (BigInt.halfBase samplerBase BigInt.samplerLimbs + 2 * limb + 1),
    loadAt rA tmpJStar, cst rB (2 ^ 128 * 512), ar .mul rA rA rB,
    cst rB (2 ^ 128 * scaleTag .pointX 0 0 limb), ar .add rA rA rB,
    loadAt rC designatedLabel, ar .add rInput rA rC,
    .op (.program 4 rIndex rInput rFirst rSecond)]

/-- The `452` hash programs, limb by limb. -/
def programs : Prog := rep (limbCount .pointX) programOne

/-- **The opening.** -/
def program : Prog :=
  seqList [tail, horner, lambdas, lifts, nonCollectors, solve, preimage, programs,
    zeroRegs allRegisters]

/-! ### Sizes and costs -/

section Sizes

/-- The simp set for straight-line blocks. -/
macro "prog_size" : tactic => `(tactic| simp only [seqList, Prog.size_seq, Prog.cost_seq,
  size_cst, cost_cst, size_loadAt, cost_loadAt, size_storeAt, cost_storeAt, size_zeroRegs,
  cost_zeroRegs, ar, Prog.size, Prog.cost, List.length_cons, List.length_nil])

theorem size_sqrtRound (bit : Nat) : (sqrtRound bit).size = 2 := by
  unfold sqrtRound; split <;> rfl
theorem cost_sqrtRound (bit : Nat) : (sqrtRound bit).cost = 2 := by
  unfold sqrtRound; split <;> rfl

theorem size_curveRoot (source : Register) : (curveRoot source).size = 509 := by
  unfold curveRoot; prog_size; rw [size_rep _ _ _ fun _ _ => size_sqrtRound _]
theorem cost_curveRoot (source : Register) : (curveRoot source).cost = 509 := by
  unfold curveRoot; prog_size; rw [cost_rep _ _ _ fun _ _ => cost_sqrtRound _]

theorem size_testCurveX : testCurveX.size = 516 := by
  unfold testCurveX; prog_size; rw [size_curveRoot]
theorem cost_testCurveX : testCurveX.cost = 516 := by
  unfold testCurveX; prog_size; rw [cost_curveRoot]

theorem size_storeCurvePoint (digit : Nat) : (storeCurvePoint digit).size = 526 := by
  unfold storeCurvePoint coinBit; prog_size; rw [size_curveRoot]
theorem cost_storeCurvePoint (digit : Nat) : (storeCurvePoint digit).cost = 524 := by
  unfold storeCurvePoint coinBit; prog_size; rw [cost_curveRoot]

theorem size_tailOne (digit : Nat) : (tailOne digit).size = 589865 := by
  unfold tailOne
  simp only [seqList, Prog.size_seq, size_zeroRegs, List.length_cons, List.length_nil, Prog.size]
  rw [size_bounded _ _ _ _ (by rw [cost_storeCurvePoint]; omega), size_testCurveX,
    size_storeCurvePoint, cost_storeCurvePoint]
  rfl
theorem cost_tailOne (digit : Nat) : (tailOne digit).cost = 459290 := by
  unfold tailOne
  simp only [seqList, Prog.cost_seq, cost_zeroRegs, List.length_cons, List.length_nil, Prog.cost]
  rw [cost_bounded _ _ _ _ (by rw [cost_storeCurvePoint]; omega), cost_testCurveX,
    cost_storeCurvePoint]
  rfl

theorem size_tail : tail.size = 90 * 589865 := size_rep _ _ _ fun _ _ => size_tailOne _
theorem cost_tail : tail.cost = 90 * 459290 := cost_rep _ _ _ fun _ _ => cost_tailOne _

theorem size_betaRound (bit : Nat) : (betaRound bit).size = 2 := by
  unfold betaRound; split <;> rfl
theorem cost_betaRound (bit : Nat) : (betaRound bit).cost = 2 := by
  unfold betaRound; split <;> rfl

theorem size_betaMul : betaMul.size = 390 := by
  unfold betaMul copyPoint clearP
  prog_size
  rw [size_rep _ _ _ fun _ _ => size_betaRound _]
theorem cost_betaMul : betaMul.cost = 390 := by
  unfold betaMul copyPoint clearP
  prog_size
  rw [cost_rep _ _ _ fun _ _ => cost_betaRound _]

theorem size_hornerStep (digit : Nat) : (hornerStep digit).size = 397 := by
  unfold hornerStep loadPoint; prog_size; rw [size_betaMul]
theorem cost_hornerStep (digit : Nat) : (hornerStep digit).cost = 397 := by
  unfold hornerStep loadPoint; prog_size; rw [cost_betaMul]

theorem size_head : head.size = 439 := by
  unfold head storePoint; prog_size; rw [size_betaMul]; simp only [Prog.padSet, Prog.padClear]
  prog_size; norm_num
theorem cost_head : head.cost = 415 := by
  unfold head storePoint; prog_size; rw [cost_betaMul]; norm_num

theorem size_horner : horner.size = 3 + 90 * 397 + 439 := by
  unfold horner clearP; prog_size
  rw [size_rep _ _ _ fun _ _ => size_hornerStep _, size_head]
theorem cost_horner : horner.cost = 3 + 90 * 397 + 415 := by
  unfold horner clearP; prog_size
  rw [cost_rep _ _ _ fun _ _ => cost_hornerStep _, cost_head]

theorem size_lambdaOne (digit : Nat) : (lambdaOne digit).size = 457743 := by
  unfold lambdaOne
  simp only [Prog.size_seq, size_zeroRegs, samplerScratch, List.length_cons, List.length_nil]
  rw [size_bounded _ _ _ _ (by rw [cost_storeAt]; omega)]
  simp only [testPositiveBelow, Prog.size_seq, size_cst, ar, Prog.size, size_storeAt, cost_storeAt,
    fieldWidth, attempts]
theorem cost_lambdaOne (digit : Nat) : (lambdaOne digit).cost = 327692 := by
  unfold lambdaOne
  simp only [Prog.cost_seq, cost_zeroRegs, samplerScratch, List.length_cons, List.length_nil]
  rw [cost_bounded _ _ _ _ (by rw [cost_storeAt]; omega)]
  simp only [testPositiveBelow, Prog.cost_seq, cost_cst, ar, Prog.cost, cost_storeAt,
    fieldWidth, attempts]

theorem size_lambdas : lambdas.size = 91 * 457743 := size_rep _ _ _ fun _ _ => size_lambdaOne _
theorem cost_lambdas : lambdas.cost = 91 * 327692 := cost_rep _ _ _ fun _ _ => cost_lambdaOne _

theorem size_liftOne (digit : Nat) : (liftOne digit).size = 34 := by
  unfold liftOne loadPoint; prog_size
theorem cost_liftOne (digit : Nat) : (liftOne digit).cost = 34 := by
  unfold liftOne loadPoint; prog_size

theorem size_lifts : lifts.size = 91 * 34 := size_rep _ _ _ fun _ _ => size_liftOne _
theorem cost_lifts : lifts.cost = 91 * 34 := cost_rep _ _ _ fun _ _ => cost_liftOne _

theorem size_storeNonCollector (element : Nat) : (storeNonCollector element).size = 10 := by
  unfold storeNonCollector; prog_size
theorem cost_storeNonCollector (element : Nat) : (storeNonCollector element).cost = 10 := by
  unfold storeNonCollector; prog_size

theorem size_nonCollectorOne (element : Nat) : (nonCollectorOne element).size = 457249 := by
  unfold nonCollectorOne
  simp only [Prog.size_seq, size_zeroRegs, List.length_cons, List.length_nil]
  rw [size_bounded _ _ _ _ (by rw [cost_storeNonCollector]; omega), size_storeNonCollector,
    cost_storeNonCollector]
  simp only [testBelow, Prog.size_seq, size_cst, ar, Prog.size, fieldWidth, attempts]
theorem cost_nonCollectorOne (element : Nat) : (nonCollectorOne element).cost = 327190 := by
  unfold nonCollectorOne
  simp only [Prog.cost_seq, cost_zeroRegs, List.length_cons, List.length_nil]
  rw [cost_bounded _ _ _ _ (by rw [cost_storeNonCollector]; omega), cost_storeNonCollector]
  simp only [testBelow, Prog.cost_seq, cost_cst, ar, Prog.cost, fieldWidth, attempts]

theorem size_nonCollectors : nonCollectors.size = 91 * (2 * 457249) :=
  size_rep _ _ _ fun _ _ => by
    rw [Prog.size_seq, size_nonCollectorOne, size_nonCollectorOne]
theorem cost_nonCollectors : nonCollectors.cost = 91 * (2 * 327190) :=
  cost_rep _ _ _ fun _ _ => by
    rw [Prog.cost_seq, cost_nonCollectorOne, cost_nonCollectorOne]

theorem size_solveDigit (digit : Nat) : (solveDigit digit).size = 104 := by
  unfold solveDigit addScaled addCell finishTarget finishScaled; prog_size
theorem cost_solveDigit (digit : Nat) : (solveDigit digit).cost = 104 := by
  unfold solveDigit addScaled addCell finishTarget finishScaled; prog_size

theorem size_solve : solve.size = 91 * 104 := size_rep _ _ _ fun _ _ => size_solveDigit _
theorem cost_solve : solve.cost = 91 * 104 := cost_rep _ _ _ fun _ _ => cost_solveDigit _

theorem size_preimage :
    preimage.size = BigInt.preimageSamplerSize BigInt.samplerLimbs BigInt.samplerDigits
      BigInt.samplerAttempts :=
  BigInt.size_preimageSampler _ _ _ _ _
theorem cost_preimage :
    preimage.cost = BigInt.preimageSamplerCost BigInt.samplerLimbs BigInt.samplerDigits
      BigInt.samplerAttempts :=
  BigInt.cost_preimageSampler _ _ _ _ _

theorem size_programOne (limb : Nat) : (programOne limb).size = 14 := by
  unfold programOne; prog_size
theorem cost_programOne (limb : Nat) : (programOne limb).cost = 14 := by
  unfold programOne; prog_size

theorem size_programs : programs.size = 452 * 14 := size_rep _ _ _ fun _ _ => size_programOne _
theorem cost_programs : programs.cost = 452 * 14 := cost_rep _ _ _ fun _ _ => cost_programOne _

/-- The opening's code size. -/
def programSize : Nat :=
  90 * 589865 + (3 + 90 * 397 + 439) + 91 * 457743 + 91 * 34 + 91 * (2 * 457249) + 91 * 104 +
    BigInt.preimageSamplerSize BigInt.samplerLimbs BigInt.samplerDigits BigInt.samplerAttempts +
    452 * 14 + 16

/-- The opening's cost. -/
def programCost : Nat :=
  90 * 459290 + (3 + 90 * 397 + 415) + 91 * 327692 + 91 * 34 + 91 * (2 * 327190) + 91 * 104 +
    BigInt.preimageSamplerCost BigInt.samplerLimbs BigInt.samplerDigits BigInt.samplerAttempts +
    452 * 14 + 16

theorem size_program : program.size = programSize := by
  unfold program
  rw [seqList, seqList, seqList, seqList, seqList, seqList, seqList, seqList, seqList, seqList,
    Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_seq,
    Prog.size_seq, Prog.size_seq, Prog.size_seq, size_tail, size_horner, size_lambdas, size_lifts,
    size_nonCollectors, size_solve, size_preimage, size_programs, size_zeroRegs, allRegisters,
    List.length_finRange]
  rfl

theorem cost_program : program.cost = programCost := by
  unfold program
  rw [seqList, seqList, seqList, seqList, seqList, seqList, seqList, seqList, seqList, seqList,
    Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq,
    Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, cost_tail, cost_horner, cost_lambdas, cost_lifts,
    cost_nonCollectors, cost_solve, cost_preimage, cost_programs, cost_zeroRegs, allRegisters,
    List.length_finRange]
  rfl

end Sizes

end Opening

end Kriterion.ArgoMAC.PlanB.SimMachine
