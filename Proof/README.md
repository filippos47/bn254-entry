# Proof map

This map covers the Plan B entry against the challenge library `aaf2789`. The top-level
`README.md` explains the construction and the argument. This file says **which module proves
which obligation**. Every obligation and every privacy input is proved.

- `proved`: proved, with `#print axioms` giving `propext`, `Classical.choice` and `Quot.sound`
  only. `#print axioms Submission.solution` gives exactly these three.

`Proof.lean` imports `Proof.Privacy`, the privacy root, so a bare `lake build` compiles every
module named here.

## 1. `Kriterion.Solution`, field by field

| field | module | theorem / definition | status |
|---|---|---|---|
| `FixedIndex`, `EncIndex`, `fixedFinite`, `encFinite` | `Construction/PGS/Index.lean`, `Construction/ArgoMAC/EncPRF.lean` | `PlanB.FixedIndex` (`card_fixedIndex = 159,016`), `EncPRF.PermutationIndex` (`card_encIndex = 508`) | proved |
| `Randomness`, `randomnessFinite`, `randomness` | `Construction/Scheme.lean` | `Scheme.Coins`, `coinsFinite`, `Scheme.witness` | proved |
| `Public`, `EncodingKey`, `encoding` | `Construction/ArgoMAC/Public.lean`, `Construction/ArgoMAC/Input.lean`, `Construction/PGS/Encoding.lean` | `PlanB.Public`, `InputMacKey`, `PlanB.Wire.encoding` | proved |
| `ciphertextBytes`, `ciphertextSize` | `Proof/CiphertextSize.lean` | `PlanB.Wire.ciphertextSize` (1,082,820) | proved |
| `scheme` | `Construction/Scheme.lean` | `Scheme.scheme` | proved |
| `garbleQueries`, `garbleProgram`, `garbleProgramCorrect` | `Construction/OraclePrograms.lean` | `Programs.garbleProgram`, `garbleBudget_eq` (1,123,253), `garbleProgram_correct` | proved |
| `evaluateQueries`, `evaluateProgram`, `evaluateProgramCorrect` | `Construction/OraclePrograms.lean` | `Programs.evaluateProgram`, `evaluateBudget_eq` (1,042,077), `evaluateProgram_correct` | proved |
| `lamportCompatible` | `Proof/LamportCompatibility/Labels.lean` | `Lamport.selectedLabels_eq` (in `Submission.lamportCompatible`) | proved |
| `functionCorrect` | `Submission.lean` | `rfl` | proved |
| `perfectCorrectness` | `Proof/Correctness/JacobianMixed.lean`, `Proof/LamportCompatibility/Labels.lean` | `JacobianMixed.evaluateCorrect`, `Lamport.restore_selected` | proved |
| `adaptivePrivacy` | `Proof/Privacy/Phase3/Glue/Final.lean`, `Proof/Privacy/Phase3/PublicFirst.lean`, `Proof/Simulator/OpeningMachine.lean` | `planB_oracleAdaptivePrivacy_of planB_publicFirst (MachineBound.of_law machineLaw_planB)` | proved |

`Proof/Correctness/` holds the supporting correctness lemmas:
- `JacobianMixed`: the decoder of README §1.8 on the sign row. `signValue` (`S₀ = L²·y_R` off
  `x = k_x`), `signRoot` (`(h²y)^((p−1)/2)·(y²)^((p+1)/4) = y` for `h ≠ 0`, by Fermat),
  `decodeSignOfXNe` (the generic case), `tangentZero_double` (off `x = k_x`, `L = 0` only at
  `2K`), `affinePoint_double`, `doubleOffset_injective` (the group has odd order), and
  `decodeTriple` and `tripleDigitCorrect` (the `T = 2K` case through the gadget's second kind);
- `CanonicalBits`: chunk recomposition for any width function (`prefix_recomposition`,
  `chunk_recomposition_nat`), used at the profile `[2, 5 × 48, 4 × 3]`;
- `PGS/OneHot`, `PGS/ScaleHot` and `PGS/AffineFp`: the switch systems deliver `a_e·x + O[e]`;
- `PGS/Row`, `PGS/EncSlots` and `PGS/ExceptionalPoints`;
- `PGS/NonResidue`: `3` is not a square in the base field, so `x ≠ 0` on the curve
  (`onCurve_x_ne_zero`) and `y² − 3 ≠ 0` for every `y` (`sq_sub_three_ne_zero`); the sign row
  needs both (README §1.7);
- `Base7Termination`.

The sampler facts (`sampleLane`, the limb bijection, `scaleInput_injective`, `bridgeInput`) are
proved next to their definitions in `Construction/PGS/BatchSampler.lean`; the sampler's bias
(`sampleLane_etvDist_le`, `laneDelta_le`) is in `Proof/Privacy/Phase3/Basic.lean`.

### The lanes

| lane | system | elements `n` (`laneCount`) | hash limbs `k` per vector (`limbCount`) | bias `laneDelta = 2^(254n − 256k)` | bound in `laneDelta_le` |
|---|---|---:|---:|---:|---:|
| `pointX` | B | 364 | 362 | `2^-216` | `2^-142` |
| `pointY` | B | 273 | 272 | `2^-290` | `2^-290` |
| `curveX` | A | 3 | 4 | `2^-262` | `2^-262` |
| `curveY` | A | 2 | 3 | `2^-260` | `2^-260` |

For `pointX`, `laneDelta_le` keeps the weaker exponent `142`, and the budget uses it. Each lane
draws `Σ_c 2^(w_c) = 1,588` mask vectors (`MaskSwap.sum_twoPow_chunkWidth`, `Glue.laneVectorCount`,
tied together by `GameSwap.laneVectorCount_eq`), `6,352` over the four lanes (`card_vectorSite`).

## 2. The privacy assembly and its inputs

`planB_oracleAdaptivePrivacy simulator hybrids H_swap H_open H_joint H_machine H_abort` has
**literally** the type of the `adaptivePrivacy` field.

- It is proved in `Proof/Privacy/Phase3/Glue/Assembly.lean`. It uses:
  - `planB_lazy_real` (`Glue/LazyReal.lean`): the scored real game equals `G0`, exactly;
  - `adaptivePrivacyTransfer` through the abstract ideal game `I`;
  - the hop bounds;
  - `chainError_budget` (`Glue/Budget.lean`);
  - the free unit `size + 1` of `T`.
- `Glue/LazyIdeal.lean` proves that the library's ideal game with any closed machine **is** the
  abstract game of the machine's two kernels (`idealGame_eq_machineAbstract`).
- `Glue/AbstractSimulator.lean` defines the abstract simulator `planBAbstractSimulator`, the
  samplers `idealSamplers`, the collector scaling `collectorScale` (`(x·x)⁻¹` for the sign-row
  collector, `1` for the others) and the game `I`.

### The error terms (`Glue/Budget.lean`)

| term | definition | value |
|---|---|---|
| `maskSwapError` | `laneVectorCount · Σ_lane laneDelta lane`, `laneVectorCount = 1,588` vectors per lane | `≤ 1589/2^142 ≈ 2^-131.37` (`maskSwapError_le_pow`) |
| `hiddenPointError q` | `3q/2^128 + 2q/(p−1)` (the bridge guess `bridgeInput t = key`, at most 2-to-1, has mass `≤ 2/(p−1)`) | linear |
| `stageOneHitError q₁` | `4q₁/2^128` | linear |
| `exceptionalError` | `364/(r−1)`: both exceptional kinds of every digit, at most 2 targets per digit (`differKind_card_le`), `(3/2)·182/#Point·(1 − 91/#Point)⁻¹ ≤ 364/(r−1)` (`reveal_numeric`) | `≈ 2^-245.09` |
| `coincidenceError` | `2^16/2^128`: the `13,813` label and bridge coincidence events of `≤ 2/2^128` each (`LawsGuess.card_eventIndex`, `guess_count_le`) | `2^-112` |
| `outputKernelError` | `455/(r−1)` (`ε_pt`): the exceptional mass `273/#Point` (`bn254_doubling_real_le`) and the two point laws `182/#Point` | `≈ 2^-244.77` |
| `abortError q₁` | `q₁ · abortQueryCharge q₁`, `abortQueryCharge q₁ = 1/(2^128 − q₁)` (input freshness only) | linear |
| `idealRefillError q₁` | `0` (lazy hash answers are exactly uniform) | `0` |
| `machineCutoffError` | `1/2^128` (`Glue/AbstractSimulator.lean`) | `2^-128` |

The public-first hop costs `stageOneHitError q₁ + exceptionalError + maskSwapError +
coincidenceError`. `chainError q₁ q₂` adds every hop, with three copies of `maskSwapError`, and
`chainError_budget` proves `chainError q₁ q₂ · 2^100 ≤ q₁ + q₂ + 1` for `q₁ + q₂ < 2^100`.

### The inputs

| input | Glue statement | error | owner module | status |
|---|---|---|---|---|
| `hybrids` = `planBHybrids` | all five `HybridGame`s | — | P1, `Proof/Privacy/Phase3/Hybrids.lean` (hop (1)'s game in `Hidden/Deleted.lean`) | proved |
| `simulator` = `planBSimulator` | a closed `BoundedMachine.Simulator` | — | P2, `Proof/Simulator/Machine.lean` (`planBSimulator`, `planBSimulator_within`); its code is `Construction/Simulator/` (`Top.machine`) | proved |
| `MaskSwapBound.real` (G0 → G0U) | `HopBound realHybrid maskSwapped` | `maskSwapError = 1588·Σ_lane laneDelta ≈ 2^-131.37` | P1, `GameSwap.lean` (`maskSwapBound_real`), from `MaskSwap.lean` (`maskSwap_etvDist_le`, the vector swap kernel) | proved (`planB_maskSwapBound`) |
| `MaskSwapBound.idealPerMask` (I^U → I) | per derived mask vector: `Σ_site laneDelta (lane site)`, with at most `laneVectorCount = 1,588` sites per lane | `maskSwapError` (the refill charge `idealRefillError` is `0`: lazy hash answers are exactly uniform) | P4, `Proof/Privacy/Phase3/Lazy/` (`maskSwapBound_of`) | proved |
| `MaskSwapBound.ideal` | the sum of `idealPerMask` | same | `Glue/Assembly.lean` (theorem) | proved, given `idealPerMask` |
| `OpeningBound.kernel` (HW → H) | `HopBound publicFirst opened` | `455/(r−1)` | P1, `Proof/Privacy/Phase3/Opening.lean` (`digitPoints_good_law`, `lifts_law`, `bn254_doubling_real_le`), `Proof/Privacy/Phase3/OpeningBound.lean` | proved (`planB_openingBound`) |
| `JointExactnessBound.hidden` (G0U → G1U) | `GameUntilBad`: flagged laws that agree when the flag is down, with the bad mass at most the error | `3q/2^128 + 2q/(p−1)` (the bridge guess `bridgeInput t = key` has mass `≤ 2/(p−1)`) | P1h, `Proof/Privacy/Phase3/Hidden/Final.lean` (`planB_hidden`) | proved |
| `JointExactnessBound.publicFirst` (G1U → HW) | `GameCoreUntilBad`, which by `coreUntilBad_iff` (`UntilBadIff.lean`) is exactly the advantage bound; the proof goes through the designed sub-hop `G1U → G1U°` (the coincidence mass) and the overlap of `G1U°` and `HW` with the middle game `M'` (the F4 lift from `designedLaws`, the flag mass from `designedBounds`, the curve lanes' share of the mask swap) | `stageOneHitError q₁ + exceptionalError + maskSwapError + coincidenceError` `= 4q₁/2^128 + 364/(r−1) + 2^-131.37 + 2^16/2^128` | P1, `Proof/Privacy/Phase3/JointExactness.lean` (`jointLaw`: the core); `Proof/Privacy/Phase3/PublicFirst/` and the root `Proof/Privacy/Phase3/PublicFirst.lean` (`planB_publicFirst`, from `designedLaws` and `designedBounds` via `planB_publicFirst_of_laws_bounds` in `LawsGuess.lean`) | proved (`Security.Phase3.PublicFirst.planB_publicFirst`) |
| `AbortBound.perQuery` (H → I^U) | per abort site, over an existential finite site type: `Σ count·abortQueryCharge q₁`, with `Σ count ≤ q₁`. P4's instance is `Lazy.AbortSite`: the chunk-0 hash cells of `pointX` (the `4·362` candidate designated inputs) and of `curveX` (`4·4`), and the level-1 fold indices of chunk 0 of both lanes. The bridges are `AbortBound.of_perQuery'` and `AbortBound.of_keyAveraged` (`Glue/AbortBridge.lean`). | `q₁/(2^128 − q₁)` (`abortQueryCharge q₁ = 1/(2^128 − q₁)`, input freshness only) | P4, `Proof/Privacy/Phase3/Lazy/AbortPerQuery.lean` (`abortBound_perQuery'_of`); P4b, `Lazy.KeyAveragedFailBound` | proved (`AbortBound.of_keyAveraged rfl rfl Lazy.keyAveragedFailBound`) |
| `MachineBound.law` (I → M) | `MachineLaw simulator (1/2^128)` | `2^-128` | P2, `Proof/Simulator/OpeningMachine.lean` (`machineLaw_planB`). `machineLaw_of` (`Law.lean`) splits it into `Stage1Law` (`Stage1Law.lean`, `stage1Law`), `Stage2Law` (from `openingLaw` in `OpeningLaw.lean` via `Stage2Valid.lean`) and `SamplerCutoff` (`CutoffMass.samplerCutoff`) | proved |
| `MachineBound.cost` | `size + 1 + firstFuel + secondFuel ≤ 2^60` | — | `Glue/Assembly.lean` (`MachineBound.of_law`, from `Simulator.within`) | proved |

The Glue's own supporting results are all proved:
- `splitCoins` and `uniform_split` (`RandomnessSplit`);
- the ported lazy-oracle law (`OracleLaw`: `public_run`, `public_initial`, `lazy_real_uniform`);
- `UntilBad.advantage_le` and `CoreUntilBad.untilBad`;
- `candidateIndex_injective`;
- `digitPoints_head`;
- `chainError_budget`.

## 3. Query-program accounting

Both programs are `FreeQuery` programs, turned into the library's `QueryProgram` at the index
proved by `garbleBudget_eq` and `evaluateBudget_eq`. That index bounds every path.

Per lane, with `k = limbCount lane` hash limbs per switch mask vector, 52 chunks (chunk 0 of
width 2 with 4 switches, chunks 1..48 of width 5 with 32 switches, chunks 49..51 of width 4 with
16 switches):

| | garbling | evaluation |
|---|---|---|
| per lane | `(4 + 4k) + 48·(60 + 32k) + 3·(28 + 16k) = 2,968 + 1,588k` | `(2 + 3k) + 48·(52 + 31k) + 3·(22 + 15k) = 2,564 + 1,536k` (the active switch is recovered) |
| `curveX` (`k = 4`) | 9,320 | 8,708 |
| `curveY` (`k = 3`) | 7,732 | 7,172 |
| `pointX` (`k = 362`) | 577,824 | 558,596 |
| `pointY` (`k = 272`) | 434,904 | 420,356 |
| bridge hash | 1 | 1 |
| EncPRF pads | 1,016 | 1,016 (508 whitening pads, plus the bit pads) |
| gadget | `91 · 1,016` = 92,456 (`gadgetPairsM`: both bits of every position of a nonzero digit) | `91 · 508` = 46,228 (`masksM`: one digest per digit, which unlocks both kinds) |
| **total** | **1,123,253** (gate 1,759,967) | **1,042,077** (gate 1,055,879) |

The per-lane closed forms are `laneGarbleBudget_closed` and `laneEvalBudget_closed`.

## 4. Simulator-machine accounting

These counts are from P2's `Construction/Simulator/Design.lean`. There, `totalCost_eq` evaluates
the closed formulas by `norm_num` and `totalCost_le` proves the bound.

| | count |
|---|---:|
| code table `size + 1` | 25,386,781,319 |
| `firstFuel` (stage 1: 33,660 field cells by bounded rejection, the 1,092 gadget bytes, the 808 fold joins, the key, serialisation) | 11,040,165,947 |
| `secondFuel` (stage 2, valid arm: parse, replay with the digit extraction of every replayed mask vector, opening, labels) | 9,909,557,896 |
| **total** `size + 1 + firstFuel + secondFuel` | **46,336,505,162 ≈ 2^35.43 ≤ 2^60** |

The 33,660 field cells are the 3 curve constants, the `91·3` row constants and the `52·642` scale
cells. The stage-2 oracle traffic is 994,979 lazy queries (`Design.stage2Queries_eq`: 10,256 fold,
984,214 hash, the bridge hash and 508 whitening pads) and 362 hash programs (`stage2Programs_eq`).
These reconcile with the honest evaluator (`evaluator_queries`):

`994,979 + 362 + 508 (bit pads) + 46,228 (gadget) = 1,042,077`

The opening (`Construction/Simulator/Opening.lean`) draws 91 lift pairs `(λ, t)` and writes the
lifts `(λ²x', t²y, tag·λ)`, with `x' = 1 + tag·(x − 1)`, so that the identity's words `(0, 0, 0)`
give `(λ², 0, 0)`. The free designated coordinate of digit `d` is `pointX` index `4d`
(`rowX_x7`), and its collectors are `4d + 1`, `4d + 2`, `4d + 3` (`rowX_x9`, `rowY_cubic` for the
sign row, `rowZ_x9`). The designated preimage is `V = enc(Y*) + p^364·t` over 363 working limbs,
362 of them programmed.

## 5. Module map for the phase-4 and phase-5 changes

Modules added by the batched sampler (phase 4) and the four-element `Y` row (phase 5):

| module | content |
|---|---|
| `Construction/PGS/BatchSampler.lean` | the sampler `sampleLane`, `limbCount`, the scale tag and `scaleInput` (below `2^150`, `scaleInput_injective`), `bridgeInput` (into `[2^150, p)`, at most 2-to-1), the limb bijection |
| `Construction/Simulator/BigInt.lean` | the machine's division-free big-integer routines: limb packing, `V mod p` by field Horner, Hensel exact division, digit extraction, the multiply-accumulate encoder and the preimage sampler |
| `Proof/Simulator/BigIntArith.lean` | the natural-number facts behind those routines (Hensel step, Horner step, multiply-accumulate carry) |
| `Proof/Simulator/BigIntDet.lean` | deterministic evaluation of plain machine blocks (`det`, `memSem_det`) and the word laws of the arithmetic operations |
| `Proof/Simulator/BigIntMachine.lean` | the routines compute what they claim (`memSem_digitsOf`, `det_exactDivP`, `det_macPasses`, …) |
| `Proof/Simulator/BigIntSampler.lean` | the preimage sampler's law (`memSem_preimageSampler`) and that it touches no oracle |
| `Proof/Simulator/BigIntAccept.lean` | the sampler's acceptance at the designated vector: `t` uniform on the whole fibre `{t : enc + p^364·t < 2^92672}`, abort mass `< 2^-138` over 80 attempts |
| `Proof/Simulator/BigIntBound.lean` | the two large-numeral facts `preimageAccept_nat` and `preimageComplete_nat` (`decide +kernel`) |
| `Proof/Simulator/OpeningFree.lean` | the opening's 91 free designated coordinates (`Opening.nonCollectors`) |
| `Proof/Simulator/ValidOps.lean` | every oracle operation of the valid arm is a permitted query or hash program (`valid_ops`) |
| `Proof/Privacy/Phase3/Hidden/Deleted.lean` | the game `G1U`: hidden-entry deletion at the input choice (split off `Hybrids.lean`) |
| `Proof/Correctness/PGS/NonResidue.lean` | `3` is not a square (Euler's criterion via `reduce_mod_char`); `onCurve_x_ne_zero`, `sq_sub_three_ne_zero` (Lazar's proof) |

Modules the two phases reworked, with what they prove at the current parameters:

| module | what it now proves |
|---|---|
| `Construction/PGS/Params.lean` | the width function `chunkWidthNat` (`[2, 5 × 48, 4 × 3]`), `chunkOffset_eq_sum`, the three-piece sums (`sum_chunkWidth`, `foldBase_eq`) |
| `Construction/ArgoMAC/Biquadratic.lean` | the row of the `Y` slot (the four-element row in phase 5, the sign row now): `evaluateEncodedY_raw` at every input, `evaluateEncodedY` on the curve |
| `Proof/Privacy/Phase3/Basic.lean` | the sampler's bias `sampleLane_etvDist_le` and the per-lane `laneDelta_le` |
| `Proof/Privacy/Phase3/MaskSwap.lean`, `GameSwap.lean` | the non-adaptive swap of every garbler mask vector (`maskSwap_etvDist_le`, `card_vectorSite = 6,352`) |
| `Proof/Privacy/Phase3/Opening.lean` | the collector solve with the `cubic` collector's coefficient `x²` (`collectorSolve`, `collectorEquiv`, `collectorsOf_eq_solve`) |
| `Proof/Privacy/Phase3/JointExactness.lean` | F4 with `r4` read back through `y² − 3` (`solvedR4`, `garbleRow_solved`, `digitEquiv`), at every input |
| `Proof/Privacy/Phase3/PublicFirst/LawsGuess.lean` | the `13,813` coincidence events and `coincidenceError` |
| `Proof/Privacy/Phase3/Lazy/` | the abort sites `Lazy.AbortSite` and the refill at charge `0` (`IdealPerMask.maskSwapBound_of`) |
| `Proof/Simulator/Stage1Serialize.lean`, `Stage1Wire.lean`, `Stage1Match.lean` | the stage-1 serializer per chunk word: `641` cells of `254` bits, then the last cell as `256` bits and two pushed zero bits; the last cell's two top bits and the two pushed bits are the word's four zero bits |
| `Proof/Simulator/OpeningSolve.lean`, `OpeningLaw.lean` | the machine's sign-row solve `finishScaled` (`memSem_finishScaled`), equal to the abstract simulator's `collectorScale` (`solveWords_component`) |

## 6. Module map for the sign row

This entry added no module. It reworked these for the sign row, the second exceptional case of
the gadget and `C = 52`:

| module | what it now proves |
|---|---|
| `Construction/ArgoMAC/Coordinates.lean` | the sign row `signCoefficients` and the tangent `tangentLine`; `evaluateSign` (`S₀·(u − a)³ = L²·jacobianY` on the curve) and `tangentFactor`; `rows` with the independent `τ` |
| `Construction/ArgoMAC/Biquadratic.lean`, `Construction/PGS/Elements.lean`, `Construction/ArgoMAC/Public.lean` | the sign row's three elements (`cubic`, `y8`, `y10`) and four constants: 7 elements and 10 constants per digit |
| `Construction/ArgoMAC/Exception.lean` | the 12-byte `Entry`, `slotOf` (kind 2 at `6 + exceptionIndex`), `doubleOffset`, `tripleInput` |
| `Construction/ArgoMAC/FieldMacToECMac.lean` | `RowRandomness.tau`, the bit-indexed `GadgetPermutations`, `garbleEntry` writing both kinds (`writeCase`), `unlockExceptional`, `unlockTriple` |
| `Construction/Garbling.lean` | the decoder `decodeHomogeneous` (`fieldPower`, `characterExponent`, `rootExponent`, `threeHalves`) |
| `Construction/PGS/Index.lean`, `Construction/PGS/Params.lean` | `FixedIndex.gadget d coord position bit`, `card_fixedIndex = 159,016`; `C = 52`, 642 elements, 20,384-byte chunk words |
| `Construction/OraclePrograms.lean` | the garbler's gadget `gadgetPairsM`, `pairsDigest`, `pairsMask` (`pairsMask_eval`); the budgets `1,123,253` and `1,042,077` |
| `Proof/Correctness/JacobianMixed.lean` | the sign-row decoding lemmas listed in §1 |
| `Proof/Privacy/Phase3/Opening.lean`, `OpeningBound.lean` | the two-scale `lift`, `realRow_double`, `realRow_triple`, `lifts_law`, `bn254_doubling_real_le` (`273/#Point`); `HW → H` at `455/(r−1)` |
| `Proof/Privacy/Phase3/JointExactness.lean` | F4 for the three-constant rows (`digitEquiv`): the 7 offsets read back from `gX, gY, gZ` and the visible values, `(K[y8], K[S.y10])` through `3 − y²` (`solvedY10`); and the two-slot gadget bijection `gadgetEquiv2` through the triangular mix `mixCoins` |
| `Proof/Privacy/Phase3/PublicFirst/Shadow.lean`, `BoundsReveal.lean`, `BoundsRevealBound.lean` | the reveal event with both kinds (`kindInput`, `RevealsAt`), `differKind_card_le`, `reveal_numeric`, `revealBound_planBShadow` at `364/(r−1)` |
| `Proof/Privacy/Phase3/PublicFirst/LawsOffCells.lean`, `LawsOffMatch.lean`, `LawsOffLaw.lean` | off the curve: the differing position `diffPos`, the index involution `indexSwap`, `omegaEquiv` |
| `Proof/Privacy/Phase3/PublicFirst/LawsOnE*.lean` | on the curve: two hidden gadget indices per digit (`PosPair`, `positionsOf`, `posK`, `posK_valid`), read through `mixW` (`ValidPair`, `readW`, `digest_splitW`) |
| `Proof/Privacy/Phase3/PublicFirst/LawsTable.lean` | the garbler's gadget asks each index once (`gadgetPairsM_once`, `garbleEntryM_once`) |
| `Proof/Privacy/Phase3/Hidden/` | the hidden hop for the garbler's gadget pairs (`GarblerAsk`) |
| `Proof/Simulator/` | the two-scale lifts (`OpeningLift.lean`: `memSem_lambdas`, `memSem_liftOne`), the collectors at `4d + 1`, `4d + 2`, `4d + 3`, and the stage sizes behind the cost constants of `Construction/Simulator/Design.lean` |

## 7. Other modules

`Proof/Privacy/PGS/` keeps only the two lemma modules the phase-3 proof imports,
`DaviesMeyerUniform.lean` and `FibreUniformity.lean`. The earlier hybrid chain, written against
the previous library interface, has been removed. Every module under `Construction/` and `Proof/`
is in the import closure of `Submission`.
