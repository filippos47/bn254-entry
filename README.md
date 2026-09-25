# Plan B: the chunked one-hot projectivisation of ArgoMAC

This is an entry for the Kriterion `scalar-multiplication` challenge: garbled BN254 scalar
multiplication `f_k(u) = k·u`, checked in Lean against the challenge library
`Kriterion-cc/kriterion-challenge` at commit `aaf2789` (Lean `v4.33.1`).

| metric | value | rule |
|---|---|---|
| `ciphertextBytes` | **1,082,820** `= 96 + 8,736 + 1,092 + 4·(254 − 52)·16 + 52·20,384` | ranked, lower is better |
| `garbleQueries` | **1,123,253** `≤ 1,759,967` | acceptance gate |
| `evaluateQueries` | **1,042,077** `≤ 1,055,879` | acceptance gate |

Every field of `Kriterion.Solution` is proved, and there is no `sorry` in the tree.
`adaptivePrivacy` is the proved assembly `planB_oracleAdaptivePrivacy_of`, applied to the proved
public-first hop `planB_publicFirst` (`G1U → HW`) and the proved machine law of the closed
simulator machine. `#print axioms Submission.solution` reports exactly `propext`,
`Classical.choice` and `Quot.sound`. §7 gives the details.

## Changes from the previous entries

**This is a fork of Lazar's sign-row entry (`Lazar955/bn254-planb`, commit `a79310d`,
1,103,204 bytes), itself built on xinshu's entry (`xinshudong/bn254-entry`).** Everything in it is
their work except one change made in this fork: the **three-constant rows** (§1.7). The slopes of
a digit's 7 encodings carry the true row coefficients, so the row randomisers are gone and each
digit publishes 3 row constants instead of 10. That saves `91·7·32 = 20,384` bytes. The lift
scales `ρ` and `τ` stay.

Phases 3 to 5b are xinshu's entry (`xinshudong/bn254-entry`); the sign row is Lazar's.
The digit MACs, the `X` and `Z` rows, the four lanes, the fold and the EncPRF gate are the same
in all five versions, and the gadget is the same in the first four. The metrics are
`ciphertextBytes / garbleQueries / evaluateQueries`.

| version | metrics | change |
|---|---|---|
| phase 3 | 3,363,376 / 1,305,053 / 990,093 | `127` chunks of 2 bits; each of the `824` mask elements of a switch reduced from three fixed-key Davies–Meyer blocks |
| phase 4 | 1,719,202 / 885,169 / 831,105 | the batched hash-vector sampler (§1.5): a switch's whole lane mask vector from `k` hash answers; ragged-first chunks `[2, 4 × 63]` |
| phase 5a | 1,534,306 / 794,089 / 745,785 | Lazar's four-element `Y` row: 8 encodings per digit, `733` elements per chunk word instead of `824` |
| phase 5b | 1,348,634 / 1,077,993 / 1,035,473 | mixed chunk widths `[2, 5 × 32, 4 × 23]`: `56` chunk words instead of `64` |
| sign row (Lazar) | 1,103,204 / 1,123,253 / 1,042,077 | the sign row replaces the `Y` row (§1.7): 7 encodings per digit, `642` elements per chunk word instead of `733`; a second exceptional case in a 12-byte gadget (§1.8); chunk widths `[2, 5 × 48, 4 × 3]`: `52` chunk words (§1.2, §3) |
| three-constant rows (this fork) | **1,082,820 / 1,123,253 / 1,042,077** | the slopes carry the true row coefficients: 3 published constants per digit instead of 10, no row randomisers (§1.7) |

**Credit.** Lazar's sign-row entry builds on xinshu's phase-5b entry. Its changes are the sign row and its
randomiser `τ` (§1.7), the second exceptional case `T = 2K` with the 12-byte gadget and
bit-indexed gadget permutations (§1.8), the garbler's gadget that asks each fixed-key index once
(§1.8), the `C = 52` profile (§1.2), and the correctness, privacy and machine proofs for all of
it. The rest is xinshu's: the chunked one-hot tables, the batched sampler, the mixed chunk widths,
the simulator machine and most of the privacy proof. The sign row keeps the `cubic` element of
Lazar's four-element `Y` row (the "Y4" row of `Lazar955/argomac-lean`, adopted in phase 5a), with
its `x²` collector scaling, the read-back of `r4` through `y² − 3`, and the proof that `3` is not a
square (`NonResidue.lean`).

---

## 1. The construction

The entry keeps everything of ArgoMAC above the affine encodings, except the `Y` row (§1.7) and
the gadget (§1.8):

- the 91 base-`(2 − ω)` digit MACs;
- the Jacobian `X` and `Z` rows of each digit;
- the curve-membership check;
- the EncPRF whitening.

The `Y` slot of each digit carries a sign row instead, a digit publishes 3 row constants, and the
doubling-exception gadget gains a second exceptional case, 12 bytes per digit.

The entry replaces how the **642 affine encodings** (`a_e·x + b_e` or `a_e·y + b_e`) reach the
evaluator. The original baseline sends one 254-row bit-adaptor table per encoding; Plan B sends
one field join per chunk.

### 1.1 Interface

| `Solution` field | value |
|---|---|
| `FixedIndex` | `PlanB.FixedIndex`. It has two families: `hot` (fold steps) and `gadget`. `#FixedIndex = 159,016` (`card_fixedIndex`: `4·52·5·32·2 = 66,560` hot indices, sized for the widest chunk, and `91·2·254·2 = 92,456` gadget indices, one per digit, coordinate, label position and label bit). The switch masks are hash-oracle queries, not fixed-key gates. |
| `EncIndex` | `EncPRF.PermutationIndex`, `#EncIndex = 508` |
| `Randomness` | `Scheme.Coins`: the private coins only. The three public oracle families are supplied by the library, not by the tape. |
| `Public` | `PlanB.Public`: eight fixed-width fields, no tags |
| `EncodingKey` | `InputMacKey`: exactly the 508 Lamport label pairs `(Z_j, Z_j ⊕ Δ_coord)` |
| `encoding` | `PlanB.Wire.encoding` |
| `scheme` | `Scheme.scheme`: the Plan B garbler and evaluator on `coins.withOracle oracle` |

### 1.2 Elements, lanes, chunks

Each digit needs 7 affine encodings: 4 of `x` and 3 of `y` (§1.7). Together with the 5 encodings
of the curve check, that gives `91·7 + 5 = 642` elements. They are split over **four lanes**:

- `curveX` (3 elements) and `curveY` (2 elements) form **system A**;
- `pointX` (364 elements, `91·4`) and `pointY` (273 elements, `91·3`) form **system B**.

Each 254-bit coordinate is cut into **`C = 52` chunks of mixed widths `[2, 5 × 48, 4 × 3]`**:
chunk 0 has 2 bits (`firstChunkBits`), chunks 1..48 have 5 bits (`chunkBits`, the widest) and
chunks 49..51 have 4 bits (`narrowChunkBits`). Chunk `c` holds `α_c < 2^(w_c)`, and
`x = Σ_c 2^(o_c)·α_c` with `o_c = Σ_{i<c} w_i`: `o_0 = 0`, `o_c = 2 + 5(c − 1)` up to chunk 48
and `o_c = 242 + 4(c − 49)` after it (`chunkOffset_eq_sum`). The recomposition is proved for any
width function (`Proof/Correctness/CanonicalBits.lean`). Keeping chunk 0 at width 2 keeps the
designated switch's analysis (§5.2) at four candidate switches.

### 1.3 `bin-to-hot`: bit labels to one-hot labels

Per chunk, the `w` bit labels are folded into `2^w` one-hot labels by free XOR, one level per bit.
Each fold step's material is the sum of **two** fixed-key permutation images,
`π_{i0}(Z) ⊕ π_{i1}(Z)`, so that no child is a raw permutation image. A chunk of width `w`
publishes `w − 1` 128-bit fold joins per lane: `1 + 48·4 + 3·3 = 202 = 254 − 52` per lane
(`foldStepCount`).

The evaluator hashes every entry except the active one, and recovers the active entry from the
join.

### 1.4 `scale-hot`: one join per chunk and lane

In lane `ℓ` (with `n_ℓ` elements), every one-hot entry `j` of chunk `c` derives a mask vector
`Y_{c,j} ∈ F_p^(n_ℓ)` from its label (§1.5). The garbler publishes the join

```
J_c = Σ_j Y_{c,j} + s_c,        s_c = (a_e · 2^(o_c))_e
```

The evaluator computes `Y_{c,j}` for the inactive `j` (3 in chunk 0, 31 in a 5-bit chunk, 15 in a
4-bit chunk). It recovers the active entry as `J_c − Σ_{j≠α_c} Y_{c,j}`, then folds against the
chunk index:

```
Σ_c Σ_j ι(j)·L_{c,j}[e] = O[e] + a_e·x,        ι(j) = (j : F_p)
```

The garbler **defines** the offset `b_e := O[e]`, so offsets cost no bytes. It derives the slopes
`a_e` from them and publishes the joins last. A chunk word packs the four lanes' joins: `642`
elements at 254 bits, then four zero bits, `163,072` bits or `20,384` bytes.

### 1.5 Rule S: the batched hash-vector sampler

A switch's whole mask vector in one lane is drawn from **`k` hash-oracle answers at once**
(`PlanB.sampleLane`, `Construction/PGS/BatchSampler.lean`). Each answer is two 128-bit blocks,
read as a number below `2^256`; the `k` answers are read as `V < 2^(256k)`; and the vector is the
`n` little-endian base-`p` digits of `V mod p^n`. There is no rejection, because correctness must
hold on every tape.

- **Hash inputs.** Limb `i` of the vector of `(lane, chunk, switch)` at label `L` is asked at
  `scaleInput = L + 2^128·tag`, `tag = ((lane·52 + chunk)·32 + switch)·512 + i`, a number below
  `2^150` (`scaleInput_injective`). The bridge hash is asked at `bridgeInput t`, which is `t`
  moved into `[2^150, p)` (`bridgeInput_val_ge`, at most 2-to-1), so it never meets a scale input.
- **Per-lane limb counts and bias.** The proved bias bound of one vector is `2^(254n − 256k)`
  (`sampleLane_etvDist_le`, `laneDelta_le`), and `k` is the least count for which it is below
  `2^-128` (for `pointY`, `k = 271` would prove only `2^-34`):

  | lane | `n` | `k` | bias bound |
  |---|---:|---:|---:|
  | `pointX` | 364 | 362 | `2^-216` |
  | `pointY` | 273 | 272 | `2^-290` |
  | `curveX` | 3 | 4 | `2^-262` |
  | `curveY` | 2 | 3 | `2^-260` |

  For `pointX`, `laneDelta_le` states only `2^-142`, and the budget uses that weaker bound.
- The garbler draws `Σ_c 2^(w_c) = 4 + 48·32 + 3·16 = 1,588` vectors per lane (`6,352` in all).
  Their total bias is `maskSwapError = 1588·Σ_lane laneDelta ≤ 1589/2^142 ≈ 2^-131.37`.

### 1.6 Two switch systems

- **System A** is keyed on the raw Lamport labels. It delivers the curve check, which publishes
  `t + mask·(x³ + 3 − y²)`. On the curve this equals the bridge key `t`; off the curve it is
  uniform.
- **System B** is keyed on labels whitened by EncPRF pads under the keys `H(bridgeInput t)`. It
  delivers the 637 point-row encodings. An evaluator that cannot produce `t` holds only garbage
  labels for system B.

### 1.7 Rows: the sign row

Each digit's three rows are affine in the delivered values, with the published `γ` fixed
(`Construction/ArgoMAC/Biquadratic.lean`). The `X` row reads three encodings (`x7`, `x9`, `y10`)
and the `Z` row one (`x9`), as in the baseline.

The `Y` slot carries the **sign row** instead of the Jacobian `Y`. Write `K = (a, b)` for a
digit's offset, `T = (u, v)` for its image of the input and `R = T + K` for its MAC point. The
row is `S = τ²·S₀` (`Coordinates.signCoefficients`), with

```
S₀ = 4b³v² + 3ab(27 − b²)u² + (b⁴ + 54b² − 243)v − 36b³
```

On the curve `S₀·(u − a)³ = L²·jacobianY` with `L = 2bv + 3a²u + 9 − b²`
(`Coordinates.evaluateSign`), so `S₀ = L²·y_R` when `u ≠ a`. When `L ≠ 0`, `S` has the quadratic
character of `y_R`, and that is all the decoder needs (§1.8). `τ` is a new nonzero randomiser per
digit, independent of the `X`/`Z` randomiser `ρ`. Off the exceptional cases of §1.8, a real row
is then a lift whose two scales are nonzero multiples of `ρ` and of `τ`, so they are independent
(for a nonzero digit with `T ≠ −K`, `λ = ρ·(u − a)` and `t = τ·L`; §5.3). A zero digit's sign row
is `τ²·b`.

`S₀` has support `{1, y, x², y²}`: no `x` and no `xy` term. So the row reads **three**
encodings: `cubic` (x-type, read with `x²`), `y8` (read with `y`) and `y10` (read with 1).

**The slopes carry the true row coefficients.** Write `c·` for the digit's scaled row coefficients
(`Coordinates.rows offset digit ρ τ`) and `K[e]` for element `e`'s offset (§1.4), which the
projectivized garbling scheme forces to be uniform. Then:

| element | read with | slope |
|---|---|---|
| `x7` | `x` | `X.c4` |
| `x9` (X collector) | `1` | `X.c1 − K[x7]` |
| `y10` (X row) | `1` | `X.c2` |
| `cubic` (S collector) | `x²` | `−s` |
| `y8` | `y` | `S.c5 + s` |
| `y10` (S row) | `1` | `S.c2 − K[y8]` |
| `x9` (Z collector) | `1` | `Z.c1` |

Here `s = (S.c0 − K[S.y10]) / 3`. Each slope reads offsets only, never another slope, so the
garbler computes all of them in one pass from the tape. The published constants are

```
gX = X.c0 − K[x9] − K[X.y10],   gY = S.c4 − K[cubic],   gZ = Z.c0 − K[z9]
```

and the evaluator computes

```
X = gX + x·d_x7 + d_x9 + d_Xy10
S = (gY + d_cubic)·x² + y·d_y8 + d_Sy10
Z = gZ + d_z9
```

`X` and `Z` are exact at every input (`evaluateEncodedX`, `evaluateEncodedZ`). `S` equals its
target plus `s·(y² − x³ − 3)` (`evaluateEncodedY_raw`), so it is exact on the curve
(`evaluateEncodedY`); the evaluator refuses an off-curve input before any query. `ρ` and `τ` stay:
they are the lift scales (`λ = ρ·(u − a)`, `t = τ·L`), and the rows are still `(λ²·x_R, t²·y_R, λ)`
multiples.

**Why this is private.** The offsets alone do the masking. For a fixed digit, the map from the 7
offsets to the 3 constants and the 4 non-collector delivered values is a bijection, and the 3
collector values are then fixed by the rows. The digit bijection of the public-first core (F4,
`JointExactness.digitEquiv`) proves this by reading the offsets back from the published and
visible cells: `K[x7]` and `K[X.y10]` directly; `(K[y8], K[S.y10])` from a `2 × 2` system
(`solvedY10`) whose determinant is `(3 − y²)/3`, never zero because `3` is not a square
(`Proof/Correctness/PGS/NonResidue.lean`); the three collector offsets from `gX`, `gY`, `gZ`. The
read-back is exact at every input, on or off the curve. The collectors' coefficients are unchanged
(`1`, `x²`, `1`), so the simulator's collector solve (§5.2) divides the sign-row target by `x²` as
before and only reads different constants. Each digit publishes `3·32 = 96` bytes instead of 320,
and `RowRandomness` keeps only `ρ` and `τ`.

**Credit.** The sign row and `τ` are Lazar's (`Lazar955/bn254-planb`); the rows' structure, the
`cubic` collector trick (the "Y4" row of `Lazar955/argomac-lean`) and the proof tree are from
Lazar's and xinshu's entries. This fork contributes only the true-coefficient slopes and the three
constants.

### 1.8 Output and gadget

The 91 decoded points are combined by `pointHorner (2 − ω)`. With `P` the input point and `φ` the
digit's endomorphism (so `T = φ(P)`), a row `(X, S, Z)` decodes as follows
(`Garbling.decodeHomogeneous`):

| row | case | decoded point |
|---|---|---|
| `Z = 0`, `X = 0` | `T = K`, the doubling case | `2·φ(P)`, digit from gadget kind 1 |
| `Z = 0`, `X ≠ 0` | `T = −K` | the identity |
| `Z ≠ 0`, `S = 0` | `T = 2K`, where `L = 0`: the tangent at `−K` meets the curve again at `2K` (`tangentZero_double`) | `(3/2)·φ(P)`, with `3/2` in the scalar field, digit from gadget kind 2 |
| otherwise | | `x = X/Z²`, `y = S^((p−1)/2)·(x³ + 3)^((p+1)/4)` |

The last line is Fermat with `p ≡ 3 (mod 4)`: `(x³ + 3)^((p+1)/4)` is a square root of `y_R²`,
and `S^((p−1)/2) = ±1` is the character of `y_R` (`JacobianMixed.signRoot`).

The exception gadget releases the digit in both exceptional cases. Its entry has 12 bytes per
digit: kind 1 at slot `exceptionIndex`, kind 2 at slot `6 + exceptionIndex`
(`Exception.slotOf`). Each written slot holds the digit's code, masked by the low byte of a
digest of the labels of the exceptional input of its kind, the input whose image is `K` or `2K`
(`Exception.exceptionalInput`, `tripleInput`). The evaluator computes one digest per digit, at its
own input (508 queries, as before), and that digest unlocks both kinds. The gadget permutations
are indexed by the label's bit, `FixedIndex.gadget d coord position bit`, so the two labels of a
position meet different permutations. The garbler asks both bits of every position of a nonzero
digit once (`Programs.gadgetPairsM`, 1,016 queries per digit) and reads both digests from these
answers (`pairsDigest`, `pairsMask`). Computing the two digests separately would ask an index
twice wherever the two exceptional inputs share a bit; this way each fixed-key index is asked at
most once, which the privacy proof needs (`FixedOnce`).

## 2. The bytes

| field | contents | bytes |
|---|---|---|
| `curve` | 3 constants | 96 |
| `rows` | 91 × 3 constants × 32 B | 8,736 |
| `exception` | 91 × 12 B (two kinds × 6 slots) | 1,092 |
| `curveXHot`, `curveYHot`, `pointXHot`, `pointYHot` | 4 lanes × 202 fold joins × 16 B | 12,928 |
| `scale` | 52 chunk words × (642 elements × 254 bits + 4 zero bits), 20,384 B each | 1,059,968 |
| **total** | | **1,082,820** |

Every field has a fixed width, so every public value encodes to the same length
(`PlanB.Wire.ciphertextSize`, `Proof/CiphertextSize.lean`; the table is `Wire.byteArithmetic`).

## 3. Query accounting

The two programs are written in `Construction/OraclePrograms.lean` as free query programs. Each
distinct question is asked once, and its answer is kept in a table. Each program is given the
library's indexed `QueryProgram` type at its exact budget (`garbleBudget_eq`,
`evaluateBudget_eq`). The budgets bound every path.

| family | garbling | evaluation |
|---|---|---|
| `scale-hot` masks, `k` hash limbs per switch and lane (`Σ k = 641`) | `1,588·641` = 1,017,908 | `1,536·641` = 984,576 (inactive switches only) |
| `bin-to-hot` fold, 2 permutations per entry at levels `≥ 1` | `4·(4 + 48·60 + 3·28)` = 11,872 | `4·(2 + 48·52 + 3·22)` = 10,256 (active entry recovered) |
| exception gadget | `91·1,016` = 92,456: both labels of every position (zero digits skip) | `91·508` = 46,228: one digest per digit at the evaluator's labels |
| EncPRF pads | 1,016 | ≤ 1,016 (508 whitening pads, plus one per set bit) |
| bridge hash `H(bridgeInput t)` | 1 | 1 |
| **total** | **1,123,253** | **1,042,077** |

- Per lane, garbling asks `2,968 + 1,588k` and evaluation `2,564 + 1,536k`
  (`laneGarbleBudget_closed`, `laneEvalBudget_closed`).
- The garbler is 36.2% under its gate and the evaluator 1.3% under its gate (13,802 queries).
- The bytes depend only on the chunk count, one chunk word per chunk. The evaluator pays for every
  **inactive** switch, `3 + 48·31 + 3·15 = 1,536` per lane, so the evaluation gate fixes the
  count. 52 chunks is the least that fits, even without keeping chunk 0 at 2 bits: the most even
  51-chunk profile, fifty 5-bit chunks and one 4-bit chunk, would need `1,060,898` evaluation
  queries.
- An off-curve input is refused before any query.

## 4. Correctness

Correctness is exact for every tape, oracle and input.

- Every gate is `F_p`-linear, so the one-hot fold is an identity, not an estimate.
- An off-curve input evaluates to `some none`. On the curve the sign row is exact (§1.7), and its
  character gives the sign of `y_R` (`JacobianMixed.signRoot`, `decodeSignOfXNe`).
- The degenerate rows follow the decoder of §1.8: the gadget unlocks the digit at `T = K` and at
  `T = 2K` (`decodeTriple`, `tripleDigitCorrect`), and `T = −K` decodes to the identity.

The proofs are in `Proof/Correctness/`. They reach `perfectCorrectness` through the Lamport label
adapter (`Lamport.restore_selected`).

## 5. Privacy: the argument

### 5.1 The obligation

`GarbledCircuit.OracleAdaptivePrivacy` asks for **one closed `BoundedMachine.Simulator`** with
`size + 1 + firstFuel + secondFuel ≤ 2^60`. For every adversary *machine* `M`, every parameter
and every scalar, it must satisfy

```
Adv(R, M) · 2^100 ≤ T + 1,        T = M.steps = size + 1 + firstFuel + secondFuel
```

- `R` is `lazyRealGame`: the private coins, then the garbler and both adversary stages, all
  against **one fixed, shared lazy oracle**.
- In the machine ideal game, the adversary's queries are answered by that same lazy oracle. The
  simulator can only `query`, `lookup` and `program` it.
- A permutation program needs a fresh input *and* a fresh output; a hash program needs only a
  fresh input. A failed program aborts the experiment to `false`.

### 5.2 The simulator

**Stage 1** receives only `n` and the byte count, and makes **no oracle call**. It publishes a
table in which every field is drawn uniformly in its source form:

- the curve constants;
- the row constants;
- the gadget bytes;
- the fold joins;
- the 52 × 642 scale joins, as canonical field elements packed exactly as the construction
  packs them.

It also keeps a uniform Lamport key. This is the real table's law once every garbler switch mask
vector is uniform. Nothing is programmed in stage 1.

**Stage 2** receives `u` and `f_k(u)`.

*Off the curve* (`f_k(u) = none`), it returns the selected labels and makes no oracle call.

*On the curve* (`f_k(u) = Q`), it proceeds in five steps.

1. **Replay.** It replays the honest evaluator's path to the rows on the lazy oracle:
   - system A;
   - `H(bridgeInput t)`;
   - the 508 whitening pads;
   - system B.

   It **skips** the 362 designated hash queries: the limbs of the mask vector of lane `pointX`,
   chunk 0, inactive switch `j* = α₀ ⊕ 1`, at that switch's label `E*`.
2. **Opening.** It draws the 90 tail digit points exactly as the garbler draws its mask points,
   i.e. the offsets of a uniform coin. The head is the clamp `D₀ = Q − β·H(tail)`, which uses
   only the group law, so `pointHorner β (D₀ :: tail) = Q`. It then draws 91 lift pairs
   `(λ_d, t_d)`, giving the target rows `W_d = lift(D_d, λ_d, t_d) = (λ_d²·x, t_d²·y, λ_d)`
   (`(λ_d², 0, 0)` at the identity).
3. **The designated vector** `Y* ∈ F_p^364`. Its 91 non-collector coordinates (`pointX` indices
   `4d`, the `x7` elements) are drawn uniformly. Each row has a private collector (273 in all, at
   `pointX` indices `4d + 1`, `4d + 2`, `4d + 3`), so the collector coordinates are solved:
   `Y*[c] = κ·(W − partial)·s_c`, where `κ = ι(j*) − ι(α₀) = ±1`, `s_c = 1` for the `X` and `Z`
   collectors (coefficient 1) and `s_c = (x·x)⁻¹` for the sign row's collector `cubic`
   (coefficient `x²`, and `x ≠ 0` on the curve).
4. **Preimage.** It draws `V = enc(Y*) + p^364·t` with `t` uniform on `{t : V < 2^92672}`: the
   `362` hash answers are then uniform on the `sampleLane` fibre over `Y*`, exactly the swapped
   game's law of those limbs.
5. **Programs.** It programs the **362 hash inputs** `scaleInput pointX 0 j* i E* ↦ V_i` (the
   `i`-th 256-bit limb of `V`), so that the evaluator's designated vector there is `Y*` and its
   rows evaluate to `W`. It then returns the labels.

Everything else the adversary later evaluates, including every other switch and fold, the bridge
hash, EncPRF and the gadget, is honest lazy sampling. There is no fixed-key and no EncPRF
programming.

### 5.3 The hybrid chain

`q₁` and `q₂` are the adversary's stage-1 and stage-2 query budgets, and `q = q₁ + q₂`.

| hop | what changes | cost |
|---|---|---|
| `R = G0` | the lazy real game is the tape-sampled game | **0** (exact) |
| `G0 → G0U` | every garbler switch mask vector is swapped to uniform `F_p^n` (its limbs uniform on the sampler's fibre), before the game, non-adaptively | `maskSwapError ≈ 2^-131.37` |
| `G0U → G1U` | the hidden entries (active switches, active fold parents, gadget positions; all of system B off the curve) are deleted at the input choice | `L1 = 3q/2^128 + 2q/(p−1)` |
| `G1U → HW` | public-first reparametrisation: the joint law of the published cells and the visible masks is exactly uniform for every selection rule (F4), off a stage-1 hit **and** off an exceptional input of either kind (where `G1U`'s real gadget unlocks the true digit and `HW`'s published gadget byte is uniform), plus one sampler-bias swap (off the curve `G1U` installs the system-A vectors with `G0U`'s uniform values, while in `HW` the adversary samples them from hash answers), plus the label-coincidence allowance of the designed sub-hop `G1U → G1U°` | `L2 + ε_exc + ε_swap + ε_coin = 4q₁/2^128 + 364/(r−1) + 2^-131.37 + 2^16/2^128` |
| `HW → H` | the real digit rows are replaced by the tail, head-clamp and lift sampler | `ε_pt = 455/(r−1) ≈ 2^-244.77` |
| `H → I^U` | the 362 lazy hash programs may abort (a used input); charged per stage-1 query at an abort site | `ε_abort = q₁/(2^128 − q₁)` |
| `I^U → I` | the non-designated mask vectors go back to `sampleLane` of lazily queried answers; lazy hash answers are exactly uniform, so there is no refill charge | `maskSwapError + 0` |
| `I → M` | the closed machine realises `I` with bounded samplers | `ε_cut ≤ 2^-128` |

The sign row and the second gadget case change the proofs of two hops:

- **`G1U → HW`, the reveal event.** It is now "some nonzero digit has an exceptional input of
  either kind that agrees with `u` off the collisions", that is, at every position whose two
  EncPRF pads do not differ by `Δ` (`Shadow.RevealsAt`, `kindInput`). Each digit has at most two
  targets, one per kind (`differKind_card_le`): the sign-zero kind goes through the double `2K`,
  and doubling is injective because the group has odd order
  (`JacobianMixed.doubleOffset_injective`). The 182 targets, with the collision factor
  `(1 + ε)^508 ≤ 3/2` and the offset restriction, give `ε_exc = 364/(r−1)`.
- **`G1U → HW`, the gadget coins.** Off the curve, a digit's two digests share every position
  where its two exceptional inputs have the same bit, so the hidden coins are the two answers at a
  position where the inputs differ (`LawsOffCells.diffPos`); `omegaEquiv` moves that position to
  position 0 of `x` by an involution of the gadget indices that depends on the offsets
  (`indexSwap`). On the curve, each nonzero digit hides two answers at distinct positions
  (`PosPair`, `positionsOf`), one where only one exceptional input differs from `u` and one where
  the other does, and the two digests read them through the triangular mix of `JointExactness`
  (`mixW`, `ValidPair`, `posK_valid`).
- **`HW → H`, the opening.** The lift has two scales, `lift D λ t = (λ²x, t²y, λ)`
  (`(λ², 0, 0)` at the identity). The real rows are lifts at uniform `(λ, t)` except at `T = K`
  (`X = Z = 0`) and `T = 2K` (`S = 0 ≠ Z`), whose mass is at most `273/#Point`
  (`bn254_doubling_real_le`); the two point laws add `182/#Point`, so `ε_pt = 455/(r−1)`.

### 5.4 The budget

- **Constant part:** `3·maskSwapError + ε_exc + ε_pt + ε_cut + ε_coin = 3·2^-131.37 + 364/(r−1) +
  455/(r−1) + 2^-128 + 2^16/2^128 ≈ 2^-112.0`, dominated by the coincidence allowance
  `coincidenceError = 2^16/2^128`. That allowance covers `13,813` label and bridge coincidence
  events of mass `≤ 2/2^128` each (`LawsGuess.card_eventIndex`, `guess_count_le`). There are three
  copies of `maskSwapError`: `G0 → G0U`, the off-curve system-A vectors in `G1U → HW`, and
  `I^U → I`. The exceptional inputs are charged twice, in `G1U → HW` (the gadget) and in `HW → H`
  (the non-lift rows against a lift): two hops, two different discrepancies on the same event.
- **Linear part:** `3 + 4 + 2 = 9` units of `q/2^128` (the abort charge `1/(2^128 − q₁)` is at
  most `2/2^128`), about `2^-124.8` per query, plus the negligible `2q/(p−1)`.

`chainError_budget` proves `chainError q₁ q₂ · 2^100 ≤ q₁ + q₂ + 1` for `q < 2^100`: in units of
`2^-100` the constant is `≈ 2^-12.0` and the linear coefficient `≈ 2^-24.8` per query. The
assembly closes with

```
Adv(R,M)·2^100 ≤ chainError·2^100 ≤ q₁ + q₂ + 1 ≤ (size + 1) + q₁ + q₂ + 1 = T + 1
```

For `q ≥ 2^100` the bound holds because `Adv ≤ 1`.

### 5.5 The machine

The simulator machine `planBSimulator` costs `size + 1 + firstFuel + secondFuel = 46,336,505,162`
(about `2^35.43`) against the allowance `2^60` (`Design.totalCost_eq`, `Design.totalCost_le`). Its
machine law `machineLaw_planB : MachineLaw planBSimulator 2^-128` is proved
(`Proof/Simulator/OpeningMachine.lean`).

- Stage 1 is dominated by bounded-rejection sampling of 33,660 field cells and by serialising
  the table.
- Stage 2 is dominated by the replay (994,979 lazy queries, with the base-`p` digit extraction of
  every replayed mask vector) and the 362 programs. Its opening draws 91 lift pairs `(λ, t)` and
  writes the two-scale lifts of §5.2.
- The fixed-key query instructions address `FixedIndex` through `Fintype.equivFin`. The machine
  embeds these ordinals as constants.
- `Construction/Simulator/` builds the machine for any two ordinal functions and is computable.
  The instance at `Fintype.equivFin` is not computable, so `planBSimulator` itself is a proof-side
  definition (`Proof/Simulator/Machine.lean`).

## 6. Proof map

| `Solution` field | where | status |
|---|---|---|
| `garbleProgram`, `evaluateProgram`, `garbleQueries`, `evaluateQueries`, `garbleProgramCorrect`, `evaluateProgramCorrect` | `Construction/OraclePrograms.lean` (`garbleProgram_correct`, `evaluateProgram_correct`, `garbleBudget_eq`, `evaluateBudget_eq`) | proved |
| `ciphertextSize` | `Proof/CiphertextSize.lean` (`PlanB.Wire.ciphertextSize`) | proved |
| `lamportCompatible` | `Proof/LamportCompatibility/Labels.lean` (`Lamport.selectedLabels_eq`) | proved |
| `functionCorrect` | `rfl` | proved |
| `perfectCorrectness` | `Proof/Correctness/JacobianMixed.lean` (`JacobianMixed.evaluateCorrect`), `Lamport.restore_selected` | proved |
| `adaptivePrivacy` | `Proof/Privacy/Phase3/Glue/Final.lean` (`planB_oracleAdaptivePrivacy_of`), `Proof/Privacy/Phase3/PublicFirst.lean` (`planB_publicFirst`), `Proof/Simulator/OpeningMachine.lean` (`machineLaw_planB`) | proved |

**The privacy assembly**, `Proof/Privacy/Phase3/Glue/`. All of it is proved. Namespace
`Kriterion.ArgoMAC.Phase3.Glue`.

| module | content |
|---|---|
| `RandomnessSplit` | `splitCoins : Garbling.Randomness ≃ Coins × Oracle`, and the uniform tape as a product |
| `OracleLaw` | the lazy-oracle / eager-completion law (`public_run`, `public_initial`, `lazy_real_uniform`), ported from the ArgoMAC baseline |
| `LazyReal` | `planB_lazy_real`: `lazyRealGame … = G0`, exactly. It consumes `garbleProgram_correct`. |
| `LazyIdeal` | `idealGame_eq_machineAbstract`: the library's ideal game **is** the abstract game of the machine's two kernels; `abstractIdealGame_eq_of_simulation` |
| `AbstractSimulator` | `planBAbstractSimulator` (§5.2), the ideal game `I`, `CandidateSite` / `candidateIndex_injective`, the collector scaling `collectorScale`, and `MachineLaw` |
| `Budget` | the error terms and `chainError_budget` |
| `Assembly` | the hypothesis structures, the identical-until-bad wrapping (`UntilBad`, `CoreUntilBad`; `untilBad_iff` and `coreUntilBad_iff` in `Phase3/UntilBadIff.lean` show each is exactly the advantage bound), and `planB_oracleAdaptivePrivacy`, whose type is literally that of the `adaptivePrivacy` field |
| `AbortBridge` | `AbortBound.of_perQuery'` and `AbortBound.of_keyAveraged`, the bridges from the lazy-oracle abort bounds |
| `Final` | `planB_oracleAdaptivePrivacy_of`: the assembly at `planBHybrids` with every proved input plugged in; its two arguments are `publicFirst` and the machine bound |

The hops themselves live beside the assembly: `Proof/Privacy/Phase3/` (the hybrids
`planBHybrids`, the mask swap, the opening bound, the exactness core), `Phase3/Hidden/` (the
hidden hop `planB_hidden`), `Phase3/PublicFirst/` and its root `Phase3/PublicFirst.lean` (the
public-first hop `planB_publicFirst`, from `designedLaws` and `designedBounds` via
`planB_publicFirst_of_laws_bounds`) and `Phase3/Lazy/` (the lazy refill and the abort bound). The
machine law is in `Proof/Simulator/`: `machineLaw_of` (`Law.lean`) splits it into `Stage1Law`
(`Stage1Law.lean`), `Stage2Law` (from `openingLaw` in `OpeningLaw.lean`, via `Stage2Valid.lean`)
and `SamplerCutoff` (`CutoffMass.samplerCutoff`). `Proof/Privacy.lean` is the single root that
imports all of it. `Proof/README.md` has the module map.

## 7. Status

**Every field is proved.** `Submission.lean` sets

```lean
adaptivePrivacy := Phase3.Glue.planB_oracleAdaptivePrivacy_of
  Security.Phase3.PublicFirst.planB_publicFirst
  (Phase3.Glue.MachineBound.of_law PlanB.SimMachine.machineLaw_planB)
```

- `planB_oracleAdaptivePrivacy_of` is in `Proof/Privacy/Phase3/Glue/Final.lean`.
- `planB_publicFirst` is in `Proof/Privacy/Phase3/PublicFirst.lean`.
- `machineLaw_planB` is in `Proof/Simulator/OpeningMachine.lean`.
- There is no `sorry` in the tree. `#print axioms Submission.solution` reports exactly
  `propext`, `Classical.choice` and `Quot.sound`.

| input | hop(s) | status |
|---|---|---|
| `hybrids = planBHybrids` | the games `G0U`, `G1U`, `HW`, `H`, `I^U` (`Proof/Privacy/Phase3/Hybrids.lean`) | **proved** |
| `H_swap = planB_maskSwapBound` | `G0 → G0U` (`maskSwapError`); `I^U → I` (per derived mask vector, `maskSwapError`, refill `0`) | **proved** |
| `H_open = planB_openingBound` | `HW → H`, `455/(r−1)` | **proved** |
| `H_joint.hidden = planB_hidden` | `G0U → G1U`, identical until a hidden entry is touched, `L1 = 3q/2^128 + 2q/(p−1)` | **proved** |
| `H_joint.publicFirst = planB_publicFirst` | `G1U → HW`: `stageOneHitError q₁ + exceptionalError + maskSwapError + coincidenceError`; from the F4 `jointLaw` core, `designedLaws` and `designedBounds` | **proved** |
| `H_abort = AbortBound.of_keyAveraged rfl rfl Lazy.keyAveragedFailBound` | `H → I^U`, per abort site, `1/(2^128 − q₁)` per stage-1 entry | **proved** |
| `H_machine = MachineBound.of_law machineLaw_planB` | `I → M`, `MachineLaw planBSimulator 2^-128`; the cost field is `planBSimulator.within` (`46,336,505,162 ≤ 2^60`) | **proved** |

## 8. Build and verify

```sh
lake exe cache get      # Mathlib build cache
lake build              # Construction, Proof (with the whole privacy tree), Submission
```

`#print axioms Submission.solution` reports exactly `propext`, `Classical.choice` and
`Quot.sound`. So do `planB_oracleAdaptivePrivacy_of`, `planB_publicFirst` and `machineLaw_planB`.
Every declaration under `Construction/` and `Proof/` uses no other axiom.

## 9. Provenance and AI assistance

**This entry is AI-assisted.** The construction, the proofs, the design notes, this README and
`Intuition.md` were written with AI coding agents under human direction and review. That changes
nothing that is checked: the verifier builds the tree against the pinned public library, rejects
`sorry` and every axiom beyond the three above, and evaluates the three metrics. Every
obligation is proved (§7). The credit paragraph under the version table says which parts are
xinshu's phase-5b entry and which are this entry's.

## 10. Layout

| path | content |
|---|---|
| `Construction/` | the executable construction: `ArgoMAC/` (rows, offsets, EncPRF, gadget, pipeline), `PGS/` (indices, fold, scale-hot, the batched sampler, packing, encoding), `Garbling`, `Scheme`, `QueryMonad`, `OraclePrograms`; `Simulator/`, the simulator machine's code (computable, generic in the index ordinals) |
| `Proof/Correctness/`, `Proof/LamportCompatibility/`, `Proof/CiphertextSize.lean` | the proved fields (with `PGS/NonResidue.lean`: `3` is not a square) |
| `Proof/Privacy.lean`, `Proof/Privacy/Phase3/` | the privacy proof: the hybrids and hops, `Hidden/`, `PublicFirst/`, `Lazy/` and the assembly `Glue/` (§6) |
| `Proof/Privacy/PGS/` | two lemma modules the phase-3 proof reuses (`DaviesMeyerUniform`, `FibreUniformity`) |
| `Proof/Simulator/` | the simulator machine `planBSimulator`, its semantics and its machine law `machineLaw_planB` |
| `Submission.lean` | the `Kriterion.Solution` instance |
| `Intuition.md` | the public design rationale the challenge requires |

Module headers cite internal design notes by file name: the plan `2026-09-17-planB.md`, the
phase-3 note `B-output-aware-simulator.md` and its review `B-review.md`, the phase-4 sampler brief
`A1-batched-sampler-design.md` (cited as "A1 §n"), the phase-5 brief `P5-brief.md`,
`phase2-dfb-design-v2.md`, `planB-hop1-review.md`, the Python reference implementation `pgs.py`,
and task labels and reports (`P1…`, `T9a`, `phase4-notes/T9a-report.md`). They are not part of
this repository; §1–§5 and `Intuition.md` summarise them.
