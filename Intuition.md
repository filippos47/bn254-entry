# Intuition: chunked one-hot projectivization of ArgoMAC

This entry garbles BN254 scalar multiplication at **1,348,634 bytes** of public ciphertext.
Garbling makes at most **1,077,993** oracle queries (gate 1,759,967) and evaluation at most
**1,035,473** (gate 1,055,879). Both figures are the exact bounds carried in the types of
`garbleProgram` and `evaluateProgram`.

This note explains the design, the byte count, the query count and the privacy argument.
Section 7 states what is proved: every obligation.

The first version of this entry (3,363,376 bytes) drew each switch mask element from three
fixed-key Davies–Meyer blocks and used 127 chunks of 2 bits. The second (1,719,202 bytes) drew each
switch's whole mask vector from one batch of hash-oracle answers (§2.3), which made switches cheap
enough for 4-bit chunks. The third (1,534,306 bytes) adopted Lazar's four-element `Y` row (§2.6),
which cuts the encodings per digit from nine to eight. This version mixes 5-bit and 4-bit chunks
(§2.1, §4), so a coordinate needs 56 chunks instead of 64.

---

## 1. Starting point: where the ArgoMAC baseline spends its bytes

The baseline follows the BaBe/ArgoMAC paper. The evaluator holds one Lamport label for each of
the 508 input bits (254 bits of `x`, then 254 bits of `y`). The garbled circuit has to turn those
labels into 91 elliptic-curve MACs, one per base-7 digit of the secret scalar. The output point
is then rebuilt from the MACs by Horner's rule.

Each digit's MAC comes from three Jacobian rows (`X`, `Y`, `Z`). Each row is a low-degree
polynomial in `(x, y)` with published coefficients `γ`. In the baseline the rows read nine
*affine encodings* of the input coordinates, values of the form `a_e · x + b_e` or
`a_e · y + b_e`.

In the baseline, each encoding comes from its own bit-adaptor table: 254 rows, one per input
bit, each a masked field element. These per-encoding tables are almost all of the baseline's
ciphertext. The published row constants (`91 · 11` field elements), the curve check and the
doubling-exception gadget together take under 33 KB.

**Plan B keeps everything above the affine encodings, with one change.** That covers the 11
published `γ` per digit, the Jacobian rows, the curve check, the EncPRF gate and the exception
gadget. The change is the `Y` row, which reads four encodings instead of five (§2.6). A digit then
reads eight encodings: five of `x` and three of `y`. With 91 digits, plus five values for the
curve-membership check, there are **733 affine encodings**: 458 of `x` and 275 of `y`. Plan B's
main work is to replace how those 733 encodings reach the evaluator.

---

## 2. The construction: one-hot switch systems over a plain group

### 2.1 Cutting a coordinate into chunks

Each 254-bit coordinate is cut into `C = 56` chunks of **mixed widths** `[2, 5 × 32, 4 × 23]`.
Chunk 0 has 2 bits, chunks 1 to 32 have 5 bits and chunks 33 to 55 have 4 bits. Chunk `c` of `x`
is a number `α_c < 2^(w_c)`, and

```
x = Σ_c 2^(o_c) · α_c        (in F_p),   o_c = w_0 + … + w_(c−1)
```

so `o_0 = 0`, `o_c = 2 + 5(c − 1)` up to chunk 32, and `o_c = 162 + 4(c − 33)` after it.

This identity holds because the Lamport bits are the canonical little-endian digits of
`x.val < p < 2^254`. `Proof/Correctness/CanonicalBits.lean` proves it for any width function.
Nothing is reduced modulo anything but `p`. The narrow chunk sits first so that the privacy
argument's designated switch (§6.2) still has only four candidates.

### 2.2 `bin-to-hot`: bit labels to a one-hot label vector

For each chunk, the `w` bit labels are folded into `2^w` *one-hot* labels. Entry `j` carries
the "active" label when `j = α_c` and a "zero" label otherwise. The fold doubles the vector once
per bit, and each level uses free XOR:

```
M_r        := π_{i0}(Z_r) ⊕ π_{i1}(Z_r)       two fixed-key permutations per entry
right child := M_r ,  left child := Z_r ⊕ M_r
join_j      := (⊕_r M_r) ⊕ (zero label of bit j)   one published 128-bit block per level
```

Level 0 is free, so a chunk of width `w` publishes `w − 1` blocks per lane:
`1 + 32 · 4 + 23 · 3 = 198` per lane. The evaluator mirrors the fold. It hashes every entry except
the active one and recovers the active entry's material from the published join.

The two-permutation step (`π_{i0} ⊕ π_{i1}` rather than one Davies–Meyer call) keeps the left
child from being a raw permutation image. A single permutation would let one inverse query
recover the free-XOR offset Δ.

### 2.3 `scale-hot`: one published join per chunk, and the batched sampler

The key cost fact: a switch system over a **plain** group publishes a single join, whatever the
one-hot length. In a lane with `n` encodings, every one-hot entry `j` of chunk `c` turns its label
into a mask vector `Y_{c,j} ∈ F_p^n`, and the garbler publishes

```
J_c := Σ_j Y_{c,j} + s_c ,      s_c := (a_e · 2^(o_c))_e        (n field elements)
```

The evaluator holds the labels of every inactive entry, so it can compute `Y_{c,j}` for every
`j ≠ α_c`. It recovers the active entry as `J_c − Σ_{j ≠ α_c} Y_{c,j}` and folds the one-hot
against the chunk index for free:

```
Σ_j ι(j) · L_{c,j} = Σ_j ι(j) · Y_{c,j} + α_c · s_c ,     ι(j) = (j : F_p)
```

Summing over the chunks gives, for every encoding `e`,

```
Σ_c Σ_j ι(j) · L_{c,j}[e] = O[e] + a_e · x ,     O[e] := Σ_c Σ_j ι(j) · Y_{c,j}[e]
```

`O[e]` is known to the garbler at garbling time, and in the underlying scheme the offsets `b_e`
are free garbler randomness. So the garbler *defines* `b_e := O[e]`: the offset costs no bytes.
It then derives the slopes `a_e` from these offsets and publishes the joins last.

**The sampler.** The whole vector `Y_{c,j}` comes from `k` hash-oracle answers at once. Each
answer is two 128-bit blocks, a number below `2^256`; the `k` answers form one number
`V < 2^(256k)`; and `Y_{c,j}` is the first `n` base-`p` digits of `V`, that is the digits of
`V mod p^n`. There is no rejection (correctness must hold on every tape); the vector is within
`(2^(256k) mod p^n) / 2^(256k) ≤ 2^(254n − 256k)` of uniform in total variation. Choosing the least
`k` for which that bound is below `2^-128`:

| lane | `n` | `k` | bias bound |
|---|---:|---:|---:|
| `pointX` | 455 | 452 | `2^-142` |
| `pointY` | 273 | 272 | `2^-290` |
| `curveX` | 3 | 4 | `2^-262` |
| `curveY` | 2 | 3 | `2^-260` |

(For `pointY`, `k = 271` would prove only `2^-34` from this bound, so the lane takes 272 limbs.)
A switch therefore costs `452 + 272 + 4 + 3 = 731` hash queries over the four lanes. The first
version's sampler reduced three blocks per field element and cost `3 · 824 = 2,472` queries per
switch.

**The hash inputs.** Limb `i` of the vector of `(lane, chunk, switch)` at label `L` is asked at
`L + 2^128 · tag`, where the tag packs lane, chunk, switch and limb in mixed radix. Every such
input is below `2^150`, and distinct `(lane, chunk, switch, limb, label)` give distinct inputs. The
only other hash question, the bridge key's, is asked at `bridgeInput t`, which moves `t` into
`[2^150, p)`; so no evaluator question ever lands on a switch limb by accident. The move is at
most two-to-one, which is why the bridge guess costs `2/(p−1)` rather than `1/(p−1)` below.

### 2.4 Two switch systems per coordinate: the curve check gates the point rows

Each coordinate carries **two** systems, so there are four *lanes*.

* **System A** (`curveX`, `curveY`) is keyed on the raw Lamport labels. It delivers the five
  curve-check encodings. The check publishes `t + mask · (x³ + 3 − y²)`, which is the bridge key
  `t` exactly on the curve and uniform off it.
* **System B** (`pointX`, `pointY`) is keyed on EncPRF-whitened labels. Their one-time pads are
  derived from `H(bridgeInput t)`, and system B delivers the 728 point-row encodings. An
  evaluator who cannot produce `t` holds only garbage labels for system B.

The whitening applies one pad per (coordinate, position) to *both* labels of a pair, so it keeps
the free-XOR offset that the fold needs. The exception gadget still reads the bit-dependent
EncPRF labels, as in the baseline.

### 2.5 The input interface

The encoding key is exactly the 508 Lamport label pairs `(Z_j, Z_j ⊕ Δ_coord)`, and `Encode`
selects one label per bit. The private coins hold the offsets, row randomizers, gadget pads,
bridge key, curve mask and the free-XOR label material. The library supplies the three public
oracle families (fixed-key permutations, EncPRF permutations, and the field hash) separately.

### 2.6 The rows, and the four-element `Y` row

Each row is affine in the delivered encodings once `γ` is fixed: the published constants cancel
the offsets of the encodings the row reads, and each encoding's slope cancels the randomizer of
the monomial it rides on.

The `Y` row reads four encodings: `cubic` and `mixed` (both of `x`, read with `x²` and with `y`),
`y8` and `y10`. The `cubic` slope `−r4` contributes `−r4 · x³`. On the curve `x³ = y² − 3`, so
that term becomes `r4 · (3 − y²)`: the `y8` slope absorbs the `y²` part and the published `c0` the
constant. So the row is exact on the curve. Off the curve it would be off by `r4 · (y² − x³ − 3)`,
but the evaluator refuses an off-curve input before it asks anything.

The four-element `Y` row is Lazar's (the "Y4" row of `Lazar955/argomac-lean`, also ported onto
this entry's phase-3 version in `Lazar955/bn254-planb`); the README's §1.7 gives the details.

---

## 3. Why the ciphertext is 1,348,634 bytes

| Field | Contents | Bytes |
|---|---|---|
| `curve` | 3 curve-check constants | 96 |
| `rows` | 91 digits × 11 constants × 32 B | 32,032 |
| `exception` | 91 digits × 6-byte gadget entry | 546 |
| 4 × `hot` | 4 lanes × 198 fold joins × 16 B | 12,672 |
| `scale` | 56 chunk words × (733 elements × 254 bits + 2 zero bits) = 23,273 B | 1,303,288 |
| **total** | | **1,348,634** |

Every field has a fixed width and there are no tags. So every public value encodes to the same
length, and the byte-count theorem (`PlanB.Wire.ciphertextSize`) does not mention `garble` at
all. Each chunk word packs its 733 field elements at 254 bits each, the exact bit length, without
padding each element to 32 bytes; two zero bits make the word fill whole bytes.

**The size is dominated by the chunk count.** Each chunk publishes one 733-element join, whatever
its width. So fewer, wider chunks mean fewer bytes: `C = 10` would give about 0.28 MB. The price
of a wide chunk is paid in **queries**, not bytes. Section 4 shows that the query gates are what
fix the chunk widths.

---

## 4. Query counts, and why the chunks are 5 and 4 bits wide

The challenge bounds garbling at 1,759,967 queries and evaluation at 1,055,879. Each count is
exact for the construction as written. Each distinct question is asked once, and a program
reuses an answer only where it keeps that answer in a local table.

| Family | Garbling | Evaluation |
|---|---|---|
| `scale-hot` masks: `731` hash limbs per switch | `731 · Σ_c 2^(w_c)` = `731 · 1,396` = 1,020,476 | `731 · Σ_c (2^(w_c) − 1)` = `731 · 1,340` = 979,540 |
| `bin-to-hot` fold: 2 permutations per entry, level `j ≥ 1` | `4·Σ_c (2^(w_c+1) − 4)` = 10,272 | `4·Σ_c (2^(w_c+1) − 2w_c − 2)` = 8,688 |
| Exception gadget: 508 labels per nonzero digit | ≤ 91 · 508 = 46,228 | 91 · 508 = 46,228 |
| EncPRF pads: whitening shares the bit-0 pad | 1,016 | ≤ 1,016 (508 + one per set bit) |
| Bridge-key hash `H(bridgeInput t)` | 1 | 1 |
| **total** | **1,077,993** (38.7% under) | **1,035,473** (1.9% under) |

The switch masks dominate. The evaluator pays for every **inactive** switch, not only the active
one, because it must strip each inactive mask from the join: `3 + 32 · 31 + 23 · 15 = 1,340` per
lane. So the evaluation gate decides how few chunks there can be. With `731` queries per switch
and chunk 0 kept at 2 bits, 56 chunks is the least that fits: 32 chunks of 5 bits and 23 of 4
bits leave a 1.9% margin, while the most even 55-chunk profile (`[2, 5 × 36, 4 × 18]`) would need
`1,071,684` evaluation queries, over the gate. Earlier versions show the same trade: with the
three-block sampler's `2,472` queries per switch the chunks had to stay at 2 bits.

### How the programs are written

The pure definitions recompute oracle values freely. For example, `offsets`, `scaleJoins` and
`evalCoord` rerun a whole fold and re-derive a whole mask vector for each element that reads it.
So they are not query programs. `Construction/OraclePrograms.lean` writes the garbler and the
evaluator in a small free monad (`FreeQuery`) that:

* runs each fold level by level and stores the answers;
* asks each switch's `k` hash limbs once and reads the vector for the offsets, the join and the
  recovery;
* shares the whitening pad with the bit-0 EncPRF pad;
* asks the gadget labels once per digit.

The program then assembles the public value from these answer tables. Two facts make it valid:

* **Exact budget.** A separate predicate, `Bounded program n`, says that every path asks at most
  `n` questions. `toProgram` turns a bounded free program into the library's indexed
  `QueryProgram` at exactly that index.
* **Equal output.** Each table's *real* counterpart, built from the oracle, is the pure
  definition by `rfl`. The theorems `garbleProgram_correct` and `evaluateProgram_correct` show
  that the programs equal the scheme for every complete oracle.

An off-curve input is refused before any query is made.

---

## 5. Perfect correctness

Correctness is exact for every tape, oracle and input, and nothing in it is probabilistic.

* Every wire is an `F_p` element and every gate is `F_p`-linear. So the one-hot fold is an
  identity (`Finset.sum_eq_single`), not an estimate. There is no working modulus and no
  wraparound.
* The switch resolution order depends only on the evaluator's cleartext input.
* An off-curve input returns `some none` before the garbled program is touched; on the curve the
  `Y` row is exact (§2.6).
* The two Jacobian degeneracies go through the exception gadget, whose entry is a deterministic
  function of the tape and the input.

These facts are proved in `Proof/Correctness/` and reach `Solution.perfectCorrectness` through
the Lamport label adapter (`Lamport.restore_selected`).

---

## 6. The privacy argument

### 6.1 What has to be shown

The adversary and the simulator share **one fixed lazy oracle**.

- Every adversary query is answered by that oracle.
- The simulator can only query it, look entries up, and *program* fresh points. A permutation
  program needs a fresh input and a fresh output; a hash program needs only a fresh input. A
  failed program ends the ideal experiment with `false`.
- The simulator is one closed arithmetic machine. Its code size plus both stage fuels must fit
  in `2^60`.
- Its first stage sees only the byte count. Its second stage sees the chosen input `u` and the
  output `f_k(u)`.

The advantage against it must satisfy `Adv · 2^100 ≤ T + 1`, where `T` is the adversary
machine's code size plus its two fuels. Since `T + 1 ≥ q + 2`, a constant term below `2·2^-100`
and a linear term below `2^-100` per query would suffice. The entry is far inside both.

### 6.2 The simulator

**Stage 1 programs nothing and asks nothing.** It publishes a table whose every field is drawn
uniformly in source form:

- the curve and row constants and the gadget bytes;
- the fold joins;
- the `56 × 733` scale joins as canonical field elements, packed exactly as the construction
  packs them.

It also keeps a uniform Lamport key.

The table is right because of one global step. If *every* garbler switch mask vector is replaced
by a uniform vector before the game starts (its limbs then drawn uniformly among those that
sample it), the real table becomes exactly uniform.
- This replacement costs the sampler's bias summed over the garbler's `1,396` vectors per lane:
  `maskSwapError ≤ 1397 · 2^-142 ≈ 2^-131.6`.
- It is non-adaptive: no mask is singled out. That is what lets the published joins be exactly
  uniform *for every way the adversary later chooses its input*.

**Stage 2 opens the rows to `f_k(u)`.**

- *Off the curve*, it returns the selected labels and nothing else. The real evaluator's
  bridge value is then wrong, so every point-lane label is hidden in the real game too.
- *On the curve*, it proceeds as follows.

1. It replays the honest evaluator on the shared oracle:
   - system A;
   - the bridge hash;
   - the 508 whitening pads;
   - system B.
2. It leaves out the 452 designated queries: the hash limbs of the mask vector of lane `pointX`,
   chunk 0, at the inactive switch `j* = α₀ ⊕ 1`.
3. It picks the digit points that the rows must reach:
   - the 90 tail points exactly as the garbler picks its mask points, i.e. the offsets of a
     uniform coin;
   - the head point by the group-law clamp `D₀ = Q − β·H(tail)`, so that Horner's rule returns
     `Q = f_k(u)`;
   - a Jacobian lift of each point with a fresh randomiser.
4. It builds the designated vector `Y* ∈ F_p^455`. Its 182 non-collector coordinates are drawn
   uniformly. Each row has a private collector, an encoding of `x` that no other row reads, and
   the designated switch enters the evaluator's sum with coefficient `±1`. So each of the 273
   collector coordinates is a subtraction; for the `Y` row, whose collector `cubic` is read with
   `x²`, it is also a division by `x²`. That division is always possible: `x ≠ 0` on the curve,
   because `3` is not a square modulo `p`.
5. It draws the 452 limbs uniformly among those that sample `Y*`: `V = enc(Y*) + p^455 · t` with
   `t` uniform below the fibre's size (a bounded rejection loop), and programs each designated
   hash input with its 256-bit limb of `V`.

The programmed switch is inactive, and that is deliberate. The evaluator never queries an
active switch: it recovers the active entry from the join. Programming an active point would
change nothing the adversary computes.

- Flipping the low bit of `α₀` keeps the programmed input on the *visible* fold material.
- Given `Y*`, the limbs are exactly uniform on the sampler's fibre, which is the swapped game's
  law of that vector's limbs. And `Y*` itself has the opening's law.

### 6.3 The chain of games

| hop | change | cost |
|---|---|---|
| `R = G0` | the scored lazy real game equals the tape-sampled real game | 0 (proved) |
| `G0 → G0U` | every garbler switch mask vector becomes uniform on `F_p^n` | `maskSwapError` |
| `G0U → G1U` | the entries the evaluator cannot compute are deleted at the input choice | `3q/2^128 + 2q/(p−1)` |
| `G1U → HW` | public-first: the published cells and visible masks are jointly uniform for every selection rule; the gadget switches from the garbler's entries to uniform bytes; off the curve, the adversary's system-A vectors go from swapped-uniform to sampled from hash answers; a label-coincidence allowance for the designed sub-hop | `4q₁/2^128 + 182/(r−1) + maskSwapError + 2^16/2^128` |
| `HW → H` | the real digit rows are replaced by the tail, clamp and lift sampler | `364/(r−1)` |
| `H → I^U` | the 452 hash programs can abort, charged per stage-1 query at an abort site | `q₁/(2^128 − q₁)` |
| `I^U → I` | the other mask vectors go back to `sampleLane` of lazily queried answers | `maskSwapError` |
| `I → M` | the machine's bounded samplers | `≤ 2^-128` |

Six points in this chain are worth stating.

- **The public-first core.** The published cells and the masks the evaluator can see are
  exactly uniform, jointly, for every input: the garbler's coins map onto them by an explicit
  bijection, one digit at a time, with a residual part the adversary never sees. With the
  four-element `Y` row the randomizer `r4` no longer appears on its own in a published constant,
  so the inverse map reads it back from the published and visible values by dividing by
  `y² − 3`. That is never zero, because `3` is not a square, so the core holds at every input,
  on or off the curve.
- **The abort term.** A hash program needs only a fresh input, and the replay never asks a
  designated input: every other replayed input has another tag, or is `bridgeInput t`, outside the
  switch range. So only the adversary's stage-1 queries can block a program. A hash input names
  its lane, chunk, switch and limb, so each stage-1 query is charged to at most one abort site:
  one of the `4 · 452` candidate designated inputs, one of the `4 · 4` chunk-0 `curveX` limbs (a
  hit there makes the curve lane read the chunk-0 labels), or a level-1 fold index of chunk 0 (the
  fold hit of `E*`). A query at a candidate input blocks the program only if the hidden label `E*`
  equals its label: mass at most `1/(2^128 − q₁)`, the label's min-entropy. There is no output
  part.
- **No refill charge.** Lazily queried hash answers are exactly uniform, so going back from
  swapped vectors to lazily sampled ones costs only the sampler's bias.
- **The doubling case.** If the adversary's input doubles a digit (the digit's point equals its
  mask point), the real rows are `(0,0,0)`, which a lift never produces. The real gadget then
  unlocks the true digit, while the simulator's gadget bytes are uniform. The simulator does not
  reproduce the case. It is charged twice, once in each hop where it makes a difference:
  - `182/(r−1)` in the public-first hop, where the gadget becomes uniform;
  - inside `364/(r−1)`, together with the offset restrictions, in the opening hop, where the rows
    become lifts.
- **The constant part** is `3·maskSwapError + 182/(r−1) + 364/(r−1) + 2^-128 + 2^16/2^128 ≈
  2^-112.0`, dominated by the coincidence allowance of the public-first hop (`12,245` label and
  bridge coincidence events of mass at most `2/2^128` each), and 12 bits under its allowance.
- **The linear part** is 9 units of `q/2^128`, about `2^-124.8` per query.

### 6.4 The machine

The simulator's machine samples 42,052 field cells by bounded rejection and serialises the
table. In stage 2 it replays 988,285 lazy queries, extracting the base-`p` digits of every
replayed mask vector with division-free big-integer arithmetic, and makes 452 hash programs. Its
exact total is `size + 1 + fuels = 56,921,991,801 ≈ 2^35.7`, far inside `2^60`.

The machine reaches `FixedIndex` through `Fintype.equivFin`, and it embeds those ordinals as
constants. Its law, `MachineLaw planBSimulator 2^-128`, is proved: stage 1 and stage 2 of the
machine are the abstract simulator's stages run on bounded samplers, and the samplers' cutoff
mass is below `2^-128`.

---

## 7. Status

Every obligation of `Kriterion.Solution` is proved. These are:

* computable garbling, with query programs at exact budgets and their equality proofs;
* Lamport compatibility;
* perfect correctness;
* function correctness;
* the fixed byte count;
* adaptive privacy.

`#print axioms Submission.solution` reports exactly `propext`, `Classical.choice` and
`Quot.sound`.

`adaptivePrivacy` is the proved top-level assembly. It yields exactly the field's type from
these inputs, all proved:

- the mask swaps;
- the hidden hop;
- the public-first hop `G1U → HW` of §6.3, on top of its exact joint-law core;
- the opening;
- the abort mass;
- the machine law of the closed simulator machine, with its `2^60` cost bound.

Also proved are:

- the exact equality of the scored real game with the tape-sampled one;
- the exact identification of the library's ideal game with the abstract simulator of §6.2;
- the budget arithmetic.

This entry was written with AI coding agents under human direction and review. The
four-element `Y` row is Lazar's (§2.6).
