/-
This file defines the Plan B `bin-to-hot` switch system: the fold that turns the bit labels of
one chunk into a one-hot label vector, and the evaluator's mirror of it.

The plan source is `2026-09-17-planB.md`, section D.2; the label
mechanics are the ones the internal Python reference (`pgs.py`) executes, which preserve
the free-XOR invariant `E_t = Z_t ^^^ h_t * delta` at every level:

```
M_r         := pi_{hot(c,j,r,0)}(Z_r) ^^^ pi_{hot(c,j,r,1)}(Z_r)     two hashes per entry
Z_(r+2^j)   := M_r                                 right child = x_j * h_r
Z_r         := Z_r ^^^ M_r                         left  child = (1 - x_j) * h_r  (free XOR)
join_j      := (^^^_r M_r) ^^^ Lzero_j             one published block per step
```

**Task 34a (the two-image step).** The step material used to be the Davies--Meyer value
`H(idx, Z) = pi(Z) ^^^ Z` of a *single* permutation. The free-XOR left child `Z ^^^ H(idx, Z)`
then cancelled the feed-forward and was the raw image `pi(Z)`; whenever the fold bit was set
that left child was the *inactive* one, so the evaluator held `pi(Z)` in the clear for the
hidden `Z`, and one `fixedInverse` query at `idx` returned `Z` and hence `Delta`
(internal review note `planB-hop1-review.md`, Sec. 1.2). The repair names **two** permutations
per gate and takes their sum:
`M_r = pi_{i0}(Z_r) ^^^ pi_{i1}(Z_r)`. Because `hash` is Davies--Meyer the two feed-forwards
cancel *each other*, so `M_r` is exactly `hash i0 Z_r ^^^ hash i1 Z_r` and neither `M_r` (the
right child) nor `Z_r ^^^ M_r` (the left child) is a single permutation image. The published
join, the level layout, the evaluator's recovery and the ciphertext bytes are untouched; only
the number of fold hashes doubles.

Level `0` is the public constant-`1` wire (`Z = delta`, `E = 0`). Step `j = 0` takes
`M_0 := Lzero_0` by fiat, so `join_0 = 0` and the step is free; the level-1 masks are then the
bit label and its complement. The evaluator mirrors the fold and, for the active parent `a`
(the low `j` bits of its cleartext chunk value), recovers the right child from the join:
`E_(a+2^j) := join_j ^^^ E(x_j) ^^^ (^^^_(r != a) U_r)` with `U_r := H(hot(c,j,r), E_r)`; the
left child is again a free XOR. A naive "hash and XOR a per-step join" fold does *not*
preserve the invariant.
-/

import Construction.PGS.Sampler

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-- The cleartext one-hot of a chunk value. -/
def binToHot (width : Nat) (value : BitVec width) : Fin (2 ^ width) → Bool :=
  fun entry => decide (entry.val = value.toNat)

/-- The one-hot label vector of a chunk of the given width. -/
abbrev HotLabels (width : Nat) := Fin (2 ^ width) → Block

/-- The fixed-key index of one half of one `bin-to-hot` fold gate. Each gate names two
independent permutations, `half = false` and `half = true`. -/
def hotIndex (lane : Lane) (chunk : Fin chunkCount) (fold : Fin chunkBits)
    (entry : Fin (2 ^ chunkBits)) (half : Bool) : FixedIndex :=
  .hot lane chunk fold entry half

/-- The XOR of a finite family of blocks. -/
def xorFold {count : Nat} (family : Fin count → Block) : Block :=
  Fin.foldl count (fun acc entry => acc ^^^ family entry) 0

/-- The XOR of a finite family of blocks with one entry skipped. -/
def xorFoldExcept {count : Nat} (skip : Fin count) (family : Fin count → Block) : Block :=
  Fin.foldl count (fun acc entry => if entry = skip then acc else acc ^^^ family entry) 0

/-- Extend one level of the fold.

The right child of entry `r` is the step material `right r`, and the left child is the free
XOR `parent r ^^^ right r`. Entries `0 .. 2 ^ step - 1` of the new level are the left
children, entries `2 ^ step .. 2 ^ (step + 1) - 1` the right children, which is the
little-endian one-hot order `h[r + 2 ^ j] = x_j * h[r]`. -/
def extendLevel (step : Nat) (parent right : Fin (2 ^ step) → Block) :
    Fin (2 ^ (step + 1)) → Block := fun entry =>
  if below : entry.val < 2 ^ step then
    parent ⟨entry.val, below⟩ ^^^ right ⟨entry.val, below⟩
  else
    right ⟨entry.val - 2 ^ step, by
      have expand : (2 : Nat) ^ (step + 1) = 2 ^ step + 2 ^ step := by
        rw [pow_succ]; omega
      have bound := entry.isLt
      omega⟩

/-- **The repaired fold-step material of one gate**: the sum of the permutation images at the
gate's two fixed-key indices, `pi_{i0}(label) ^^^ pi_{i1}(label)`.

It is written as a sum of two `hash` (Davies--Meyer) calls, which is the same block: the two
feed-forward copies of `label` cancel each other (`foldMask_eq_perm`). That is the whole point
of the repair -- the material carries **no** copy of its own input, so the free-XOR left child
`label ^^^ foldMask` is not a permutation image either. -/
def foldMask (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (step entry : Nat) (label : Block) : Block :=
  hash oracle (hotIndexNat lane chunk step entry false) label
    ^^^ hash oracle (hotIndexNat lane chunk step entry true) label

/-- **The step material is a sum of two raw permutation images.** The Davies--Meyer
feed-forwards of the two halves cancel, so `foldMask` is `pi_{i0}(label) ^^^ pi_{i1}(label)`. -/
theorem foldMask_eq_perm (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (step entry : Nat) (label : Block) :
    foldMask oracle lane chunk step entry label
      = oracle.permutation (hotIndexNat lane chunk step entry false) label
        ^^^ oracle.permutation (hotIndexNat lane chunk step entry true) label := by
  show (oracle.permutation _ label ^^^ label) ^^^ (oracle.permutation _ label ^^^ label) = _
  generalize oracle.permutation (hotIndexNat lane chunk step entry false) label = first
  generalize oracle.permutation (hotIndexNat lane chunk step entry true) label = second
  refine BitVec.eq_of_getLsbD_eq fun index _ => ?_
  simp only [BitVec.getLsbD_xor]
  cases first.getLsbD index <;> cases second.getLsbD index <;> cases label.getLsbD index <;> rfl

/-- The garbler's step material `M_r`. Step `0` takes the bit's zero label by fiat, which is
what makes it free. -/
def garbleStep (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (step : Nat) (zeroLabel : Block)
    (parent : Fin (2 ^ step) → Block) : Fin (2 ^ step) → Block := fun entry =>
  if step = 0 then zeroLabel
  else foldMask oracle lane chunk step entry.val (parent entry)

/-- The published join of one fold step: `(^^^_r M_r) ^^^ Lzero_j`.

This is the switch-system join `sum_r y_(r + 2^j) = x_j`: its right-hand side is a wire, so the
published material is `sum (output masks) - (input mask)`. At step `0` it is `0`. -/
def stepJoin (step : Nat) (zeroLabel : Block) (right : Fin (2 ^ step) → Block) : Block :=
  xorFold right ^^^ zeroLabel

/-- The evaluator's step material. At the active parent the right child is recovered from the
published join; everywhere else it is the hash of the held label. -/
def evalStep (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (step : Nat) (bitLabel join : Block)
    (active : Fin (2 ^ step)) (parent : Fin (2 ^ step) → Block) :
    Fin (2 ^ step) → Block := fun entry =>
  if entry = active then
    join ^^^ bitLabel ^^^
      xorFoldExcept active fun other =>
        foldMask oracle lane chunk step other.val (parent other)
  else foldMask oracle lane chunk step entry.val (parent entry)

/-- The active parent at step `j`: the low `j` bits of the cleartext chunk value. -/
def activeAt (value step : Nat) : Fin (2 ^ step) :=
  ⟨value % 2 ^ step, Nat.mod_lt _ (Nat.two_pow_pos step)⟩

/-- A `Fin`-indexed label family read as a total function of a natural number. -/
def labelAt {width : Nat} (labels : Fin width → Block) (step : Nat) : Block :=
  if inRange : step < width then labels ⟨step, inRange⟩ else 0

/-- The published join of step `step`, read out of the `width - 1` published blocks.
Step `0` is free, so its join is `0` and it occupies no slot. -/
def joinAt {width : Nat} (joins : Vector Block (width - 1)) (step : Nat) : Block :=
  if step = 0 then 0
  else if inRange : step - 1 < width - 1 then joins.get ⟨step - 1, inRange⟩ else 0

/-- The garbler's fold, carrying the level masks and every step's join. -/
def garbleFold (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (delta : Block) (zeroLabel : Nat → Block) :
    (steps : Nat) → (Fin (2 ^ steps) → Block) × (Nat → Block)
  | 0 => (fun _ => delta, fun _ => 0)
  | steps + 1 =>
    let previous := garbleFold oracle lane chunk delta zeroLabel steps
    let right := garbleStep oracle lane chunk steps (zeroLabel steps) previous.1
    (extendLevel steps previous.1 right,
      fun step => if step = steps then stepJoin steps (zeroLabel steps) right else previous.2 step)

/-- The evaluator's fold, carrying the held labels. -/
def evalFold (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (value : Nat) (bitLabel join : Nat → Block) :
    (steps : Nat) → Fin (2 ^ steps) → Block
  | 0 => fun _ => 0
  | steps + 1 =>
    let previous := evalFold oracle lane chunk value bitLabel join steps
    let right :=
      evalStep oracle lane chunk steps (bitLabel steps) (join steps) (activeAt value steps)
        previous
    extendLevel steps previous right

/-- **`bin-to-hot`, garbler side.** From the chunk's `width` zero labels and the global
correlation `delta`, produce the one-hot label vector and the `width - 1` published join
blocks (step `0` is free, so it publishes nothing).

The flat layout of a coordinate's `Vector Block foldStepCount` puts this vector at offset
`foldBase chunk`. -/
def garbleHot (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (width : Nat) (delta : Block) (bitLabels : Fin width → Block) :
    HotLabels width × Vector Block (width - 1) :=
  let folded := garbleFold oracle lane chunk delta (labelAt bitLabels) width
  (folded.1, Vector.ofFn fun slot : Fin (width - 1) => folded.2 (slot.val + 1))

/-- **`bin-to-hot`, evaluator side.** From the held bit labels, the published joins and the
cleartext chunk value, reconstruct the one-hot label vector. -/
def evalHot (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (width : Nat) (joins : Vector Block (width - 1))
    (bitLabels : Fin width → Block) (value : BitVec width) : HotLabels width :=
  evalFold oracle lane chunk value.toNat (labelAt bitLabels) (joinAt joins) width

/-- The evaluator's held bit labels: the garbler's zero label of bit `j`, complemented by
`delta` when the bit is set. -/
def selectBits {width : Nat} (bitKey : Fin width → Block × Block) (value : BitVec width) :
    Fin width → Block :=
  fun position => if value[position] then (bitKey position).2 else (bitKey position).1

end Kriterion.ArgoMAC.PlanB
