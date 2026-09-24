/-
This file defines the Plan B fixed-key hash.

Rule S: every `F_p` sampler is a total function of hash output bits, reduced -- never rejected.
`PerfectCorrectness` quantifies over every tape, and a rejection loop is tape-dependent.
The plan source is `2026-09-17-planB.md`, section D.3 and Rule S.

The `scale-hot` switch masks are drawn by the batched hash-vector sampler `sampleLane` of
`Construction/PGS/BatchSampler.lean` (one vector per (lane, chunk, switch), the base-`p` digits
of `k` hash answers, reduced), which is the only field sampler. The fixed-key `hash` below
serves the `bin-to-hot` fold.
-/

import Construction.PGS.Index

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-- The Plan B hash: Davies--Meyer at the permutation the index names.

No tweak is applied. The index already names the gate uniquely, which is what makes
"one construction query per `FixedIndex`" hold. -/
def hash (oracle : PermutationOracle FixedIndex Block) (index : FixedIndex)
    (label : Block) : Block :=
  daviesMeyer (oracle.permutation index) label

/-- The modulus fits in 254 bits. -/
theorem baseFieldModulus_lt : baseFieldModulus < 2 ^ 254 := by
  unfold baseFieldModulus
  norm_num

end Kriterion.ArgoMAC.PlanB
