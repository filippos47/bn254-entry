/-
This test re-runs the M0 elaboration spike at the real Plan B index type.
It is not shipped: the verifier copies only `Construction*`, `Proof*` and `Submission`.

Run with `lake env lean tests/PGSIndex.lean`.
-/

import Construction.PGS.Index

namespace Kriterion.ArgoMAC.PlanB

open Cryptography

/-- The permutation-oracle family over the real index elaborates without enumeration. -/
noncomputable example : Fintype (PermutationOracle FixedIndex Block) := inferInstance

/-- Its uniform distribution elaborates without enumeration. -/
noncomputable example : PMF (PermutationOracle FixedIndex Block) := PMF.uniformOfFintype _

/-- The cardinality is the product/sum count, never an enumeration. -/
example : Fintype.card FixedIndex = 117908 := card_fixedIndex

end Kriterion.ArgoMAC.PlanB
