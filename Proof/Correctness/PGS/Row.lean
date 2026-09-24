/-
This file discharges the projectivized garbling scheme's delivery hypothesis (plan
`2026-09-17-planB.md`, Task 20, step 2).

`Construction` may not import `Proof`, so `Construction/ArgoMAC/Pipeline.lean` states the fact
that the switch systems deliver `slope * coordinate + offset` as a named `Prop`,
`Pipeline.Delivers`, whose statement is character for character `evalCoord_garbleCoord`. Here
it is supplied, for every tape and every one of the four lanes at once. With it,
`Pipeline.evaluateEncoded` and `Garbling.evaluateEncodeRows` become unconditional: the 733
values the evaluator obtains are exactly the `a_e * coord + K e` the row layer expects.
-/

import Construction.Garbling
import Proof.Correctness.PGS.AffineFp

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-- **The delivery hypothesis, discharged.** For every fixed-key oracle, every hash oracle,
every lane, every free-XOR label family and every slope vector, the evaluator's fold of that
lane's switch system returns the element's slope times the coordinate, offset by the garbler's
own output mask `O[e]`. -/
theorem delivers (oracle : PermutationOracle FixedIndex Block) (hashOracle : EncPRF.HashOracle) :
    Pipeline.Delivers oracle hashOracle := by
  intro lane delta bitKey correlated slopes value element
  exact evalCoord_garbleCoord oracle hashOracle lane delta bitKey correlated slopes value element

end Kriterion.ArgoMAC.PlanB
