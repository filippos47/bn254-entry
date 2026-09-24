/-
**The Plan B privacy root.**

This module is the proof side's single entry point for `Solution.adaptivePrivacy`. It imports the
three phase-3 trees and the closed simulator machine:

* `Proof.Privacy.Phase3`: the hybrid chain `G0 → G0U → G1U → HW → H` (`planBHybrids`), with the
  mask swap, the hidden hop, the opening bound and the exactness lemmas;
* `Proof.Privacy.Phase3.Glue`: the assembly against the library's
  `GarbledCircuit.OracleAdaptivePrivacy`; its chain-end module `Proof.Privacy.Phase3.Glue.Final`
  ends in `Kriterion.ArgoMAC.Phase3.Glue.planB_oracleAdaptivePrivacy_of`, whose conclusion is
  literally the type of `Solution.adaptivePrivacy`;
* `Proof.Privacy.Phase3.Lazy`: the lazy-oracle refill `I^U → I` and the programming-failure
  (abort) bound `H → I^U`;
* `Proof.Simulator.OpeningMachine`: `Kriterion.ArgoMAC.PlanB.SimMachine.machineLaw_planB`, the
  machine law `MachineLaw planBSimulator 2^-128` of the closed bounded machine `planBSimulator`.

`Submission.solution` sets `adaptivePrivacy := planB_oracleAdaptivePrivacy_of planB_publicFirst
(MachineBound.of_law machineLaw_planB)`. Here
`Kriterion.ArgoMAC.Security.Phase3.PublicFirst.planB_publicFirst` is the hop `G1U → HW`
(`JointExactnessBound.publicFirst` at `planBHybrids`). It is proved in
`Proof/Privacy/Phase3/PublicFirst.lean` (the root of the public-first family) and reached through `Proof.Privacy.Phase3`.
-/

import Proof.Privacy.Phase3
import Proof.Privacy.Phase3.Glue
import Proof.Privacy.Phase3.Glue.Final
import Proof.Privacy.Phase3.Lazy
import Proof.Simulator.OpeningMachine
