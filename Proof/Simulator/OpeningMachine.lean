/-
**The machine law of the Plan B simulator**, closed.

`openingLaw` (P2e, `OpeningLaw.lean`) is the one premise P2d's assembly left open
(`Stage2Valid.machineLaw_of_opening`); with it, `MachineLaw planBSimulator 2^-128` holds.
-/

import Proof.Simulator.OpeningLaw
import Proof.Simulator.Stage2Valid

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Kriterion.ArgoMAC.Phase3.Glue

/-- **`Stage2Law`**, from the opening law. -/
theorem stage2Law : Stage2Law := stage2Law_of_opening openingLaw

/-- **`MachineLaw planBSimulator 2^-128`**: the library's ideal game with the closed machine is
within `2^-128` of P3's abstract ideal game, against every adversary. -/
theorem machineLaw_planB : MachineLaw planBSimulator machineCutoffError :=
  machineLaw_of_opening openingLaw

end Kriterion.ArgoMAC.PlanB.SimMachine
