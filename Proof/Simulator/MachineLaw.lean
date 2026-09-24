/-
**P3's `MachineLaw` for the Plan B machine, from the one open premise.**

`samplerCutoff` (`CutoffMass`) and `stage1Law` (`Stage1Law`) are proved; `machineLaw_of_stage2`
closes `MachineLaw planBSimulator machineCutoffError` from `Stage2Law` alone.
-/

import Proof.Simulator.CutoffMass
import Proof.Simulator.Stage1Law

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Kriterion.ArgoMAC.Phase3.Glue

/-- **The machine law, from the stage-2 law.** -/
theorem machineLaw_of_stage2 (stage2 : Stage2Law) :
    MachineLaw planBSimulator machineCutoffError :=
  machineLaw_of stage1Law stage2 samplerCutoff

end Kriterion.ArgoMAC.PlanB.SimMachine
