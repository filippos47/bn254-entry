/-
**Phase 3, P1b — the `Hybrids` data.**

`Glue.Hybrids` (`Glue/Assembly.lean`) is five `HybridGame`s. This module supplies all five:

| field | game | defined in |
|---|---|---|
| `maskSwapped` (`G0U`) | `maskSwappedHybrid` | `GameSwap.lean` (P1) |
| `hiddenDeleted` (`G1U`) | `hiddenDeletedHybrid` | `Hidden/Deleted.lean` |
| `publicFirst` (`HW`) | `publicFirstHybrid` | `Opened.lean` |
| `opened` (`H`) | `openedHybrid` | `Opened.lean` |
| `idealUniform` (`I^U`) | `Lazy.idealUniformHybrid` | `Lazy/Refill.lean` (P4) |

`G1U` (hidden-entry deletion at the input choice) and its transcripts live in `Hidden/Deleted.lean`,
so that hop (1) (`Hidden/*`) builds on `G0U` alone.
-/

import Proof.Privacy.Phase3.OpeningBound
import Proof.Privacy.Phase3.Lazy.IdealPerMask
import Proof.Privacy.Phase3.Hidden.Deleted

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB

noncomputable section

/-! ### The record -/

/-- **P1's proof-only hybrids** (`Glue.Hybrids`): `G0U`, `G1U`, `HW`, `H`, `I^U`. -/
def planBHybrids : Kriterion.ArgoMAC.Phase3.Glue.Hybrids where
  maskSwapped := maskSwappedHybrid
  hiddenDeleted := hiddenDeletedHybrid
  publicFirst := publicFirstHybrid
  opened := openedHybrid
  idealUniform := Kriterion.ArgoMAC.Phase3.Lazy.idealUniformHybrid

/-- `H_swap.real` against the record (P1's `maskSwapBound_real`). -/
theorem planB_maskSwap_real :
    Kriterion.ArgoMAC.Phase3.Glue.HopBound Kriterion.ArgoMAC.Phase3.Glue.realHybrid
      planBHybrids.maskSwapped fun _ _ => Kriterion.ArgoMAC.Phase3.Glue.maskSwapError :=
  maskSwapBound_real

/-- **`H_swap`, whole**, against the record: P1's `G0 → G0U` and P4's lazy refill
(`Lazy.maskSwapBound_of`). -/
theorem planB_maskSwapBound : Kriterion.ArgoMAC.Phase3.Glue.MaskSwapBound planBHybrids :=
  Kriterion.ArgoMAC.Phase3.Lazy.maskSwapBound_of planBHybrids rfl rfl

/-- **`H_open`** against the record: `HW → H` at `outputKernelError = 364/(r−1)`. -/
theorem planB_openingBound : Kriterion.ArgoMAC.Phase3.Glue.OpeningBound planBHybrids :=
  ⟨openingBound_kernel⟩

end

end Kriterion.ArgoMAC.Security.Phase3
