/-
**Phase 3, P1h — hop (1), `G0U → G1U`, against the record.**

A chain-end module: it imports `Hybrids` for the record `planBHybrids` (whose other fields are the
public-first, opening and lazy-oracle games) and restates `hidden` (`Hidden/CurveView.lean`) as the
record's field `JointExactnessBound.hidden`:

```
planB_hidden : GameUntilBad planBHybrids.maskSwapped planBHybrids.hiddenDeleted
  fun q₁ q₂ => hiddenPointError (q₁ + q₂)
```

per query exactly `3/2^128 + 2/(p − 1)` (L1's constant), no additive constant: a fixed-key query
pays its input and output hits (`2 · 2^-128`), a hash query the larger of one scale site's label
guess (`2^-128`) and the bridge input's guess (`2/(p − 1)` off the curve, `2/p` in stage 1).
-/

import Proof.Privacy.Phase3.Hidden.CurveView
import Proof.Privacy.Phase3.Hybrids

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

noncomputable section

/-- **Hop (1), `G0U → G1U`**, as `planBHybrids`' field (`JointExactnessBound.hidden`). -/
theorem planB_hidden :
    Kriterion.ArgoMAC.Phase3.Glue.GameUntilBad planBHybrids.maskSwapped planBHybrids.hiddenDeleted
      fun first second => Kriterion.ArgoMAC.Phase3.Glue.hiddenPointError (first + second) :=
  hidden

end

end Kriterion.ArgoMAC.Security.Phase3
