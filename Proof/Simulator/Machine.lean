/-
**The Plan B simulator** at the index instances of `Solution.adaptivePrivacy`.

`Construction/Simulator.lean` assembles the machine `Top.machine ordF ordE` for any two ordinal
functions, computably. The privacy proof needs one fixed instance: the ordinals of
`Fintype.equivFin` at the `Fintype.ofFinite` instances that `Solution.adaptivePrivacy` installs,
which is what `queryFromRegisters` decodes. `Fintype.equivFin` is noncomputable, so that instance
is a proof-only definition and lives here rather than in the construction.
-/

import Construction.Simulator

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine

/-- The ordinal of an index under a `Fintype` instance: what `queryFromRegisters` decodes. -/
noncomputable def ordinal (α : Type) [Fintype α] (index : α) : Nat := (Fintype.equivFin α index).val

/-- **The Plan B simulator** at the index instances of `Solution.adaptivePrivacy`
(`Fintype.ofFinite` on both index types). -/
noncomputable def planBSimulator : Simulator :=
  Top.machine (@ordinal FixedIndex (Fintype.ofFinite FixedIndex))
    (@ordinal EncPRF.PermutationIndex (Fintype.ofFinite EncPRF.PermutationIndex))

theorem planBSimulator_within :
    planBSimulator.size + 1 + planBSimulator.firstFuel + planBSimulator.secondFuel ≤ 2 ^ 60 :=
  planBSimulator.within

end Kriterion.ArgoMAC.PlanB.SimMachine
