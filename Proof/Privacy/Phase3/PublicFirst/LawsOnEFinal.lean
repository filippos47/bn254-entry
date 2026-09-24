/-
**Phase 3, P1s — `LawOn` and `DesignedLaws`, real.**

* **`lawOn_all`**: `LawOn` at every on-curve input, at any instances — P1q's `lawOn_all_of_E` from
  step (E) (`OnE.onJoint`);
* **`designedLaws`**: `DesignedLaws` — P1n's `lawOff_all` off the curve, `lawOn_all` on it.

The Glue's field `planB_publicFirst` is stated in the root `PublicFirst.lean` (§5) from
`designedLaws`.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEPrivForm
import Proof.Privacy.Phase3.PublicFirst.LawsOff

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB

/-- **`LawOn` at every on-curve input**, at any instances: step (E) at every valid input. -/
theorem lawOn_all [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
    [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (parameter : ℕ) (scalar : NonZeroScalar) :
    ∀ input target, Scheme.scheme.function scalar input = some target → LawOn parameter scalar input :=
  OnLaw.lawOn_all_of_E parameter scalar fun input valid => OnE.onJoint scalar input valid

/-- **`DesignedLaws`, real**: `LawOff` off the curve, `LawOn` on it, at every input. -/
theorem designedLaws : DesignedLaws := by
  intro field group parameter scalar
  let := field
  let := group
  let : Fintype FixedIndex := Fintype.ofFinite FixedIndex
  let : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
  let : DecidableEq FixedIndex := Classical.decEq FixedIndex
  let : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
  refine ⟨fun input off => ?_, lawOn_all parameter scalar⟩
  have global := lawOff_all parameter scalar input off
  convert global using 1

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
