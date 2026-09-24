/-
**Phase 3, P1q — `LawOn` from the joint law (the assembly of steps C, D and E).**

Step (D) turned the left side of `LawOn` into `onPrivForm` (`lawOn_private`), step (C) the right
side into `onGarbForm` (`lawOn_garbler`), both with **equality**. What remains is step (E), the joint
law of the two forms, stated here as `OnJoint`:

```
OnJoint scalar input := ∀ Ψ lookup-invariant, onPrivForm scalar input Ψ ≤ onGarbForm scalar input Ψ
```

* **`lawOn_of_E`**: on the curve, `OnJoint scalar input → LawOn parameter scalar input`;
* `lawOn_all_of_E`: at every on-curve input, in the shape `DesignedLaws` takes.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnC

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source)
open Kriterion.ArgoMAC.Phase3.Lazy (LState)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
  [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **Step (E), the joint law on the curve**: for every lookup-invariant weight, the private side's
target form is at most the garbler's (P1r's statement to prove). -/
def OnJoint (scalar : NonZeroScalar) (input : AffineInput) : Prop :=
  ∀ Ψ : Public → LamportSignature → LState → ℝ≥0∞,
    (∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second) →
    onPrivForm scalar input Ψ ≤ onGarbForm scalar input Ψ

/-- An on-curve input is valid. -/
theorem validate_of_on (scalar : NonZeroScalar) (input : AffineInput) (target : Point)
    (on : Scheme.scheme.function scalar input = some target) : validate input = true := by
  cases valid : validate input
  · exfalso
    have decoded : decodePoint input = none := by simp [decodePoint, valid]
    have off : Scheme.scheme.function scalar input = none := Option.map_eq_none_iff.mpr decoded
    rw [off] at on
    cases on
  · rfl

/-- **`LawOn` from the joint law**: the assembly of steps (C), (D) and (E). -/
theorem lawOn_of_E (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (valid : validate input = true) (joint : OnJoint scalar input) : LawOn parameter scalar input := by
  intro Ψ invariant
  exact le_trans (le_of_eq (lawOn_private scalar input Ψ invariant)) (le_trans (joint Ψ invariant)
    (le_of_eq (lawOn_garbler parameter scalar input valid Ψ invariant).symm))

/-- **`LawOn` at every on-curve input**, from the joint law at every valid input — the on-curve
conjunct of `DesignedLaws` at fixed certificates and instances. -/
theorem lawOn_all_of_E (parameter : ℕ) (scalar : NonZeroScalar)
    (joint : ∀ input, validate input = true → OnJoint scalar input) :
    ∀ input target, Scheme.scheme.function scalar input = some target → LawOn parameter scalar input :=
  fun input target on =>
    lawOn_of_E parameter scalar input (validate_of_on scalar input target on)
      (joint input (validate_of_on scalar input target on))

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
