/-
**Phase 3, P1r — `LawOn`, step (E), part 11: the garbler's side off `Exact0` is the core.**

`onCore`: at uniform clamped offsets `K`, off `Exact0 K`, the average over uniform EncPRF
permutations and hash off the scale range of `coreKEH` (uniform cells, visible masks, `ρ`, key, view
answers, the per-site limb laws of the view's vector sites at the visible masks and F4's designated
solve).
**`realCore_eq`**: the garbler's side after (C), off `Exact0`, is `onCore`.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEPerK

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (input : AffineInput)

open Classical in
/-- **The common core of `LawOn`'s two sides, off `Exact0`.** -/
def onCore (Ψ : Public → LamportSignature → LState → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' K, PMF.uniformOfFintype ClampedOffsets K * if Exact0 scalar input K.1 then 0 else
    ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
      ∑' H, PMF.uniformOfFintype OtherTable H * coreKEH scalar input Ψ K E H

/-- **The garbler's side after (C), off `Exact0`, is the core.** -/
theorem realCore_eq (valid : validate input = true) (Ψ : Public → LamportSignature → LState → ℝ≥0∞) :
    realCore scalar input Ψ = onCore scalar input Ψ := by
  unfold realCore onCore
  simp only [real_view scalar input Ψ]
  rw [tsum_equiv_uniform coinsSplit, tsum_uniform_prod (α := ClampedOffsets) (β := CoinsRest)]
  refine tsum_congr fun K => congrArg _ ?_
  by_cases h : Exact0 scalar input K.1
  · rw [if_pos h]
    refine ENNReal.tsum_eq_zero.mpr fun b => ?_
    rw [if_pos (show Exact0 scalar input (coinsSplit.symm (K, b)).offsets from h), mul_zero]
  · rw [if_neg h, tsum_congr fun b => congrArg _
      (if_neg (show ¬ Exact0 scalar input (coinsSplit.symm (K, b)).offsets from h))]
    rw [tsum_swap_mul]
    refine tsum_congr fun E => congrArg _ ?_
    rw [tsum_swap_mul]
    refine tsum_congr fun H => congrArg _ ?_
    exact real_perK scalar input K h valid Ψ E H

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
