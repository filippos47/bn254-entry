/-
**Phase 3, P4 — from the stage-2 kernels to the abstract ideal game.**

`abstractIdealGame_stage2_etvDist_le`: two abstract simulators with the same stage 1 whose stage-2
kernels are within `bound oracle` at every oracle state give games within the **average** of
`bound` over the oracle state the adversary's stage 1 leaves -- the expectation over the shared
prefix (the simulator's stage 1, then the adversary's first stage on the lazy oracle), the
stage-2 difference (data processing through the common continuation: the adversary's second
stage and its bit).
-/

import Proof.Privacy.Phase3.Lazy.RunBound

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.Phase3 (etvDist_bind_left_le etvDist_map_le')
open scoped ENNReal

noncomputable section

/-! ### `OptionT PMF` binds -/

/-- The run of a bind out of an abort-or-value kernel. -/
theorem optionT_run_bind_mk {α β : Type} (distribution : PMF (Option α))
    (next : α → OptionT PMF β) :
    (OptionT.mk distribution >>= next).run =
      distribution.bind fun option => match option with
        | some value => (next value).run
        | none => PMF.pure none := rfl

/-- A shared abort-or-value first draw: the average distance of the continuations over its values. -/
theorem optionT_bind_etvDist_le {α β : Type} (distribution : PMF (Option α))
    (first second : α → OptionT PMF β) :
    ((OptionT.mk distribution >>= first).run).etvDist ((OptionT.mk distribution >>= second).run) ≤
      ∑' value, distribution (some value) * ((first value).run.etvDist (second value).run) := by
  rw [optionT_run_bind_mk, optionT_run_bind_mk]
  refine le_trans (etvDist_bind_left_le _ _ _) (le_of_eq ?_)
  have noneTerm : ∀ option : Option α,
      ((match option with
          | some value => (first value).run
          | none => PMF.pure none : PMF (Option β)).etvDist
        (match option with
          | some value => (second value).run
          | none => PMF.pure none) * distribution option) =
      (match option with
        | some value => distribution (some value) * ((first value).run.etvDist (second value).run)
        | none => 0) := by
    intro option
    cases option with
    | none => simp
    | some value => exact mul_comm _ _
  simp only [noneTerm]
  refine (Function.Injective.tsum_eq (Option.some_injective α) ?_).symm
  intro option member
  cases option with
  | none => exact absurd rfl member
  | some value => exact ⟨value, rfl⟩

/-- A lifted first draw: the average distance of the continuations. -/
theorem optionT_lift_bind_etvDist_le {α β : Type} (distribution : PMF α)
    (first second : α → OptionT PMF β) :
    ((liftM distribution >>= first : OptionT PMF β).run).etvDist
        ((liftM distribution >>= second : OptionT PMF β).run) ≤
      ∑' value, distribution value * ((first value).run.etvDist (second value).run) := by
  have lifted : ∀ next : α → OptionT PMF β, (liftM distribution >>= next : OptionT PMF β).run =
      distribution.bind fun value => (next value).run := by
    intro next
    show (distribution.bind fun value => PMF.pure (some value)).bind (fun option =>
      match option with
        | some value => (next value).run
        | none => PMF.pure none) = _
    rw [PMF.bind_bind]
    simp only [PMF.pure_bind]
  rw [lifted, lifted]
  refine le_trans (etvDist_bind_left_le _ _ _) (le_of_eq ?_)
  exact tsum_congr fun value => mul_comm _ _

/-- Two abort-or-value first draws with a common continuation: data processing. -/
theorem optionT_bind_mk_etvDist_le {α β : Type} (first second : PMF (Option α))
    (next : α → OptionT PMF β) :
    ((OptionT.mk first >>= next).run).etvDist ((OptionT.mk second >>= next).run) ≤
      first.etvDist second := by
  rw [optionT_run_bind_mk, optionT_run_bind_mk]
  exact PMF.etvDist_bind_right_le _ _ _

/-! ### The abstract ideal game -/

/-- **Swapping stage 2 of an abstract simulator.** If the new stage-2 kernel is within
`bound oracle` of the old one at every oracle state, the two abstract ideal games are within the
average of `bound` over the oracle state left by the adversary's first stage. -/
theorem abstractIdealGame_stage2_etvDist_le [FieldCertificate]
    {FixedIndex EncIndex Randomness Public Key Oracle Aux : Type}
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      Key LamportSignature Oracle)
    (simulator : LazyAbstractSimulator FixedIndex EncIndex Public)
    (stage2 : simulator.State → AffineInput → Option Point →
      LazyOracle.State FixedIndex EncIndex →
        PMF (Option (LamportSignature × LazyOracle.State FixedIndex EncIndex)))
    (bound : LazyOracle.State FixedIndex EncIndex → ℝ≥0∞)
    (close : ∀ state input output oracle,
      (stage2 state input output oracle).etvDist (simulator.stage2 state input output oracle) ≤
        bound oracle)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedIndex EncIndex)
      AffineInput Public LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    (abstractIdealGame scheme { simulator with stage2 := stage2 } adversary parameter scalar
        auxiliary).etvDist
      (abstractIdealGame scheme simulator adversary parameter scalar auxiliary) ≤
      ∑' first, simulator.stage1 parameter LazyOracle.empty (some first) *
        ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter first.1 auxiliary)
          first.2.2) chosen * bound chosen.2 := by
  unfold abstractIdealGame
  refine le_trans (etvDist_map_le' _ _ _) ?_
  refine le_trans (optionT_bind_etvDist_le _ _ _) ?_
  refine ENNReal.tsum_le_tsum fun first => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  obtain ⟨circuit, state, oracle⟩ := first
  refine le_trans (optionT_lift_bind_etvDist_le _ _ _) ?_
  refine ENNReal.tsum_le_tsum fun chosen => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  obtain ⟨selected, chosen⟩ := chosen
  refine le_trans (optionT_bind_mk_etvDist_le _ _ _) ?_
  exact close _ _ _ _

end

end Kriterion.ArgoMAC.Phase3.Lazy
