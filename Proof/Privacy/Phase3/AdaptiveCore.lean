/-
**Phase 3, P1b — the adaptive core: per-shape exactness is adaptive exactness.**

F4 (`JointExactness.jointLaw`) is a `PMF` equation **for one fixed shape** (input `u`, designated
switch): jointly with the published cells, the designated masks and the bridge key are the
simulator's solve. In the games the adversary chooses `u` *after* seeing the published value (and
its own stage-1 randomness, independent of the hidden vector). `adaptive_of_each` is the step that
turns the per-shape equations into the adaptive one: if for **every** shape `u` the joint law of
(public part, `u`-hidden vector) is the same under two readings `first u`, `second u` of one
randomness law `μ`, then for **every** adaptive choice `choose : P → PMF (U × S)` of the shape (and
a state) from the public part, the joint law of (public part, state, chosen shape with its hidden
vector) is the same. No independence across shapes is used or claimed; only each shape's
conditional law of the hidden vector given the public part enters.

`jointLaw_adaptive` is the instance at F4: with the context fixed, the coins' designated masks and
bridge key can be replaced by the simulator's solve and key **at the adaptively chosen shape**.
-/

import Proof.Privacy.Phase3.JointExactness

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open scoped ENNReal

noncomputable section

/-- The law of (public part, state, chosen shape with its hidden vector) at one point. -/
theorem adaptive_apply {X P S U : Type} {H : U → Type} (μ : PMF X) (pub : X → P)
    (hidden : (u : U) → X → H u) (choose : P → PMF (U × S)) (point : P) (state : S) (u : U)
    (value : H u) :
    (μ.bind fun x => (choose (pub x)).map fun us =>
        (pub x, us.2, (⟨us.1, hidden us.1 x⟩ : Σ u, H u))) (point, state, ⟨u, value⟩)
      = choose point (u, state) * (μ.map fun x => (pub x, hidden u x)) (point, value) := by
  classical
  rw [PMF.bind_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun x => ?_
  rw [PMF.map_apply]
  by_cases hit : pub x = point ∧ hidden u x = value
  · obtain ⟨rfl, rfl⟩ := hit
    rw [tsum_eq_single (u, state)]
    · simp only [if_true]
      rw [mul_comm]
    · intro us different
      rw [if_neg]
      intro same
      apply different
      simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at same
      obtain ⟨-, sameState, sameShape, -⟩ := same
      exact Prod.ext sameShape.symm sameState.symm
  · rw [if_neg (fun same => hit ⟨(Prod.mk.inj same).1.symm, (Prod.mk.inj same).2.symm⟩),
      mul_zero]
    refine mul_eq_zero.mpr (Or.inr (ENNReal.tsum_eq_zero.mpr fun us => ?_))
    rw [if_neg]
    intro same
    simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at same
    obtain ⟨samePoint, -, sameShape, sameValue⟩ := same
    subst sameShape
    exact hit ⟨samePoint.symm, (eq_of_heq sameValue).symm⟩

/-- **Per-shape exactness is adaptive exactness.** -/
theorem adaptive_of_each {X P S U : Type} {H : U → Type} (μ : PMF X) (pub : X → P)
    (first second : (u : U) → X → H u)
    (each : ∀ u, (μ.map fun x => (pub x, first u x)) = μ.map fun x => (pub x, second u x))
    (choose : P → PMF (U × S)) :
    (μ.bind fun x => (choose (pub x)).map fun us =>
        (pub x, us.2, (⟨us.1, first us.1 x⟩ : Σ u, H u)))
      = μ.bind fun x => (choose (pub x)).map fun us =>
        (pub x, us.2, (⟨us.1, second us.1 x⟩ : Σ u, H u)) := by
  refine PMF.ext fun ⟨point, state, u, value⟩ => ?_
  rw [adaptive_apply, adaptive_apply, each u]

/-! ### The instance at F4 -/

section Instance

variable [FieldCertificate] (context : JointContext)

/-- A valid shape. -/
abbrev ValidShape := {shape : JointShape // OnCurve shape.input}

/-- The hidden vector at a shape. -/
abbrev HiddenVector (shape : ValidShape) :=
  VisibleCells shape.1 × (Fin digitCount → Biquadratic.Element → BaseField) × BaseField

/-- The coins' hidden vector at a shape: the visible masks, the designated masks, the bridge key. -/
def coinsHidden (shape : ValidShape) (coins : JointCoins) : HiddenVector shape :=
  (visibleOf shape.1 coins, designatedOf shape.1 coins, bridgeKeyOf coins)

/-- The simulator's hidden vector at a shape: the visible masks, and the solve and key computed from
the published and visible cells. -/
def solvedHidden (shape : ValidShape) (coins : JointCoins) : HiddenVector shape :=
  (visibleOf shape.1 coins,
    simulatorDesignated shape.1 context (publicOf context coins, visibleOf shape.1 coins),
    simulatorKey shape.1 (publicOf context coins, visibleOf shape.1 coins))

/-- Regroup F4's output as (published, hidden vector). -/
def regroupHidden {V D : Type} (result : (PublicCells × V) × D × BaseField) :
    PublicCells × (V × D × BaseField) :=
  (result.1.1, (result.1.2, result.2.1, result.2.2))

/-- F4 at one shape, in the form `adaptive_of_each` reads. -/
theorem jointLaw_each (shape : ValidShape) :
    ((PMF.uniformOfFintype JointCoins).map fun coins =>
        (publicOf context coins, coinsHidden shape coins))
      = (PMF.uniformOfFintype JointCoins).map fun coins =>
        (publicOf context coins, solvedHidden context shape coins) := by
  have law := jointLaw shape.1 context shape.2
  rw [← jointExactness shape.1 context, PMF.map_comp] at law
  have mapped := congrArg (PMF.map regroupHidden) law
  rw [PMF.map_comp, PMF.map_comp] at mapped
  exact mapped

/-- **F4, adaptively**: for any choice of a valid shape (and a state) from the published cells, the
coins' visible masks, designated masks and bridge key, read at the chosen shape, have jointly with
the published cells the law of the visible masks with the simulator's solve and key. -/
theorem jointLaw_adaptive {S : Type} (choose : PublicCells → PMF (ValidShape × S)) :
    ((PMF.uniformOfFintype JointCoins).bind fun coins =>
        (choose (publicOf context coins)).map fun (choice : ValidShape × S) =>
          (publicOf context coins, choice.2,
            Sigma.mk (β := HiddenVector) choice.1 (coinsHidden choice.1 coins)))
      = (PMF.uniformOfFintype JointCoins).bind fun coins =>
        (choose (publicOf context coins)).map fun (choice : ValidShape × S) =>
          (publicOf context coins, choice.2,
            Sigma.mk (β := HiddenVector) choice.1 (solvedHidden context choice.1 coins)) :=
  by
  apply adaptive_of_each
  exact jointLaw_each context

end Instance

end

end Kriterion.ArgoMAC.Security.Phase3
