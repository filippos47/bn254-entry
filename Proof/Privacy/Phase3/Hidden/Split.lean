/-
**Phase 3, P1h — generic: the swap kernel splits over any set of vector sites.**

For a predicate `p` on the vector sites, the limb values split into those of the sites off `p` and
on `p` (`splitSlots`), the vectors likewise (`splitVectors`), and `masksOf` respects the split
(`masksOf_split`). Given the vectors, the limbs are uniform on the vectors' fibre, and that fibre is
the product of the two sub-fibres, so the fibre law is the product of the two sub-fibre laws
(`fibreLaw_masksOf_split`, from `fibreLaw_map_equiv'` and `fibreLaw_prod`). Under the swap kernel,
therefore, the limb values of the sites off `p` and the vectors of the sites on `p` are independent:
the former have the swapped law of their own sites (`swapLimbLaw`), the latter are uniform
(`swapKernel_split_law`) — whatever the points.
-/

import Proof.Privacy.Phase3.MaskSwap
import Proof.Privacy.Phase3.Hidden.Resample

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv)
open scoped ENNReal

noncomputable section

/-! ### Fibre laws -/

/-- **A fibre law moves along equivalences.** -/
theorem fibreLaw_map_equiv' {A A' B B' : Type} [Fintype A] [Fintype A'] [DecidableEq B] [DecidableEq B']
    (g : A → B) (g' : A' → B') (onto : Function.Surjective g) (onto' : Function.Surjective g')
    (eA : A ≃ A') (eB : B ≃ B') (compat : ∀ a, g' (eA a) = eB (g a)) (b : B) :
    (fibreLaw g onto b).map eA = fibreLaw g' onto' (eB b) := by
  classical
  have cards : Fintype.card {y : A // g y = b} = Fintype.card {y : A' // g' y = eB b} :=
    Fintype.card_congr
      { toFun := fun y => ⟨eA y.1, by rw [compat, y.2]⟩
        invFun := fun y => ⟨eA.symm y.1, by
          apply eB.injective
          rw [← compat, Equiv.apply_symm_apply]
          exact y.2⟩
        left_inv := fun y => Subtype.ext (eA.symm_apply_apply y.1)
        right_inv := fun y => Subtype.ext (eA.apply_symm_apply y.1) }
  refine PMF.ext fun x => ?_
  rw [PMF.map_apply, tsum_eq_single (eA.symm x)]
  · rw [if_pos (eA.apply_symm_apply x).symm, fibreLaw_apply, fibreLaw_apply, cards]
    have iff : g (eA.symm x) = b ↔ g' x = eB b := by
      constructor
      · intro h
        rw [← Equiv.apply_symm_apply eA x, compat, h]
      · intro h
        apply eB.injective
        rw [← compat, Equiv.apply_symm_apply]
        exact h
    by_cases h : g' x = eB b
    · rw [if_pos (iff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (iff.mp h')), if_neg h]
  · intro other miss
    rw [if_neg (fun same => miss (by rw [same, Equiv.symm_apply_apply]))]

/-- **The fibre law of a product map is the product of the fibre laws.** -/
theorem fibreLaw_prod {A₁ A₂ B₁ B₂ : Type} [Fintype A₁] [Fintype A₂] [DecidableEq B₁] [DecidableEq B₂]
    (g₁ : A₁ → B₁) (g₂ : A₂ → B₂) (onto₁ : Function.Surjective g₁) (onto₂ : Function.Surjective g₂)
    (onto : Function.Surjective (Prod.map g₁ g₂)) (b₁ : B₁) (b₂ : B₂) :
    fibreLaw (Prod.map g₁ g₂) onto (b₁, b₂) = productPMF (fibreLaw g₁ onto₁ b₁) (fibreLaw g₂ onto₂ b₂) := by
  classical
  have cards : Fintype.card {y : A₁ × A₂ // Prod.map g₁ g₂ y = (b₁, b₂)} =
      Fintype.card {y : A₁ // g₁ y = b₁} * Fintype.card {y : A₂ // g₂ y = b₂} := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr
      { toFun := fun y => (⟨y.1.1, (Prod.mk.inj y.2).1⟩, ⟨y.1.2, (Prod.mk.inj y.2).2⟩)
        invFun := fun y => ⟨(y.1.1, y.2.1), by rw [Prod.map_apply, y.1.2, y.2.2]⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
  refine PMF.ext fun x => ?_
  obtain ⟨x₁, x₂⟩ := x
  rw [productPMF_apply, fibreLaw_apply, fibreLaw_apply, fibreLaw_apply, cards]
  simp only [Prod.map_apply, Prod.mk.injEq]
  by_cases h₁ : g₁ x₁ = b₁ <;> by_cases h₂ : g₂ x₂ = b₂ <;>
    simp only [h₁, h₂, and_self, and_false, false_and, if_true, if_false, mul_zero, zero_mul]
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

/-- Independent binds. -/
theorem productPMF_bind {A₁ A₂ B₁ B₂ : Type} (μ₁ : PMF B₁) (μ₂ : PMF B₂) (κ₁ : B₁ → PMF A₁)
    (κ₂ : B₂ → PMF A₂) :
    (productPMF μ₁ μ₂).bind (fun b => productPMF (κ₁ b.1) (κ₂ b.2)) =
      productPMF (μ₁.bind κ₁) (μ₂.bind κ₂) := by
  unfold productPMF
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.map_bind]
  refine congrArg (PMF.bind μ₁) (funext fun b₁ => ?_)
  rw [PMF.bind_comm]

/-! ### Splitting the vector sites -/

section Split

variable {V : Type} [Fintype V] [DecidableEq V] (laneOf : V → Lane) (p : V → Prop) [DecidablePred p]

/-- The lane of a site off `p`. -/
abbrev offLane : {v : V // ¬ p v} → Lane := fun v => laneOf v.1

/-- The lane of a site on `p`. -/
abbrev onLane : {v : V // p v} → Lane := fun v => laneOf v.1

/-- **The limb values, split** into those of the sites off `p` and on `p`. -/
def splitSlots : (LimbSlot laneOf → Block × Block) ≃
    (LimbSlot (offLane laneOf p) → Block × Block) × (LimbSlot (onLane laneOf p) → Block × Block)
        where
  toFun f := (fun s => f ⟨s.1.1, s.2⟩, fun s => f ⟨s.1.1, s.2⟩)
  invFun g := fun s => if h : p s.1 then g.2 ⟨⟨s.1, h⟩, s.2⟩ else g.1 ⟨⟨s.1, h⟩, s.2⟩
  left_inv f := funext fun s => by by_cases h : p s.1 <;> simp [h]
  right_inv g := by
    refine Prod.ext (funext fun s => ?_) (funext fun s => ?_)
    · simp [s.1.2]
    · simp [s.1.2]

/-- **The vectors, split.** -/
def splitVectors : LaneVectors laneOf ≃ LaneVectors (offLane laneOf p) × LaneVectors (onLane laneOf
    p) where
  toFun f := (fun v => f v.1, fun v => f v.1)
  invFun g := fun v => if h : p v then g.2 ⟨v, h⟩ else g.1 ⟨v, h⟩
  left_inv f := funext fun v => by by_cases h : p v <;> simp [h]
  right_inv g := by
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
    · simp [v.2]
    · simp [v.2]

/-- The batched sampler respects the split. -/
theorem masksOf_split (values : LimbSlot laneOf → Block × Block) :
    splitVectors laneOf p (masksOf laneOf values) =
      Prod.map (masksOf (offLane laneOf p)) (masksOf (onLane laneOf p)) (splitSlots laneOf p
          values) :=
  rfl

/-- **Given the vectors, the limbs of the two sets of sites are independent**, each uniform on its
own fibre. -/
theorem fibreLaw_masksOf_split (vectors : LaneVectors laneOf) :
    (fibreLaw (masksOf laneOf) (masksOf_surjective laneOf) vectors).map (splitSlots laneOf p) =
      productPMF
        (fibreLaw (masksOf (offLane laneOf p)) (masksOf_surjective _) (splitVectors laneOf p
            vectors).1)
        (fibreLaw (masksOf (onLane laneOf p)) (masksOf_surjective _) (splitVectors laneOf p
            vectors).2) := by
  have onto : Function.Surjective (Prod.map (masksOf (offLane laneOf p)) (masksOf (onLane laneOf
      p))) :=
    fun b => ⟨((masksOf_surjective _ b.1).choose, (masksOf_surjective _ b.2).choose),
      Prod.ext (masksOf_surjective _ b.1).choose_spec (masksOf_surjective _ b.2).choose_spec⟩
  rw [fibreLaw_map_equiv' (masksOf laneOf) _ (masksOf_surjective laneOf) onto (splitSlots laneOf p)
    (splitVectors laneOf p) (fun values => (masksOf_split laneOf p values).symm) vectors]
  exact fibreLaw_prod _ _ _ _ onto _ _

/-- **The swapped law of the limbs of a family of sites**: the vectors uniform, then the limbs
uniform on their fibre. -/
def swapLimbLaw : PMF (LimbSlot laneOf → Block × Block) :=
  (PMF.uniformOfFintype (LaneVectors laneOf)).bind fun vectors =>
    fibreLaw (masksOf laneOf) (masksOf_surjective laneOf) vectors

/-- **Under the swap kernel, the limb values off `p` and the vectors on `p` are independent**: the
former swapped, the latter uniform, whatever the points. -/
theorem swapKernel_split_law {D : Type} [Fintype D] [DecidableEq D] (point : LimbSlot laneOf ↪ D) :
    (swapKernel point).map (fun table => ((splitSlots laneOf p (evalAt point table)).1,
        (splitVectors laneOf p (maskMap point table)).2)) =
      productPMF (swapLimbLaw (offLane laneOf p))
        (PMF.uniformOfFintype (LaneVectors (onLane laneOf p))) := by
  have each : ∀ vectors : LaneVectors laneOf,
      (fibreKernel point vectors).map (fun table => ((splitSlots laneOf p (evalAt point table)).1,
          (splitVectors laneOf p (maskMap point table)).2)) =
        productPMF (fibreLaw (masksOf (offLane laneOf p)) (masksOf_surjective _)
          (splitVectors laneOf p vectors).1) (PMF.pure (splitVectors laneOf p vectors).2) := by
    intro vectors
    unfold fibreKernel
    rw [PMF.map_bind]
    have inner : ∀ values : LimbSlot laneOf → Block × Block,
        ((PMF.uniformOfFintype (D → Block × Block)).map (Function.extend point values)).map
            (fun table => ((splitSlots laneOf p (evalAt point table)).1,
              (splitVectors laneOf p (maskMap point table)).2)) =
          PMF.pure ((splitSlots laneOf p values).1,
            (splitVectors laneOf p (masksOf laneOf values)).2) := by
      intro values
      rw [PMF.map_comp]
      have constant : ((fun table => ((splitSlots laneOf p (evalAt point table)).1,
            (splitVectors laneOf p (maskMap point table)).2)) ∘ Function.extend point values) =
          Function.const _ ((splitSlots laneOf p values).1,
            (splitVectors laneOf p (masksOf laneOf values)).2) := by
        funext table
        simp only [Function.comp_apply, maskMap, evalAt_extend]
        rfl
      rw [constant, PMF.map_const]
    simp only [inner]
    have onFibre : ∀ values ∈ (fibreLaw (masksOf laneOf) (masksOf_surjective laneOf)
        vectors).support,
        PMF.pure ((splitSlots laneOf p values).1, (splitVectors laneOf p (masksOf laneOf
            values)).2) =
          PMF.pure (Prod.map id (Function.const _ (splitVectors laneOf p vectors).2)
            (splitSlots laneOf p values)) := by
      intro values member
      have masks : masksOf laneOf values = vectors := by
        have := (PMF.mem_support_iff _ _).mp member
        rw [fibreLaw_apply] at this
        by_contra ne
        exact this (if_neg ne)
      rw [masks]
      rfl
    rw [Hidden.bind_support_congr _ _ _ onFibre]
    show (fibreLaw (masksOf laneOf) (masksOf_surjective laneOf) vectors).bind
      (PMF.pure ∘ (Prod.map id (Function.const _ (splitVectors laneOf p vectors).2) ∘
        splitSlots laneOf p)) = _
    rw [PMF.bind_pure_comp, ← PMF.map_comp, fibreLaw_masksOf_split, productPMF_map, PMF.map_id,
      PMF.map_const]
  unfold swapKernel
  rw [PMF.map_bind]
  simp only [each]
  have uniform : PMF.uniformOfFintype (LaneVectors laneOf) =
      (productPMF (PMF.uniformOfFintype (LaneVectors (offLane laneOf p)))
        (PMF.uniformOfFintype (LaneVectors (onLane laneOf p)))).map (splitVectors laneOf p).symm :=
            by
    rw [← uniformOfFintype_productPMF, uniformOfFintype_map_equiv]
  rw [uniform, PMF.bind_map]
  have back : ∀ pair : LaneVectors (offLane laneOf p) × LaneVectors (onLane laneOf p),
      splitVectors laneOf p ((splitVectors laneOf p).symm pair) = pair :=
    (splitVectors laneOf p).apply_symm_apply
  simp only [Function.comp_def, back]
  rw [productPMF_bind, PMF.bind_pure]
  rfl

end Split

end

end Kriterion.ArgoMAC.Security.Phase3
