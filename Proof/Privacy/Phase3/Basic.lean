/-
**Phase 3, P1 — shared probability lemmas.**

The phase-3 route (`B-output-aware-simulator.md`) needs these generic facts about
finite uniform laws, which this module proves once:

* `etvDist_bind_left_le_const` — a *shared* first draw followed by two kernels that are pointwise
  `ε`-close gives two laws that are `ε`-close (VCV-io proves the `ℝ`-valued form; its `ℝ≥0∞` step is
  `private`, so it is re-proved here);
* `uniform_eq_bind_fibreLaw` — the uniform law on `A` disintegrates along any surjection `g` as
  "draw `g a` from its pushforward, then draw `a` uniformly on that fibre";
* `uniform_map_of_fibre_equiv` — a map whose fibres are pairwise equinumerous pushes the uniform law
  to the uniform law (no fibre is ever counted);
* `etvDist_reduction_le_card` and `etvDist_dpi_map_uniform_le` — the reduction bias of one Rule S
  draw onto any finite target, and the sum of the per-coordinate biases of independent draws;
* `sampleLane_etvDist_le` and `laneDelta_le` — the bias of the phase-4 batched sampler
  (`PlanB.sampleLane`, one lane vector from `k` hash answers),
  `(2 ^ (256 k) mod p ^ n) / 2 ^ (256 k) ≤ 2 ^ (254 n) / 2 ^ (256 k)`, and its four lane values.

**Why these are local proofs.** `uniform_map_of_fibre_equiv` and the reduction bias restate,
generically and in the `Phase3` namespace, the arguments of two modules of the earlier hybrid
chain, which targeted a superseded profile and have been removed from this repository.
-/

import Proof.Privacy.PGS.DaviesMeyerUniform
import Construction.PGS.Sampler
import Construction.PGS.BatchSampler

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 400

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv uniformOfFintype_map_fst card_block)
open scoped ENNReal

noncomputable section

/-! ### Data processing, in `PMF.map` spelling -/

/-- `PMF.etvDist_map_le` is stated with `<$>`; this is the same fact for `PMF.map`. -/
theorem etvDist_map_le' {A B : Type} (f : A → B) (p q : PMF A) :
    (p.map f).etvDist (q.map f) ≤ p.etvDist q :=
  PMF.etvDist_map_le f p q

/-! ### A shared first draw -/

/-- **A shared first draw.** Two kernels behind one common law differ by at most the
`p`-average of their pointwise distances. (VCV-io's `pmf_etvDist_bind_left_le`, which is
`private`.) -/
theorem etvDist_bind_left_le {α β : Type} (p : PMF α) (f g : α → PMF β) :
    (p.bind f).etvDist (p.bind g) ≤ ∑' a, (f a).etvDist (g a) * p a := by
  have hrhs :
      (∑' a, (f a).etvDist (g a) * p a) =
        (∑' a, (∑' b, ENNReal.absDiff ((f a) b) ((g a) b)) * p a) / 2 := by
    simp only [PMF.etvDist, div_eq_mul_inv, ← ENNReal.tsum_mul_right, mul_right_comm]
  rw [PMF.etvDist, hrhs]
  refine ENNReal.div_le_div_right ?_ 2
  calc ∑' y, ENNReal.absDiff (∑' x, p x * (f x) y) (∑' x, p x * (g x) y)
      ≤ ∑' y, ∑' x, ENNReal.absDiff (p x * (f x) y) (p x * (g x) y) :=
        ENNReal.tsum_le_tsum fun y => ENNReal.absDiff_tsum_le _ _
    _ ≤ ∑' y, ∑' x, ENNReal.absDiff ((f x) y) ((g x) y) * p x :=
        ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun x => by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            ENNReal.absDiff_mul_right_le ((f x) y) ((g x) y) (p x)
    _ = ∑' x, ∑' y, ENNReal.absDiff ((f x) y) ((g x) y) * p x := ENNReal.tsum_comm
    _ = ∑' x, (∑' y, ENNReal.absDiff ((f x) y) ((g x) y)) * p x := by
        simp_rw [ENNReal.tsum_mul_right]

/-- **A shared first draw, uniform bound.** If the two kernels are pointwise `bound`-close, so are
the two laws. This is the step that lets a per-point-set bound (`MaskSwap.swapKernel_etvDist_le`)
cover the whole tape, whatever the law of the points. -/
theorem etvDist_bind_left_le_const {α β : Type} (p : PMF α) (f g : α → PMF β) (bound : ℝ≥0∞)
    (each : ∀ a, (f a).etvDist (g a) ≤ bound) :
    (p.bind f).etvDist (p.bind g) ≤ bound := by
  refine le_trans (etvDist_bind_left_le p f g) ?_
  calc ∑' a, (f a).etvDist (g a) * p a ≤ ∑' a, bound * p a :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_left (each a) _
    _ = bound * ∑' a, p a := ENNReal.tsum_mul_left
    _ = bound := by rw [p.tsum_coe, mul_one]

/-! ### Pushforwards of a uniform law, counted -/

/-- The pushforward mass of one point is its fibre's share. -/
theorem uniform_map_apply {A B : Type} [Fintype A] [Nonempty A] [DecidableEq B]
    (g : A → B) (point : B) :
    ((PMF.uniformOfFintype A).map g) point
      = (Fintype.card {x : A // g x = point} : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ := by
  classical
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply]
  rw [tsum_fintype, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp [eq_comm]

/-- **Equinumerous fibres push uniform to uniform.** If every two fibres of `g` are in bijection
(`shift`), then `g` pushes the uniform law on `A` to the uniform law on `B`. No fibre is counted:
the common cardinality cancels against `#A = #B · #fibre`. -/
theorem uniform_map_of_fibre_equiv {A B : Type} [Fintype A] [Nonempty A] [Fintype B]
    [Nonempty B] [DecidableEq B] (g : A → B)
    (shift : ∀ first second : B, {x : A // g x = first} ≃ {x : A // g x = second}) :
    (PMF.uniformOfFintype A).map g = PMF.uniformOfFintype B := by
  classical
  obtain ⟨base⟩ := (inferInstance : Nonempty B)
  have fibreCard : ∀ point : B,
      Fintype.card {x : A // g x = point} = Fintype.card {x : A // g x = base} :=
    fun point => Fintype.card_congr (shift point base)
  have total : Fintype.card A = Fintype.card B * Fintype.card {x : A // g x = base} := by
    calc Fintype.card A = Fintype.card (Σ point : B, {x : A // g x = point}) :=
          Fintype.card_congr (Equiv.sigmaFiberEquiv g).symm
      _ = ∑ point : B, Fintype.card {x : A // g x = point} := Fintype.card_sigma
      _ = ∑ _point : B, Fintype.card {x : A // g x = base} :=
          Finset.sum_congr rfl fun point _ => fibreCard point
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have fibrePos : 0 < Fintype.card {x : A // g x = base} := by
    rcases Nat.eq_zero_or_pos (Fintype.card {x : A // g x = base}) with zero | pos
    · have : Fintype.card A = 0 := by rw [total, zero, mul_zero]
      exact absurd this Fintype.card_ne_zero
    · exact pos
  refine PMF.ext fun point => ?_
  rw [uniform_map_apply, PMF.uniformOfFintype_apply, fibreCard point, total, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    mul_comm ((Fintype.card B : ℝ≥0∞)⁻¹), ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr fibrePos.ne') (ENNReal.natCast_ne_top _),
    one_mul]

/-! ### The fibre disintegration -/

section Fibre

variable {A B : Type} [Fintype A] [DecidableEq B] (g : A → B) (onto : Function.Surjective g)

/-- The uniform law on the fibre of `g` over `point`, read as a law on `A`. -/
def fibreLaw (point : B) : PMF A :=
  haveI : Nonempty {x : A // g x = point} :=
    ⟨⟨Classical.choose (onto point), Classical.choose_spec (onto point)⟩⟩
  (PMF.uniformOfFintype {x : A // g x = point}).map Subtype.val

theorem fibreLaw_apply (point : B) (x : A) :
    fibreLaw g onto point x
      = if g x = point then (Fintype.card {y : A // g y = point} : ℝ≥0∞)⁻¹ else 0 := by
  classical
  unfold fibreLaw
  rw [PMF.map_apply]
  split_ifs with hit
  · rw [tsum_eq_single ⟨x, hit⟩]
    · simp [PMF.uniformOfFintype_apply]
    · intro other miss
      have : x ≠ other.1 := fun same => miss (Subtype.ext same.symm)
      simp [this]
  · refine ENNReal.tsum_eq_zero.mpr fun other => ?_
    have : x ≠ other.1 := fun same => hit (same ▸ other.2)
    simp [this]

/-- Every point the fibre law can draw lies in the fibre. -/
theorem fibreLaw_map (point : B) : (fibreLaw g onto point).map g = PMF.pure point := by
  classical
  unfold fibreLaw
  rw [PMF.map_comp]
  have constant : (g ∘ Subtype.val : {x : A // g x = point} → B) = fun _ => point := by
    funext x; exact x.2
  rw [constant]
  exact PMF.map_const _ point

/-- **The fibre disintegration of the uniform law.** Drawing `a` uniformly is drawing `g a` from its
pushforward and then `a` uniformly on the fibre over it. -/
theorem uniform_eq_bind_fibreLaw [Nonempty A] :
    PMF.uniformOfFintype A = ((PMF.uniformOfFintype A).map g).bind (fibreLaw g onto) := by
  classical
  refine PMF.ext fun x => ?_
  rw [PMF.bind_apply, tsum_eq_single (g x)]
  · rw [fibreLaw_apply, if_pos rfl, uniform_map_apply, PMF.uniformOfFintype_apply, mul_comm,
      ← mul_assoc]
    have fibrePos : 0 < Fintype.card {y : A // g y = g x} :=
      Fintype.card_pos_iff.mpr ⟨⟨x, rfl⟩⟩
    rw [ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr fibrePos.ne') (ENNReal.natCast_ne_top _),
      one_mul]
  · intro other miss
    rw [fibreLaw_apply, if_neg (fun same => miss same.symm), mul_zero]

end Fibre

/-! ### The one-sided form of total variation -/

/-- **Total variation is one-sided.** Only the outcomes the first law undershoots contribute. -/
theorem etvDist_eq_tsum_tsub {A : Type} (first second : PMF A) :
    first.etvDist second = ∑' value, (second value - first value) := by
  have minLe : (∑' value, (first value ⊓ second value)) ≤ 1 :=
    le_of_le_of_eq (ENNReal.tsum_le_tsum fun value => inf_le_left) first.tsum_coe
  have left : (∑' value, (first value - second value))
      + (∑' value, (first value ⊓ second value)) = 1 := by
    rw [← ENNReal.tsum_add, ← first.tsum_coe]
    exact tsum_congr fun value => tsub_add_min
  have right : (∑' value, (second value - first value))
      + (∑' value, (first value ⊓ second value)) = 1 := by
    rw [← ENNReal.tsum_add, ← second.tsum_coe]
    refine tsum_congr fun value => ?_
    rw [inf_comm]
    exact tsub_add_min
  have equal : (∑' value, (first value - second value))
      = ∑' value, (second value - first value) :=
    (ENNReal.add_left_inj (ne_top_of_le_ne_top ENNReal.one_ne_top minLe)).mp
      (left.trans right.symm)
  rw [PMF.etvDist]
  simp only [ENNReal.absDiff]
  rw [ENNReal.tsum_add, equal,
    show (∑' value, (second value - first value)) + ∑' value, (second value - first value)
      = 2 * ∑' value, (second value - first value) from by ring, mul_div_assoc]
  simp [ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-! ### Independent pairs and independent coordinates -/

/-- Two independent draws. -/
def productPMF {A C : Type} (first : PMF A) (second : PMF C) : PMF (A × C) :=
  first.bind fun value => second.map (Prod.mk value)

@[simp] theorem productPMF_apply {A C : Type} (first : PMF A) (second : PMF C) (point : A × C) :
    productPMF first second point = first point.1 * second point.2 := by
  classical
  obtain ⟨left, right⟩ := point
  rw [productPMF, PMF.bind_apply]
  have inner : ∀ value : A,
      (second.map (Prod.mk value)) (left, right) = if value = left then second right else 0 := by
    intro value
    rw [PMF.map_apply]
    by_cases hit : value = left
    · subst hit
      rw [if_pos rfl, tsum_eq_single right]
      · simp
      · intro other miss
        simp [Prod.ext_iff, Ne.symm miss]
    · rw [if_neg hit, ENNReal.tsum_eq_zero]
      intro other
      exact if_neg fun same => hit (congrArg Prod.fst same).symm
  simp only [inner]
  rw [tsum_eq_single left]
  · simp
  · intro other miss
    simp [miss]

theorem productPMF_swap {A C : Type} (first : PMF A) (second : PMF C) :
    (productPMF first second).map Prod.swap = productPMF second first := by
  refine PMF.ext fun point => ?_
  obtain ⟨right, left⟩ := point
  rw [PMF.map_apply, tsum_eq_single (left, right)]
  · simp [mul_comm]
  · intro other miss
    refine if_neg fun same => miss ?_
    obtain ⟨a, c⟩ := other
    cases same
    rfl

/-- A uniform law on a product is the independent pair of uniform laws. -/
theorem uniformOfFintype_productPMF {A C : Type} [Fintype A] [Nonempty A] [Fintype C]
    [Nonempty C] :
    PMF.uniformOfFintype (A × C)
      = productPMF (PMF.uniformOfFintype A) (PMF.uniformOfFintype C) := by
  refine PMF.ext fun point => ?_
  rw [productPMF_apply, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
    PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
      (Or.inl (ENNReal.natCast_ne_top _))]

theorem etvDist_productPMF_left_le {A C : Type} (first second : PMF A) (common : PMF C) :
    (productPMF first common).etvDist (productPMF second common) ≤ first.etvDist second :=
  PMF.etvDist_bind_right_le _ first second

theorem etvDist_productPMF_right_le {A C : Type} (common : PMF A) (first second : PMF C) :
    (productPMF common first).etvDist (productPMF common second) ≤ first.etvDist second := by
  rw [← productPMF_swap first common, ← productPMF_swap second common]
  exact le_trans (etvDist_map_le' Prod.swap _ _) (etvDist_productPMF_left_le first second common)

theorem etvDist_productPMF_le {A C : Type} (firstLeft secondLeft : PMF A)
    (firstRight secondRight : PMF C) :
    (productPMF firstLeft firstRight).etvDist (productPMF secondLeft secondRight)
      ≤ firstLeft.etvDist secondLeft + firstRight.etvDist secondRight :=
  le_trans (PMF.etvDist_triangle _ (productPMF secondLeft firstRight) _)
    (add_le_add (etvDist_productPMF_left_le firstLeft secondLeft firstRight)
      (etvDist_productPMF_right_le secondLeft firstRight secondRight))

theorem productPMF_map {A B C D : Type} (first : PMF A) (second : PMF C) (left : A → B)
    (right : C → D) :
    (productPMF first second).map (Prod.map left right)
      = productPMF (first.map left) (second.map right) := by
  rw [productPMF, productPMF, PMF.map_bind, PMF.bind_map]
  refine congrArg (PMF.bind first) (funext fun value => ?_)
  show PMF.map (Prod.map left right) (PMF.map (Prod.mk value) second)
    = PMF.map (Prod.mk (left value)) (PMF.map right second)
  rw [PMF.map_comp, PMF.map_comp]
  rfl

/-- **Per-coordinate biases add up, for coordinates of different types**, over `Fin n`: one
coordinate at a time through `Fin.consEquiv`. -/
theorem etvDist_pi_fin_map_uniform_le (n : Nat) :
    ∀ (A B : Fin n → Type) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, Fintype (B i)]
      [∀ i, Nonempty (B i)] (g : ∀ i, A i → B i) (bound : Fin n → ℝ≥0∞),
      (∀ i, ((PMF.uniformOfFintype (A i)).map (g i)).etvDist (PMF.uniformOfFintype (B i))
        ≤ bound i) →
      ((PMF.uniformOfFintype (∀ i, A i)).map (fun family i => g i (family i))).etvDist
          (PMF.uniformOfFintype (∀ i, B i))
        ≤ ∑ i, bound i := by
  induction n with
  | zero =>
      intro A B _ _ _ _ g bound _
      have same : (PMF.uniformOfFintype (∀ i : Fin 0, A i)).map (fun family i => g i (family i))
          = PMF.uniformOfFintype (∀ i : Fin 0, B i) :=
        uniformOfFintype_map_equiv
          (⟨fun family i => g i (family i), fun _ i => i.elim0, fun _ => funext fun i => i.elim0,
            fun _ => funext fun i => i.elim0⟩ : (∀ i : Fin 0, A i) ≃ ∀ i : Fin 0, B i)
      rw [same, PMF.etvDist_self]
      exact zero_le
  | succ n ih =>
      intro A B _ _ _ _ g bound perDraw
      have left : (PMF.uniformOfFintype (A 0 × ∀ i : Fin n, A i.succ)).map (Fin.consEquiv A)
          = PMF.uniformOfFintype (∀ i, A i) := uniformOfFintype_map_equiv _
      have right : (PMF.uniformOfFintype (B 0 × ∀ i : Fin n, B i.succ)).map (Fin.consEquiv B)
          = PMF.uniformOfFintype (∀ i, B i) := uniformOfFintype_map_equiv _
      rw [← left, ← right, PMF.map_comp, uniformOfFintype_productPMF, uniformOfFintype_productPMF]
      have commute : (fun family i => g i (family i)) ∘ Fin.consEquiv A
          = Fin.consEquiv B ∘ Prod.map (g 0) (fun tail i => g i.succ (tail i)) := by
        funext pair i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.consEquiv]
      rw [commute, ← PMF.map_comp, productPMF_map, Fin.sum_univ_succ]
      exact le_trans (etvDist_map_le' _ _ _) (le_trans (etvDist_productPMF_le _ _ _ _)
        (add_le_add (perDraw 0) (ih (fun i => A i.succ) (fun i => B i.succ) (fun i => g i.succ)
          (fun i => bound i.succ) fun i => perDraw i.succ)))

/-- **Per-coordinate biases add up**, for independent coordinates of different types over any
finite index type, with a bound per index. -/
theorem etvDist_dpi_map_uniform_le {I : Type} [Fintype I] [DecidableEq I] (A B : I → Type)
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, Fintype (B i)] [∀ i, Nonempty (B i)]
    (g : ∀ i, A i → B i) (bound : I → ℝ≥0∞)
    (perDraw : ∀ i,
      ((PMF.uniformOfFintype (A i)).map (g i)).etvDist (PMF.uniformOfFintype (B i)) ≤ bound i) :
    ((PMF.uniformOfFintype (∀ i, A i)).map (fun family i => g i (family i))).etvDist
        (PMF.uniformOfFintype (∀ i, B i))
      ≤ ∑ i, bound i := by
  have roundTrip : ∀ law : PMF (∀ i, B i),
      (law.map (Equiv.piCongrLeft' B (Fintype.equivFin I))).map
        (Equiv.piCongrLeft' B (Fintype.equivFin I)).symm = law := fun law => by
    rw [PMF.map_comp, Equiv.symm_comp_self, PMF.map_id]
  have leftLaw : ((PMF.uniformOfFintype (∀ i, A i)).map (fun family i => g i (family i))).map
        (Equiv.piCongrLeft' B (Fintype.equivFin I))
      = (PMF.uniformOfFintype (∀ k, A ((Fintype.equivFin I).symm k))).map
          (fun family k => g ((Fintype.equivFin I).symm k) (family k)) := by
    rw [PMF.map_comp, ← uniformOfFintype_map_equiv (Equiv.piCongrLeft' A (Fintype.equivFin I)),
      PMF.map_comp]
    rfl
  calc ((PMF.uniformOfFintype (∀ i, A i)).map (fun family i => g i (family i))).etvDist
          (PMF.uniformOfFintype (∀ i, B i))
      = ((((PMF.uniformOfFintype (∀ i, A i)).map (fun family i => g i (family i))).map
            (Equiv.piCongrLeft' B (Fintype.equivFin I))).map
            (Equiv.piCongrLeft' B (Fintype.equivFin I)).symm).etvDist
          (((PMF.uniformOfFintype (∀ i, B i)).map
            (Equiv.piCongrLeft' B (Fintype.equivFin I))).map
            (Equiv.piCongrLeft' B (Fintype.equivFin I)).symm) := by
        rw [roundTrip, roundTrip]
    _ ≤ (((PMF.uniformOfFintype (∀ i, A i)).map (fun family i => g i (family i))).map
            (Equiv.piCongrLeft' B (Fintype.equivFin I))).etvDist
          ((PMF.uniformOfFintype (∀ i, B i)).map (Equiv.piCongrLeft' B (Fintype.equivFin I))) :=
        etvDist_map_le' _ _ _
    _ = ((PMF.uniformOfFintype (∀ k, A ((Fintype.equivFin I).symm k))).map
            (fun family k => g ((Fintype.equivFin I).symm k) (family k))).etvDist
          (PMF.uniformOfFintype (∀ k, B ((Fintype.equivFin I).symm k))) := by
        rw [leftLaw, uniformOfFintype_map_equiv]
    _ ≤ ∑ k, bound ((Fintype.equivFin I).symm k) :=
        etvDist_pi_fin_map_uniform_le _ (fun k => A ((Fintype.equivFin I).symm k))
          (fun k => B ((Fintype.equivFin I).symm k)) (fun k => g ((Fintype.equivFin I).symm k))
          (fun k => bound ((Fintype.equivFin I).symm k))
          fun k => perDraw ((Fintype.equivFin I).symm k)
    _ = ∑ i, bound i := Equiv.sum_comp (Fintype.equivFin I).symm bound

/-! ### Independent draws of different types -/

/-- A map along a bijection moves each point's mass to its image. -/
theorem map_equiv_apply {A B : Type} (law : PMF A) (e : A ≃ B) (point : B) :
    (law.map e) point = law (e.symm point) := by
  rw [PMF.map_apply, tsum_eq_single (e.symm point)]
  · rw [if_pos (e.apply_symm_apply point).symm]
  · intro other miss
    exact if_neg fun same => miss (by rw [same, e.symm_apply_apply])

section Pi

variable {I : Type} [Fintype I] [DecidableEq I]

/-- **Independent draws, one per index**, of possibly different types: the product law. -/
def piPMF {β : I → Type} [∀ i, Fintype (β i)] (law : ∀ i, PMF (β i)) : PMF (∀ i, β i) :=
  PMF.ofFintype (fun family => ∏ i, law i (family i)) (by
    rw [← Fintype.prod_sum fun i (value : β i) => law i value]
    exact Finset.prod_eq_one fun i _ => by
      have total := (law i).tsum_coe
      rwa [tsum_fintype] at total)

theorem piPMF_apply {β : I → Type} [∀ i, Fintype (β i)] (law : ∀ i, PMF (β i))
    (family : ∀ i, β i) : piPMF law family = ∏ i, law i (family i) :=
  rfl

/-- A uniform law on a dependent product is the product of the uniform laws. -/
theorem uniform_pi_eq_piPMF {β : I → Type} [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)] :
    PMF.uniformOfFintype (∀ i, β i) = piPMF fun i => PMF.uniformOfFintype (β i) := by
  refine PMF.ext fun family => ?_
  rw [piPMF_apply, PMF.uniformOfFintype_apply, Fintype.card_pi, Nat.cast_prod]
  simp only [PMF.uniformOfFintype_apply]
  exact ENNReal.prod_inv_distrib fun _ _ _ _ _ => Or.inr (ENNReal.natCast_ne_top _)

/-- Point masses, one per index, make the point mass of the family. -/
theorem piPMF_pure {β : I → Type} [∀ i, Fintype (β i)] (family : ∀ i, β i) :
    piPMF (fun i => PMF.pure (family i)) = PMF.pure family := by
  classical
  refine PMF.ext fun other => ?_
  rw [piPMF_apply, PMF.pure_apply]
  simp only [PMF.pure_apply]
  rw [Fintype.prod_ite_zero, Finset.prod_const_one]
  by_cases same : other = family
  · rw [if_pos fun i => congrFun same i, if_pos same]
  · rw [if_neg fun all => same (funext all), if_neg same]

/-- **Independent kernels after independent draws are independent draws.** -/
theorem piPMF_bind {β γ : I → Type} [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)]
    (law : ∀ i, PMF (β i)) (kernel : ∀ i, β i → PMF (γ i)) :
    (piPMF law).bind (fun family => piPMF fun i => kernel i (family i))
      = piPMF fun i => (law i).bind (kernel i) := by
  refine PMF.ext fun result => ?_
  simp only [PMF.bind_apply, tsum_fintype, piPMF_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun family _ => ?_
  rw [Finset.prod_mul_distrib]

/-- Pointwise maps of independent draws are independent draws of the images. -/
theorem piPMF_map {β γ : I → Type} [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)]
    (law : ∀ i, PMF (β i)) (g : ∀ i, β i → γ i) :
    (piPMF law).map (fun family i => g i (family i)) = piPMF fun i => (law i).map (g i) := by
  have pointMass : (PMF.pure ∘ fun (family : ∀ i, β i) i => g i (family i))
      = fun family : ∀ i, β i => piPMF fun i => PMF.pure (g i (family i)) :=
    funext fun family => (piPMF_pure fun i => g i (family i)).symm
  rw [← PMF.bind_pure_comp, pointMass]
  exact piPMF_bind law fun i value => PMF.pure (g i value)

/-- **One index against all the others**: the product law splits at any index into that
index's law and the product law of the rest, independently (`Equiv.piSplitAt`). -/
theorem piPMF_split {β : I → Type} [∀ i, Fintype (β i)] (law : ∀ i, PMF (β i)) (index : I) :
    (piPMF law).map (Equiv.piSplitAt index β)
      = productPMF (law index) (piPMF fun other : {j // j ≠ index} => law other) := by
  refine PMF.ext fun pair => ?_
  obtain ⟨head, tail⟩ := pair
  rw [map_equiv_apply, piPMF_apply, productPMF_apply, piPMF_apply,
    Fintype.prod_eq_mul_prod_subtype_ne _ index]
  congr 1
  · rw [Equiv.piSplitAt_symm_apply, dif_pos rfl]
  · refine Finset.prod_congr rfl fun other _ => ?_
    rw [Equiv.piSplitAt_symm_apply, dif_neg other.2]

end Pi

/-! ### The reduction bias of one Rule S draw -/

/-- **The reduction bias, any target.** A map onto a type of `m` points from a domain of size
`m * q + r` whose every fibre has at least `q` points pushes the uniform law to within
`r / (m * q + r)` of uniform. -/
theorem etvDist_reduction_le_card {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [DecidableEq B] (m q r : Nat) (g : A → B) (cardB : Fintype.card B = m)
    (cardA : Fintype.card A = m * q + r)
    (fibres : ∀ point : B, q ≤ Fintype.card {x : A // g x = point}) :
    ((PMF.uniformOfFintype A).map g).etvDist (PMF.uniformOfFintype B)
      ≤ (r : ℝ≥0∞) / (m * q + r : Nat) := by
  classical
  have sizePos : 0 < Fintype.card A := Fintype.card_pos
  have sizeNe : (Fintype.card A : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr sizePos.ne'
  have sizeTop : (Fintype.card A : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have modNe : (m : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (cardB ▸ Fintype.card_ne_zero)
  have modTop : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have lower : ∀ point : B,
      (q : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹
        ≤ ((PMF.uniformOfFintype A).map g) point := by
    intro point
    rw [uniform_map_apply]
    exact mul_le_mul_left (Nat.cast_le.mpr (fibres point)) _
  have termwise : ∀ point : B,
      (PMF.uniformOfFintype B) point - ((PMF.uniformOfFintype A).map g) point
        ≤ (m : ℝ≥0∞)⁻¹ - (q : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ := by
    intro point
    rw [PMF.uniformOfFintype_apply, cardB]
    exact tsub_le_tsub_left (lower point) _
  rw [etvDist_eq_tsum_tsub]
  calc (∑' point : B, ((PMF.uniformOfFintype B) point
          - ((PMF.uniformOfFintype A).map g) point))
      ≤ ∑' _point : B,
          ((m : ℝ≥0∞)⁻¹ - (q : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹) :=
        ENNReal.tsum_le_tsum termwise
    _ = (m : ℝ≥0∞) * ((m : ℝ≥0∞)⁻¹ - (q : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, cardB, nsmul_eq_mul]
    _ = (r : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.mul_sub (fun _ _ => modTop), ENNReal.mul_inv_cancel modNe modTop,
          ← mul_assoc]
        refine (ENNReal.sub_eq_of_eq_add
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top modTop (ENNReal.natCast_ne_top q))
            (ENNReal.inv_ne_top.mpr sizeNe)) ?_)
        rw [← add_mul]
        have total : ((r : ℝ≥0∞) + (m : ℝ≥0∞) * (q : ℝ≥0∞)) = (Fintype.card A : ℝ≥0∞) := by
          rw [cardA]
          push_cast
          ring
        rw [total, ENNReal.mul_inv_cancel sizeNe sizeTop]
    _ = (r : ℝ≥0∞) / (m * q + r : Nat) := by
        rw [ENNReal.div_eq_inv_mul, mul_comm, cardA]

/-! ### The batched sampler: one lane vector from `k` hash answers -/

/-- `k` hash answers carry `2 ^ (256 k)` values (`PlanB.limbsEquiv`). -/
theorem card_limbs (k : Nat) : Fintype.card (Fin k → Block × Block) = 2 ^ (256 * k) := by
  rw [Fintype.card_congr (limbsEquiv k), Fintype.card_fin]

/-- A lane vector of `n` field elements takes `p ^ n` values. -/
theorem card_laneVector (n : Nat) : Fintype.card (Fin n → BaseField) = baseFieldModulus ^ n := by
  simp [ZMod.card]

/-- **Every vector has at least `⌊2 ^ (256 k) / p ^ n⌋` preimages under `sampleLane n k`.** The
witnesses are the answers of `enc(Y) + p ^ n · t` for `t < ⌊2 ^ (256 k) / p ^ n⌋`. -/
theorem sampleLane_fibre_card (n k : Nat) (vector : Fin n → BaseField) :
    2 ^ (256 * k) / baseFieldModulus ^ n
      ≤ Fintype.card {h : Fin k → Block × Block // sampleLane n k h = vector} := by
  classical
  have powPos : 0 < baseFieldModulus ^ n := baseFieldModulus_pow_pos n
  have encSmall : laneEncode vector < baseFieldModulus ^ n := laneEncode_lt vector
  have bound : ∀ t : Fin (2 ^ (256 * k) / baseFieldModulus ^ n),
      laneEncode vector + baseFieldModulus ^ n * t.val < 2 ^ (256 * k) := by
    intro t
    have step : laneEncode vector + baseFieldModulus ^ n * t.val
        < baseFieldModulus ^ n * (t.val + 1) := by
      rw [Nat.mul_succ]
      omega
    have grow : baseFieldModulus ^ n * (t.val + 1)
        ≤ baseFieldModulus ^ n * (2 ^ (256 * k) / baseFieldModulus ^ n) :=
      Nat.mul_le_mul_left _ t.isLt
    have final : baseFieldModulus ^ n * (2 ^ (256 * k) / baseFieldModulus ^ n)
        ≤ 2 ^ (256 * k) := Nat.mul_div_le _ _
    exact lt_of_lt_of_le step (le_trans grow final)
  have hit : ∀ t : Fin (2 ^ (256 * k) / baseFieldModulus ^ n),
      sampleLane n k (natToLimbs k (laneEncode vector + baseFieldModulus ^ n * t.val))
        = vector := by
    intro t
    rw [sampleLane_eq_iff, limbsToNat_natToLimbs_of_lt k _ (bound t), Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt encSmall]
  let embed : Fin (2 ^ (256 * k) / baseFieldModulus ^ n)
      → {h : Fin k → Block × Block // sampleLane n k h = vector} := fun t =>
    ⟨natToLimbs k (laneEncode vector + baseFieldModulus ^ n * t.val), hit t⟩
  have injective : Function.Injective embed := by
    intro first second same
    have recovered := congrArg
      (fun point : {h : Fin k → Block × Block // sampleLane n k h = vector} =>
        limbsToNat k point.1) same
    simp only [embed, limbsToNat_natToLimbs_of_lt k _ (bound first),
      limbsToNat_natToLimbs_of_lt k _ (bound second), Nat.add_left_cancel_iff] at recovered
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left powPos recovered)
  simpa using Fintype.card_le_of_injective embed injective

/-- **The batched sampler, exact residue form.** `sampleLane n k` of `k` uniform hash answers is
within `(2 ^ (256 k) mod p ^ n) / 2 ^ (256 k)` of the uniform vector. -/
theorem sampleLane_etvDist_le_mod (n k : Nat) :
    ((PMF.uniformOfFintype (Fin k → Block × Block)).map (sampleLane n k)).etvDist
        (PMF.uniformOfFintype (Fin n → BaseField))
      ≤ ((2 ^ (256 * k) % baseFieldModulus ^ n : Nat) : ℝ≥0∞) / 2 ^ (256 * k) := by
  have split : baseFieldModulus ^ n * (2 ^ (256 * k) / baseFieldModulus ^ n)
      + 2 ^ (256 * k) % baseFieldModulus ^ n = 2 ^ (256 * k) := Nat.div_add_mod _ _
  have cards : Fintype.card (Fin k → Block × Block)
      = baseFieldModulus ^ n * (2 ^ (256 * k) / baseFieldModulus ^ n)
        + 2 ^ (256 * k) % baseFieldModulus ^ n := by
    rw [card_limbs, split]
  have bound := etvDist_reduction_le_card (A := Fin k → Block × Block) (B := Fin n → BaseField)
    (baseFieldModulus ^ n) (2 ^ (256 * k) / baseFieldModulus ^ n)
    (2 ^ (256 * k) % baseFieldModulus ^ n) (sampleLane n k) (card_laneVector n) cards
    (sampleLane_fibre_card n k)
  rw [split] at bound
  refine le_trans bound (le_of_eq ?_)
  rw [Nat.cast_pow, Nat.cast_ofNat]

/-- **`sampleLane_etvDist_le`: the batched sampler's bias.** `sampleLane n k` of `k` uniform hash
answers is within `2 ^ (254 n) / 2 ^ (256 k)` of the uniform vector in `F_p ^ n`. -/
theorem sampleLane_etvDist_le (n k : Nat) :
    ((PMF.uniformOfFintype (Fin k → Block × Block)).map (sampleLane n k)).etvDist
        (PMF.uniformOfFintype (Fin n → BaseField))
      ≤ (2 : ℝ≥0∞) ^ (254 * n) / 2 ^ (256 * k) := by
  refine le_trans (sampleLane_etvDist_le_mod n k) (ENNReal.div_le_div_right ?_ _)
  have residue : 2 ^ (256 * k) % baseFieldModulus ^ n ≤ 2 ^ (254 * n) :=
    le_trans (le_of_lt (Nat.mod_lt _ (baseFieldModulus_pow_pos n))) (baseFieldModulus_pow_le_two_pow n)
  calc ((2 ^ (256 * k) % baseFieldModulus ^ n : Nat) : ℝ≥0∞)
      ≤ ((2 ^ (254 * n) : Nat) : ℝ≥0∞) := Nat.cast_le.mpr residue
    _ = (2 : ℝ≥0∞) ^ (254 * n) := by rw [Nat.cast_pow, Nat.cast_ofNat]

/-! ### The four lanes -/

/-- The proof bias `2 ^ (254 n) / 2 ^ (256 k)` of one `sampleLane n k` vector. -/
def sampleLaneDelta (n k : Nat) : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (254 * n) / 2 ^ (256 * k)

theorem sampleLane_etvDist_le_delta (n k : Nat) :
    ((PMF.uniformOfFintype (Fin k → Block × Block)).map (sampleLane n k)).etvDist
        (PMF.uniformOfFintype (Fin n → BaseField))
      ≤ sampleLaneDelta n k :=
  sampleLane_etvDist_le n k

/-- **Exponent arithmetic.** If `254 n + e ≤ 256 k` then `2 ^ (254 n) / 2 ^ (256 k) ≤ 2 ^ -e`. -/
theorem sampleLaneDelta_le (n k e : Nat) (exponents : 254 * n + e ≤ 256 * k) :
    sampleLaneDelta n k ≤ ((2 : ℝ≥0∞) ^ e)⁻¹ := by
  unfold sampleLaneDelta
  refine ENNReal.div_le_of_le_mul ?_
  obtain ⟨extra, total⟩ : ∃ extra, 256 * k = 254 * n + e + extra :=
    ⟨256 * k - (254 * n + e), by omega⟩
  have powNe : (2 : ℝ≥0∞) ^ e ≠ 0 := pow_ne_zero _ two_ne_zero
  have powTop : (2 : ℝ≥0∞) ^ e ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc (2 : ℝ≥0∞) ^ (254 * n) = 2 ^ (254 * n) * 1 := (mul_one _).symm
    _ ≤ 2 ^ (254 * n) * 2 ^ extra := mul_le_mul_right (one_le_pow₀ one_le_two) _
    _ = 2 ^ (254 * n) * 2 ^ extra * ((2 ^ e)⁻¹ * 2 ^ e) := by
        rw [ENNReal.inv_mul_cancel powNe powTop, mul_one]
    _ = ((2 : ℝ≥0∞) ^ e)⁻¹ * 2 ^ (256 * k) := by
        rw [total, pow_add, pow_add]
        ring

/-- **The per-lane proof bias** `laneDelta lane = 2 ^ (254 n - 256 k)`, with `n` the lane's vector
length (curveX 3, curveY 2, pointX 364, pointY 273) and `k = limbCount lane`. -/
def laneDelta : Lane → ℝ≥0∞
  | .curveX => sampleLaneDelta curveElementCountX (limbCount .curveX)
  | .curveY => sampleLaneDelta curveElementCountY (limbCount .curveY)
  | .pointX => sampleLaneDelta pointElementCountX (limbCount .pointX)
  | .pointY => sampleLaneDelta pointElementCountY (limbCount .pointY)

/-- The exponent of each lane's proof bias: `256 k - 254 n`. -/
def laneDeltaExponent : Lane → Nat
  | .curveX => 262
  | .curveY => 260
  | .pointX => 142
  | .pointY => 290

/-- pointX: `n = 364`, `k = 362`, `2 ^ (254 · 364 - 256 · 362) = 2 ^ -216 ≤ 2 ^ -142`. -/
theorem laneDelta_pointX_le : laneDelta .pointX ≤ ((2 : ℝ≥0∞) ^ 142)⁻¹ :=
  sampleLaneDelta_le _ _ _ (by decide)

/-- pointY: `n = 273`, `k = 272`, `2 ^ (254 · 273 - 256 · 272) = 2 ^ -290`. -/
theorem laneDelta_pointY_le : laneDelta .pointY ≤ ((2 : ℝ≥0∞) ^ 290)⁻¹ :=
  sampleLaneDelta_le _ _ _ (by decide)

/-- curveX: `n = 3`, `k = 4`, `2 ^ -262`. -/
theorem laneDelta_curveX_le : laneDelta .curveX ≤ ((2 : ℝ≥0∞) ^ 262)⁻¹ :=
  sampleLaneDelta_le _ _ _ (by decide)

/-- curveY: `n = 2`, `k = 3`, `2 ^ -260`. -/
theorem laneDelta_curveY_le : laneDelta .curveY ≤ ((2 : ℝ≥0∞) ^ 260)⁻¹ :=
  sampleLaneDelta_le _ _ _ (by decide)

/-- **`laneDelta_le`**: the four lane biases, `2 ^ -142`, `2 ^ -290`, `2 ^ -262`, `2 ^ -260`. -/
theorem laneDelta_le (lane : Lane) : laneDelta lane ≤ ((2 : ℝ≥0∞) ^ laneDeltaExponent lane)⁻¹ := by
  cases lane
  · exact laneDelta_curveX_le
  · exact laneDelta_curveY_le
  · exact laneDelta_pointX_le
  · exact laneDelta_pointY_le

/-- Each lane bias is finite, so its `toReal` is faithful. -/
theorem laneDelta_ne_top (lane : Lane) : laneDelta lane ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero)) (laneDelta_le lane)

end

end Kriterion.ArgoMAC.Security.Phase3
