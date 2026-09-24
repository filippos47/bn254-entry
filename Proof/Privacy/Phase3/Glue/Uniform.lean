/-
Phase 3 glue: uniform finite laws.

Ported verbatim (up to the namespace) from the baseline
`argomac-lean/Proof/Privacy/Simulator/OperationalOracleLaw.lean` (`uniform_product`,
`uniform_equiv`, `productFiberEquiv`, `uniform_fiber`). The namespace is
`Kriterion.ArgoMAC.Phase3.Glue`, so a second port of the same baseline file elsewhere in the tree
cannot clash with these names.
-/

import Cryptography.LazyOracle

namespace Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-- A product of uniform finite samples is uniform. -/
theorem uniform_product {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (PMF.uniformOfFintype A).bind (fun a => (PMF.uniformOfFintype B).map (fun b => (a, b))) =
      PMF.uniformOfFintype (A × B) := by
  classical
  letI : DecidableEq A := Classical.decEq A
  letI : DecidableEq B := Classical.decEq B
  apply PMF.ext
  rintro ⟨a, b⟩
  simp only [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply, Prod.mk.injEq,
    ite_and, Fintype.card_prod, Nat.cast_mul]
  have inner (a' : A) :
      (∑' b' : B, if a = a' then if b = b' then (Fintype.card B : ENNReal)⁻¹ else 0 else 0) =
        if a = a' then (Fintype.card B : ENNReal)⁻¹ else 0 := by
    by_cases equal : a = a'
    · simp only [if_pos equal]
      simp_rw [@eq_comm B b]
      exact tsum_ite_eq _ _
    · simp only [if_neg equal, tsum_zero]
  simp_rw [inner]
  simp_rw [mul_ite, mul_zero, @eq_comm A a]
  rw [tsum_ite_eq]
  exact (ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))).symm

/-- A finite bijection preserves the uniform law. -/
theorem uniform_equiv {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (equiv : A ≃ B) : (PMF.uniformOfFintype A).map equiv = PMF.uniformOfFintype B :=
  PMF.uniformOfFintype_map_of_bijective equiv equiv.bijective

/-- A product representation identifies each conditional fiber exactly. -/
def productFiberEquiv {A B C : Type} (equiv : A ≃ B × C) (value : B) :
    C ≃ {a : A // (equiv a).1 = value} where
  toFun c := ⟨equiv.symm (value, c), by simp⟩
  invFun a := (equiv a.val).2
  left_inv c := by simp
  right_inv a := by
    apply Subtype.ext
    apply equiv.injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext a.property.symm rfl

/-- A uniform sample splits into a uniform answer and its full conditional fiber. -/
theorem uniform_fiber {A B C : Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq B]
    [Nonempty A] [Nonempty B] [Nonempty C] (equiv : A ≃ B × C) :
    PMF.uniformOfFintype A =
      (PMF.uniformOfFintype B).bind (fun b =>
        letI : Nonempty {a : A // (equiv a).1 = b} :=
          ⟨productFiberEquiv equiv b (Classical.choice inferInstance)⟩
        (PMF.uniformOfFintype {a : A // (equiv a).1 = b}).map Subtype.val) := by
  classical
  have fiber (b : B) :
      letI : Nonempty {a : A // (equiv a).1 = b} :=
        ⟨productFiberEquiv equiv b (Classical.choice inferInstance)⟩
      (PMF.uniformOfFintype {a : A // (equiv a).1 = b}).map Subtype.val =
        (PMF.uniformOfFintype C).map (fun c => equiv.symm (b, c)) := by
    letI : Nonempty {a : A // (equiv a).1 = b} :=
      ⟨productFiberEquiv equiv b (Classical.choice inferInstance)⟩
    rw [← uniform_equiv (productFiberEquiv equiv b), PMF.map_comp]
    rfl
  simp_rw [fiber]
  have law := congrArg (fun distribution : PMF (B × C) => distribution.map equiv.symm)
    (uniform_product (A := B) (B := C))
  simp only [PMF.map_bind, PMF.map_comp] at law
  exact (law.trans (uniform_equiv equiv.symm)).symm

/-- The first marginal of a uniform product is uniform. -/
theorem uniform_map_fst {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (PMF.uniformOfFintype (A × B)).map Prod.fst = PMF.uniformOfFintype A := by
  have constant (distribution : PMF B) (value : A) :
      distribution.map (fun _ => value) = PMF.pure value := PMF.map_const _ _
  rw [← uniform_product, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, constant]
  exact PMF.bind_pure _

/-- The second marginal of a uniform product is uniform. -/
theorem uniform_map_snd {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (PMF.uniformOfFintype (A × B)).map Prod.snd = PMF.uniformOfFintype B := by
  rw [← uniform_equiv (Equiv.prodComm B A), PMF.map_comp]
  exact uniform_map_fst

end

end Kriterion.ArgoMAC.Phase3.Glue
