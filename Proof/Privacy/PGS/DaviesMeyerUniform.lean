import Construction.ArgoMAC.Exception
import Cryptography.Permutation
import Cryptography.Primitives
import Cryptography.Probability
import Mathlib.Tactic.Linarith

/-!
# Davies–Meyer uniformity on a uniform permutation

Ported verbatim (up to namespace) from an internal research spike (`Spike/DaviesMeyer.lean` and
`Spike/GeneralK.lean`, not part of this repository), which answered
the question "is the Davies–Meyer value `π u ⊕ u` of a uniform permutation exactly uniform, and
what does the `k`-point version cost?".

* one point: exactly uniform, no error term (`daviesMeyer_uniform`);
* `k` points: within `C(k, 2) / 2 ^ 128` total variation of `k` independent uniform blocks
  (`daviesMeyer_tuple_etvDist_le`), with the `k = 2` case an equality (`etvDist_uniformPerm_pair`).

These are ingredient 2 of the E2 gadget-pad hop: the gadget mask of output `j` is the low byte of
a XOR of Davies–Meyer values of the gadget-bucket permutations at the point-layer labels of the
exceptional input, and the hop needs those values to be uniform at a bucket point that the
transcript does not determine.

## Friction notes carried over from the spike's `REPORT.md`

* **Instance-polymorphic `Fintype.card` on set coercions.** `injectiveAssignment_mass` (in
  `Cryptography/Permutation.lean`) states its bound with `Fintype.card ↥s` for a `Fintype ↥s`
  instance that is *not* syntactically the one a local `by simp` produces, so `rw [cardOne] at
  mass` fails with "did not find an occurrence" even though the terms print identically. The fix
  used throughout this file is to prove the card fact quantified over the instance
  (`∀ i : Fintype ↥{u₁, u₂}, @Fintype.card _ i = 2`, discharged via the instance-free `Nat.card`)
  and then `simp only [...] at mass`.
* **`classical` changes `Decidable` instances**, so a `have` about `if … then … else …` will not
  `simp`-rewrite into a goal produced by `PMF.map_apply`. Use `ENNReal.tsum_eq_zero` + `if_neg`
  rather than a simp lemma about the `ite`.
* Minor: `Nat.cast_sub` does not apply in `ℝ≥0∞` (use `ENNReal.natCast_sub`); `mul_le_mul_left'` /
  `mul_le_mul_right'` do not resolve by name in this Mathlib (use `gcongr`); `ENNReal.sub_mul`'s
  side condition is about the *right* factor, `ENNReal.mul_sub`'s about the left.
* **Known duplication, deliberately kept.** The `k = 2` section computes the two-point distance as
  an explicit double sum and gets the *exact* value `1 / #α`; the general-`k` section gets only the
  `≤` (its equality `1 - n.descFactorial k / n ^ k` is inlined in `etvDist_uniformPerm_tuple`, not
  exported). Exporting that equality and deriving `k = 2` from it would delete roughly 90 lines;
  the exact two-point value is used as a tightness check, so the refactor was not taken here.
-/

namespace Kriterion.ArgoMAC.Security.PGS

open scoped ENNReal
open Kriterion.Cryptography

noncomputable section

/-! ### Generic uniform-distribution plumbing -/

/-- Pushing a uniform distribution through a bijection gives the uniform distribution. -/
theorem uniformOfFintype_map_equiv {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (e : A ≃ B) : (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype B := by
  classical
  refine PMF.ext fun b => ?_
  rw [PMF.map_apply]
  rw [tsum_eq_single (e.symm b) (fun a hne => ?_)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · have notHit : b ≠ e a := fun hit => hne (by rw [hit, Equiv.symm_apply_apply])
    simp [notHit]

/-- `a / (b * a) = b⁻¹` for a finite nonzero `a`. -/
theorem div_mul_self_cancel {a b : ℝ≥0∞} (nonzero : a ≠ 0) (finite : a ≠ ⊤) :
    a / (b * a) = b⁻¹ := by
  rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inr finite) (Or.inr nonzero), ← mul_assoc,
    mul_comm a b⁻¹, mul_assoc, ENNReal.mul_inv_cancel nonzero finite, mul_one]

/-! ### The one-point law -/

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- The fibre of "evaluate at `u`" is the set of permutations compatible with one assignment. -/
theorem eval_preimage_singleton (u v : α) :
    (fun π : Equiv.Perm α => π u) ⁻¹' {v} = {π : Equiv.Perm α | ∀ x : ({u} : Set α), π x = v} := by
  ext π
  simp

/-- A uniform permutation evaluated at a fixed point is exactly uniform. -/
theorem uniformPerm_map_eval [Nonempty α] (u : α) :
    (PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => π u) = PMF.uniformOfFintype α := by
  classical
  refine PMF.ext fun v => ?_
  have mass := injectiveAssignment_mass (α := α) ({u} : Set α) (fun _ => v)
    (Function.injective_of_subsingleton _)
  have cardOne : ∀ i : Fintype ({u} : Set α), @Fintype.card _ i = 1 := fun i =>
    (@Fintype.card_eq_one_iff _ i).mpr ⟨⟨u, rfl⟩, by rintro ⟨x, hx⟩; exact Subtype.ext hx⟩
  simp only [cardOne] at mass
  have fibre : ((PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => π u)) v =
      (PMF.uniformOfFintype (Equiv.Perm α)).toOuterMeasure
        {π : Equiv.Perm α | ∀ x : ({u} : Set α), π x = v} := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      eval_preimage_singleton u v]
  rw [fibre, mass, PMF.uniformOfFintype_apply]
  have pos : 0 < Fintype.card α := Fintype.card_pos
  rw [← Nat.mul_factorial_pred pos.ne', Nat.cast_mul]
  exact div_mul_self_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (ENNReal.natCast_ne_top _)

/-! ### Davies–Meyer at one point -/

/-- XOR with a fixed block is a bijection of blocks. -/
def xorEquiv (u : Block) : Block ≃ Block where
  toFun value := value ^^^ u
  invFun value := value ^^^ u
  left_inv value := by simp [BitVec.xor_assoc]
  right_inv value := by simp [BitVec.xor_assoc]

/-- **Term 2 at one point is zero.** The Davies–Meyer value of a uniform permutation at a fixed
input is exactly uniform, with no error term at all. -/
theorem daviesMeyer_uniform (u : Block) :
    (PMF.uniformOfFintype (Equiv Block Block)).map (fun π => π u ^^^ u) =
      PMF.uniformOfFintype Block := by
  have step : (fun π : Equiv.Perm Block => π u ^^^ u) = (xorEquiv u) ∘ (fun π => π u) := rfl
  rw [step, ← PMF.map_comp, uniformPerm_map_eval u]
  exact uniformOfFintype_map_equiv (xorEquiv u)

/-- The same statement in the challenge library's own spelling of Davies–Meyer. -/
theorem daviesMeyer_uniform' (u : Block) :
    (PMF.uniformOfFintype (Equiv Block Block)).map (fun π => daviesMeyer π u) =
      PMF.uniformOfFintype Block :=
  daviesMeyer_uniform u


/-! ### Cardinality of `Block` -/

/-- The block space has `2 ^ 128` elements. -/
theorem card_block : Fintype.card Block = 2 ^ 128 := by
  rw [Fintype.card_congr (BitVec.equivFin (m := 128)).toEquiv]
  exact Fintype.card_fin _

/-! ### The two-point law -/

/-- The assignment sending `u₁ ↦ v₁` and `u₂ ↦ v₂`, as a function on the two-element input set. -/
def pairAssign (u₁ u₂ v₁ v₂ : α) : (({u₁, u₂} : Set α)) → α :=
  fun x => if (x : α) = u₁ then v₁ else v₂

omit [Fintype α] in
/-- The two-point assignment is injective when both inputs and both outputs are distinct. -/
theorem pairAssign_injective {u₁ u₂ v₁ v₂ : α} (hu : u₁ ≠ u₂) (hv : v₁ ≠ v₂) :
    Function.Injective (pairAssign u₁ u₂ v₁ v₂) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ same
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  simp only [pairAssign] at same
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp_all [hu.symm, hv.symm]

omit [Fintype α] [DecidableEq α] in
/-- A two-element input set has cardinality two, for any `Fintype` instance on it. -/
theorem card_pairSet {u₁ u₂ : α} (hu : u₁ ≠ u₂) :
    ∀ i : Fintype (({u₁, u₂} : Set α)), @Fintype.card _ i = 2 := fun i => by
  rw [← @Nat.card_eq_fintype_card _ i, Nat.card_coe_set_eq, Set.ncard_pair hu]

omit [Fintype α] in
/-- The fibre of the two-point evaluation map over a pair of outputs. -/
theorem evalPair_preimage_singleton {u₁ u₂ : α} (hu : u₁ ≠ u₂) (v₁ v₂ : α) :
    (fun π : Equiv.Perm α => (π u₁, π u₂)) ⁻¹' {(v₁, v₂)} =
      {π : Equiv.Perm α | ∀ x : (({u₁, u₂} : Set α)), π x = pairAssign u₁ u₂ v₁ v₂ x} := by
  have hne : u₂ ≠ u₁ := hu.symm
  ext π
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨first, second⟩ ⟨x, hx⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simp [pairAssign, first]
    · simp [pairAssign, hne, second]
  · intro compat
    have first := compat ⟨u₁, by simp⟩
    have second := compat ⟨u₂, by simp⟩
    simp only [pairAssign, if_neg hne] at first second
    exact ⟨first, second⟩

/-- The exact two-point law of a uniform permutation: uniform on ordered pairs of distinct
outputs, and zero on the diagonal. -/
theorem uniformPerm_pair_apply [Nonempty α] {u₁ u₂ : α} (hu : u₁ ≠ u₂) (v₁ v₂ : α) :
    ((PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => (π u₁, π u₂))) (v₁, v₂) =
      if v₁ = v₂ then 0
      else ((Fintype.card α : ℝ≥0∞) * ((Fintype.card α - 1 : ℕ) : ℝ≥0∞))⁻¹ := by
  classical
  by_cases hv : v₁ = v₂
  · subst hv
    rw [if_pos rfl, PMF.map_apply]
    refine ENNReal.tsum_eq_zero.mpr fun π => ?_
    have distinct : ((v₁, v₁) : α × α) ≠ (π u₁, π u₂) := by
      intro hit
      exact hu (π.injective ((congrArg Prod.fst hit).symm.trans (congrArg Prod.snd hit)))
    exact if_neg distinct
  · rw [if_neg hv]
    have mass := injectiveAssignment_mass (α := α) (({u₁, u₂} : Set α))
      (pairAssign u₁ u₂ v₁ v₂) (pairAssign_injective hu hv)
    simp only [card_pairSet hu] at mass
    have fibre : ((PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => (π u₁, π u₂))) (v₁, v₂) =
        (PMF.uniformOfFintype (Equiv.Perm α)).toOuterMeasure
          {π : Equiv.Perm α | ∀ x : (({u₁, u₂} : Set α)), π x = pairAssign u₁ u₂ v₁ v₂ x} := by
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
        evalPair_preimage_singleton hu v₁ v₂]
    have twoLe : 2 ≤ Fintype.card α := Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨u₁, u₂, hu⟩⟩
    have posOne : Fintype.card α ≠ 0 := by omega
    have posTwo : Fintype.card α - 1 ≠ 0 := by omega
    have expand : (Fintype.card α).factorial =
        Fintype.card α * ((Fintype.card α - 1) * (Fintype.card α - 2).factorial) := by
      have shift : Fintype.card α - 1 - 1 = Fintype.card α - 2 := by omega
      rw [← shift, Nat.mul_factorial_pred posTwo, Nat.mul_factorial_pred posOne]
    rw [fibre, mass, expand, Nat.cast_mul, Nat.cast_mul, ← mul_assoc]
    exact div_mul_self_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (ENNReal.natCast_ne_top _)

/-- **The two-point birthday term.** The joint law of a uniform permutation at two distinct inputs
is at total-variation distance exactly `1 / #α` from the product of two independent uniforms. -/
theorem etvDist_uniformPerm_pair [Nonempty α] {u₁ u₂ : α} (hu : u₁ ≠ u₂) :
    ((PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => (π u₁, π u₂))).etvDist
        (PMF.uniformOfFintype (α × α)) = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  classical
  have twoLe : 2 ≤ Fintype.card α := Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨u₁, u₂, hu⟩⟩
  set N : ℝ≥0∞ := (Fintype.card α : ℝ≥0∞) with hNdef
  set D : ℝ≥0∞ := ((Fintype.card α - 1 : ℕ) : ℝ≥0∞) with hDdef
  have hN0 : N ≠ 0 := by
    simp only [hNdef, ne_eq, Nat.cast_eq_zero]
    omega
  have hNtop : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have hD0 : D ≠ 0 := by
    simp only [hDdef, ne_eq, Nat.cast_eq_zero]
    omega
  have hDtop : D ≠ ⊤ := ENNReal.natCast_ne_top _
  have hDN : D ≤ N := by
    simp only [hDdef, hNdef, Nat.cast_le]
    omega
  have hsum : D + 1 = N := by
    simp only [hDdef, hNdef]
    rw [← Nat.cast_one (R := ℝ≥0∞), ← Nat.cast_add]
    congr 1
    omega
  -- pointwise values of the two distributions
  have ideal : ∀ x : α × α, (PMF.uniformOfFintype (α × α)) x = (N * N)⁻¹ := by
    intro x
    rw [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  have real := uniformPerm_pair_apply hu
  -- the pointwise absolute difference
  have term : ∀ v₁ v₂ : α,
      ENNReal.absDiff (((PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => (π u₁, π u₂)))
        (v₁, v₂)) ((PMF.uniformOfFintype (α × α)) (v₁, v₂)) =
      if v₁ = v₂ then (N * N)⁻¹ else (N * D)⁻¹ - (N * N)⁻¹ := by
    intro v₁ v₂
    rw [real v₁ v₂, ideal]
    by_cases hv : v₁ = v₂
    · rw [if_pos hv, if_pos hv, ENNReal.absDiff, zero_tsub, tsub_zero, zero_add]
    · rw [if_neg hv, if_neg hv, ENNReal.absDiff,
        tsub_eq_zero_of_le (ENNReal.inv_le_inv.mpr (by gcongr : N * D ≤ N * N)), add_zero]
  -- inverse arithmetic
  have invProd : (N * N)⁻¹ = N⁻¹ * N⁻¹ := ENNReal.mul_inv (Or.inl hN0) (Or.inl hNtop)
  have selfCancel : N * N⁻¹ = 1 := ENNReal.mul_inv_cancel hN0 hNtop
  have firstTerm : N * (N * N)⁻¹ = N⁻¹ := by
    rw [invProd, ← mul_assoc, selfCancel, one_mul]
  have secondTerm : N * D * ((N * D)⁻¹ - (N * N)⁻¹) = N⁻¹ := by
    rw [ENNReal.mul_sub (fun _ _ => ENNReal.mul_ne_top hNtop hDtop),
      ENNReal.mul_inv_cancel (mul_ne_zero hN0 hD0) (ENNReal.mul_ne_top hNtop hDtop), invProd]
    have reduce : N * D * (N⁻¹ * N⁻¹) = D * N⁻¹ := by
      calc N * D * (N⁻¹ * N⁻¹) = (N * N⁻¹) * (D * N⁻¹) := by ring
        _ = D * N⁻¹ := by rw [selfCancel, one_mul]
    rw [reduce]
    refine ENNReal.sub_eq_of_eq_add (by finiteness) ?_
    calc (1 : ℝ≥0∞) = N * N⁻¹ := selfCancel.symm
      _ = (1 + D) * N⁻¹ := by rw [add_comm 1 D, hsum]
      _ = N⁻¹ + D * N⁻¹ := by rw [add_mul, one_mul]
  -- the full sum
  have total : (∑' x : α × α,
      ENNReal.absDiff (((PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => (π u₁, π u₂))) x)
        ((PMF.uniformOfFintype (α × α)) x)) = 2 * N⁻¹ := by
    rw [tsum_fintype, Fintype.sum_prod_type]
    have inner : ∀ v₁ : α, (∑ v₂ : α,
        ENNReal.absDiff (((PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => (π u₁, π u₂)))
          (v₁, v₂)) ((PMF.uniformOfFintype (α × α)) (v₁, v₂))) =
        (N * N)⁻¹ + D * ((N * D)⁻¹ - (N * N)⁻¹) := by
      intro v₁
      rw [Finset.sum_congr rfl (fun v₂ _ => term v₁ v₂), Finset.sum_ite, Finset.sum_const,
        Finset.sum_const]
      have cardPos : (Finset.univ.filter (fun v₂ => v₁ = v₂)).card = 1 := by
        rw [Finset.filter_eq Finset.univ v₁]
        simp
      have cardAll := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset α)) (p := fun v₂ => v₁ = v₂)
      rw [Finset.card_univ] at cardAll
      have cardNeg : (Finset.univ.filter (fun v₂ => ¬ v₁ = v₂)).card = Fintype.card α - 1 := by
        omega
      rw [cardPos, cardNeg, one_nsmul, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun v₁ _ => inner v₁), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_add, ← mul_assoc, firstTerm, secondTerm, two_mul]
  simp only [PMF.etvDist, total]
  rw [mul_comm, mul_div_assoc, ENNReal.div_self two_ne_zero (by finiteness), mul_one]

/-- XOR by a fixed pair of blocks is a bijection of block pairs. -/
def xorPairEquiv (u₁ u₂ : Block) : Block × Block ≃ Block × Block :=
  (xorEquiv u₁).prodCongr (xorEquiv u₂)

/-- **The `k = 2` Davies–Meyer birthday bound.** At two distinct inputs the pair of Davies–Meyer
values of a uniform permutation is within `2 · (2 - 1) / 2 / 2 ^ 128 = 1 / 2 ^ 128` total variation
of two independent uniform blocks. -/
theorem daviesMeyer_pair_etvDist_le {u₁ u₂ : Block} (hu : u₁ ≠ u₂) :
    ((PMF.uniformOfFintype (Equiv Block Block)).map
        (fun π => (π u₁ ^^^ u₁, π u₂ ^^^ u₂))).etvDist (PMF.uniformOfFintype (Block × Block)) ≤
      1 / 2 ^ 128 := by
  have factor : (fun π : Equiv.Perm Block => (π u₁ ^^^ u₁, π u₂ ^^^ u₂)) =
      (xorPairEquiv u₁ u₂) ∘ (fun π => (π u₁, π u₂)) := rfl
  have invariant : (PMF.uniformOfFintype (Block × Block)).map (xorPairEquiv u₁ u₂) =
      PMF.uniformOfFintype (Block × Block) := uniformOfFintype_map_equiv (xorPairEquiv u₁ u₂)
  calc ((PMF.uniformOfFintype (Equiv Block Block)).map
        (fun π => (π u₁ ^^^ u₁, π u₂ ^^^ u₂))).etvDist (PMF.uniformOfFintype (Block × Block))
      = (((PMF.uniformOfFintype (Equiv Block Block)).map
          (fun π => (π u₁, π u₂))).map (xorPairEquiv u₁ u₂)).etvDist
            ((PMF.uniformOfFintype (Block × Block)).map (xorPairEquiv u₁ u₂)) := by
        rw [invariant, factor, PMF.map_comp]
    _ ≤ ((PMF.uniformOfFintype (Equiv Block Block)).map (fun π => (π u₁, π u₂))).etvDist
          (PMF.uniformOfFintype (Block × Block)) := by
        simpa only [PMF.monad_map_eq_map] using
          PMF.etvDist_map_le (xorPairEquiv u₁ u₂)
            ((PMF.uniformOfFintype (Equiv Block Block)).map (fun π => (π u₁, π u₂)))
            (PMF.uniformOfFintype (Block × Block))
    _ = (Fintype.card Block : ℝ≥0∞)⁻¹ := etvDist_uniformPerm_pair hu
    _ = 1 / 2 ^ 128 := by rw [card_block, one_div]; norm_num

/-! ### M0 fintype spike at the planned `FixedIndex` size

The design review asks whether the `Fintype`/`Finite`/`uniformOfFintype` chain elaborates at
`FixedIndex := Fin (2 ^ 28)` without enumerating the index type. Each declaration below is
accepted in milliseconds: instance synthesis is structural (`Pi.fintype`, `Fintype.ofEquiv`) and
never evaluates a cardinality. -/

/-- The planned index type is a `Fintype` by inference. -/
example : Fintype (Fin (2 ^ 28)) := inferInstance

/-- The planned index type is `Finite` by inference. -/
example : Finite (Fin (2 ^ 28)) := inferInstance

/-- A `2 ^ 28`-indexed permutation oracle over `Block` is a `Fintype` by inference
(`Fintype.ofEquiv` over `Pi.fintype`). -/
example : Fintype (PermutationOracle (Fin (2 ^ 28)) Block) := inferInstance

/-- The same oracle type is `Finite`, and `Fintype.ofFinite` recovers a `Fintype` from it. -/
example : Fintype (PermutationOracle (Fin (2 ^ 28)) Block) := Fintype.ofFinite _

/-- The uniform permutation tape at the planned index size elaborates. -/
example : PMF (PermutationOracle (Fin (2 ^ 28)) Block) :=
  uniformPermutationTape (Fin (2 ^ 28)) Block

/-- `PMF.uniformOfFintype` at the planned index size elaborates. -/
example : PMF (PermutationOracle (Fin (2 ^ 28)) Block) :=
  PMF.uniformOfFintype (PermutationOracle (Fin (2 ^ 28)) Block)

/-- Davies–Meyer's one-point uniformity applies verbatim to any permutation drawn from a
`2 ^ 28`-indexed tape, one index at a time. -/
example (index : Fin (2 ^ 28)) (u : Block) :
    ((uniformPermutationTape (Fin (2 ^ 28)) Block).map
        (fun oracle => oracle.permutation index)).map (fun π => daviesMeyer π u) =
      ((uniformPermutationTape (Fin (2 ^ 28)) Block).map
        (fun oracle => oracle.permutation index)).map (fun π => π u ^^^ u) := rfl


/-! ### A natural-number birthday inequality -/

/-- `n^k` overshoots the number of injective `k`-tuples by at most `C(k,2)·n^(k-1)`, in the
multiplied-out form that avoids truncated subtraction. -/
theorem descFactorial_pow_bound (n : ℕ) :
    ∀ k : ℕ, k ≤ n → n * n ^ k ≤ n * n.descFactorial k + (k.choose 2) * n ^ k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := Nat.le_of_succ_le hk
    have step : n * (n * n ^ k) ≤ n * (n * n.descFactorial k + (k.choose 2) * n ^ k) :=
      Nat.mul_le_mul_left n (ih hkn)
    have split : n * n.descFactorial k = n.descFactorial (k + 1) + k * n.descFactorial k := by
      rw [Nat.descFactorial_succ]
      have : n - k + k = n := Nat.sub_add_cancel hkn
      calc n * n.descFactorial k = (n - k + k) * n.descFactorial k := by rw [this]
        _ = (n - k) * n.descFactorial k + k * n.descFactorial k := by rw [add_mul]
    have descLe : n.descFactorial k ≤ n ^ k := Nat.descFactorial_le_pow n k
    have choose : (k + 1).choose 2 = k.choose 2 + k := by
      simp [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
    calc n * n ^ (k + 1) = n * (n * n ^ k) := by ring
      _ ≤ n * (n * n.descFactorial k + (k.choose 2) * n ^ k) := step
      _ = n * (n.descFactorial (k + 1) + k * n.descFactorial k) + (k.choose 2) * (n * n ^ k) := by
          rw [split]; ring
      _ ≤ n * (n.descFactorial (k + 1) + k * n ^ k) + (k.choose 2) * (n * n ^ k) := by
          have : k * n.descFactorial k ≤ k * n ^ k := Nat.mul_le_mul_left k descLe
          have := Nat.add_le_add_left this (n.descFactorial (k + 1))
          exact Nat.add_le_add_right (Nat.mul_le_mul_left n this) _
      _ = n * n.descFactorial (k + 1) + (k.choose 2 + k) * n ^ (k + 1) := by ring
      _ = n * n.descFactorial (k + 1) + ((k + 1).choose 2) * n ^ (k + 1) := by rw [choose]

/-! ### The `k`-point law of a uniform permutation -/

variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

omit [Fintype α] [DecidableEq α] in
/-- The `k`-point fibre is the set of permutations compatible with one injective assignment. -/
theorem evalTuple_preimage_singleton {u : Fin k → α} (hu : Function.Injective u)
    (v : Fin k → α) :
    (fun π : Equiv.Perm α => fun i => π (u i)) ⁻¹' {v} =
      {π : Equiv.Perm α | ∀ x : (Set.range u),
        π x = v ((Equiv.ofInjective u hu).symm x)} := by
  ext π
  constructor
  · intro hit x
    have hx : ((Equiv.ofInjective u hu) ((Equiv.ofInjective u hu).symm x) : α) = (x : α) := by
      rw [Equiv.apply_symm_apply]
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hit
    calc π (x : α) = π (u ((Equiv.ofInjective u hu).symm x)) := by rw [← hx]; rfl
      _ = v ((Equiv.ofInjective u hu).symm x) := congrFun hit _
  · intro compat
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    funext i
    have hit := compat ⟨u i, Set.mem_range_self i⟩
    have key : (Equiv.ofInjective u hu).symm ⟨u i, Set.mem_range_self i⟩ = i := by
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext rfl
    rw [key] at hit
    exact hit

omit [Fintype α] [DecidableEq α] in
/-- Any `Fintype` instance on the range of an injective `k`-tuple counts `k` elements. -/
theorem card_rangeSet {u : Fin k → α} (hu : Function.Injective u) :
    ∀ i : Fintype (Set.range u), @Fintype.card _ i = k := fun i => by
  rw [← @Nat.card_eq_fintype_card _ i, Nat.card_congr (Equiv.ofInjective u hu).symm,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The exact `k`-point law of a uniform permutation: uniform on injective `k`-tuples, zero
elsewhere. -/
theorem uniformPerm_tuple_apply [Nonempty α] {u : Fin k → α} (hu : Function.Injective u)
    (v : Fin k → α) :
    ((PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => fun i => π (u i))) v =
      if Function.Injective v then
        ((Fintype.card α - k).factorial : ℝ≥0∞) / ((Fintype.card α).factorial : ℝ≥0∞)
      else 0 := by
  classical
  by_cases hv : Function.Injective v
  · rw [if_pos hv]
    have assignInj : Function.Injective
        (fun x : (Set.range u) => v ((Equiv.ofInjective u hu).symm x)) :=
      hv.comp (Equiv.ofInjective u hu).symm.injective
    have mass := injectiveAssignment_mass (α := α) (Set.range u)
      (fun x => v ((Equiv.ofInjective u hu).symm x)) assignInj
    simp only [card_rangeSet hu] at mass
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      evalTuple_preimage_singleton hu v]
    exact mass
  · rw [if_neg hv, PMF.map_apply]
    refine ENNReal.tsum_eq_zero.mpr fun π => ?_
    have distinct : v ≠ fun i => π (u i) := by
      intro hit
      exact hv (hit ▸ (π.injective.comp hu))
    exact if_neg distinct

/-! ### The `k`-point birthday bound -/

/-- **The `k`-point birthday term.** The joint law of a uniform permutation at `k` distinct inputs
is within `k(k-1)/2 / #α` total variation of `k` independent uniforms. -/
theorem etvDist_uniformPerm_tuple [Nonempty α] {u : Fin k → α} (hu : Function.Injective u) :
    ((PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => fun i => π (u i))).etvDist
        (PMF.uniformOfFintype (Fin k → α)) ≤
      (k.choose 2 : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) := by
  classical
  have hkn : k ≤ Fintype.card α := by
    have bound := Fintype.card_le_of_injective u hu
    simpa only [Fintype.card_fin] using bound
  have hn0 : Fintype.card α ≠ 0 := Fintype.card_ne_zero
  set I : ℕ := (Fintype.card α).descFactorial k with hIdef
  set T : ℕ := Fintype.card α ^ k with hTdef
  have hIT : I ≤ T := Nat.descFactorial_le_pow _ _
  have hI0 : I ≠ 0 := by
    simp only [hIdef, ne_eq, Nat.descFactorial_eq_zero_iff_lt]
    omega
  have hT0 : T ≠ 0 := by
    simp only [hTdef]
    exact pow_ne_zero _ hn0
  set N : ℝ≥0∞ := (Fintype.card α : ℝ≥0∞) with hNdef
  set Q : ℝ≥0∞ := ((T : ℕ) : ℝ≥0∞)⁻¹ with hQdef
  set R : ℝ≥0∞ :=
    ((Fintype.card α - k).factorial : ℝ≥0∞) / ((Fintype.card α).factorial : ℝ≥0∞) with hRdef
  have hN0 : N ≠ 0 := by simp [hNdef]
  have hNtop : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have hTcast0 : ((T : ℕ) : ℝ≥0∞) ≠ 0 := by simpa using hT0
  have hTtop : ((T : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hIcast0 : ((I : ℕ) : ℝ≥0∞) ≠ 0 := by simpa using hI0
  have hItop : ((I : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  -- the ideal law
  have ideal : ∀ v : Fin k → α, (PMF.uniformOfFintype (Fin k → α)) v = Q := by
    intro v
    rw [PMF.uniformOfFintype_apply, Fintype.card_pi_const, hQdef, hTdef]
  -- counting injective tuples
  have cardInj : (Finset.univ.filter (fun v : Fin k → α => Function.Injective v)).card = I := by
    rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) α),
      Fintype.card_embedding_eq, Fintype.card_fin]
  have cardAll := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k → α))) (p := fun v : Fin k → α => Function.Injective v)
  rw [Finset.card_univ, Fintype.card_pi_const, ← hTdef, cardInj] at cardAll
  have cardNotInj :
      (Finset.univ.filter (fun v : Fin k → α => ¬ Function.Injective v)).card = T - I := by
    omega
  -- normalisation gives the value on the support without touching factorials
  have normalize : ((I : ℕ) : ℝ≥0∞) * R = 1 := by
    have total := ((PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => fun i => π (u i))).tsum_coe
    rw [tsum_fintype, Finset.sum_congr rfl (fun v _ => uniformPerm_tuple_apply hu v),
      Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_zero, add_zero, cardInj,
      nsmul_eq_mul] at total
    exact total
  have hRvalue : R = ((I : ℕ) : ℝ≥0∞)⁻¹ := by
    calc R = 1 * R := (one_mul R).symm
      _ = (((I : ℕ) : ℝ≥0∞)⁻¹ * ((I : ℕ) : ℝ≥0∞)) * R := by
          rw [ENNReal.inv_mul_cancel hIcast0 hItop]
      _ = ((I : ℕ) : ℝ≥0∞)⁻¹ * (((I : ℕ) : ℝ≥0∞) * R) := by rw [mul_assoc]
      _ = ((I : ℕ) : ℝ≥0∞)⁻¹ := by rw [normalize, mul_one]
  have hQR : Q ≤ R := by
    rw [hRvalue, hQdef]
    exact ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr hIT)
  -- pointwise absolute difference
  have term : ∀ v : Fin k → α,
      ENNReal.absDiff (((PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => fun i => π (u i))) v)
        ((PMF.uniformOfFintype (Fin k → α)) v) =
      if Function.Injective v then R - Q else Q := by
    intro v
    rw [uniformPerm_tuple_apply hu v, ideal]
    by_cases hv : Function.Injective v
    · rw [if_pos hv, if_pos hv, ENNReal.absDiff, tsub_eq_zero_of_le hQR, add_zero]
    · rw [if_neg hv, if_neg hv, ENNReal.absDiff, zero_tsub, tsub_zero, zero_add]
  -- the total sum
  have split₁ : ((I : ℕ) : ℝ≥0∞) * (R - Q) = 1 - ((I : ℕ) : ℝ≥0∞) * Q := by
    rw [ENNReal.mul_sub (fun _ _ => hItop), normalize]
  have hQtop : Q ≠ ⊤ := by
    rw [hQdef]
    exact ENNReal.inv_ne_top.mpr hTcast0
  have split₂ : ((T - I : ℕ) : ℝ≥0∞) * Q = 1 - ((I : ℕ) : ℝ≥0∞) * Q := by
    rw [ENNReal.natCast_sub, ENNReal.sub_mul (fun _ _ => hQtop), hQdef,
      ENNReal.mul_inv_cancel hTcast0 hTtop]
  have total : (∑' v : Fin k → α,
      ENNReal.absDiff (((PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => fun i => π (u i))) v)
        ((PMF.uniformOfFintype (Fin k → α)) v)) = 2 * (1 - ((I : ℕ) : ℝ≥0∞) * Q) := by
    rw [tsum_fintype, Finset.sum_congr rfl (fun v _ => term v), Finset.sum_ite, Finset.sum_const,
      Finset.sum_const, cardInj, cardNotInj, nsmul_eq_mul, nsmul_eq_mul, split₁, split₂,
      two_mul]
  -- the birthday bound
  have key : Fintype.card α * T ≤ Fintype.card α * I + (k.choose 2) * T :=
    descFactorial_pow_bound (Fintype.card α) k hkn
  have keyCast : N * ((T : ℕ) : ℝ≥0∞) ≤
      N * ((I : ℕ) : ℝ≥0∞) + ((k.choose 2 : ℕ) : ℝ≥0∞) * ((T : ℕ) : ℝ≥0∞) := by
    have := Nat.cast_le (α := ℝ≥0∞).mpr key
    push_cast at this
    simpa [hNdef] using this
  have invProd : (N * ((T : ℕ) : ℝ≥0∞))⁻¹ = N⁻¹ * ((T : ℕ) : ℝ≥0∞)⁻¹ :=
    ENNReal.mul_inv (Or.inl hN0) (Or.inl hNtop)
  have bound : (1 : ℝ≥0∞) ≤ ((k.choose 2 : ℕ) : ℝ≥0∞) / N + ((I : ℕ) : ℝ≥0∞) * Q := by
    calc (1 : ℝ≥0∞) = (N * ((T : ℕ) : ℝ≥0∞)) * (N * ((T : ℕ) : ℝ≥0∞))⁻¹ :=
          (ENNReal.mul_inv_cancel (mul_ne_zero hN0 hTcast0)
            (ENNReal.mul_ne_top hNtop hTtop)).symm
      _ ≤ (N * ((I : ℕ) : ℝ≥0∞) + ((k.choose 2 : ℕ) : ℝ≥0∞) * ((T : ℕ) : ℝ≥0∞)) *
            (N * ((T : ℕ) : ℝ≥0∞))⁻¹ := by
          gcongr
      _ = ((k.choose 2 : ℕ) : ℝ≥0∞) / N + ((I : ℕ) : ℝ≥0∞) * Q := by
          rw [invProd, add_mul, hQdef, div_eq_mul_inv]
          have left : N * ((I : ℕ) : ℝ≥0∞) * (N⁻¹ * ((T : ℕ) : ℝ≥0∞)⁻¹) =
              ((I : ℕ) : ℝ≥0∞) * ((T : ℕ) : ℝ≥0∞)⁻¹ := by
            calc N * ((I : ℕ) : ℝ≥0∞) * (N⁻¹ * ((T : ℕ) : ℝ≥0∞)⁻¹)
                = (N * N⁻¹) * (((I : ℕ) : ℝ≥0∞) * ((T : ℕ) : ℝ≥0∞)⁻¹) := by ring
              _ = ((I : ℕ) : ℝ≥0∞) * ((T : ℕ) : ℝ≥0∞)⁻¹ := by
                  rw [ENNReal.mul_inv_cancel hN0 hNtop, one_mul]
          have right : ((k.choose 2 : ℕ) : ℝ≥0∞) * ((T : ℕ) : ℝ≥0∞) *
              (N⁻¹ * ((T : ℕ) : ℝ≥0∞)⁻¹) = ((k.choose 2 : ℕ) : ℝ≥0∞) * N⁻¹ := by
            calc ((k.choose 2 : ℕ) : ℝ≥0∞) * ((T : ℕ) : ℝ≥0∞) * (N⁻¹ * ((T : ℕ) : ℝ≥0∞)⁻¹)
                = (((T : ℕ) : ℝ≥0∞) * ((T : ℕ) : ℝ≥0∞)⁻¹) *
                    (((k.choose 2 : ℕ) : ℝ≥0∞) * N⁻¹) := by ring
              _ = ((k.choose 2 : ℕ) : ℝ≥0∞) * N⁻¹ := by
                  rw [ENNReal.mul_inv_cancel hTcast0 hTtop, one_mul]
          rw [left, right, add_comm]
  simp only [PMF.etvDist, total]
  rw [mul_comm, mul_div_assoc, ENNReal.div_self two_ne_zero (by finiteness), mul_one]
  exact tsub_le_iff_right.mpr bound

/-- XOR by a fixed `k`-tuple of blocks is a bijection of block tuples. -/
def xorTupleEquiv (u : Fin k → Block) : (Fin k → Block) ≃ (Fin k → Block) :=
  Equiv.piCongrRight (fun i => xorEquiv (u i))

/-- **The `k`-point Davies–Meyer birthday bound.** At `k` distinct inputs the tuple of
Davies–Meyer values of a uniform permutation is within `k(k-1)/2 / 2 ^ 128` total variation of `k`
independent uniform blocks. -/
theorem daviesMeyer_tuple_etvDist_le {u : Fin k → Block} (hu : Function.Injective u) :
    ((PMF.uniformOfFintype (Equiv Block Block)).map
        (fun π => fun i => π (u i) ^^^ u i)).etvDist (PMF.uniformOfFintype (Fin k → Block)) ≤
      (k.choose 2 : ℝ≥0∞) / 2 ^ 128 := by
  have factor : (fun π : Equiv.Perm Block => fun i => π (u i) ^^^ u i) =
      (xorTupleEquiv u) ∘ (fun π => fun i => π (u i)) := rfl
  have invariant : (PMF.uniformOfFintype (Fin k → Block)).map (xorTupleEquiv u) =
      PMF.uniformOfFintype (Fin k → Block) := uniformOfFintype_map_equiv (xorTupleEquiv u)
  calc ((PMF.uniformOfFintype (Equiv Block Block)).map
        (fun π => fun i => π (u i) ^^^ u i)).etvDist (PMF.uniformOfFintype (Fin k → Block))
      = (((PMF.uniformOfFintype (Equiv Block Block)).map
          (fun π => fun i => π (u i))).map (xorTupleEquiv u)).etvDist
            ((PMF.uniformOfFintype (Fin k → Block)).map (xorTupleEquiv u)) := by
        rw [invariant, factor, PMF.map_comp]
    _ ≤ ((PMF.uniformOfFintype (Equiv Block Block)).map
          (fun π => fun i => π (u i))).etvDist (PMF.uniformOfFintype (Fin k → Block)) := by
        simpa only [PMF.monad_map_eq_map] using
          PMF.etvDist_map_le (xorTupleEquiv u)
            ((PMF.uniformOfFintype (Equiv Block Block)).map (fun π => fun i => π (u i)))
            (PMF.uniformOfFintype (Fin k → Block))
    _ ≤ (k.choose 2 : ℝ≥0∞) / (Fintype.card Block : ℝ≥0∞) := etvDist_uniformPerm_tuple hu
    _ = (k.choose 2 : ℝ≥0∞) / 2 ^ 128 := by rw [card_block]; norm_num

/-- Sanity check that the general bound is not vacuous and is tight at the bottom: at `k = 1` the
bound is `0`, so it collapses back to the exact one-point uniformity of `daviesMeyer_uniform`. -/
example (u : Block) :
    (PMF.uniformOfFintype (Equiv Block Block)).map (fun π => fun _ : Fin 1 => π u ^^^ u) =
      PMF.uniformOfFintype (Fin 1 → Block) := by
  have inj : Function.Injective (fun _ : Fin 1 => u) := by
    intro i j _
    exact Subsingleton.elim i j
  have bound := daviesMeyer_tuple_etvDist_le inj
  norm_num at bound
  exact bound

/-! ### XOR with a uniform block, and the low byte

These are the small pieces the downstream PGS privacy tasks ask of this module: XOR by any fixed
block (or by a uniform independent block) leaves the uniform law on `Block` alone, and truncating a
uniform block to its low byte gives a uniform byte, with no rounding loss because
`2 ^ 128 = 2 ^ 8 * 2 ^ 120` exactly.
-/

/-- The first coordinate of a uniform product law is uniform. -/
theorem uniformOfFintype_map_fst {First Second : Type*}
    [Fintype First] [Nonempty First] [Fintype Second] [Nonempty Second] :
    (PMF.uniformOfFintype (First × Second)).map Prod.fst = PMF.uniformOfFintype First := by
  classical
  apply PMF.ext
  intro output
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod]
  rw [ENNReal.tsum_prod']
  push_cast
  rw [ENNReal.mul_inv] <;> try simp [Fintype.card_ne_zero]
  rw [mul_left_comm, ENNReal.mul_inv_cancel]
  · simp
  · exact_mod_cast Fintype.card_ne_zero
  · simp

/-- XOR by a fixed block preserves the uniform law on blocks. -/
theorem uniform_xor_const (u : Block) :
    (PMF.uniformOfFintype Block).map (fun value => value ^^^ u) = PMF.uniformOfFintype Block :=
  uniformOfFintype_map_equiv (xorEquiv u)

/-- XOR by a fixed block on the other side preserves the uniform law on blocks. -/
theorem uniform_const_xor (u : Block) :
    (PMF.uniformOfFintype Block).map (fun value => u ^^^ value) = PMF.uniformOfFintype Block := by
  have swap : (fun value : Block => u ^^^ value) = (fun value : Block => value ^^^ u) := by
    funext value; exact BitVec.xor_comm u value
  rw [swap]
  exact uniform_xor_const u

/-- Masking anything by an independent uniform block gives a uniform block: the pad law does not
depend on the value being masked. This is the shape the PGS pad hops use. -/
theorem uniform_pad_xor {Value : Type*} (value : Value) (mask : Value → Block) :
    (PMF.uniformOfFintype Block).map (fun pad => mask value ^^^ pad) =
      PMF.uniformOfFintype Block :=
  uniform_const_xor (mask value)

/-- This equivalence splits a block into its low byte and its remaining 120 bits. -/
def blockLowByteEquiv : Block ≃ BitVec 8 × BitVec 120 where
  toFun block := (BitVec.ofNat 8 block.toNat, BitVec.ofNat 120 (block.toNat / 256))
  invFun pair := BitVec.ofNat 128 (pair.1.toNat + 256 * pair.2.toNat)
  left_inv block := by
    have byteWidth : (2 : Nat) ^ 8 = 256 := by norm_num
    have bound : block.toNat < 2 ^ 128 := block.isLt
    have divLt : block.toNat / 256 < 2 ^ 120 := by omega
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, byteWidth]
    rw [Nat.mod_eq_of_lt divLt, Nat.mod_add_div, Nat.mod_eq_of_lt bound]
  right_inv pair := by
    obtain ⟨low, high⟩ := pair
    have byteWidth : (2 : Nat) ^ 8 = 256 := by norm_num
    have lowBound : low.toNat < 256 := by simpa [byteWidth] using low.isLt
    have highBound : high.toNat < 2 ^ 120 := high.isLt
    have small : low.toNat + 256 * high.toNat < 2 ^ 128 := by omega
    have quotient : (low.toNat + 256 * high.toNat) / 256 = high.toNat := by omega
    apply Prod.ext
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, byteWidth]
      rw [Nat.mod_eq_of_lt small]
      omega
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt small, quotient, Nat.mod_eq_of_lt highBound]

@[simp] theorem blockLowByteEquiv_fst (block : Block) :
    (blockLowByteEquiv block).1 = Exception.lowByte block := rfl

/-- Truncating a uniform block to its low byte gives a uniform byte: `2 ^ 128 = 2 ^ 8 * 2 ^ 120`
exactly, so there is no rounding loss. -/
theorem map_uniform_lowByte :
    (PMF.uniformOfFintype Block).map Exception.lowByte = PMF.uniformOfFintype (BitVec 8) := by
  have split := congrArg (fun law => law.map Prod.fst)
    (uniformOfFintype_map_equiv blockLowByteEquiv)
  simpa only [PMF.map_comp, uniformOfFintype_map_fst, Function.comp_def, blockLowByteEquiv_fst]
    using split

/-- The low byte of a Davies–Meyer value at a fixed point is a uniform byte. -/
theorem daviesMeyer_lowByte_uniform (u : Block) :
    (PMF.uniformOfFintype (Equiv Block Block)).map
        (fun π => Exception.lowByte (daviesMeyer π u)) = PMF.uniformOfFintype (BitVec 8) := by
  have factor : (fun π : Equiv.Perm Block => Exception.lowByte (daviesMeyer π u)) =
      Exception.lowByte ∘ (fun π => daviesMeyer π u) := rfl
  rw [factor, ← PMF.map_comp, daviesMeyer_uniform' u]
  exact map_uniform_lowByte


end

end Kriterion.ArgoMAC.Security.PGS
