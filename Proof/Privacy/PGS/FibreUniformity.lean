/-
This file proves **Lemma C.2**, the hardest lemma of the Plan B privacy argument: chunk-switch
fibre uniformity over `F_p`.

The plan source is `2026-09-17-planB.md`, section D.7 and Task 23; the
corrected statement is in the internal design note `phase2-dfb-design-v2.md`, §C.3.

Setting. Fix one chunk of one lane. The chunk has `n = 2 ^ b` switches (`b = firstChunkBits = 2`
for chunk `0`, `b = chunkBits = 5` for the `32` wide chunks and `b = narrowChunkBits = 4` for the
`23` narrow ones, `56` chunks in all: the ragged-first profile), and the lane delivers `S` element
values per switch. The
garbler publishes, in stage 1, one join `J : Fin S → F_p` for the chunk. In stage 2 the adversary
picks the active switch `α : Fin n` adaptively -- it is the chunk of the input -- and the evaluator
holds the `n - 1` masks `Y j` of the closed switches; at `α` it recovers the open label from the
join as `J - ∑_{j ≠ α} Y j`. The chunk's contribution to the output label is the free fold
`Ψ_α(Y) = ∑_{j} ι j • Ŷ j`, which is exactly the shape of `PlanB.evalScale` (see
`evalScale_eq_psi` below).

The content of the lemma is that, conditioned on the *published* join `J` and on any adaptively
chosen `α`, that fold is **one** surjective `F_p`-linear functional of the free masks, not two.
Every coefficient `ι j - ι α` with `j ≠ α` is a unit, because `ι` is injective on `Fin n` for
`n ≤ 2 ^ chunkBits << p`; so the fold is surjective with all fibres of the same cardinality
`p ^ ((n - 2) * S)`, the pushforward of the uniform law on the masks is uniform, and the
simulator's conditional law on the masks is *identical* to the real one -- zero statistical loss.

Design v1 claimed the two-functional version (join *and* fold as a joint output), which is false at
`n = 2`; the join is a stage-1 *condition*, not a stage-2 output, and once conditioned on, one
functional remains. That is why the `b = 2` first chunk is sound here.

Rule O: no sum over `Fin (2 ^ b)` is ever unfolded, enumerated or decided; every step is a
`Finset` identity.

## Divergences from the plan's literal statements (Task 23), each with its reason

* The plan writes the free sums as `∑ j ∈ Finset.univ.erase α, … Y ⟨j, by simp⟩`. That does not
  elaborate: under a `Finset.sum` binder the body has no access to the membership hypothesis, so
  `by simp` cannot prove `j ≠ α`. Every free sum here is therefore a sum over the subtype,
  `∑ j : {j : Fin n // j ≠ α}, …`, which is the same sum (`Finset.sum_subtype`) and is exactly the
  index type the masks are already given on.
* The plan writes the conditional law with a `PMF.condOn` on a predicate. No such operation exists
  in this library; the conditioning operator that does is Mathlib's `PMF.filter` on a set, so
  `psi_conditional_uniform` is stated with `PMF.filter` and the fibre's own uniform law. The
  content -- real conditional law = uniform on the fibre -- is unchanged.
* `fibreEquiv` is stated with the chosen free index `j₀` as an explicit argument (the plan's own
  step 4 requires choosing one) and is a plain `def` in a `noncomputable section`.
-/

import Construction.PGS.ScaleHot
import Proof.Privacy.PGS.DaviesMeyerUniform

namespace Kriterion.ArgoMAC.Security.PGS

open BN254 Cryptography Kriterion.ArgoMAC.PlanB

open scoped ENNReal

noncomputable section

variable {S n : ℕ}

/-! ### The free masks, the recovered labels, and the fold -/

/-- The coefficient that the free mask of switch `j` carries into the fold once the open label at
the active switch `α` has been substituted: `ι j - ι α`. -/
def coeff (α j : Fin n) : BaseField := iota n j - iota n α

@[simp] theorem coeff_self (α : Fin n) : coeff α α = 0 := sub_self _

/-- **The unit step.** For `j ≠ α` the coefficient is nonzero, because `ι` is injective on any
switch range up to `2 ^ chunkBits`. This is the step that is false for design v1's two-functional
statement and true for the single-functional one, and it is why the two-bit first chunk
(`n = 4`) is sound. -/
theorem coeff_ne_zero (bound : n ≤ 2 ^ chunkBits) {α j : Fin n} (distinct : j ≠ α) :
    coeff α j ≠ 0 :=
  sub_ne_zero.mpr fun equal => distinct (iota_injective bound equal)

/-- The evaluator-computable masks extended by `0` at the active switch. -/
def extend (α : Fin n) (Y : {j : Fin n // j ≠ α} → Fin S → BaseField) (j : Fin n) :
    Fin S → BaseField :=
  if h : j = α then 0 else Y ⟨j, h⟩

@[simp] theorem extend_of_ne (α : Fin n) (Y : {j : Fin n // j ≠ α} → Fin S → BaseField)
    (j : {j : Fin n // j ≠ α}) : extend α Y j.val = Y j := by
  simp only [extend, dif_neg j.prop, Subtype.coe_eta]

/-- `Ŷ`: the label the evaluator holds at switch `j`. Off the active switch it is the mask itself;
at the active switch it is recovered from the published join. -/
def hatY (α : Fin n) (J : Fin S → BaseField)
    (Y : {j : Fin n // j ≠ α} → Fin S → BaseField) (j : Fin n) : Fin S → BaseField :=
  if h : j = α then J - ∑ k : {j : Fin n // j ≠ α}, Y k else Y ⟨j, h⟩

@[simp] theorem hatY_active (α : Fin n) (J : Fin S → BaseField)
    (Y : {j : Fin n // j ≠ α} → Fin S → BaseField) :
    hatY α J Y α = J - ∑ k : {j : Fin n // j ≠ α}, Y k := by
  simp only [hatY, dif_pos]

@[simp] theorem hatY_closed (α : Fin n) (J : Fin S → BaseField)
    (Y : {j : Fin n // j ≠ α} → Fin S → BaseField) (j : {j : Fin n // j ≠ α}) :
    hatY α J Y j.val = Y j := by
  simp only [hatY, dif_neg j.prop, Subtype.coe_eta]

/-- **`Ψ_α`** -- the evaluated output label of the chunk, as a function of the free masks with the
published join held fixed. This is `PlanB.evalScale` written abstractly. -/
def Psi (α : Fin n) (J : Fin S → BaseField)
    (Y : {j : Fin n // j ≠ α} → Fin S → BaseField) : Fin S → BaseField :=
  ∑ j : Fin n, iota n j • hatY α J Y j

/-- The free part of the fold: the single linear functional of the masks that Lemma C.2 is about. -/
def freeFold (α : Fin n) (Y : {j : Fin n // j ≠ α} → Fin S → BaseField) : Fin S → BaseField :=
  ∑ j : {j : Fin n // j ≠ α}, coeff α j.val • Y j

/-! ### Step 1 -- the algebraic identity -/

/-- Rewriting a sum over `Fin n` as the active term plus a sum over the free indices. -/
theorem sum_univ_eq_active_add {M : Type*} [AddCommMonoid M] (α : Fin n) (f : Fin n → M) :
    ∑ j : Fin n, f j = f α + ∑ j : {j : Fin n // j ≠ α}, f j.val := by
  rw [← Finset.sum_subtype (Finset.univ.erase α) (fun x => by simp) f]
  exact (Finset.add_sum_erase _ f (Finset.mem_univ α)).symm

/-- **Lemma C.2, step 1.** Substituting the recovered label at the active switch and collecting,
the fold is affine in the free masks: a single linear functional plus the published join's
contribution. No case split on `α`. -/
theorem psi_eq (α : Fin n) (J : Fin S → BaseField)
    (Y : {j : Fin n // j ≠ α} → Fin S → BaseField) :
    Psi α J Y = (∑ j : {j : Fin n // j ≠ α}, (iota n j.val - iota n α) • Y j) + iota n α • J := by
  unfold Psi
  rw [sum_univ_eq_active_add α (fun j => iota n j • hatY α J Y j)]
  simp only [hatY_active, hatY_closed, smul_sub, Finset.smul_sum, sub_smul,
    Finset.sum_sub_distrib]
  abel

/-- The same identity in terms of `freeFold`. -/
theorem psi_eq_freeFold (α : Fin n) (J : Fin S → BaseField)
    (Y : {j : Fin n // j ≠ α} → Fin S → BaseField) :
    Psi α J Y = freeFold α Y + iota n α • J :=
  psi_eq α J Y

/-- The fold, recentred: the pure linear functional the simulator inverts. -/
theorem psi_sub_join (α : Fin n) (J : Fin S → BaseField)
    (Y : {j : Fin n // j ≠ α} → Fin S → BaseField) :
    Psi α J Y - iota n α • J = freeFold α Y := by
  rw [psi_eq_freeFold]; abel

/-! ### Splitting the free masks at one chosen index -/

/-- Split a sum over the free indices at a chosen free index `j₀`. -/
theorem sum_split_at {M : Type*} [AddCommMonoid M] {α j₀ : Fin n} (free : j₀ ≠ α) (f : Fin n → M) :
    ∑ j : {j : Fin n // j ≠ α}, f j.val
      = f j₀ + ∑ q : {j : Fin n // j ≠ α ∧ j ≠ j₀}, f q.val := by
  rw [← Finset.sum_subtype (Finset.univ.erase α) (fun x => by simp) f,
    ← Finset.sum_subtype ((Finset.univ.erase α).erase j₀)
      (fun x => by simp only [Finset.mem_erase, Finset.mem_univ, and_true]; tauto) f]
  exact (Finset.add_sum_erase _ f (Finset.mem_erase.mpr ⟨free, Finset.mem_univ j₀⟩)).symm

/-- `freeFold`, split at a chosen free index. -/
theorem freeFold_split {α j₀ : Fin n} (free : j₀ ≠ α)
    (Y : {j : Fin n // j ≠ α} → Fin S → BaseField) :
    freeFold α Y = coeff α j₀ • Y ⟨j₀, free⟩
      + ∑ q : {j : Fin n // j ≠ α ∧ j ≠ j₀}, coeff α q.val • Y ⟨q.val, q.prop.1⟩ := by
  have rewritten : freeFold α Y = ∑ j : {j : Fin n // j ≠ α},
      (fun k => coeff α k • extend α Y k) j.val := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [extend_of_ne]
  rw [rewritten, sum_split_at free (fun k => coeff α k • extend α Y k)]
  simp only [extend, dif_neg free]
  refine congrArg _ (Finset.sum_congr rfl fun q _ => ?_)
  simp only [dif_neg q.prop.1]

/-! ### Steps 2-4 -- the split equivalence, surjectivity, and the fibres

The `F_p`-linear functional `freeFold` is split off by an explicit equivalence that solves for the
mask at one chosen free index `j₀`; this is the route the design prescribes instead of rank-nullity
over `ZMod p`. Everything below needs the field structure of `F_p`, hence the certificate.
-/

variable [FieldCertificate]

/-- **The split equivalence.** With the published join fixed and one free index `j₀ ≠ α` chosen,
the free masks are equivalent to a pair: the value of the fold, and the masks at the remaining
`n - 2` free indices. The inverse solves for the mask at `j₀`, which is possible because
`coeff α j₀` is a unit. -/
def splitEquiv (bound : n ≤ 2 ^ chunkBits) {α j₀ : Fin n} (free : j₀ ≠ α) :
    ({j : Fin n // j ≠ α} → Fin S → BaseField) ≃
      (Fin S → BaseField) × ({j : Fin n // j ≠ α ∧ j ≠ j₀} → Fin S → BaseField) where
  toFun Y := (freeFold α Y, fun q => Y ⟨q.val, q.prop.1⟩)
  invFun pair := fun j =>
    if h : j.val = j₀ then
      (coeff α j₀)⁻¹ • (pair.1
        - ∑ q : {j : Fin n // j ≠ α ∧ j ≠ j₀}, coeff α q.val • pair.2 q)
    else pair.2 ⟨j.val, ⟨j.prop, h⟩⟩
  left_inv Y := by
    funext j
    dsimp only
    by_cases h : j.val = j₀
    · rw [dif_pos h, freeFold_split free Y, add_sub_cancel_right,
        inv_smul_smul₀ (coeff_ne_zero bound free)]
      exact congrArg Y (Subtype.ext h.symm)
    · rw [dif_neg h]
  right_inv pair := by
    obtain ⟨t, R⟩ := pair
    set free_masks : {j : Fin n // j ≠ α} → Fin S → BaseField := fun j =>
      if h : j.val = j₀ then
        (coeff α j₀)⁻¹ • (t - ∑ q : {j : Fin n // j ≠ α ∧ j ≠ j₀}, coeff α q.val • R q)
      else R ⟨j.val, ⟨j.prop, h⟩⟩ with free_masks_def
    have closed : ∀ q : {j : Fin n // j ≠ α ∧ j ≠ j₀}, free_masks ⟨q.val, q.prop.1⟩ = R q :=
      fun q => dif_neg q.prop.2
    have active : free_masks ⟨j₀, free⟩ =
        (coeff α j₀)⁻¹ • (t - ∑ q : {j : Fin n // j ≠ α ∧ j ≠ j₀}, coeff α q.val • R q) :=
      dif_pos rfl
    refine Prod.ext ?_ (funext closed)
    show freeFold α free_masks = t
    rw [freeFold_split free free_masks, active, smul_inv_smul₀ (coeff_ne_zero bound free)]
    simp only [closed]
    exact sub_add_cancel _ _

@[simp] theorem splitEquiv_fst (bound : n ≤ 2 ^ chunkBits) {α j₀ : Fin n} (free : j₀ ≠ α)
    (Y : {j : Fin n // j ≠ α} → Fin S → BaseField) :
    (splitEquiv (S := S) bound free Y).1 = freeFold α Y := rfl

omit [FieldCertificate] in
/-- With at least two switches there is a free index. -/
theorem exists_free (two : 2 ≤ n) (α : Fin n) : ∃ j₀ : Fin n, j₀ ≠ α := by
  have card : 1 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  exact Fintype.exists_ne_of_one_lt_card card α

/-- **Lemma C.2, step 3.** The free fold is a surjective linear functional. -/
theorem freeFold_surjective (bound : n ≤ 2 ^ chunkBits) (two : 2 ≤ n) (α : Fin n) :
    Function.Surjective
      (freeFold α : ({j : Fin n // j ≠ α} → Fin S → BaseField) → Fin S → BaseField) := by
  obtain ⟨j₀, free⟩ := exists_free two α
  intro target
  refine ⟨(splitEquiv bound free).symm (target, fun _ => 0), ?_⟩
  exact congrArg Prod.fst ((splitEquiv (S := S) bound free).apply_symm_apply (target, fun _ => 0))

/-- **Lemma C.2, step 3, as the plan states it.** The map from the free masks to the evaluated
output label, recentred by the published join's contribution, is surjective. -/
theorem psi_surjective (bound : n ≤ 2 ^ chunkBits) (two : 2 ≤ n) (α : Fin n)
    (J : Fin S → BaseField) :
    Function.Surjective (fun Y : {j : Fin n // j ≠ α} → Fin S → BaseField =>
      Psi α J Y - iota n α • J) := by
  intro target
  obtain ⟨Y, hY⟩ := freeFold_surjective (S := S) bound two α target
  exact ⟨Y, by show Psi α J Y - iota n α • J = target; rw [psi_sub_join]; exact hY⟩

/-- The fibre of the first coordinate of a product is the second factor. -/
def fstFibre {A B : Type*} (t : A) : {q : A × B // q.1 = t} ≃ B where
  toFun q := q.val.2
  invFun b := ⟨(t, b), rfl⟩
  left_inv := by rintro ⟨⟨a, b⟩, rfl⟩; rfl
  right_inv _ := rfl

/-- **Lemma C.2, step 4.** Every fibre of the fold is equinumerous with the masks at the `n - 2`
indices other than `α` and `j₀` -- built by *solving for the mask at `j₀`*, not by rank-nullity
over `ZMod p`. -/
def fibreEquiv (bound : n ≤ 2 ^ chunkBits) (α : Fin n) (J t : Fin S → BaseField) (j₀ : Fin n)
    (free : j₀ ≠ α) :
    {Y : {j : Fin n // j ≠ α} → Fin S → BaseField // Psi α J Y - iota n α • J = t} ≃
      ({j : Fin n // j ≠ α ∧ j ≠ j₀} → Fin S → BaseField) :=
  ((Equiv.subtypeEquivRight (fun Y => by rw [psi_sub_join])).trans
    (Equiv.subtypeEquiv (splitEquiv (S := S) bound free)
      (fun _ => by rw [splitEquiv_fst]))).trans (fstFibre t)

/-! ### Step 4 -- the fibre cardinality -/

omit [FieldCertificate] in
/-- There are `n - 2` free indices other than the chosen one. -/
theorem card_other (α j₀ : Fin n) (free : j₀ ≠ α) :
    Fintype.card {j : Fin n // j ≠ α ∧ j ≠ j₀} = n - 2 := by
  classical
  have shape : Finset.univ.filter (fun j : Fin n => j ≠ α ∧ j ≠ j₀)
      = (Finset.univ.erase α).erase j₀ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  have member : j₀ ∈ Finset.univ.erase α := Finset.mem_erase.mpr ⟨free, Finset.mem_univ j₀⟩
  rw [Fintype.card_subtype, shape, Finset.card_erase_of_mem member, Finset.card_erase_of_mem
    (Finset.mem_univ α), Finset.card_univ, Fintype.card_fin]
  omega

/-- **Lemma C.2, step 4, the count.** Every fibre of the fold has exactly `p ^ ((n - 2) * S)`
elements: the domain has dimension `(n - 1) * S`, the image `S`, so the fibre has `(n - 2) * S`. -/
theorem card_fibre (bound : n ≤ 2 ^ chunkBits) (α : Fin n) (J t : Fin S → BaseField)
    (j₀ : Fin n) (free : j₀ ≠ α) :
    Fintype.card
        {Y : {j : Fin n // j ≠ α} → Fin S → BaseField // Psi α J Y - iota n α • J = t}
      = baseFieldModulus ^ ((n - 2) * S) := by
  classical
  rw [Fintype.card_congr (fibreEquiv bound α J t j₀ free), Fintype.card_fun, Fintype.card_fun,
    ZMod.card, Fintype.card_fin, card_other α j₀ free, ← pow_mul, Nat.mul_comm]

/-! ### Step 5 -- the uniform pushforward -/

/-- The free fold carries the uniform law on the masks to the uniform law on the fold values. -/
theorem freeFold_map_uniform (bound : n ≤ 2 ^ chunkBits) (two : 2 ≤ n) (α : Fin n) :
    (PMF.uniformOfFintype ({j : Fin n // j ≠ α} → Fin S → BaseField)).map (freeFold α)
      = PMF.uniformOfFintype (Fin S → BaseField) := by
  obtain ⟨j₀, free⟩ := exists_free two α
  have factor : (freeFold α : ({j : Fin n // j ≠ α} → Fin S → BaseField) → Fin S → BaseField)
      = Prod.fst ∘ (splitEquiv (S := S) bound free) := rfl
  rw [factor, ← PMF.map_comp, uniformOfFintype_map_equiv (splitEquiv (S := S) bound free)]
  exact uniformOfFintype_map_fst

/-- **Lemma C.2.** With the published join held fixed and the active index chosen adaptively, the
uniform law on the `n - 1` evaluator-computable switch masks pushes forward to the uniform law on
the chunk's output label. -/
theorem psi_map_uniform (bound : n ≤ 2 ^ chunkBits) (two : 2 ≤ n) (α : Fin n)
    (J : Fin S → BaseField) :
    (PMF.uniformOfFintype ({j : Fin n // j ≠ α} → Fin S → BaseField)).map (fun Y => Psi α J Y)
      = PMF.uniformOfFintype (Fin S → BaseField) := by
  have factor : (fun Y : {j : Fin n // j ≠ α} → Fin S → BaseField => Psi α J Y)
      = (fun value => value + iota n α • J) ∘ (freeFold α) :=
    funext fun Y => psi_eq_freeFold α J Y
  rw [factor, ← PMF.map_comp, freeFold_map_uniform bound two α]
  exact uniformOfFintype_map_equiv (Equiv.addRight (iota n α • J))

/-! ### Step 6 -- the conditional law the simulator uses -/

omit [FieldCertificate] in
/-- Conditioning a uniform law on a nonempty subset gives the uniform law on that subset. -/
theorem uniform_filter_eq {A : Type*} [Fintype A] [Nonempty A] (s : Set A) [Fintype ↥s]
    [Nonempty ↥s] (hit : ∃ a ∈ s, a ∈ (PMF.uniformOfFintype A).support) :
    (PMF.uniformOfFintype A).filter s hit = (PMF.uniformOfFintype ↥s).map Subtype.val := by
  classical
  have cardA : (Fintype.card A : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have cardAtop : (Fintype.card A : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have cardS : (Fintype.card ↥s : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have cardStop : (Fintype.card ↥s : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have total : ∑' a, s.indicator (⇑(PMF.uniformOfFintype A)) a
      = (Fintype.card ↥s : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ := by
    rw [← tsum_subtype s (⇑(PMF.uniformOfFintype A))]
    simp only [PMF.uniformOfFintype_apply]
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine PMF.ext fun value => ?_
  rw [PMF.filter_apply, total, PMF.map_apply]
  by_cases inside : value ∈ s
  · rw [Set.indicator_of_mem inside, PMF.uniformOfFintype_apply,
      tsum_eq_single ⟨value, inside⟩ (fun y distinct => if_neg fun equal =>
        distinct (Subtype.ext equal.symm)), if_pos rfl, PMF.uniformOfFintype_apply,
      ENNReal.mul_inv (Or.inl cardS) (Or.inl cardStop), inv_inv, ← mul_assoc,
      mul_comm ((Fintype.card A : ℝ≥0∞))⁻¹ ((Fintype.card ↥s : ℝ≥0∞))⁻¹, mul_assoc,
      ENNReal.inv_mul_cancel cardA cardAtop, mul_one]
  · rw [Set.indicator_of_notMem inside, zero_mul]
    exact (ENNReal.tsum_eq_zero.mpr fun y =>
      if_neg fun equal => inside (by rw [equal]; exact y.prop)).symm

/-- The fibre of the fold at any target is nonempty. -/
theorem fibre_nonempty (bound : n ≤ 2 ^ chunkBits) (two : 2 ≤ n) (α : Fin n)
    (J v : Fin S → BaseField) :
    Nonempty {Y : {j : Fin n // j ≠ α} → Fin S → BaseField // Psi α J Y = v} := by
  obtain ⟨Y, hY⟩ := psi_surjective bound two α J (v - iota n α • J)
  exact ⟨⟨Y, by simpa using congrArg (fun value => value + iota n α • J) hY⟩⟩

/-- The conditioning event is hit, so `PMF.filter` is defined on it. -/
theorem fibre_hit (bound : n ≤ 2 ^ chunkBits) (two : 2 ≤ n) (α : Fin n)
    (J v : Fin S → BaseField) :
    ∃ Y ∈ {Y : {j : Fin n // j ≠ α} → Fin S → BaseField | Psi α J Y = v},
      Y ∈ (PMF.uniformOfFintype ({j : Fin n // j ≠ α} → Fin S → BaseField)).support := by
  obtain ⟨⟨Y, hY⟩⟩ := fibre_nonempty bound two α J v
  exact ⟨Y, hY, by simp⟩

/-- **Lemma C.2, the conditional form the simulator uses.** For every adaptively chosen active
index `α`, every published join `J` and every stage-2 target `v`, the real law on the
evaluator-computable masks conditioned on the evaluated output being `v` is *exactly* the uniform
law on the fibre -- which is what the simulator samples. Zero statistical loss. -/
theorem psi_conditional_uniform (bound : n ≤ 2 ^ chunkBits) (two : 2 ≤ n) (α : Fin n)
    (J v : Fin S → BaseField)
    [Fintype ↥{Y : {j : Fin n // j ≠ α} → Fin S → BaseField | Psi α J Y = v}]
    [Nonempty ↥{Y : {j : Fin n // j ≠ α} → Fin S → BaseField | Psi α J Y = v}] :
    (PMF.uniformOfFintype ({j : Fin n // j ≠ α} → Fin S → BaseField)).filter
        {Y | Psi α J Y = v} (fibre_hit bound two α J v)
      = (PMF.uniformOfFintype ↥{Y : {j : Fin n // j ≠ α} → Fin S → BaseField | Psi α J Y = v}).map
          Subtype.val :=
  uniform_filter_eq _ _

/-! ### Step 7 -- instances at the wide and the first chunk widths -/

/-- **Lemma C.2 at the `chunkBits`-wide chunks** (the wide chunks `1 .. 32`;
`n = 2 ^ chunkBits`). -/
theorem psi_map_uniform_wide (α : Fin (2 ^ chunkBits)) (J : Fin S → BaseField) :
    (PMF.uniformOfFintype ({j : Fin (2 ^ chunkBits) // j ≠ α} → Fin S → BaseField)).map
        (fun Y => Psi α J Y) = PMF.uniformOfFintype (Fin S → BaseField) :=
  psi_map_uniform le_rfl (by norm_num [chunkBits]) α J

/-- **Lemma C.2 at the first chunk**, `b = firstChunkBits = 2`, `n = 4`. This is the instance
design v1's two-functional statement could not support. -/
theorem psi_map_uniform_first (α : Fin (2 ^ firstChunkBits)) (J : Fin S → BaseField) :
    (PMF.uniformOfFintype ({j : Fin (2 ^ firstChunkBits) // j ≠ α} → Fin S → BaseField)).map
        (fun Y => Psi α J Y) = PMF.uniformOfFintype (Fin S → BaseField) :=
  psi_map_uniform (by norm_num [chunkBits, firstChunkBits]) (by norm_num [firstChunkBits]) α J

/-- The fibre count at a `chunkBits`-wide chunk: `p ^ ((2 ^ chunkBits - 2) * S)`. -/
theorem card_fibre_wide (α : Fin (2 ^ chunkBits)) (J t : Fin S → BaseField) (j₀ : Fin (2 ^ chunkBits))
    (free : j₀ ≠ α) :
    Fintype.card {Y : {j : Fin (2 ^ chunkBits) // j ≠ α} → Fin S → BaseField //
        Psi α J Y - iota (2 ^ chunkBits) α • J = t}
      = baseFieldModulus ^ ((2 ^ chunkBits - 2) * S) :=
  card_fibre le_rfl α J t j₀ free

/-- The fibre count at the first chunk: `p ^ (2 * S)`. -/
theorem card_fibre_first (α : Fin (2 ^ firstChunkBits)) (J t : Fin S → BaseField)
    (j₀ : Fin (2 ^ firstChunkBits)) (free : j₀ ≠ α) :
    Fintype.card {Y : {j : Fin (2 ^ firstChunkBits) // j ≠ α} → Fin S → BaseField //
        Psi α J Y - iota (2 ^ firstChunkBits) α • J = t}
      = baseFieldModulus ^ (2 * S) := by
  rw [card_fibre (by norm_num [chunkBits, firstChunkBits]) α J t j₀ free]
  norm_num [firstChunkBits]

/-! ### The bridge to the landed construction

`Psi` is not an invention of this file: it is exactly `PlanB.evalScale`, the evaluator's free fold
on the landed `scale-hot` join, with the free masks instantiated at the closed switches'
`switchMask`s. Everything above therefore speaks about the real evaluated output label.
-/

omit [FieldCertificate] in
/-- The landed evaluator-side fold is `Psi` at the published join. -/
theorem evalScale_eq_psi (hashOracle : EncPRF.HashOracle) (lane : Lane)
    (chunk : Fin chunkCount) (width : ℕ) (hot : HotLabels width) (alpha : Fin (2 ^ width))
    (join : Fin (laneCount lane) → BaseField) :
    evalScale hashOracle lane chunk width hot alpha join
      = Psi alpha join (fun j => switchMask hashOracle lane chunk j.val.val (hot j.val)) := by
  funext element
  unfold evalScale Psi
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun switch _ => ?_
  by_cases active : switch = alpha
  · subst active
    rw [if_pos rfl]
    simp only [hatY_active, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply]
    congr 2
    exact Finset.sum_subtype (Finset.univ.erase switch) (fun x => by simp)
      (fun other => switchMask hashOracle lane chunk other.val (hot other) element)
  · rw [if_neg active]
    simp only [hatY, dif_neg active, Pi.smul_apply, smul_eq_mul]

end

end Kriterion.ArgoMAC.Security.PGS
