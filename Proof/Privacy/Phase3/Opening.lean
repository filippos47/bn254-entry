/-
**Phase 3, P1, theorem 2 — the output-aware opening.**

`B-output-aware-simulator.md` §1.1–1.3 and `B-review.md` (1).

### (a) The row solve

With the published constants `γ = rows[d]` and the input `u` fixed, each of a digit's three rows is
affine in the seven delivered element values (`evaluateGamma_eq_affine`: a `γ`-and-`u` constant
plus the linear form `rowLinear u`, which does not mention `γ`), and each row has a **collector**
that no other row reads (see `rowLinear`): `rowX_x9` for `X` and `rowZ_x9` for `Z`, with
coefficient one, and `rowY_cubic` for the sign row, with coefficient `x²`. All three are x-type
elements of lane `pointX`. Every curve point has `x ≠ 0` (`onCurve_x_ne_zero`), so the sign row's
solve divides by `x²`.

`collectorEquiv γ u v : F_p³ ≃ HomogeneousValue` is the solve: its forward map writes the collector
triple into `v` and evaluates the three rows, its inverse is the closed form `collectorSolve`
(note §1.3, E3), for `x ≠ 0`. `collectorSolve` reads `v` only at the four non-collector elements,
so for every fixed value of the four free elements and the ten published constants the
collector triple and the row triple determine each other (`collectorsOf_eq_solve`).

### (b) The digit-point law

Generic over a finite abelian group `G` with an injective additive radix map `f` (for BN254:
`G = Point`, `f = radix • ·`, `pointHorner_ofFn`). The construction's offsets are
`K = (−f(H(K_tail)), K_tail)` (`Offsets.clampOffsets`, `FieldMacToECMac.clampedFirst`), the real digit
points are `D = T + K` with `H(T) = Q`, and the simulator draws `D_tail` and clamps
`D_0 = Q − f(H(D_tail))`.

* **Exact** (`digitPoints_law`): if the offset tail is uniform on `G ^ n`, the real digit points
  have *exactly* the simulator's law, for every output `Q` — `Q = 0` (the identity) included; no
  case split on `Q` exists anywhere.
* **Exact** (`digitPoints_good_law`): the construction's actual offset law — uniform on tails whose
  every entry *and* clamped head are non-identity — gives *exactly* the simulator's law
  conditioned on the no-hit event `∀ d, D_d ≠ T_d`.
* **Statistical cost** (`digitPoints_good_etvDist_le`): that conditioning costs at most
  `#digits / #G` (`91 / #Point` for `90` tail points, `bn254_digitPoints_good_etvDist_le`). It is a
  genuine cost: the event depends on `T`, i.e. on the secret scalar, so no output-only sampler can
  reproduce the conditioning.

**The rows.** `lift D λ t = (λ² x, t² y, λ)` for a finite point and `(λ², 0, 0)` for `O`. The
real row of a digit (Jacobian `X` and `Z` at `ρ`, the sign row `S = τ² L² y_R` at the independent
`τ`) is (`realRow_digitZero`, `realRow_xNe`, `realRow_neg`): digit zero `lift K ρ τ`; nonzero digit
with `x' ≠ k_x` and `L ≠ 0` `lift (T + K) (ρ (x' − k_x)) (τ L)`; inverse case `T = −K`
`lift O (2 ρ k_y) τ` (the sign row vanishes there: the tangent at `−K` passes through `−K`). In all
three the multipliers are non-zero, so under uniform `ρ, τ ∈ F_p^*` the row law is **exactly** the
lift of `D` at uniform `λ, t ∈ F_p^*` (`lifts_law`, jointly over all digits for any law of the
points: `rowsLaw_eq`). Two cases are not lifts: the **doubling** case `T = K` gives `X = Z = 0`
(`realRow_double`), and the sign row's other zero `T = 2K` (`L = 0`, `x' ≠ k_x`) gives
`S = 0 ≠ Z` (`realRow_triple`); the gadget resolves both, and the simulator never produces them.
They are the second statistical cost: under the simulator's point law each digit hits any fixed
target point with probability at most `1 / #G` (`clamp_hit_le`), so the exceptional event
`∃ d, D_d = 2 T_d ∨ D_d = (3/2) T_d` has mass at most `182 / #Point` under the simulator's law
(`bn254_doubling_le`) and at most `273 / #Point` under the construction's
(`bn254_doubling_real_le`, adding the offset-restriction distance). The exception gadget is
**not** smoothed over: it is exactly this event, charged, and never simulated.
-/

import Proof.Privacy.Phase3.Basic
import Proof.Correctness.JacobianMixed
import Proof.Correctness.PGS.NonResidue

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv)
open scoped ENNReal

noncomputable section

/-! ## (a) The three rows, affine in the delivered values, and the collector solve -/

/-- The `X` row's collector: x-type element `rowX_x9`. -/
abbrev collectorX : Biquadratic.Element := .inl .rowX_x9

/-- The `Y` row's collector: x-type element `rowY_cubic`, read with coefficient `x²`. -/
abbrev collectorY : Biquadratic.Element := .inl .rowY_cubic

/-- The `Z` row's collector: x-type element `rowZ_x9`. -/
abbrev collectorZ : Biquadratic.Element := .inl .rowZ_x9

/-- The three collectors, as a predicate. -/
def IsCollector (element : Biquadratic.Element) : Prop :=
  element = collectorX ∨ element = collectorY ∨ element = collectorZ

instance (element : Biquadratic.Element) : Decidable (IsCollector element) := by
  unfold IsCollector; infer_instance

/-- The row triple's linear part in the delivered values. It does not mention `γ`. -/
def rowLinear (input : AffineInput) (values : Biquadratic.Values) : HomogeneousValue where
  x := values (.inl .rowX_x7) * input.x + values (.inl .rowX_x9) + values (.inr .rowX_y10)
  y := values (.inl .rowY_cubic) * input.x ^ 2 + values (.inr .rowY_y8) * input.y
    + values (.inr .rowY_y10)
  z := values (.inl .rowZ_x9)

/-- The row triple's constant part: the published constants on the input's monomials. -/
def rowConstant (gamma : RowGamma) (input : AffineInput) : HomogeneousValue where
  x := gamma.xC0 + gamma.xC1 * input.x + gamma.xC2 * input.y + gamma.xC4 * input.x ^ 2
  y := gamma.yC0 + gamma.yC2 * input.y + gamma.yC4 * input.x ^ 2 + gamma.yC5 * input.y ^ 2
  z := gamma.zC0 + gamma.zC1 * input.x

/-- **The rows are affine in the delivered values, with `γ` fixed.** -/
theorem evaluateGamma_eq_affine (gamma : RowGamma) (input : AffineInput)
    (values : Biquadratic.Values) :
    evaluateGamma gamma input values
      = ⟨(rowConstant gamma input).x + (rowLinear input values).x,
         (rowConstant gamma input).y + (rowLinear input values).y,
         (rowConstant gamma input).z + (rowLinear input values).z⟩ := by
  simp only [evaluateGamma, Biquadratic.evaluateX, Biquadratic.evaluateY, Biquadratic.evaluateZ,
    xGammaOf, yGammaOf, zGammaOf, rowConstant, rowLinear]
  congr 1 <;> ring

/-- Write a collector triple into a digit's element family. -/
def setCollectors (values : Biquadratic.Values) (triple : BaseField × BaseField × BaseField) :
    Biquadratic.Values := fun element =>
  if element = collectorX then triple.1
  else if element = collectorY then triple.2.1
  else if element = collectorZ then triple.2.2
  else values element

/-- Read the collector triple off a digit's element family. -/
def collectorsOf (values : Biquadratic.Values) : BaseField × BaseField × BaseField :=
  (values collectorX, values collectorY, values collectorZ)

theorem setCollectors_collectorsOf (values : Biquadratic.Values) :
    setCollectors values (collectorsOf values) = values := by
  funext element
  simp only [setCollectors, collectorsOf]
  split_ifs with hx hy hz <;> first | rw [hx] | rw [hy] | rw [hz] | rfl

/-- **The collector solve** (note §1.3, E3): the collector triple that makes the three rows equal a
target, given the published constants and the four other delivered values. The sign component
divides by the `Y` collector's coefficient `x²`, as the inverse `(x · x)⁻¹` (the machine's
`Opening.finishScaled`; the inverse of `0` is `0`, and on the curve `x ≠ 0`). -/
def collectorSolve (gamma : RowGamma) (input : AffineInput)
    (values : Biquadratic.Values) (target : HomogeneousValue) : BaseField × BaseField × BaseField :=
  (target.x - (gamma.xC0 + gamma.xC1 * input.x + gamma.xC2 * input.y + gamma.xC4 * input.x ^ 2
      + values (.inl .rowX_x7) * input.x + values (.inr .rowX_y10)),
   (target.y - (gamma.yC0 + gamma.yC2 * input.y + gamma.yC4 * input.x ^ 2
      + gamma.yC5 * input.y ^ 2 + values (.inr .rowY_y8) * input.y + values (.inr .rowY_y10)))
      * (input.x * input.x)⁻¹,
   target.z - (gamma.zC0 + gamma.zC1 * input.x))

/-- **The collector triple and the row triple determine each other**, for every fixed value of the
four free elements and the published constants, when `x ≠ 0`. -/
def collectorEquiv [FieldCertificate] (gamma : RowGamma) (input : AffineInput)
    (values : Biquadratic.Values) (xNe : input.x ≠ 0) :
    (BaseField × BaseField × BaseField) ≃ HomogeneousValue where
  toFun triple := evaluateGamma gamma input (setCollectors values triple)
  invFun target := collectorSolve gamma input values target
  left_inv triple := by
    obtain ⟨cx, cy, cz⟩ := triple
    have square : input.x * input.x ≠ 0 := mul_ne_zero xNe xNe
    simp only [collectorSolve, evaluateGamma, Biquadratic.evaluateX, Biquadratic.evaluateY,
      Biquadratic.evaluateZ, xGammaOf, yGammaOf, zGammaOf, setCollectors]
    simp only [reduceCtorEq, if_false, if_true, Sum.inl.injEq]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    field_simp
  right_inv target := by
    obtain ⟨tx, ty, tz⟩ := target
    have square : input.x * input.x ≠ 0 := mul_ne_zero xNe xNe
    simp only [collectorSolve, evaluateGamma, Biquadratic.evaluateX, Biquadratic.evaluateY,
      Biquadratic.evaluateZ, xGammaOf, yGammaOf, zGammaOf, setCollectors]
    simp only [reduceCtorEq, if_false, if_true, Sum.inl.injEq]
    congr 1
    · ring
    · field_simp
      ring
    · ring

/-- Conversely, any family whose rows hit the target carries the solved collectors. -/
theorem collectorsOf_eq_solve [FieldCertificate] (gamma : RowGamma) (input : AffineInput)
    (values : Biquadratic.Values) (target : HomogeneousValue) (xNe : input.x ≠ 0)
    (hits : evaluateGamma gamma input values = target) :
    collectorsOf values = collectorSolve gamma input values target := by
  have forward : collectorEquiv gamma input values xNe (collectorsOf values) = target := by
    show evaluateGamma gamma input (setCollectors values (collectorsOf values)) = target
    rw [setCollectors_collectorsOf, hits]
  rw [← forward]
  exact ((collectorEquiv gamma input values xNe).left_inv (collectorsOf values)).symm

/-! ## (b) The digit-point law -/

section Horner

variable {G : Type} [AddCommGroup G]

/-- Horner's rule with an additive radix map: `H(D) = D_0 + f(H(D_1, …))`. -/
def horner (f : G →+ G) : (n : ℕ) → (Fin n → G) → G
  | 0, _ => 0
  | n + 1, points => points 0 + f (horner f n (Fin.tail points))

theorem horner_add (f : G →+ G) :
    ∀ (n : ℕ) (first second : Fin n → G),
      horner f n (first + second) = horner f n first + horner f n second
  | 0, _, _ => by simp [horner]
  | n + 1, first, second => by
      have tail : Fin.tail (first + second) = Fin.tail first + Fin.tail second := rfl
      simp only [horner, tail, horner_add f n, map_add, Pi.add_apply]
      abel

/-- The construction's `pointHorner` is `horner` at `radix • ·`. -/
theorem pointHorner_ofFn [FieldCertificate] [GroupCertificate] (beta : ScalarField) :
    ∀ (n : ℕ) (points : Fin n → Point),
      Kriterion.ArgoMAC.pointHorner beta (List.ofFn points)
        = horner (DistribSMul.toAddMonoidHom Point beta) n points
  | 0, _ => rfl
  | n + 1, points => by
      rw [List.ofFn_succ, Kriterion.ArgoMAC.pointHorner, pointHorner_ofFn beta n]
      rfl

/-- **The simulator's digit points**: the tail as drawn, the head clamped to the output. -/
def clampPoints (f : G →+ G) (output : G) {n : ℕ} (tail : Fin n → G) : Fin (n + 1) → G :=
  Fin.cons (output - f (horner f n tail)) tail

theorem horner_clampPoints (f : G →+ G) (output : G) {n : ℕ} (tail : Fin n → G) :
    horner f (n + 1) (clampPoints f output tail) = output := by
  simp only [horner, clampPoints, Fin.cons_zero, Fin.tail_cons, sub_add_cancel]

/-- **The construction's offsets**: the tail as drawn, the head clamped so that `H(K) = 0`
(`Offsets.clampOffsets`, `FieldMacToECMac.clampedFirst`). -/
def clampOffsets (f : G →+ G) {n : ℕ} (tail : Fin n → G) : Fin (n + 1) → G :=
  Fin.cons (-(f (horner f n tail))) tail

theorem horner_clampOffsets (f : G →+ G) {n : ℕ} (tail : Fin n → G) :
    horner f (n + 1) (clampOffsets f tail) = 0 := by
  simp only [horner, clampOffsets, Fin.cons_zero, Fin.tail_cons, neg_add_cancel]

/-- **The real digit points**: the digit multiples `T` of the input, translated by the offsets. -/
def realPoints (f : G →+ G) {n : ℕ} (multiples : Fin (n + 1) → G) (tail : Fin n → G) :
    Fin (n + 1) → G :=
  multiples + clampOffsets f tail

/-- The real points are the simulator's points at the translated tail. -/
theorem realPoints_eq_clamp (f : G →+ G) {n : ℕ} (multiples : Fin (n + 1) → G) (output : G)
    (hits : horner f (n + 1) multiples = output) (tail : Fin n → G) :
    realPoints f multiples tail = clampPoints f output (Fin.tail multiples + tail) := by
  funext digit
  refine Fin.cases ?_ (fun place => ?_) digit
  · simp only [realPoints, clampOffsets, clampPoints, Pi.add_apply, Fin.cons_zero,
      horner_add, map_add]
    rw [← hits]
    simp only [horner]
    abel
  · simp [realPoints, clampOffsets, clampPoints, Fin.tail]

variable [Fintype G] [DecidableEq G]

/-- **The digit-point law, exact.** With the offset tail uniform on `G ^ n`, the real digit
points have exactly the simulator's law, for every output — the identity included. -/
theorem digitPoints_law (f : G →+ G) {n : ℕ} (multiples : Fin (n + 1) → G) (output : G)
    (hits : horner f (n + 1) multiples = output) :
    (PMF.uniformOfFintype (Fin n → G)).map (realPoints f multiples)
      = (PMF.uniformOfFintype (Fin n → G)).map (clampPoints f output) := by
  have factor : realPoints f multiples
      = clampPoints f output ∘ Equiv.addLeft (Fin.tail multiples) := by
    funext tail
    exact realPoints_eq_clamp f multiples output hits tail
  rw [factor, ← PMF.map_comp, uniformOfFintype_map_equiv]

/-- The offset tails the construction accepts: every tail offset and the clamped head are
non-identity (`AffineOffset` is a non-identity affine point; `SuccessfulOffsets.IsClamped`). -/
def GoodTail (f : G →+ G) {n : ℕ} (tail : Fin n → G) : Prop :=
  (∀ index, tail index ≠ 0) ∧ f (horner f n tail) ≠ 0

instance (f : G →+ G) {n : ℕ} (tail : Fin n → G) : Decidable (GoodTail f tail) := by
  unfold GoodTail; infer_instance

/-- The no-hit event: no digit point equals its digit multiple (no offset is the identity). -/
def NoHit (f : G →+ G) {n : ℕ} (output : G) (multiples : Fin (n + 1) → G) (tail : Fin n → G) :
    Prop :=
  ∀ digit, clampPoints f output tail digit ≠ multiples digit

instance (f : G →+ G) {n : ℕ} (output : G) (multiples : Fin (n + 1) → G) (tail : Fin n → G) :
    Decidable (NoHit f output multiples tail) := by
  unfold NoHit; infer_instance

theorem goodTail_iff_noHit (f : G →+ G) {n : ℕ} (multiples : Fin (n + 1) → G) (output : G)
    (hits : horner f (n + 1) multiples = output) (tail : Fin n → G) :
    GoodTail f tail ↔ NoHit f output multiples (Fin.tail multiples + tail) := by
  unfold GoodTail NoHit
  rw [← realPoints_eq_clamp f multiples output hits tail]
  constructor
  · rintro ⟨tailGood, headGood⟩ digit
    refine Fin.cases ?_ (fun place => ?_) digit
    · simp only [realPoints, clampOffsets, Pi.add_apply, Fin.cons_zero, ne_eq,
        add_eq_left, neg_eq_zero]
      exact headGood
    · simp only [realPoints, clampOffsets, Pi.add_apply, Fin.cons_succ, ne_eq, add_eq_left]
      exact tailGood place
  · intro noHit
    refine ⟨fun place => ?_, ?_⟩
    · have := noHit place.succ
      simpa [realPoints, clampOffsets] using this
    · have := noHit 0
      simpa [realPoints, clampOffsets] using this

/-- **The construction's offset law, exact.** Uniform good tails give exactly the simulator's law
conditioned on the no-hit event. -/
theorem digitPoints_good_law (f : G →+ G) {n : ℕ} (multiples : Fin (n + 1) → G) (output : G)
    (hits : horner f (n + 1) multiples = output) [Nonempty {tail : Fin n → G // GoodTail f tail}]
    [Nonempty {tail : Fin n → G // NoHit f output multiples tail}] :
    (PMF.uniformOfFintype {tail : Fin n → G // GoodTail f tail}).map
        (fun tail => realPoints f multiples tail.1)
      = (PMF.uniformOfFintype {tail : Fin n → G // NoHit f output multiples tail}).map
        (fun tail => clampPoints f output tail.1) := by
  let shift : {tail : Fin n → G // GoodTail f tail}
      ≃ {tail : Fin n → G // NoHit f output multiples tail} :=
    (Equiv.addLeft (Fin.tail multiples)).subtypeEquiv fun tail =>
      goodTail_iff_noHit f multiples output hits tail
  have factor : (fun tail : {tail : Fin n → G // GoodTail f tail} => realPoints f multiples tail.1)
      = (fun tail : {tail : Fin n → G // NoHit f output multiples tail} =>
          clampPoints f output tail.1) ∘ shift := by
    funext tail
    exact realPoints_eq_clamp f multiples output hits tail.1
  rw [factor, ← PMF.map_comp, uniformOfFintype_map_equiv shift]

/-- Uniform on a subset, against uniform on the whole space: exactly the outside's mass. -/
theorem etvDist_uniform_subtype_le {X : Type} [Fintype X] [Nonempty X] (P : X → Prop)
    [DecidablePred P] [Nonempty {x : X // P x}] :
    ((PMF.uniformOfFintype {x : X // P x}).map Subtype.val).etvDist (PMF.uniformOfFintype X)
      ≤ (PMF.uniformOfFintype X).toOuterMeasure {x | ¬ P x} := by
  classical
  rw [etvDist_eq_tsum_tsub, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases inside : P x
  · have mass : ((PMF.uniformOfFintype {x : X // P x}).map Subtype.val) x
        = (Fintype.card {x : X // P x} : ℝ≥0∞)⁻¹ := by
      rw [uniform_map_apply]
      have one : Fintype.card {y : {x : X // P x} // y.1 = x} = 1 :=
        Fintype.card_eq_one_iff.mpr ⟨⟨⟨x, inside⟩, rfl⟩, fun y => Subtype.ext (Subtype.ext y.2)⟩
      rw [one, Nat.cast_one, one_mul]
    rw [mass, PMF.uniformOfFintype_apply]
    have smaller : Fintype.card {x : X // P x} ≤ Fintype.card X := Fintype.card_subtype_le P
    rw [tsub_eq_zero_of_le (ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr smaller))]
    simp
  · rw [Set.indicator_of_mem (show x ∈ {x | ¬ P x} from inside)]
    exact tsub_le_self

/-- Horner at a uniform tail is uniform: shifting the head moves every fibre onto every other. -/
theorem horner_uniform (f : G →+ G) (n : ℕ) :
    (PMF.uniformOfFintype (Fin (n + 1) → G)).map (horner f (n + 1))
      = PMF.uniformOfFintype G := by
  refine uniform_map_of_fibre_equiv _ fun first second => ?_
  let bump : (Fin (n + 1) → G) := Fin.cons (second - first) 0
  have moved : ∀ points : Fin (n + 1) → G,
      horner f (n + 1) (points + bump) = horner f (n + 1) points + (second - first) := by
    intro points
    rw [horner_add]
    congr 1
    simp only [bump, horner, Fin.cons_zero, Fin.tail_cons]
    have zero : ∀ m, horner f m (0 : Fin m → G) = 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => simp only [horner]; rw [show Fin.tail (0 : Fin (m + 1) → G) = 0 from rfl, ih,
          map_zero, Pi.zero_apply, add_zero]
    rw [zero, map_zero, add_zero]
  exact (Equiv.addRight bump).subtypeEquiv fun points => by
    show horner f (n + 1) points = first ↔ horner f (n + 1) (points + bump) = second
    rw [moved]
    constructor
    · intro same; rw [same]; abel
    · intro same; have := congrArg (· - (second - first)) same; simpa using this

/-- **Each simulator digit point hits a fixed target with probability at most `1 / #G`.** -/
theorem clamp_hit_le (f : G →+ G) (injective : Function.Injective f) (output : G) (n : ℕ)
    (digit : Fin (n + 2)) (target : G) :
    (PMF.uniformOfFintype (Fin (n + 1) → G)).toOuterMeasure
        {tail | clampPoints f output tail digit = target}
      ≤ (Fintype.card G : ℝ≥0∞)⁻¹ := by
  classical
  refine Fin.cases ?_ (fun place => ?_) digit
  · -- the head: `output - f (H tail) = target` pins `H tail` to at most one value
    by_cases reachable : ∃ value, f value = output - target
    · obtain ⟨value, hvalue⟩ := reachable
      have set_eq : {tail : Fin (n + 1) → G | clampPoints f output tail 0 = target}
          = horner f (n + 1) ⁻¹' {value} := by
        ext tail
        simp only [clampPoints, Fin.cons_zero, Set.mem_setOf_eq, Set.mem_preimage,
          Set.mem_singleton_iff]
        constructor
        · intro same
          apply injective
          rw [hvalue, ← same]
          abel
        · intro same
          rw [same, hvalue]
          abel
      rw [set_eq, ← PMF.toOuterMeasure_map_apply, horner_uniform,
        PMF.toOuterMeasure_uniformOfFintype_apply]
      simp
    · have empty : {tail : Fin (n + 1) → G | clampPoints f output tail 0 = target} = ∅ := by
        ext tail
        simp only [clampPoints, Fin.cons_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false]
        intro same
        exact reachable ⟨horner f (n + 1) tail, by rw [← same]; abel⟩
      rw [empty, MeasureTheory.measure_empty]
      simp
  · -- a tail point: one uniform coordinate
    have set_eq : {tail : Fin (n + 1) → G | clampPoints f output tail place.succ = target}
        = (fun tail : Fin (n + 1) → G => tail place) ⁻¹' {target} := by
      ext tail
      simp [clampPoints]
    have coordinate : (PMF.uniformOfFintype (Fin (n + 1) → G)).map (fun tail => tail place)
        = PMF.uniformOfFintype G :=
      uniform_map_of_fibre_equiv _ fun first second =>
        (Equiv.addRight (Pi.single place (second - first))).subtypeEquiv fun tail => by
          show tail place = first
            ↔ tail place + (Pi.single place (second - first) : Fin (n + 1) → G) place = second
          rw [Pi.single_eq_same]
          constructor
          · intro same; rw [same]; abel
          · intro same; have := congrArg (· - (second - first)) same; simpa using this
    rw [set_eq, ← PMF.toOuterMeasure_map_apply, coordinate,
      PMF.toOuterMeasure_uniformOfFintype_apply]
    simp

/-- **Union over the digits.** The simulator's points hit one of `n + 2` fixed targets with
probability at most `(n + 2) / #G`. -/
theorem clamp_anyHit_le (f : G →+ G) (injective : Function.Injective f) (output : G) (n : ℕ)
    (targets : Fin (n + 2) → G) :
    (PMF.uniformOfFintype (Fin (n + 1) → G)).toOuterMeasure
        {tail | ∃ digit, clampPoints f output tail digit = targets digit}
      ≤ ((n + 2 : ℕ) : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have union : {tail : Fin (n + 1) → G | ∃ digit, clampPoints f output tail digit = targets digit}
      = ⋃ digit, {tail | clampPoints f output tail digit = targets digit} := by
    ext tail; simp
  rw [union]
  refine le_trans (MeasureTheory.measure_iUnion_fintype_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun digit _ =>
    clamp_hit_le f injective output n digit (targets digit)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The statistical cost of the offset restriction**: the construction's point law is within
`(n + 2) / #G` of the simulator's (`91 / #G` for `90` tail points). -/
theorem digitPoints_good_etvDist_le (f : G →+ G) (injective : Function.Injective f) {n : ℕ}
    (multiples : Fin (n + 2) → G) (output : G) (hits : horner f (n + 2) multiples = output)
    [Nonempty {tail : Fin (n + 1) → G // GoodTail f tail}]
    [Nonempty {tail : Fin (n + 1) → G // NoHit f output multiples tail}] :
    ((PMF.uniformOfFintype {tail : Fin (n + 1) → G // GoodTail f tail}).map
        (fun tail => realPoints f multiples tail.1)).etvDist
      ((PMF.uniformOfFintype (Fin (n + 1) → G)).map (clampPoints f output))
      ≤ ((n + 2 : ℕ) : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  rw [digitPoints_good_law f multiples output hits]
  have factor : (fun tail : {tail : Fin (n + 1) → G // NoHit f output multiples tail} =>
      clampPoints f output tail.1) = clampPoints f output ∘ Subtype.val := rfl
  rw [factor, ← PMF.map_comp]
  refine le_trans (etvDist_map_le' _ _ _) (le_trans (etvDist_uniform_subtype_le _) ?_)
  refine le_trans (le_of_eq (congrArg _ ?_)) (clamp_anyHit_le f injective output n multiples)
  ext tail
  simp [NoHit]

end Horner

/-! ### The rows: homogeneous lifts -/

section Lift

variable [FieldCertificate] [GroupCertificate]

/-- **The homogeneous lift** of a point at a scale pair: `(λ² x, t² y, λ)` for a finite point,
`(λ², 0, 0)` for the identity. -/
def lift (point : Point) (scale signScale : BaseField) : HomogeneousValue :=
  match point with
  | .zero => ⟨scale ^ 2, 0, 0⟩
  | .some x y _ => ⟨scale ^ 2 * x, signScale ^ 2 * y, scale⟩

/-- A lift decodes to its point. -/
theorem decode_lift (point : Point) {scale signScale : BaseField} (nonzero : scale ≠ 0)
    (signNonzero : signScale ≠ 0) (digit tripleDigit : Digit) (inputPoint : Point) :
    Garbling.decodeHomogeneous (lift point scale signScale) digit tripleDigit inputPoint =
      some point := by
  cases point with
  | zero =>
      unfold lift Garbling.decodeHomogeneous
      dsimp only
      rw [if_pos rfl, if_neg (pow_ne_zero 2 nonzero)]
      rfl
  | some x y valid =>
      have onCurve : OnCurve ⟨x, y⟩ :=
        (equation_iff_onCurve ⟨x, y⟩).mp
          ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mpr valid)
      have yNe : y ≠ 0 := JacobianMixed.noAffineYZero ⟨x, y⟩ onCurve
      have cubic : x ^ 3 + 3 = y ^ 2 := onCurve.symm
      unfold lift Garbling.decodeHomogeneous
      dsimp only
      rw [if_neg nonzero, if_neg (mul_ne_zero (pow_ne_zero 2 signNonzero) yNe)]
      have xs : scale ^ 2 * x / scale ^ 2 = x := by field_simp
      rw [xs, cubic, JacobianMixed.signRoot _ _ signNonzero,
        JacobianMixed.decodePoint_eq_affinePoint _ onCurve]
      rfl

/-- **Digit zero**: the row is the offset's lift at `(ρ, τ)`. -/
theorem realRow_digitZero (offset : AffineInput) (onCurve : OnCurve offset) (input : AffineInput)
    (rho tau : BaseField) :
    evaluateRow (Coordinates.rows offset none rho tau) input
      = lift (JacobianMixed.affinePoint offset onCurve) rho tau := by
  rw [evaluateRowsNone]
  rfl

/-- **Non-zero digit, `x' ≠ k_x`**: the row is the lift of `T + K` at `(ρ (x' − k_x), τ L)`. -/
theorem realRow_xNe (offset input : AffineInput) (offsetOnCurve : OnCurve offset)
    (inputOnCurve : OnCurve input) (xNe : input.x ≠ offset.x) (rho tau : BaseField) :
    (⟨rho ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset) input,
      tau ^ 2 * Coordinates.evaluate (Coordinates.signCoefficients offset) input,
      rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input⟩ : HomogeneousValue)
      = lift (JacobianMixed.affinePoint input inputOnCurve
          + JacobianMixed.affinePoint offset offsetOnCurve) (rho * (input.x - offset.x))
          (tau * Coordinates.tangentLine offset input) := by
  have dNe : input.x - offset.x ≠ 0 := sub_ne_zero.mpr xNe
  have xValue : Coordinates.evaluate (Coordinates.xCoefficients offset) input =
      (input.x - offset.x) ^ 2 * curve.toAffine.addX input.x offset.x
        (curve.toAffine.slope input.x offset.x input.y offset.y) := by
    rw [← JacobianMixed.xRow_div offset input offsetOnCurve inputOnCurve xNe]
    field_simp
  have sValue := JacobianMixed.signValue offset input offsetOnCurve inputOnCurve xNe
  have zValue : Coordinates.evaluate (Coordinates.zCoefficients offset) input =
      input.x - offset.x := Coordinates.evaluateZ offset input
  simp only [JacobianMixed.affinePoint]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne xNe]
  simp only [lift]
  rw [xValue, sValue, zValue]
  congr 1 <;> ring

/-- The sign row vanishes at `T = −K`: the tangent at `−K` passes through `−K`. -/
theorem sign_neg (offset input : AffineInput) (offsetOnCurve : OnCurve offset)
    (sameX : input.x = offset.x) (negY : input.y = -offset.y) :
    Coordinates.evaluate (Coordinates.signCoefficients offset) input = 0 := by
  have curveK : offset.y ^ 2 = offset.x ^ 3 + 3 := offsetOnCurve
  simp only [Coordinates.evaluate, Coordinates.signCoefficients]
  rw [sameX, negY]
  linear_combination (3 * offset.y ^ 3 - 81 * offset.y) * curveK

/-- **The inverse case `T = −K`**: the row is the identity's lift at `2 ρ k_y`. -/
theorem realRow_neg (offset input : AffineInput) (offsetOnCurve : OnCurve offset)
    (inputOnCurve : OnCurve input) (sameX : input.x = offset.x) (negY : input.y = -offset.y)
    (rho tau : BaseField) :
    (⟨rho ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset) input,
      tau ^ 2 * Coordinates.evaluate (Coordinates.signCoefficients offset) input,
      rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input⟩ : HomogeneousValue)
      = lift 0 (2 * rho * offset.y) tau := by
  rw [Coordinates.exceptionalX offset input offsetOnCurve inputOnCurve sameX,
    sign_neg offset input offsetOnCurve sameX negY,
    Coordinates.exceptionalZ offset input sameX, negY]
  show _ = (⟨(2 * rho * offset.y) ^ 2, 0, 0⟩ : HomogeneousValue)
  congr 1 <;> ring

/-- **The doubling case `T = K`**: the row has `X = Z = 0`, which no lift has. -/
theorem realRow_double (offset input : AffineInput) (offsetOnCurve : OnCurve offset)
    (inputOnCurve : OnCurve input) (sameX : input.x = offset.x) (sameY : input.y = offset.y)
    (rho tau : BaseField) :
    rho ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset) input = 0 ∧
      rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input = 0 := by
  rw [Coordinates.exceptionalX offset input offsetOnCurve inputOnCurve sameX,
    Coordinates.exceptionalZ offset input sameX, sameY]
  constructor <;> ring

/-- No lift at a nonzero scale has `X = Z = 0`. -/
theorem lift_not_double (point : Point) {scale : BaseField} (nonzero : scale ≠ 0)
    (signScale : BaseField) :
    ¬ ((lift point scale signScale).x = 0 ∧ (lift point scale signScale).z = 0) := by
  cases point with
  | zero => exact fun both => pow_ne_zero 2 nonzero both.1
  | some x y valid => exact fun both => nonzero both.2

/-- **The sign row's other zero `T = 2K`** (`L = 0`, `x' ≠ k_x`): the row has `S = 0 ≠ Z`, which
no lift has. -/
theorem realRow_triple (offset input : AffineInput) (offsetOnCurve : OnCurve offset)
    (inputOnCurve : OnCurve input) (xNe : input.x ≠ offset.x)
    (lineZero : Coordinates.tangentLine offset input = 0) (rho tau : BaseField) (rhoNe : rho ≠ 0) :
    tau ^ 2 * Coordinates.evaluate (Coordinates.signCoefficients offset) input = 0 ∧
      rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input ≠ 0 := by
  constructor
  · rw [JacobianMixed.signValue offset input offsetOnCurve inputOnCurve xNe, lineZero]
    ring
  · rw [Coordinates.evaluateZ offset input]
    exact mul_ne_zero rhoNe (sub_ne_zero.mpr xNe)

/-- No lift at a nonzero sign scale has `S = 0 ≠ Z`: a finite point has `y ≠ 0`. -/
theorem lift_not_triple (point : Point) (scale : BaseField) {signScale : BaseField}
    (signNonzero : signScale ≠ 0) :
    ¬ ((lift point scale signScale).y = 0 ∧ (lift point scale signScale).z ≠ 0) := by
  cases point with
  | zero => exact fun both => both.2 rfl
  | some x y valid =>
      have onCurve : OnCurve ⟨x, y⟩ :=
        (equation_iff_onCurve ⟨x, y⟩).mp
          ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mpr valid)
      exact fun both => mul_ne_zero (pow_ne_zero 2 signNonzero)
        (JacobianMixed.noAffineYZero ⟨x, y⟩ onCurve) both.1

/-- The non-zero field elements, the range of `ρ` and of `λ`. -/
abbrev NonZeroField := {value : BaseField // value ≠ 0}

instance : Nonempty NonZeroField := ⟨⟨1, one_ne_zero⟩⟩

/-- Multiplication by a non-zero constant, as a bijection of `F_p^*`. -/
def scaleEquiv (factor : BaseField) (nonzero : factor ≠ 0) : NonZeroField ≃ NonZeroField where
  toFun value := ⟨value.1 * factor, mul_ne_zero value.2 nonzero⟩
  invFun value := ⟨value.1 * factor⁻¹, mul_ne_zero value.2 (inv_ne_zero nonzero)⟩
  left_inv value := Subtype.ext (by field_simp)
  right_inv value := Subtype.ext (by field_simp)

/-- **The lift law, jointly over all digits.** For fixed points and any non-zero multiplier pairs,
lifting at `(ρ_d · c_d, τ_d · e_d)` with `(ρ, τ)` uniform on `((F_p^*)²)^m` is lifting at a uniform
`(λ, t)`. -/
theorem lifts_law {m : ℕ} (points : Fin m → Point) (multiplier signMultiplier : Fin m → BaseField)
    (nonzero : ∀ digit, multiplier digit ≠ 0) (signNonzero : ∀ digit, signMultiplier digit ≠ 0) :
    (PMF.uniformOfFintype (Fin m → NonZeroField × NonZeroField)).map
        (fun scales digit => lift (points digit) ((scales digit).1.1 * multiplier digit)
          ((scales digit).2.1 * signMultiplier digit))
      = (PMF.uniformOfFintype (Fin m → NonZeroField × NonZeroField)).map
        (fun scales digit => lift (points digit) (scales digit).1.1 (scales digit).2.1) := by
  let rescale : (Fin m → NonZeroField × NonZeroField) ≃ (Fin m → NonZeroField × NonZeroField) :=
    Equiv.piCongrRight fun digit => (scaleEquiv (multiplier digit) (nonzero digit)).prodCongr
      (scaleEquiv (signMultiplier digit) (signNonzero digit))
  have factor : (fun (scales : Fin m → NonZeroField × NonZeroField) digit =>
        lift (points digit) ((scales digit).1.1 * multiplier digit)
          ((scales digit).2.1 * signMultiplier digit))
      = (fun (scales : Fin m → NonZeroField × NonZeroField) digit =>
          lift (points digit) (scales digit).1.1 (scales digit).2.1) ∘ rescale := rfl
  rw [factor, ← PMF.map_comp, uniformOfFintype_map_equiv rescale]

/-- **The row law given the points, for any point law.** Whatever law the digit points have, rows
lifted at `(ρ_d · c_d(D), τ_d · e_d(D))` (non-zero multipliers that may depend on the points and on
anything fixed, such as the digit multiples) have exactly the law of rows lifted at uniform
`(λ, t)` — which depends on the point law alone. -/
theorem rowsLaw_eq {m : ℕ} (pointsLaw : PMF (Fin m → Point))
    (multiplier signMultiplier : (Fin m → Point) → Fin m → BaseField)
    (nonzero : ∀ points digit, multiplier points digit ≠ 0)
    (signNonzero : ∀ points digit, signMultiplier points digit ≠ 0) :
    pointsLaw.bind (fun points => (PMF.uniformOfFintype (Fin m → NonZeroField × NonZeroField)).map
        (fun scales digit => lift (points digit) ((scales digit).1.1 * multiplier points digit)
          ((scales digit).2.1 * signMultiplier points digit)))
      = pointsLaw.bind (fun points =>
          (PMF.uniformOfFintype (Fin m → NonZeroField × NonZeroField)).map
            (fun scales digit => lift (points digit) (scales digit).1.1 (scales digit).2.1)) :=
  congrArg _ (funext fun points => lifts_law points (multiplier points) (signMultiplier points)
    (nonzero points) (signNonzero points))

end Lift

/-! ### The BN254 instance of the digit-point law -/

section Instance

variable [FieldCertificate] [GroupCertificate]

/-- The radix map `radix • ·` on points. -/
def radixMap : Point →+ Point := DistribSMul.toAddMonoidHom Point radix

theorem radix_ne_zero : radix ≠ 0 := by
  unfold radix
  decide

/-- `radix • ·` is injective: `radix ≠ 0` in the prime field `F_r`. -/
theorem radixMap_injective : Function.Injective radixMap := by
  haveI : Fact (Nat.Prime scalarFieldModulus) := ⟨scalarFieldPrime⟩
  intro first second same
  have := congrArg (fun point : Point => radix⁻¹ • point) same
  simpa only [radixMap, DistribSMul.toAddMonoidHom_apply, inv_smul_smul₀ radix_ne_zero]
    using this

/-- **The digit-point law at BN254**, `90` tail points: exact for uniform offsets, at every output
including the identity. -/
theorem bn254_digitPoints_law [Fintype Point] (multiples : Fin 91 → Point) (output : Point)
    (hits : horner radixMap 91 multiples = output) :
    (PMF.uniformOfFintype (Fin 90 → Point)).map (realPoints radixMap multiples)
      = (PMF.uniformOfFintype (Fin 90 → Point)).map (clampPoints radixMap output) :=
  digitPoints_law radixMap multiples output hits

/-- **The offset restriction at BN254 costs at most `91 / #Point`.** -/
theorem bn254_digitPoints_good_etvDist_le [Fintype Point] (multiples : Fin 91 → Point)
    (output : Point) (hits : horner radixMap 91 multiples = output)
    [Nonempty {tail : Fin 90 → Point // GoodTail radixMap tail}]
    [Nonempty {tail : Fin 90 → Point // NoHit radixMap output multiples tail}] :
    ((PMF.uniformOfFintype {tail : Fin 90 → Point // GoodTail radixMap tail}).map
        (fun tail => realPoints radixMap multiples tail.1)).etvDist
      ((PMF.uniformOfFintype (Fin 90 → Point)).map (clampPoints radixMap output))
      ≤ (91 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  classical
  have := digitPoints_good_etvDist_le (n := 89) radixMap radixMap_injective multiples output hits
  simpa using this

/-- The exceptional digit points of a multiple `T`: `2 T` (the doubling input `T = K`) and
`(3/2) T` (the sign row's other zero `T = 2K`). -/
def Exceptional (multiple point : Point) : Prop :=
  point = multiple + multiple ∨ point = Garbling.threeHalves • multiple

/-- **The exceptional event under the simulator's point law**: some digit point is exceptional
for its multiple with probability at most `182 / #Point` (`91` for each of the two targets). -/
theorem bn254_doubling_le [Fintype Point] (multiples : Fin 91 → Point) (output : Point) :
    (PMF.uniformOfFintype (Fin 90 → Point)).toOuterMeasure
        {tail | ∃ digit, Exceptional (multiples digit) (clampPoints radixMap output tail digit)}
      ≤ (182 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  classical
  have double := clamp_anyHit_le (n := 89) radixMap radixMap_injective output
    (fun digit => multiples digit + multiples digit)
  have triple := clamp_anyHit_le (n := 89) radixMap radixMap_injective output
    (fun digit => Garbling.threeHalves • multiples digit)
  have split : {tail : Fin 90 → Point |
      ∃ digit, Exceptional (multiples digit) (clampPoints radixMap output tail digit)} =
      {tail | ∃ digit, clampPoints radixMap output tail digit = multiples digit + multiples digit} ∪
      {tail | ∃ digit, clampPoints radixMap output tail digit =
        Garbling.threeHalves • multiples digit} := by
    ext tail
    simp only [Exceptional, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨digit, same | same⟩
      · exact Or.inl ⟨digit, same⟩
      · exact Or.inr ⟨digit, same⟩
    · rintro (⟨digit, same⟩ | ⟨digit, same⟩)
      · exact ⟨digit, Or.inl same⟩
      · exact ⟨digit, Or.inr same⟩
  rw [split]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  calc _ ≤ (91 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ +
        (91 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := add_le_add (by simpa using double)
          (by simpa using triple)
    _ = (182 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
        rw [← add_mul]
        norm_num

/-- An event's mass moves by at most the total-variation distance. -/
theorem toOuterMeasure_le_add_etvDist {A : Type} (first second : PMF A) (event : Set A) :
    first.toOuterMeasure event ≤ second.toOuterMeasure event + first.etvDist second := by
  rw [PMF.etvDist_comm, etvDist_eq_tsum_tsub, PMF.toOuterMeasure_apply,
    PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun point => ?_
  by_cases inside : point ∈ event
  · rw [Set.indicator_of_mem inside, Set.indicator_of_mem inside]
    exact le_add_tsub
  · rw [Set.indicator_of_notMem inside]
    exact zero_le

/-- **The exceptional event under the construction's point law**: at most `273 / #Point` — the
simulator's `182 / #Point` plus the offset-restriction distance. -/
theorem bn254_doubling_real_le [Fintype Point] (multiples : Fin 91 → Point) (output : Point)
    (hits : horner radixMap 91 multiples = output)
    [Nonempty {tail : Fin 90 → Point // GoodTail radixMap tail}]
    [Nonempty {tail : Fin 90 → Point // NoHit radixMap output multiples tail}] :
    ((PMF.uniformOfFintype {tail : Fin 90 → Point // GoodTail radixMap tail}).map
        (fun tail => realPoints radixMap multiples tail.1)).toOuterMeasure
        {points | ∃ digit, Exceptional (multiples digit) (points digit)}
      ≤ (273 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  classical
  refine le_trans (toOuterMeasure_le_add_etvDist _
    ((PMF.uniformOfFintype (Fin 90 → Point)).map (clampPoints radixMap output)) _) ?_
  have idealMass : ((PMF.uniformOfFintype (Fin 90 → Point)).map
      (clampPoints radixMap output)).toOuterMeasure
        {points | ∃ digit, Exceptional (multiples digit) (points digit)}
      ≤ (182 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
    rw [PMF.toOuterMeasure_map_apply]
    exact bn254_doubling_le multiples output
  refine le_trans (add_le_add idealMass
    (bn254_digitPoints_good_etvDist_le multiples output hits)) (le_of_eq ?_)
  rw [← add_mul]
  norm_num

end Instance

end

end Kriterion.ArgoMAC.Security.Phase3
