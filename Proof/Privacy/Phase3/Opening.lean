/-
**Phase 3, P1, theorem 2 — the output-aware opening.**

`B-output-aware-simulator.md` §1.1–1.3 and `B-review.md` (1).

### (a) The row solve

With the published constants `γ = rows[d]` and the input `u` fixed, each of a digit's three rows is
affine in the eight delivered element values (`evaluateGamma_eq_affine`: a `γ`-and-`u` constant
plus the linear form `rowLinear u`, which does not mention `γ`), and each row has a **collector**
that no other row reads (see `rowLinear`): `rowX_x9` for `X` and `rowZ_x9` for `Z`, with
coefficient one, and `rowY_cubic` for `Y`, with coefficient `x²`. All three are x-type elements of
lane `pointX`. Every curve point has `x ≠ 0` (`onCurve_x_ne_zero`), so the `Y` solve divides by
`x²`.

`collectorEquiv γ u v : F_p³ ≃ HomogeneousValue` is the solve: its forward map writes the collector
triple into `v` and evaluates the three rows, its inverse is the closed form `collectorSolve`
(note §1.3, E3), for `x ≠ 0`. `collectorSolve` reads `v` only at the five non-collector elements,
so for every fixed value of the five free elements and the eleven published constants the
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

**The rows.** `lift D λ = (λ² x, λ³ y, λ)` for a finite point and `(λ², λ³, 0)` for `O`. The real
row of a digit is (`realRow_digitZero`, `realRow_xNe`, `realRow_neg`):
digit zero `lift K ρ`; nonzero digit with `x' ≠ k_x` `lift (T + K) (ρ (x' − k_x))`; inverse case
`T = −K` `lift O (2 ρ k_y)`. In all three the multiplier is non-zero, so under a uniform `ρ ∈ F_p^*`
the row law is **exactly** the lift of `D` at a uniform `λ ∈ F_p^*` (`lifts_law`, jointly over
all digits for any law of the points: `rowsLaw_eq`). The **doubling** case `T = K` gives the row
`(0, 0, 0)` (`realRow_double`), which the gadget resolves; **no lift is ever `(0, 0, 0)`**
(`lift_ne_zero`), so the simulator never produces a doubling row. That event is the second
statistical cost; under the simulator's point law each digit hits any fixed target point with
probability at most `1 / #G` (`clamp_hit_le`), so the doubling event `∃ d, D_d = 2 T_d` has mass at
most `91 / #Point` under the simulator's law (`bn254_doubling_le`) and at most `182 / #Point` under
the construction's (`bn254_doubling_real_le`, adding the offset-restriction distance). The
exception gadget is **not** smoothed over: it is exactly this event, charged, and never
simulated. Together the two costs are the note's `ε_pt = 182 / (r − 1)` order term.
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
  y := values (.inl .rowY_mixed) * input.y + values (.inl .rowY_cubic) * input.x ^ 2
    + values (.inr .rowY_y8) * input.y + values (.inr .rowY_y10)
  z := values (.inl .rowZ_x9)

/-- The row triple's constant part: the published constants on the input's monomials. -/
def rowConstant (gamma : RowGamma) (input : AffineInput) : HomogeneousValue where
  x := gamma.xC0 + gamma.xC1 * input.x + gamma.xC2 * input.y + gamma.xC4 * input.x ^ 2
  y := gamma.yC0 + gamma.yC2 * input.y + gamma.yC3 * input.x * input.y + gamma.yC4 * input.x ^ 2
    + gamma.yC5 * input.y ^ 2
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
target, given the published constants and the five other delivered values. The `Y` component
divides by the `Y` collector's coefficient `x²`, as the inverse `(x · x)⁻¹` (the machine's
`Opening.finishScaled`; the inverse of `0` is `0`, and on the curve `x ≠ 0`). -/
def collectorSolve (gamma : RowGamma) (input : AffineInput)
    (values : Biquadratic.Values) (target : HomogeneousValue) : BaseField × BaseField × BaseField :=
  (target.x - (gamma.xC0 + gamma.xC1 * input.x + gamma.xC2 * input.y + gamma.xC4 * input.x ^ 2
      + values (.inl .rowX_x7) * input.x + values (.inr .rowX_y10)),
   (target.y - (gamma.yC0 + gamma.yC2 * input.y + gamma.yC3 * input.x * input.y
      + gamma.yC4 * input.x ^ 2 + gamma.yC5 * input.y ^ 2 + values (.inl .rowY_mixed) * input.y
      + values (.inr .rowY_y8) * input.y + values (.inr .rowY_y10))) * (input.x * input.x)⁻¹,
   target.z - (gamma.zC0 + gamma.zC1 * input.x))

/-- **The collector triple and the row triple determine each other**, for every fixed value of the
five free elements and the published constants, when `x ≠ 0`. -/
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

/-- **The homogeneous lift** of a point at a scale: `(λ² x, λ³ y, λ)` for a finite point,
`(λ², λ³, 0)` for the identity. -/
def lift (point : Point) (scale : BaseField) : HomogeneousValue :=
  match point with
  | .zero => ⟨scale ^ 2, scale ^ 3, 0⟩
  | .some x y _ => ⟨scale ^ 2 * x, scale ^ 3 * y, scale⟩

/-- **No lift is the doubling row.** -/
theorem lift_ne_zero (point : Point) {scale : BaseField} (nonzero : scale ≠ 0) :
    lift point scale ≠ ⟨0, 0, 0⟩ := by
  cases point with
  | zero =>
      intro same
      have := congrArg HomogeneousValue.x same
      exact pow_ne_zero 2 nonzero this
  | some x y valid =>
      intro same
      have := congrArg HomogeneousValue.z same
      exact nonzero this

/-- A lift decodes to its point. -/
theorem decode_lift (point : Point) {scale : BaseField} (nonzero : scale ≠ 0) (digit : Digit)
    (inputPoint : Point) :
    Garbling.decodeHomogeneous (lift point scale) digit inputPoint = some point := by
  cases point with
  | zero =>
      unfold lift Garbling.decodeHomogeneous
      dsimp only
      rw [if_pos rfl, if_neg (fun both => pow_ne_zero 2 nonzero both.1)]
      rfl
  | some x y valid =>
      unfold lift Garbling.decodeHomogeneous
      dsimp only
      rw [if_neg nonzero]
      have xs : scale ^ 2 * x / scale ^ 2 = x := by field_simp
      have ys : scale ^ 3 * y / scale ^ 3 = y := by field_simp
      rw [xs, ys]
      have onCurve : OnCurve ⟨x, y⟩ :=
        (equation_iff_onCurve ⟨x, y⟩).mp
          ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mpr valid)
      rw [JacobianMixed.decodePoint_eq_affinePoint _ onCurve]
      rfl

/-- A row with non-zero `Z` that decodes to a point is that point's lift at scale `Z`. -/
theorem eq_lift_of_decode (row : HomogeneousValue) (digit : Digit)
    (inputPoint point : Point)
    (decoded : Garbling.decodeHomogeneous row digit inputPoint = some point)
    (nonzero : row.z ≠ 0) :
    row = lift point row.z := by
  obtain ⟨X, Y, Z⟩ := row
  change Z ≠ 0 at nonzero
  simp only [Garbling.decodeHomogeneous, if_neg nonzero, decodePoint] at decoded
  split_ifs at decoded with valid
  cases decoded
  simp only [lift]
  congr 1 <;> field_simp

/-- **Digit zero**: the row is the offset's lift at `ρ`. -/
theorem realRow_digitZero (offset : AffineInput) (onCurve : OnCurve offset) (input : AffineInput)
    (rho : BaseField) :
    evaluateRow (Coordinates.rows offset none rho) input
      = lift (JacobianMixed.affinePoint offset onCurve) rho := by
  rw [evaluateRowsNone]
  rfl

/-- **Non-zero digit, `x' ≠ k_x`**: the row is the lift of `T + K` at `ρ (x' − k_x)`. -/
theorem realRow_xNe (offset input : AffineInput) (offsetOnCurve : OnCurve offset)
    (inputOnCurve : OnCurve input) (xNe : input.x ≠ offset.x) (rho : BaseField) (rhoNe : rho ≠ 0) :
    (⟨rho ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset) input,
      rho ^ 3 * Coordinates.evaluate (Coordinates.yCoefficients offset) input,
      rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input⟩ : HomogeneousValue)
      = lift (JacobianMixed.affinePoint input inputOnCurve
          + JacobianMixed.affinePoint offset offsetOnCurve) (rho * (input.x - offset.x)) := by
  have decoded := JacobianMixed.decodeJacobianOfXNe offset input offsetOnCurve inputOnCurve xNe
    rho rhoNe .zero 0
  have zValue : rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input
      = rho * (input.x - offset.x) := by rw [Coordinates.evaluateZ]; rfl
  have nonzero : rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input ≠ 0 := by
    rw [zValue]; exact mul_ne_zero rhoNe (sub_ne_zero.mpr xNe)
  have := eq_lift_of_decode _ .zero 0 _ decoded nonzero
  rw [this]
  simp only
  rw [zValue]

/-- **The inverse case `T = −K`**: the row is the identity's lift at `2 ρ k_y`. -/
theorem realRow_neg (offset input : AffineInput) (offsetOnCurve : OnCurve offset)
    (inputOnCurve : OnCurve input) (sameX : input.x = offset.x) (negY : input.y = -offset.y)
    (rho : BaseField) :
    (⟨rho ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset) input,
      rho ^ 3 * Coordinates.evaluate (Coordinates.yCoefficients offset) input,
      rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input⟩ : HomogeneousValue)
      = lift 0 (2 * rho * offset.y) := by
  rw [Coordinates.exceptionalX offset input offsetOnCurve inputOnCurve sameX,
    Coordinates.exceptionalY offset input offsetOnCurve inputOnCurve sameX,
    Coordinates.exceptionalZ offset input sameX, negY]
  show _ = (⟨(2 * rho * offset.y) ^ 2, (2 * rho * offset.y) ^ 3, 0⟩ : HomogeneousValue)
  congr 1 <;> ring

/-- **The doubling case `T = K`**: the row is `(0, 0, 0)`, which no lift is. -/
theorem realRow_double (offset input : AffineInput) (offsetOnCurve : OnCurve offset)
    (inputOnCurve : OnCurve input) (sameX : input.x = offset.x) (sameY : input.y = offset.y)
    (rho : BaseField) :
    (⟨rho ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset) input,
      rho ^ 3 * Coordinates.evaluate (Coordinates.yCoefficients offset) input,
      rho * Coordinates.evaluate (Coordinates.zCoefficients offset) input⟩ : HomogeneousValue)
      = ⟨0, 0, 0⟩ := by
  rw [Coordinates.exceptionalX offset input offsetOnCurve inputOnCurve sameX,
    Coordinates.exceptionalY offset input offsetOnCurve inputOnCurve sameX,
    Coordinates.exceptionalZ offset input sameX, sameY]
  congr 1 <;> ring

/-- The non-zero field elements, the range of `ρ` and of `λ`. -/
abbrev NonZeroField := {value : BaseField // value ≠ 0}

instance : Nonempty NonZeroField := ⟨⟨1, one_ne_zero⟩⟩

/-- Multiplication by a non-zero constant, as a bijection of `F_p^*`. -/
def scaleEquiv (factor : BaseField) (nonzero : factor ≠ 0) : NonZeroField ≃ NonZeroField where
  toFun value := ⟨value.1 * factor, mul_ne_zero value.2 nonzero⟩
  invFun value := ⟨value.1 * factor⁻¹, mul_ne_zero value.2 (inv_ne_zero nonzero)⟩
  left_inv value := Subtype.ext (by field_simp)
  right_inv value := Subtype.ext (by field_simp)

/-- **The lift law, jointly over all digits.** For fixed points and any non-zero multipliers,
lifting at `ρ_d · c_d` with `ρ` uniform on `(F_p^*)^m` is lifting at a uniform `λ`. -/
theorem lifts_law {m : ℕ} (points : Fin m → Point) (multiplier : Fin m → BaseField)
    (nonzero : ∀ digit, multiplier digit ≠ 0) :
    (PMF.uniformOfFintype (Fin m → NonZeroField)).map
        (fun rho digit => lift (points digit) ((rho digit).1 * multiplier digit))
      = (PMF.uniformOfFintype (Fin m → NonZeroField)).map
        (fun scale digit => lift (points digit) (scale digit).1) := by
  let rescale : (Fin m → NonZeroField) ≃ (Fin m → NonZeroField) :=
    Equiv.piCongrRight fun digit => scaleEquiv (multiplier digit) (nonzero digit)
  have factor : (fun (rho : Fin m → NonZeroField) digit =>
        lift (points digit) ((rho digit).1 * multiplier digit))
      = (fun (scale : Fin m → NonZeroField) digit => lift (points digit) (scale digit).1)
        ∘ rescale := rfl
  rw [factor, ← PMF.map_comp, uniformOfFintype_map_equiv rescale]

/-- **The row law given the points, for any point law.** Whatever law the digit points have, rows
lifted at `ρ_d · c_d(D)` (non-zero multipliers that may depend on the points and on anything
fixed, such as the digit multiples) have exactly the law of rows lifted at uniform `λ` — which
depends on the point law alone. -/
theorem rowsLaw_eq {m : ℕ} (pointsLaw : PMF (Fin m → Point))
    (multiplier : (Fin m → Point) → Fin m → BaseField)
    (nonzero : ∀ points digit, multiplier points digit ≠ 0) :
    pointsLaw.bind (fun points => (PMF.uniformOfFintype (Fin m → NonZeroField)).map
        (fun rho digit => lift (points digit) ((rho digit).1 * multiplier points digit)))
      = pointsLaw.bind (fun points => (PMF.uniformOfFintype (Fin m → NonZeroField)).map
        (fun scale digit => lift (points digit) (scale digit).1)) :=
  congrArg _ (funext fun points => lifts_law points (multiplier points) (nonzero points))

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

/-- **The doubling event under the simulator's point law**: some digit point is twice its
multiple (`T_d = K_d`) with probability at most `91 / #Point`. -/
theorem bn254_doubling_le [Fintype Point] (multiples : Fin 91 → Point) (output : Point) :
    (PMF.uniformOfFintype (Fin 90 → Point)).toOuterMeasure
        {tail | ∃ digit, clampPoints radixMap output tail digit = multiples digit + multiples digit}
      ≤ (91 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  classical
  have := clamp_anyHit_le (n := 89) radixMap radixMap_injective output
    (fun digit => multiples digit + multiples digit)
  simpa using this

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

/-- **The doubling event under the construction's point law**: at most `182 / #Point` — the
simulator's `91 / #Point` plus the offset-restriction distance. -/
theorem bn254_doubling_real_le [Fintype Point] (multiples : Fin 91 → Point) (output : Point)
    (hits : horner radixMap 91 multiples = output)
    [Nonempty {tail : Fin 90 → Point // GoodTail radixMap tail}]
    [Nonempty {tail : Fin 90 → Point // NoHit radixMap output multiples tail}] :
    ((PMF.uniformOfFintype {tail : Fin 90 → Point // GoodTail radixMap tail}).map
        (fun tail => realPoints radixMap multiples tail.1)).toOuterMeasure
        {points | ∃ digit, points digit = multiples digit + multiples digit}
      ≤ (182 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  classical
  refine le_trans (toOuterMeasure_le_add_etvDist _
    ((PMF.uniformOfFintype (Fin 90 → Point)).map (clampPoints radixMap output)) _) ?_
  have idealMass : ((PMF.uniformOfFintype (Fin 90 → Point)).map
      (clampPoints radixMap output)).toOuterMeasure
        {points | ∃ digit, points digit = multiples digit + multiples digit}
      ≤ (91 : ℝ≥0∞) * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
    rw [PMF.toOuterMeasure_map_apply]
    exact bn254_doubling_le multiples output
  refine le_trans (add_le_add idealMass
    (bn254_digitPoints_good_etvDist_le multiples output hits)) (le_of_eq ?_)
  rw [← add_mul]
  norm_num

end Instance

end

end Kriterion.ArgoMAC.Security.Phase3
