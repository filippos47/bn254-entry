/-
**Phase 3, P1, theorem 3 — F4: the JOINT exactness of `G1U → H`.**

`B-output-aware-simulator.md` §1.5, and `B-review.md` (3) and required change 2: the
note proved per-component bijections and asserted the joint statement. This module states and
proves **one** joint lemma, over all components at once, assembled from per-component
bijections by an explicit `Equiv` product — never by composing marginal statements.

### The object whose law is claimed

Fix the adversary's (valid) input `u` and the designated switch `(c*, j*)` (`JointShape`); the
active switches are `α^x_c = chunk_c(u.x)` on the x lanes and `α^y_c = chunk_c(u.y)` on the y lanes,
**separately**. Fix every quantity the simulator does *not* sample (`JointContext`): the true row
coefficients of the 91 digits (offsets, digits, `ρ`), the evaluator-visible part of every fold
join and gadget digest (as functions of the bridge key, since system B's labels are whitened by
`hash(t)`), and each gadget entry's slot and digit code — the labels and `Δ` are deferred into this
context, as the note says.

The **G1U coins** (`JointCoins`) are what is uniform after `G0 → G0U` (`MaskSwap`) and the
hidden-entry deletion of `G0U → G1U`: every scale mask of every lane (both point lanes of every
digit, both curve lanes, all 52 chunks, all `2 ^ b_c` switches), the curve coins `(t, mask, r1, r2)`, the hidden fold material of every (lane, chunk), and
the gadget pad and hidden digest part of every digit.

The claimed object is the **published cells** (`PublicCells`: every digit's joins on both lanes
and its three row constants, the curve joins and three constants, every fold join, every gadget
entry) **together with the visible masks** (`VisibleCells`: every inactive scale mask the
evaluator queries, minus the three designated collector masks per digit).

### The theorem

`jointExactness`: `(uniform JointCoins).map (published, visible) = uniform (PublicCells × VisibleCells)`
— exact, as a `PMF` equation. It is proved by one explicit bijection `jointEquiv :
JointCoins ≃ (PublicCells × VisibleCells) × Residual`, assembled by `Equiv.piCongrRight` over the
91 digits (`digitEquiv`: both lanes of the digit and its row constants), `Equiv.prodShear` over the
bridge key (`curveEquiv`, then the fold and gadget bijections, which depend on `t`), and a
reassociation.

`jointLaw` then gives the full statement the simulator needs: jointly with the published and
visible cells, the designated masks are **the simulator's collector solve** at the true rows
(`designated_eq_solve`) and the bridge key is **the evaluator's curve value** on the public and
visible cells (`bridgeKey_eq_eval`), so

```
(uniform coins).map (published, visible, designated, t)
  = (uniform (PublicCells × VisibleCells)).map (P, V ↦ (P, V, solve(P, V, W), tEval(P, V)))
```

with `W` the true rows at `u` — whose law given the output is `Opening`'s theorem.
-/

import Proof.Privacy.Phase3.Opening
import Proof.Privacy.Phase3.MaskSwap
import Proof.Privacy.PGS.FibreUniformity
import Proof.Correctness.CanonicalBits

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv sum_univ_eq_active_add)
open scoped ENNReal

noncomputable section

/-! ## The chunk/switch index and the element algebra -/

/-- A (chunk, switch of that chunk) pair: the index of one scale mask of one element. -/
abbrev ChunkSwitch := Σ c : Fin chunkCount, Fin (2 ^ chunkWidth c)

/-- One active switch per chunk: the chunk values of one coordinate. -/
abbrev Alpha := (c : Fin chunkCount) → Fin (2 ^ chunkWidth c)

/-- The place value of a chunk: `2 ^ chunkOffset c` (`PlanB.chunkScalar`). -/
def weight (c : Fin chunkCount) : BaseField := (2 : BaseField) ^ chunkOffset c

/-- `ι` at a (chunk, switch) pair. -/
def switchIota (cs : ChunkSwitch) : BaseField := iota _ cs.2

/-- **The published join of one chunk** (`PlanB.garbleScale`): `Σ_j Y_{c,j} + a · 2 ^ {off c}`. -/
def joinOf (Y : ChunkSwitch → BaseField) (a : BaseField) (c : Fin chunkCount) : BaseField :=
  (∑ j : Fin (2 ^ chunkWidth c), Y ⟨c, j⟩) + a * weight c

/-- **The element offset** (`PlanB.offsets`): `O = Σ_c Σ_j ι(j) Y_{c,j}`. -/
def offsetOf (Y : ChunkSwitch → BaseField) : BaseField :=
  ∑ c : Fin chunkCount, ∑ j : Fin (2 ^ chunkWidth c), iota _ j * Y ⟨c, j⟩

theorem offsetOf_eq_sum (Y : ChunkSwitch → BaseField) :
    offsetOf Y = ∑ cs : ChunkSwitch, switchIota cs * Y cs := by
  rw [offsetOf, Fintype.sum_sigma]
  rfl

section Element

variable (α : Alpha)

/-- A (chunk, switch) pair is active when the switch is the chunk's value. -/
def Active (cs : ChunkSwitch) : Prop := cs.2 = α cs.1

instance : DecidablePred (Active α) := fun cs => inferInstanceAs (Decidable (cs.2 = α cs.1))

/-- **The evaluator's delivered value** from the joins and the inactive masks
(`PlanB.evalScale`, summed over chunks; `FibreUniformity.psi_eq` is its per-chunk form). -/
def deliveredOf (J : Fin chunkCount → BaseField) (Y : ChunkSwitch → BaseField) : BaseField :=
  (∑ c : Fin chunkCount, iota _ (α c) * J c)
    + ∑ cs : {cs : ChunkSwitch // ¬ Active α cs}, (switchIota cs.1 - iota _ (α cs.1.1)) * Y cs.1

/-- `σ(α) = Σ_c ι(α_c) 2 ^ {off c}`: the coordinate itself (`sigmaOf_chunks`). -/
def sigmaOf : BaseField := ∑ c : Fin chunkCount, iota _ (α c) * weight c

/-- The chunks read back to the coordinate (`PlanB.chunk_recomposition`). -/
theorem sigmaOf_chunks (value : BaseField) :
    sigmaOf (fun c => chunkOf (coordWord value) c) = value := by
  rw [sigmaOf]
  conv_rhs => rw [← chunk_recomposition value]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [weight, mul_comm]

/-- The active pairs are one per chunk. -/
def activeEquiv : Fin chunkCount ≃ {cs : ChunkSwitch // Active α cs} where
  toFun c := ⟨⟨c, α c⟩, rfl⟩
  invFun cs := cs.1.1
  left_inv c := rfl
  right_inv cs := Subtype.ext (Sigma.ext rfl (heq_of_eq cs.2.symm))

/-- Split a sum over all pairs into the active switch of each chunk and the inactive pairs. -/
theorem sum_split_active (g : ChunkSwitch → BaseField) :
    ∑ cs, g cs = (∑ c, g ⟨c, α c⟩) + ∑ cs : {cs // ¬ Active α cs}, g cs.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (Active α) g,
    Fintype.sum_equiv (activeEquiv α) (fun c => g ⟨c, α c⟩) (fun cs => g cs.1) (fun c => rfl)]

/-- **Delivery (E1).** At the published joins, the evaluator's value is the element offset plus
the slope times the coordinate. -/
theorem deliveredOf_joinOf (Y : ChunkSwitch → BaseField) (a : BaseField) :
    deliveredOf α (joinOf Y a) Y = offsetOf Y + a * sigmaOf α := by
  have joins : (∑ c : Fin chunkCount, iota _ (α c) * joinOf Y a c)
      = (∑ cs : ChunkSwitch, iota _ (α cs.1) * Y cs) + a * sigmaOf α := by
    rw [Fintype.sum_sigma (fun cs : ChunkSwitch => iota _ (α cs.1) * Y cs), sigmaOf,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [joinOf, mul_add, Finset.mul_sum]
    ring
  rw [deliveredOf, joins, offsetOf_eq_sum,
    sum_split_active α (fun cs => iota _ (α cs.1) * Y cs),
    sum_split_active α (fun cs => switchIota cs * Y cs)]
  have same : ∀ c : Fin chunkCount,
      switchIota ⟨c, α c⟩ * Y ⟨c, α c⟩ = iota _ (α c) * Y ⟨c, α c⟩ := fun c => rfl
  simp only [same, sub_mul, Finset.sum_sub_distrib]
  ring

/-- The evaluator's value reads only the inactive masks. -/
theorem deliveredOf_congr (J : Fin chunkCount → BaseField)
    {first second : ChunkSwitch → BaseField}
    (agree : ∀ cs, ¬ Active α cs → first cs = second cs) :
    deliveredOf α J first = deliveredOf α J second := by
  unfold deliveredOf
  congr 1
  exact Finset.sum_congr rfl fun cs _ => by rw [agree cs.1 cs.2]

/-- The active mask recovered from the join (the open wire of `PlanB.evalScale`). -/
def hiddenOf (J : Fin chunkCount → BaseField) (a : BaseField) (Y : ChunkSwitch → BaseField)
    (c : Fin chunkCount) : BaseField :=
  J c - a * weight c - ∑ j : {j : Fin (2 ^ chunkWidth c) // j ≠ α c}, Y ⟨c, j.1⟩

/-- Overwrite the active mask of every chunk. -/
def withHidden (Y : ChunkSwitch → BaseField) (hidden : Fin chunkCount → BaseField) :
    ChunkSwitch → BaseField :=
  fun cs => if Active α cs then hidden cs.1 else Y cs

theorem withHidden_inactive (Y : ChunkSwitch → BaseField) (hidden : Fin chunkCount → BaseField)
    {cs : ChunkSwitch} (inactive : ¬ Active α cs) : withHidden α Y hidden cs = Y cs := by
  simp only [withHidden, if_neg inactive]

theorem joinOf_eq_split (Y : ChunkSwitch → BaseField) (a : BaseField) (c : Fin chunkCount) :
    joinOf Y a c = Y ⟨c, α c⟩ + (∑ j : {j : Fin (2 ^ chunkWidth c) // j ≠ α c}, Y ⟨c, j.1⟩)
      + a * weight c := by
  rw [joinOf, sum_univ_eq_active_add (α c) (fun j => Y ⟨c, j⟩)]

/-- **The hidden mask absorbs the join**: filling the active masks from the joins reproduces them. -/
theorem joinOf_withHidden_hiddenOf (J : Fin chunkCount → BaseField) (a : BaseField)
    (Y : ChunkSwitch → BaseField) :
    joinOf (withHidden α Y (hiddenOf α J a Y)) a = J := by
  funext c
  rw [joinOf_eq_split α]
  have active : withHidden α Y (hiddenOf α J a Y) ⟨c, α c⟩ = hiddenOf α J a Y c := by
    simp only [withHidden, Active, ↓reduceIte]
  have rest : (∑ j : {j : Fin (2 ^ chunkWidth c) // j ≠ α c},
      withHidden α Y (hiddenOf α J a Y) ⟨c, j.1⟩)
      = ∑ j : {j : Fin (2 ^ chunkWidth c) // j ≠ α c}, Y ⟨c, j.1⟩ :=
    Finset.sum_congr rfl fun j _ => withHidden_inactive α Y _ (fun same => j.2 same)
  rw [active, rest, hiddenOf]
  ring

/-- … and the recovery reads the true active mask back. -/
theorem hiddenOf_joinOf (Y : ChunkSwitch → BaseField) (a : BaseField) (c : Fin chunkCount) :
    hiddenOf α (joinOf Y a) a Y c = Y ⟨c, α c⟩ := by
  rw [hiddenOf, joinOf_eq_split α]
  ring

/-- Filling from the joins reproduces any mask family that makes those joins. -/
theorem withHidden_joinOf (Y : ChunkSwitch → BaseField) (a : BaseField) :
    withHidden α Y (hiddenOf α (joinOf Y a) a Y) = Y := by
  funext cs
  by_cases active : Active α cs
  · obtain ⟨c, j⟩ := cs
    change j = α c at active
    subst active
    simp only [withHidden, Active, ↓reduceIte, hiddenOf_joinOf]
  · exact withHidden_inactive α Y _ active

/-- The recovered active masks depend only on the inactive ones. -/
theorem hiddenOf_congr (J : Fin chunkCount → BaseField) (a : BaseField)
    {first second : ChunkSwitch → BaseField} (agree : ∀ cs, ¬ Active α cs → first cs = second cs) :
    hiddenOf α J a first = hiddenOf α J a second := by
  funext c
  unfold hiddenOf
  congr 1
  exact Finset.sum_congr rfl fun j _ => agree _ (fun same => j.2 same)

end Element

/-! ## The shape: the input, both lanes' active switches, and the designated switch -/

/-- What the simulator's opening is keyed on: the valid input and the designated switch. -/
structure JointShape where
  /-- The adversary's input `u`. -/
  input : AffineInput
  /-- The chunk of the designated switch (`c* = 0` in the note). -/
  designatedChunk : Fin chunkCount
  /-- The designated switch (`j* = α^x_0 ⊕ 1` in the note). -/
  designatedSwitch : Fin (2 ^ chunkWidth designatedChunk)
  /-- It is inactive on the x lanes, so the evaluator queries it. -/
  designated_inactive : designatedSwitch ≠ chunkOf (coordWord input.x) designatedChunk

namespace JointShape

variable (shape : JointShape)

/-- The x lanes' active switches: the chunks of `u.x`. -/
def alphaX : Alpha := fun c => chunkOf (coordWord shape.input.x) c

/-- The y lanes' active switches: the chunks of `u.y`. -/
def alphaY : Alpha := fun c => chunkOf (coordWord shape.input.y) c

/-- The designated (chunk, switch) pair. -/
def designated : ChunkSwitch := ⟨shape.designatedChunk, shape.designatedSwitch⟩

/-- A digit element's lane decides its active switches: x-type elements ride on `pointX`, y-type
elements on `pointY`. -/
def digitAlpha : Biquadratic.Element → Alpha
  | .inl _ => shape.alphaX
  | .inr _ => shape.alphaY

/-- The same for the curve elements (`curveX`, `curveY`). -/
def curveAlpha : CurveMembership.Element → Alpha
  | .inl _ => shape.alphaX
  | .inr _ => shape.alphaY

/-- The designated switch's coefficient in the delivered value, `ι(j*) − ι(α^x_{c*})`. -/
def kappa : BaseField :=
  iota _ shape.designatedSwitch - iota _ (shape.alphaX shape.designatedChunk)

theorem sigmaOf_alphaX : sigmaOf shape.alphaX = shape.input.x := sigmaOf_chunks _

theorem sigmaOf_alphaY : sigmaOf shape.alphaY = shape.input.y := sigmaOf_chunks _

theorem kappa_ne_zero : shape.kappa ≠ 0 :=
  sub_ne_zero.mpr fun same => shape.designated_inactive
    (iota_injective (Nat.pow_le_pow_right (by omega) (chunkWidth_le _)) same)

theorem designated_inactive' : ¬ Active shape.alphaX shape.designated :=
  shape.designated_inactive

/-- The digit cells the evaluator reads and the simulator samples: inactive, and not a designated
collector mask. -/
def DigitVisibleAt (element : Biquadratic.Element) (cs : ChunkSwitch) : Prop :=
  ¬ Active (shape.digitAlpha element) cs ∧ ¬ (IsCollector element ∧ cs = shape.designated)

instance (element : Biquadratic.Element) : DecidablePred (shape.DigitVisibleAt element) := by
  intro cs; unfold DigitVisibleAt; infer_instance

/-- **The note's designated switch**: chunk `0`, `j* = α₀ xor 1` (P3's `designatedSwitch`). -/
def ofInput (input : AffineInput) : JointShape where
  input := input
  designatedChunk := ⟨0, chunkCount_pos⟩
  designatedSwitch := ⟨(chunkOf (coordWord input.x) ⟨0, chunkCount_pos⟩).val ^^^ 1, by
    have := chunkWidth_pos (⟨0, chunkCount_pos⟩ : Fin chunkCount)
    exact Nat.xor_lt_two_pow (chunkOf (coordWord input.x) ⟨0, chunkCount_pos⟩).isLt
      (Nat.one_lt_two_pow (by omega))⟩
  designated_inactive := by
    intro same
    have values := congrArg Fin.val same
    simp only at values
    have bound : (chunkOf (coordWord input.x) ⟨0, chunkCount_pos⟩).val < 4 :=
      lt_of_lt_of_eq (chunkOf (coordWord input.x) ⟨0, chunkCount_pos⟩).isLt (by decide)
    generalize (chunkOf (coordWord input.x) ⟨0, chunkCount_pos⟩).val = value at bound values
    interval_cases value <;> simp only [Nat.reduceXor] at values <;> omega

/-- For `j* = α₀ xor 1` the designated coefficient is `±1`, so `κ⁻¹ = κ` (P3 multiplies by `κ`). -/
theorem ofInput_kappa_mul_self (input : AffineInput) :
    (ofInput input).kappa * (ofInput input).kappa = 1 := by
  have bound : (chunkOf (coordWord input.x) ⟨0, chunkCount_pos⟩).val < 4 :=
    lt_of_lt_of_eq (chunkOf (coordWord input.x) ⟨0, chunkCount_pos⟩).isLt (by decide)
  simp only [kappa, ofInput, alphaX, iota]
  generalize (chunkOf (coordWord input.x) ⟨0, chunkCount_pos⟩).val = value at bound ⊢
  interval_cases value <;> simp only [Nat.reduceXor] <;> norm_num

end JointShape

/-! ## Finite-type plumbing for the row data -/

/-- `RowGamma` is a plain triple. -/
def rowGammaEquiv' : RowGamma ≃ BaseField × BaseField × BaseField where
  toFun g := (g.gX, g.gY, g.gZ)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype RowGamma := Fintype.ofEquiv _ rowGammaEquiv'.symm
instance : Nonempty RowGamma := ⟨rowGammaEquiv'.symm (0, 0, 0)⟩

/-! ## One digit: both lanes, all chunks, the three row constants -/

/-- One digit's scale masks: seven elements (four on `pointX`, three on `pointY`), every chunk,
every switch. -/
abbrev DigitMasks := Biquadratic.Element → ChunkSwitch → BaseField

/-- One digit's G1U coins: its masks. The slopes carry the true row coefficients, so a digit has
no row randomisers; its element offsets are its only masks. -/
abbrev DigitCoins := DigitMasks

/-- One digit's joins, both lanes, every chunk. -/
abbrev DigitJoins := Biquadratic.Element → Fin chunkCount → BaseField

/-- One digit's visible masks. -/
abbrev DigitVisible (shape : JointShape) :=
  (element : Biquadratic.Element) → {cs : ChunkSwitch // shape.DigitVisibleAt element cs} → BaseField

/-- `3 − y² ≠ 0` for every field element: `3` is not a square. -/
theorem three_sub_sq_ne_zero [FieldCertificate] (value : BaseField) : 3 - value ^ 2 ≠ 0 := by
  intro zero
  exact sq_sub_three_ne_zero value (by linear_combination -zero)

section Digit

variable [FieldCertificate] (shape : JointShape) (rows : Coordinates.Rows)

/-- The element offsets `K` of a digit, from its masks (`Pipeline.digitK`). -/
def digitOffsets (masks : DigitMasks) : Biquadratic.Values := fun element => offsetOf (masks element)

/-- The seven slopes, from the true row coefficients and the offsets (`Pipeline.pointSlopes`). -/
def digitSlopes (masks : DigitMasks) : Biquadratic.Values :=
  Biquadratic.slopes rows (digitOffsets masks)

/-- **The digit's published joins** (`Pipeline.pointXGarbled`/`pointYGarbled`, per element). -/
def digitJoins (masks : DigitMasks) : DigitJoins :=
  fun element c => joinOf (masks element) (digitSlopes rows masks element) c

/-- **The digit's three published constants** (`FieldMacToECMac.garbleRow`). -/
def digitGamma (masks : DigitMasks) : RowGamma :=
  garbleRow rows (digitOffsets masks)

/-- The digit's visible masks. -/
def digitVisible (masks : DigitMasks) : DigitVisible shape := fun element cs => masks element cs.1

/-- The visible masks, extended by `0` everywhere else. -/
def extendVisible (visible : DigitVisible shape) (element : Biquadratic.Element) :
    ChunkSwitch → BaseField := fun cs =>
  if h : shape.DigitVisibleAt element cs then visible element ⟨cs, h⟩ else 0

/-- The evaluator's delivered value computed from the published joins and the visible masks only
(the designated term, whose mask the simulator programs, is left out). -/
def digitPartial (joins : DigitJoins) (visible : DigitVisible shape)
    (element : Biquadratic.Element) : BaseField :=
  deliveredOf (shape.digitAlpha element) (joins element) (extendVisible shape visible element)

/-- The coordinate an element is chunked against, as `σ(α)`. -/
def digitSigma (element : Biquadratic.Element) : BaseField := sigmaOf (shape.digitAlpha element)

/-- The numerator of the sign row's `y10` offset read-back. With `d8`, `d10` the delivered `y8`,
`y10` values, the chain `d8 = (c5 + (c0 − K10)/3) y + K8`,
`d10 = (c2 − K8) y + K10` is a `2 × 2` system in `(K8, K10)` whose determinant is
`(3 − y²)/3`; this is `3 − y²` times `K10 / 3` (`solvedY10_forward`). -/
def solvedY10Numerator (joins : DigitJoins) (visible : DigitVisible shape) : BaseField :=
  digitPartial shape joins visible (.inr .rowY_y10)
    - (rows.y.y - digitPartial shape joins visible (.inr .rowY_y8))
      * digitSigma shape (.inr .rowY_y10)
    - (rows.y.ySquared + rows.y.constant * Biquadratic.inv3)
      * digitSigma shape (.inr .rowY_y10) ^ 2

/-- **The sign row's `y10` offset, read back.** The division is by `3 − y²`, which is never zero,
because `3` is not a square in the base field (`three_sub_sq_ne_zero`), so the read-back is exact
at every input, on or off the curve. -/
def solvedY10 (joins : DigitJoins) (visible : DigitVisible shape) : BaseField :=
  3 * solvedY10Numerator shape rows joins visible / (3 - digitSigma shape (.inr .rowY_y10) ^ 2)

/-- **The offsets solved from the public and visible cells.** The four free elements come from
their delivered values -- `x7` and the `X` row's `y10` directly, the sign row's `y10` from the
`2 × 2` system (`solvedY10`), then `y8` -- and the three collectors from the published constants
(`gX` for the `X` row's `x9`, `gY` for the sign row's `cubic`, `gZ` for the `Z` row's `x9`). -/
def solvedOffsets (joins : DigitJoins) (gamma : RowGamma) (visible : DigitVisible shape) :
    Biquadratic.Values
  | .inl .rowX_x7 => digitPartial shape joins visible (.inl .rowX_x7)
      - rows.x.xSquared * digitSigma shape (.inl .rowX_x7)
  | .inr .rowX_y10 => digitPartial shape joins visible (.inr .rowX_y10)
      - rows.x.y * digitSigma shape (.inr .rowX_y10)
  | .inr .rowY_y10 => solvedY10 shape rows joins visible
  | .inr .rowY_y8 => digitPartial shape joins visible (.inr .rowY_y8)
      - (rows.y.ySquared + (rows.y.constant - solvedY10 shape rows joins visible)
          * Biquadratic.inv3) * digitSigma shape (.inr .rowY_y8)
  | .inl .rowX_x9 => rows.x.constant - gamma.gX
      - (digitPartial shape joins visible (.inr .rowX_y10)
        - rows.x.y * digitSigma shape (.inr .rowX_y10))
  | .inl .rowY_cubic => rows.y.xSquared - gamma.gY
  | .inl .rowZ_x9 => rows.z.constant - gamma.gZ

/-- The slopes at the solved offsets. -/
def solvedSlopes (joins : DigitJoins) (gamma : RowGamma) (visible : DigitVisible shape) :
    Biquadratic.Values :=
  Biquadratic.slopes rows (solvedOffsets shape rows joins gamma visible)

/-- **The designated mask of a collector, solved**: what makes its offset come out right. -/
def solvedDesignated (joins : DigitJoins) (gamma : RowGamma) (visible : DigitVisible shape)
    (element : Biquadratic.Element) : BaseField :=
  shape.kappa⁻¹ * (solvedOffsets shape rows joins gamma visible element
    - digitPartial shape joins visible element
    + solvedSlopes shape rows joins gamma visible element * digitSigma shape element)

/-- The inactive masks: visible ones as given, the designated one as solved. -/
def inactiveFill (visible : DigitVisible shape) (designated : Biquadratic.Values)
    (element : Biquadratic.Element) : ChunkSwitch → BaseField := fun cs =>
  if h : shape.DigitVisibleAt element cs then visible element ⟨cs, h⟩
  else if IsCollector element ∧ cs = shape.designated then designated element else 0

/-- **The digit's masks, rebuilt from its public and visible cells.** -/
def digitMasksOf (joins : DigitJoins) (gamma : RowGamma) (visible : DigitVisible shape) :
    DigitMasks := fun element =>
  let fill := inactiveFill shape visible (solvedDesignated shape rows joins gamma visible) element
  withHidden (shape.digitAlpha element) fill
    (hiddenOf (shape.digitAlpha element) (joins element)
      (solvedSlopes shape rows joins gamma visible element) fill)

/-- On a collector the evaluator's value is the visible part plus `κ` times the designated mask;
on the other four elements it is the visible part. -/
theorem deliveredOf_split (joins : DigitJoins) (visible : DigitVisible shape)
    (element : Biquadratic.Element) (masks : ChunkSwitch → BaseField)
    (agree : ∀ cs (h : shape.DigitVisibleAt element cs), masks cs = visible element ⟨cs, h⟩) :
    deliveredOf (shape.digitAlpha element) (joins element) masks
      = digitPartial shape joins visible element
        + (if IsCollector element then shape.kappa * masks shape.designated else 0) := by
  unfold digitPartial deliveredOf
  rw [add_assoc]
  congr 1
  have pointwise : ∀ cs : {cs : ChunkSwitch // ¬ Active (shape.digitAlpha element) cs},
      (switchIota cs.1 - iota _ (shape.digitAlpha element cs.1.1)) * masks cs.1
        = (switchIota cs.1 - iota _ (shape.digitAlpha element cs.1.1))
            * extendVisible shape visible element cs.1
          + (if IsCollector element ∧ cs.1 = shape.designated then
              shape.kappa * masks shape.designated else 0) := by
    intro cs
    by_cases visibleHere : shape.DigitVisibleAt element cs.1
    · have notDes : ¬ (IsCollector element ∧ cs.1 = shape.designated) := visibleHere.2
      rw [if_neg notDes, add_zero, extendVisible, dif_pos visibleHere, agree cs.1 visibleHere]
    · have des : IsCollector element ∧ cs.1 = shape.designated := by
        by_contra hnot
        exact visibleHere ⟨cs.2, hnot⟩
      rw [if_pos des, extendVisible, dif_neg visibleHere, mul_zero, zero_add, des.2]
      have lane : shape.digitAlpha element = shape.alphaX := by
        rcases des.1 with h | h | h <;> subst h <;> rfl
      rw [lane]
      rfl
  rw [Finset.sum_congr rfl fun cs _ => pointwise cs, Finset.sum_add_distrib]
  congr 1
  by_cases collector : IsCollector element
  · rw [if_pos collector]
    have inactive : ¬ Active (shape.digitAlpha element) shape.designated := by
      have lane : shape.digitAlpha element = shape.alphaX := by
        rcases collector with h | h | h <;> subst h <;> rfl
      rw [lane]
      exact shape.designated_inactive'
    rw [Fintype.sum_eq_single ⟨shape.designated, inactive⟩]
    · simp [collector]
    · intro cs other
      rw [if_neg]
      rintro ⟨_, same⟩
      exact other (Subtype.ext same)
  · rw [if_neg collector]
    exact Finset.sum_eq_zero fun cs _ => by rw [if_neg (fun both => collector both.1)]

/-- The rebuilt masks agree with the visible cells. -/
theorem inactiveFill_visible (visible : DigitVisible shape) (designated : Biquadratic.Values)
    (element : Biquadratic.Element) (cs : ChunkSwitch) (h : shape.DigitVisibleAt element cs) :
    inactiveFill shape visible designated element cs = visible element ⟨cs, h⟩ := by
  simp only [inactiveFill, dif_pos h]

theorem inactiveFill_designated (visible : DigitVisible shape) (designated : Biquadratic.Values)
    (element : Biquadratic.Element) (collector : IsCollector element) :
    inactiveFill shape visible designated element shape.designated = designated element := by
  have notVisible : ¬ shape.DigitVisibleAt element shape.designated :=
    fun h => h.2 ⟨collector, rfl⟩
  simp only [inactiveFill, dif_neg notVisible, and_true, if_pos collector]

/-- The rebuilt masks: visible cells as given. -/
theorem digitMasksOf_visible (joins : DigitJoins) (gamma : RowGamma) (visible : DigitVisible shape)
    (element : Biquadratic.Element) (cs : ChunkSwitch) (h : shape.DigitVisibleAt element cs) :
    digitMasksOf shape rows joins gamma visible element cs = visible element ⟨cs, h⟩ := by
  simp only [digitMasksOf]
  rw [withHidden_inactive _ _ _ h.1, inactiveFill_visible shape visible _ element cs h]

/-- `solvedY10` times `3 − y²` is three times its numerator (`y² ≠ 3`). -/
theorem solvedY10_mul (joins : DigitJoins) (visible : DigitVisible shape) :
    solvedY10 shape rows joins visible * (3 - digitSigma shape (.inr .rowY_y10) ^ 2)
      = 3 * solvedY10Numerator shape rows joins visible :=
  div_mul_cancel₀ _ (three_sub_sq_ne_zero _)

/-- The fixed-point form of the `y10` read-back: `K10 = num + K10 y² / 3`. -/
theorem solvedY10_fixed (joins : DigitJoins) (visible : DigitVisible shape) :
    solvedY10 shape rows joins visible
      = solvedY10Numerator shape rows joins visible
        + solvedY10 shape rows joins visible * Biquadratic.inv3
          * digitSigma shape (.inr .rowY_y10) ^ 2 := by
  have key := solvedY10_mul shape rows joins visible
  have third := Biquadratic.three_mul_inv3
  linear_combination Biquadratic.inv3 * key
    - (solvedY10 shape rows joins visible - solvedY10Numerator shape rows joins visible) * third

/-- **The key identity of the rebuild**: the rebuilt masks have exactly the solved offsets. -/
theorem offsetOf_digitMasksOf (joins : DigitJoins) (gamma : RowGamma)
    (visible : DigitVisible shape) (element : Biquadratic.Element) :
    offsetOf (digitMasksOf shape rows joins gamma visible element)
      = solvedOffsets shape rows joins gamma visible element := by
  have delivered := deliveredOf_joinOf (shape.digitAlpha element)
    (digitMasksOf shape rows joins gamma visible element)
    (solvedSlopes shape rows joins gamma visible element)
  have joinsBack : joinOf (digitMasksOf shape rows joins gamma visible element)
      (solvedSlopes shape rows joins gamma visible element) = joins element :=
    joinOf_withHidden_hiddenOf _ _ _ _
  rw [joinsBack] at delivered
  have inactiveSame : ∀ cs, ¬ Active (shape.digitAlpha element) cs →
      digitMasksOf shape rows joins gamma visible element cs
        = inactiveFill shape visible (solvedDesignated shape rows joins gamma visible) element cs :=
    fun cs inactive => withHidden_inactive _ _ _ inactive
  rw [deliveredOf_congr _ _ inactiveSame, deliveredOf_split shape joins visible element _
    (fun cs h => inactiveFill_visible shape visible _ element cs h)] at delivered
  by_cases collector : IsCollector element
  · rw [if_pos collector, inactiveFill_designated shape visible _ element collector] at delivered
    have offset : offsetOf (digitMasksOf shape rows joins gamma visible element)
        = digitPartial shape joins visible element
          + shape.kappa * solvedDesignated shape rows joins gamma visible element
          - solvedSlopes shape rows joins gamma visible element
            * sigmaOf (shape.digitAlpha element) := by
      rw [delivered]; ring
    rw [offset, solvedDesignated, ← mul_assoc, mul_inv_cancel₀ shape.kappa_ne_zero, one_mul]
    simp only [digitSigma]
    ring
  · rw [if_neg collector, add_zero] at delivered
    have offset : offsetOf (digitMasksOf shape rows joins gamma visible element)
        = digitPartial shape joins visible element
          - solvedSlopes shape rows joins gamma visible element
            * sigmaOf (shape.digitAlpha element) := by
      rw [delivered]; ring
    rw [offset]
    -- the cases in constructor order: x7, x9, cubic, z9 | y10 (X row), y8, y10 (sign row)
    rcases element with (_ | _ | _ | _) | (_ | _ | _)
    · simp only [solvedSlopes, solvedOffsets, Biquadratic.slopes, digitSigma] <;> ring
    · exact absurd (Or.inl rfl) collector
    · exact absurd (Or.inr (Or.inl rfl)) collector
    · exact absurd (Or.inr (Or.inr rfl)) collector
    · simp only [solvedSlopes, solvedOffsets, Biquadratic.slopes, digitSigma] <;> ring
    · simp only [solvedSlopes, solvedOffsets, Biquadratic.slopes, Biquadratic.cubicSlope,
        digitSigma] <;> ring
    · have fixed := solvedY10_fixed shape rows joins visible
      rw [solvedY10Numerator] at fixed
      simp only [solvedSlopes, solvedOffsets, Biquadratic.slopes, digitSigma,
        JointShape.digitAlpha] at fixed ⊢
      linear_combination (-1 : BaseField) * fixed

/-! ### The digit bijection -/

/-- At the published cells of a mask family, the visible part of the delivered value is the offset
plus slope times coordinate, less the designated term. -/
theorem digitPartial_forward (masks : DigitMasks) (element : Biquadratic.Element) :
    digitPartial shape (digitJoins rows masks) (digitVisible shape masks) element
      = digitOffsets masks element + digitSlopes rows masks element * digitSigma shape element
        - (if IsCollector element then shape.kappa * masks element shape.designated else 0) := by
  have delivered := deliveredOf_joinOf (shape.digitAlpha element) (masks element)
    (digitSlopes rows masks element)
  have split := deliveredOf_split shape (digitJoins rows masks) (digitVisible shape masks) element
    (masks element) (fun cs h => rfl)
  have joinsEq : digitJoins rows masks element
      = joinOf (masks element) (digitSlopes rows masks element) := rfl
  rw [joinsEq] at split
  rw [split] at delivered
  rw [digitSigma, digitOffsets]
  rw [← delivered]
  ring

/-- **`K[y10]` is read back exactly**: at the published and visible cells of a mask family, the
numerator is `(3 − y²) K10 / 3`. -/
theorem solvedY10_forward (masks : DigitMasks) :
    solvedY10 shape rows (digitJoins rows masks) (digitVisible shape masks)
      = digitOffsets masks (.inr .rowY_y10) := by
  have evalParts := digitPartial_forward shape rows masks
  have third := Biquadratic.three_mul_inv3
  rw [solvedY10, div_eq_iff (three_sub_sq_ne_zero _)]
  simp only [solvedY10Numerator, evalParts, digitSlopes, Biquadratic.slopes,
    Biquadratic.cubicSlope, IsCollector, reduceCtorEq, Sum.inl.injEq, or_self, if_false, sub_zero,
    digitSigma, JointShape.digitAlpha]
  linear_combination (-(digitOffsets masks (.inr .rowY_y10) * sigmaOf shape.alphaY ^ 2)) * third

/-- The solved offsets are the true offsets. -/
theorem solvedOffsets_forward (masks : DigitMasks) :
    solvedOffsets shape rows (digitJoins rows masks) (digitGamma rows masks)
      (digitVisible shape masks) = digitOffsets masks := by
  have y10Back := solvedY10_forward shape rows masks
  have evalParts := digitPartial_forward shape rows masks
  funext element
  rcases element with (_ | _ | _ | _ | _) | (_ | _ | _) <;>
    simp only [solvedOffsets, y10Back, evalParts, digitSlopes, Biquadratic.slopes,
      Biquadratic.cubicSlope, IsCollector, reduceCtorEq, Sum.inl.injEq, or_self, if_false,
      sub_zero] <;>
    (try simp only [digitGamma, garbleRow, Biquadratic.garble]) <;> ring

/-- The solved slopes are the true slopes. -/
theorem solvedSlopes_forward (masks : DigitMasks) :
    solvedSlopes shape rows (digitJoins rows masks) (digitGamma rows masks)
      (digitVisible shape masks) = digitSlopes rows masks := by
  rw [solvedSlopes, solvedOffsets_forward]
  rfl

/-- **The solved designated mask is the true one.** -/
theorem solvedDesignated_forward (masks : DigitMasks)
    (element : Biquadratic.Element) (collector : IsCollector element) :
    solvedDesignated shape rows (digitJoins rows masks) (digitGamma rows masks)
      (digitVisible shape masks) element = masks element shape.designated := by
  rw [solvedDesignated, solvedOffsets_forward, solvedSlopes_forward, digitPartial_forward,
    if_pos collector]
  have cancel : digitOffsets masks element
      - (digitOffsets masks element + digitSlopes rows masks element * digitSigma shape element
        - shape.kappa * masks element shape.designated)
      + digitSlopes rows masks element * digitSigma shape element
      = shape.kappa * masks element shape.designated := by ring
  rw [cancel, ← mul_assoc, inv_mul_cancel₀ shape.kappa_ne_zero, one_mul]

/-- **The published constants come back** from the solved offsets. -/
theorem garbleRow_solved (joins : DigitJoins) (gamma : RowGamma) (visible : DigitVisible shape) :
    garbleRow rows (solvedOffsets shape rows joins gamma visible) = gamma := by
  obtain ⟨gX, gY, gZ⟩ := gamma
  simp only [garbleRow, Biquadratic.garble, solvedOffsets, RowGamma.mk.injEq]
  refine ⟨by ring1, by ring1, by ring1⟩

/-- **The digit bijection**: a digit's masks (both lanes, every chunk and switch) against its
published joins, its three published constants and its visible masks. -/
def digitEquiv : DigitCoins ≃ (DigitJoins × RowGamma) × DigitVisible shape where
  toFun masks := ((digitJoins rows masks, digitGamma rows masks), digitVisible shape masks)
  invFun out := digitMasksOf shape rows out.1.1 out.1.2 out.2
  left_inv masks := by
    funext element
    show withHidden (shape.digitAlpha element)
        (inactiveFill shape (digitVisible shape masks)
          (solvedDesignated shape rows (digitJoins rows masks) (digitGamma rows masks)
            (digitVisible shape masks)) element)
        (hiddenOf (shape.digitAlpha element) (digitJoins rows masks element)
          (solvedSlopes shape rows (digitJoins rows masks) (digitGamma rows masks)
            (digitVisible shape masks) element)
          (inactiveFill shape (digitVisible shape masks)
            (solvedDesignated shape rows (digitJoins rows masks) (digitGamma rows masks)
              (digitVisible shape masks)) element)) = masks element
    have agree : ∀ cs, ¬ Active (shape.digitAlpha element) cs →
        inactiveFill shape (digitVisible shape masks)
          (solvedDesignated shape rows (digitJoins rows masks) (digitGamma rows masks)
            (digitVisible shape masks)) element cs = masks element cs := by
      intro cs inactive
      by_cases visibleHere : shape.DigitVisibleAt element cs
      · rw [inactiveFill_visible shape _ _ element cs visibleHere]
        rfl
      · have des : IsCollector element ∧ cs = shape.designated := by
          by_contra hnot
          exact visibleHere ⟨inactive, hnot⟩
        rw [des.2, inactiveFill_designated shape _ _ element des.1,
          solvedDesignated_forward shape rows masks element des.1]
    have sameFill : withHidden (shape.digitAlpha element)
        (inactiveFill shape (digitVisible shape masks)
          (solvedDesignated shape rows (digitJoins rows masks) (digitGamma rows masks)
            (digitVisible shape masks)) element)
        = withHidden (shape.digitAlpha element) (masks element) := by
      funext hidden cs
      by_cases active : Active (shape.digitAlpha element) cs
      · simp only [withHidden, if_pos active]
      · rw [withHidden_inactive _ _ _ active, withHidden_inactive _ _ _ active, agree cs active]
    rw [sameFill, hiddenOf_congr _ _ _ agree, solvedSlopes_forward]
    exact withHidden_joinOf _ (masks element) (digitSlopes rows masks element)
  right_inv out := by
    obtain ⟨⟨joins, gamma⟩, visible⟩ := out
    have offsets : digitOffsets (digitMasksOf shape rows joins gamma visible)
        = solvedOffsets shape rows joins gamma visible :=
      funext fun element => offsetOf_digitMasksOf shape rows joins gamma visible element
    have slopes : digitSlopes rows (digitMasksOf shape rows joins gamma visible)
        = solvedSlopes shape rows joins gamma visible := by
      rw [digitSlopes, offsets]
      rfl
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext element c
      show joinOf (digitMasksOf shape rows joins gamma visible element)
          (digitSlopes rows (digitMasksOf shape rows joins gamma visible) element) c
        = joins element c
      rw [slopes]
      exact congrFun (joinOf_withHidden_hiddenOf _ _ _ _) c
    · show garbleRow rows (digitOffsets (digitMasksOf shape rows joins gamma visible)) = gamma
      rw [offsets]
      exact garbleRow_solved shape rows joins gamma visible
    · funext element cs
      exact digitMasksOf_visible shape rows joins gamma visible element cs.1 cs.2

end Digit

/-! ## The curve check: both curve lanes, the three constants, the bridge key -/

/-- `F_p^*`, without the field certificate (the same type as `Opening.NonZeroField`). -/
abbrev NonZeroBaseField := {value : BaseField // value ≠ 0}

/-- The curve check's scale masks: five elements (three on `curveX`, two on `curveY`). -/
abbrev CurveMasks := CurveMembership.Element → ChunkSwitch → BaseField

/-- The curve coins: its masks, the bridge key `t`, the mask `∈ F_p^*` and `r1, r2`. -/
abbrev CurveCoins := CurveMasks × BaseField × NonZeroBaseField × BaseField × BaseField

/-- The curve joins, both lanes, every chunk. -/
abbrev CurveJoins := CurveMembership.Element → Fin chunkCount → BaseField

/-- The curve lanes' visible masks: every inactive one (no designated switch on system A). -/
abbrev CurveVisible (shape : JointShape) :=
  (element : CurveMembership.Element) →
    {cs : ChunkSwitch // ¬ Active (shape.curveAlpha element) cs} → BaseField

section Curve

variable [FieldCertificate] (shape : JointShape)

/-- The curve check's element offsets (`Pipeline.curveK`). -/
def curveOffsets (masks : CurveMasks) : CurveMembership.Values := fun element => offsetOf (masks element)

/-- The five slopes (`Pipeline.curveSlopes`). -/
def curveSlopes (masks : CurveMasks) (r1 r2 : BaseField) : CurveMembership.Values :=
  CurveMembership.slopes r1 r2 (curveOffsets masks)

/-- **The curve joins** (`Pipeline.curveXGarbled`/`curveYGarbled`, per element). -/
def curveJoins (masks : CurveMasks) (r1 r2 : BaseField) : CurveJoins :=
  fun element c => joinOf (masks element) (curveSlopes masks r1 r2 element) c

/-- **The three published constants** (`CurveMembership.garble`). -/
def curveTable (masks : CurveMasks) (bridgeKey : BaseField) (mask : NonZeroBaseField)
    (r1 r2 : BaseField) : CurveMembership.Table :=
  CurveMembership.garble bridgeKey mask.1 r1 r2 (curveOffsets masks)

/-- The curve lanes' visible masks. -/
def curveVisible (masks : CurveMasks) : CurveVisible shape := fun element cs => masks element cs.1

/-- The visible curve masks extended by `0`. -/
def extendCurve (visible : CurveVisible shape) (element : CurveMembership.Element) :
    ChunkSwitch → BaseField := fun cs =>
  if h : ¬ Active (shape.curveAlpha element) cs then visible element ⟨cs, h⟩ else 0

/-- **The evaluator's curve element values** from the published joins and the visible masks. -/
def curveDelivered (joins : CurveJoins) (visible : CurveVisible shape) : CurveMembership.Values :=
  fun element => deliveredOf (shape.curveAlpha element) (joins element) (extendCurve shape visible element)

/-- The coordinate a curve element is chunked against, as `σ(α)`. -/
def curveSigma (element : CurveMembership.Element) : BaseField := sigmaOf (shape.curveAlpha element)

/-- The offsets solved from the public and visible cells and the mask: the chains
`x3 → x5 → x7` and `y4 → y6`. -/
def curveSolvedOffsets (joins : CurveJoins) (table : CurveMembership.Table)
    (visible : CurveVisible shape) (mask : NonZeroBaseField) : CurveMembership.Values
  | .inl .x3 => curveDelivered shape joins visible (.inl .x3)
      + (table.2.1 - mask.1) * curveSigma shape (.inl .x3)
  | .inl .x5 => curveDelivered shape joins visible (.inl .x5)
      + (curveDelivered shape joins visible (.inl .x3)
        + (table.2.1 - mask.1) * curveSigma shape (.inl .x3)) * curveSigma shape (.inl .x5)
  | .inl .x7 => curveDelivered shape joins visible (.inl .x7)
      + (curveDelivered shape joins visible (.inl .x5)
        + (curveDelivered shape joins visible (.inl .x3)
          + (table.2.1 - mask.1) * curveSigma shape (.inl .x3)) * curveSigma shape (.inl .x5))
        * curveSigma shape (.inl .x7)
  | .inr .y4 => curveDelivered shape joins visible (.inr .y4)
      + (table.2.2 + mask.1) * curveSigma shape (.inr .y4)
  | .inr .y6 => curveDelivered shape joins visible (.inr .y6)
      + (curveDelivered shape joins visible (.inr .y4)
        + (table.2.2 + mask.1) * curveSigma shape (.inr .y4)) * curveSigma shape (.inr .y6)

/-- The curve slopes at the solved offsets. -/
def curveSolvedSlopes (joins : CurveJoins) (table : CurveMembership.Table)
    (visible : CurveVisible shape) (mask : NonZeroBaseField) : CurveMembership.Values :=
  CurveMembership.slopes (table.2.1 - mask.1) (table.2.2 + mask.1)
    (curveSolvedOffsets shape joins table visible mask)

/-- The curve masks rebuilt from the public and visible cells and the mask. -/
def curveMasksOf (joins : CurveJoins) (table : CurveMembership.Table)
    (visible : CurveVisible shape) (mask : NonZeroBaseField) : CurveMasks := fun element =>
  withHidden (shape.curveAlpha element) (extendCurve shape visible element)
    (hiddenOf (shape.curveAlpha element) (joins element)
      (curveSolvedSlopes shape joins table visible mask element) (extendCurve shape visible element))

/-- The bridge key rebuilt from the public cells, the solved offsets and the mask. -/
def curveSolvedKey (joins : CurveJoins) (table : CurveMembership.Table)
    (visible : CurveVisible shape) (mask : NonZeroBaseField) : BaseField :=
  table.1 - 3 * mask.1 + curveSolvedOffsets shape joins table visible mask (.inr .y6)
    + curveSolvedOffsets shape joins table visible mask (.inl .x7)

theorem curveMasksOf_visible (joins : CurveJoins) (table : CurveMembership.Table)
    (visible : CurveVisible shape) (mask : NonZeroBaseField) (element : CurveMembership.Element)
    (cs : ChunkSwitch) (h : ¬ Active (shape.curveAlpha element) cs) :
    curveMasksOf shape joins table visible mask element cs = visible element ⟨cs, h⟩ := by
  simp only [curveMasksOf]
  rw [withHidden_inactive _ _ _ h, extendCurve, dif_pos h]

theorem offsetOf_curveMasksOf (joins : CurveJoins) (table : CurveMembership.Table)
    (visible : CurveVisible shape) (mask : NonZeroBaseField) (element : CurveMembership.Element) :
    offsetOf (curveMasksOf shape joins table visible mask element)
      = curveSolvedOffsets shape joins table visible mask element := by
  have delivered := deliveredOf_joinOf (shape.curveAlpha element)
    (curveMasksOf shape joins table visible mask element)
    (curveSolvedSlopes shape joins table visible mask element)
  rw [show joinOf (curveMasksOf shape joins table visible mask element)
      (curveSolvedSlopes shape joins table visible mask element) = joins element from
    joinOf_withHidden_hiddenOf _ _ _ _] at delivered
  have inactiveSame : ∀ cs, ¬ Active (shape.curveAlpha element) cs →
      curveMasksOf shape joins table visible mask element cs = extendCurve shape visible element cs :=
    fun cs inactive => withHidden_inactive _ _ _ inactive
  rw [deliveredOf_congr _ _ inactiveSame] at delivered
  have offset : offsetOf (curveMasksOf shape joins table visible mask element)
      = curveDelivered shape joins visible element
        - curveSolvedSlopes shape joins table visible mask element
          * sigmaOf (shape.curveAlpha element) := by
    rw [curveDelivered, delivered]; ring
  rw [offset]
  rcases element with (_ | _ | _) | (_ | _) <;>
    simp only [curveSolvedSlopes, curveSolvedOffsets, CurveMembership.slopes, curveSigma] <;> ring

/-- At the published cells of a mask family, the evaluator's curve values are the offsets plus the
slopes times the coordinates. -/
theorem curveDelivered_forward (masks : CurveMasks) (r1 r2 : BaseField)
    (element : CurveMembership.Element) :
    curveDelivered shape (curveJoins masks r1 r2) (curveVisible shape masks) element
      = curveOffsets masks element + curveSlopes masks r1 r2 element * curveSigma shape element := by
  have delivered := deliveredOf_joinOf (shape.curveAlpha element) (masks element)
    (curveSlopes masks r1 r2 element)
  rw [curveDelivered, curveSigma, curveOffsets, ← delivered]
  refine deliveredOf_congr _ _ fun cs inactive => ?_
  rw [extendCurve, dif_pos inactive]
  rfl

/-- The solved curve offsets are the true ones. -/
theorem curveSolvedOffsets_forward (masks : CurveMasks) (bridgeKey : BaseField)
    (mask : NonZeroBaseField) (r1 r2 : BaseField) :
    curveSolvedOffsets shape (curveJoins masks r1 r2) (curveTable masks bridgeKey mask r1 r2)
      (curveVisible shape masks) mask = curveOffsets masks := by
  have values := curveDelivered_forward shape masks r1 r2
  funext element
  rcases element with (_ | _ | _) | (_ | _) <;>
    simp only [curveSolvedOffsets, values, curveTable, CurveMembership.garble, curveSlopes,
      CurveMembership.slopes] <;> ring

/-- **The curve bijection**: the curve masks, bridge key, mask and `r1, r2` against the curve
joins, the three constants, the visible masks and the mask (the fibre coordinate of the
`(p − 1)`-to-one map of note §1.5, C2). -/
def curveEquiv : CurveCoins ≃ ((CurveJoins × CurveMembership.Table) × CurveVisible shape) × NonZeroBaseField where
  toFun coins := (((curveJoins coins.1 coins.2.2.2.1 coins.2.2.2.2,
      curveTable coins.1 coins.2.1 coins.2.2.1 coins.2.2.2.1 coins.2.2.2.2),
    curveVisible shape coins.1), coins.2.2.1)
  invFun out := (curveMasksOf shape out.1.1.1 out.1.1.2 out.1.2 out.2,
    curveSolvedKey shape out.1.1.1 out.1.1.2 out.1.2 out.2, out.2,
    out.1.1.2.2.1 - out.2.1, out.1.1.2.2.2 + out.2.1)
  left_inv coins := by
    obtain ⟨masks, bridgeKey, mask, r1, r2⟩ := coins
    have offsets := curveSolvedOffsets_forward shape masks bridgeKey mask r1 r2
    have r1Back : (curveTable masks bridgeKey mask r1 r2).2.1 - mask.1 = r1 := by
      simp only [curveTable, CurveMembership.garble]; ring
    have r2Back : (curveTable masks bridgeKey mask r1 r2).2.2 + mask.1 = r2 := by
      simp only [curveTable, CurveMembership.garble]; ring
    have slopes : curveSolvedSlopes shape (curveJoins masks r1 r2)
        (curveTable masks bridgeKey mask r1 r2) (curveVisible shape masks) mask
        = curveSlopes masks r1 r2 := by
      rw [curveSolvedSlopes, offsets, r1Back, r2Back]
      rfl
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl (Prod.ext r1Back r2Back)))
    · funext element
      show withHidden (shape.curveAlpha element)
          (extendCurve shape (curveVisible shape masks) element)
          (hiddenOf (shape.curveAlpha element) (curveJoins masks r1 r2 element)
            (curveSolvedSlopes shape (curveJoins masks r1 r2)
              (curveTable masks bridgeKey mask r1 r2) (curveVisible shape masks) mask element)
            (extendCurve shape (curveVisible shape masks) element)) = masks element
      have agree : ∀ cs, ¬ Active (shape.curveAlpha element) cs →
          extendCurve shape (curveVisible shape masks) element cs = masks element cs := by
        intro cs inactive
        rw [extendCurve, dif_pos inactive]
        rfl
      have sameFill : withHidden (shape.curveAlpha element)
          (extendCurve shape (curveVisible shape masks) element)
          = withHidden (shape.curveAlpha element) (masks element) := by
        funext hidden cs
        by_cases active : Active (shape.curveAlpha element) cs
        · simp only [withHidden, if_pos active]
        · rw [withHidden_inactive _ _ _ active, withHidden_inactive _ _ _ active, agree cs active]
      rw [sameFill, hiddenOf_congr _ _ _ agree, slopes]
      exact withHidden_joinOf _ (masks element) (curveSlopes masks r1 r2 element)
    · show curveSolvedKey shape (curveJoins masks r1 r2) (curveTable masks bridgeKey mask r1 r2)
        (curveVisible shape masks) mask = bridgeKey
      rw [curveSolvedKey, offsets]
      simp only [curveTable, CurveMembership.garble, curveOffsets]
      ring
  right_inv out := by
    obtain ⟨⟨⟨joins, table⟩, visible⟩, mask⟩ := out
    have offsets : curveOffsets (curveMasksOf shape joins table visible mask)
        = curveSolvedOffsets shape joins table visible mask :=
      funext fun element => offsetOf_curveMasksOf shape joins table visible mask element
    have slopes : curveSlopes (curveMasksOf shape joins table visible mask)
        (table.2.1 - mask.1) (table.2.2 + mask.1)
        = curveSolvedSlopes shape joins table visible mask := by
      rw [curveSlopes, offsets]
      rfl
    refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) rfl
    · funext element c
      show joinOf (curveMasksOf shape joins table visible mask element)
          (curveSlopes (curveMasksOf shape joins table visible mask)
            (table.2.1 - mask.1) (table.2.2 + mask.1) element) c = joins element c
      rw [slopes]
      exact congrFun (joinOf_withHidden_hiddenOf _ _ _ _) c
    · show CurveMembership.garble (curveSolvedKey shape joins table visible mask) mask.1
          (table.2.1 - mask.1) (table.2.2 + mask.1)
          (curveOffsets (curveMasksOf shape joins table visible mask)) = table
      rw [offsets]
      obtain ⟨c0, c1, c2⟩ := table
      simp only [CurveMembership.garble, curveSolvedKey]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring
    · funext element cs
      exact curveMasksOf_visible shape joins table visible mask element cs.1 cs.2

/-- **The bridge key is the evaluator's curve value** on the public and visible cells, for a
valid input (note §1.6: there is no "true `t`" to hit). -/
theorem bridgeKey_eq_eval (onCurve : OnCurve shape.input) (masks : CurveMasks)
    (bridgeKey : BaseField) (mask : NonZeroBaseField) (r1 r2 : BaseField) :
    CurveMembership.evaluate (curveTable masks bridgeKey mask r1 r2) shape.input
        (curveDelivered shape (curveJoins masks r1 r2) (curveVisible shape masks))
      = bridgeKey := by
  have values : curveDelivered shape (curveJoins masks r1 r2) (curveVisible shape masks)
      = CurveMembership.delivered r1 r2 (curveOffsets masks) shape.input := by
    funext element
    rw [curveDelivered_forward, CurveMembership.delivered, curveSigma]
    rcases element with (_ | _ | _) | (_ | _) <;>
      simp only [JointShape.curveAlpha, JointShape.sigmaOf_alphaX, JointShape.sigmaOf_alphaY,
        CurveMembership.coordValue, curveSlopes] <;> ring
  rw [values]
  exact CurveMembership.evaluateEncodedOnCurve bridgeKey mask.1 r1 r2 (curveOffsets masks)
    shape.input onCurve

end Curve

/-! ## The fold joins and the gadget entries -/

/-- One fold join per (lane, paid fold step): `foldStepCount = 202` per lane (`b_c − 1` per
chunk). -/
abbrev FoldCells := Lane → Fin foldStepCount → Block

/-- **The fold bijection.** The published join of each (lane, paid step) is its hidden material
(the active parent's) XOR the evaluator-visible remainder (`OneHot.stepJoin`). -/
def foldEquiv (visibleFold : Lane → Fin foldStepCount → Block) : FoldCells ≃ FoldCells :=
  Equiv.piCongrRight fun lane => Equiv.piCongrRight fun c =>
    Kriterion.ArgoMAC.Security.PGS.xorEquiv (visibleFold lane c)

/-- Writing a byte and reading the old one back is its own inverse. -/
def entrySwap (slot : Fin 12) : (Exception.Entry × BitVec 8) ≃ (Exception.Entry × BitVec 8) where
  toFun pair := (Exception.writeEntry pair.1 slot pair.2, pair.1.get slot)
  invFun pair := (Exception.writeEntry pair.1 slot pair.2, pair.1.get slot)
  left_inv pair := by
    obtain ⟨entry, byte⟩ := pair
    simp only [Exception.writeEntry, Vector.get_eq_getElem, Vector.set_set,
      Vector.set_getElem_self, Vector.getElem_set_self]
  right_inv pair := by
    obtain ⟨entry, byte⟩ := pair
    simp only [Exception.writeEntry, Vector.get_eq_getElem, Vector.set_set,
      Vector.set_getElem_self, Vector.getElem_set_self]

/-- **One written gadget slot**: the pad, with the slot (if any) overwritten by the digest's low
byte XOR the digit code. The digest is the evaluator-visible part XOR the hidden part. -/
def gadgetEntry (slot : Option (Fin 12)) (code : BitVec 8) (visibleDigest : Block)
    (pad : Exception.Entry) (hidden : Block) : Exception.Entry :=
  match slot with
  | none => pad
  | some index => Exception.writeEntry pad index (Exception.lowByte (hidden ^^^ visibleDigest) ^^^ code)

/-- **The one-slot gadget bijection**, against the entry and a residual byte and 120 bits. -/
def gadgetEquiv (slot : Option (Fin 12)) (code : BitVec 8) (visibleDigest : Block) :
    (Exception.Entry × Block) ≃ (Exception.Entry × (BitVec 8 × BitVec 120)) :=
  match slot with
  | none => Equiv.prodCongr (Equiv.refl _) Kriterion.ArgoMAC.Security.PGS.blockLowByteEquiv
  | some index =>
    { toFun := fun pair =>
        (Exception.writeEntry pair.1 index
          ((Kriterion.ArgoMAC.Security.PGS.blockLowByteEquiv (pair.2 ^^^ visibleDigest)).1 ^^^ code),
         (pair.1.get index,
          (Kriterion.ArgoMAC.Security.PGS.blockLowByteEquiv (pair.2 ^^^ visibleDigest)).2))
      invFun := fun pair =>
        (Exception.writeEntry pair.1 index pair.2.1,
         Kriterion.ArgoMAC.Security.PGS.blockLowByteEquiv.symm
           (pair.1.get index ^^^ code, pair.2.2) ^^^ visibleDigest)
      left_inv := fun pair => by
        obtain ⟨entry, hidden⟩ := pair
        simp only [Exception.writeEntry, Vector.get_eq_getElem, Vector.set_set,
          Vector.set_getElem_self, Vector.getElem_set_self, BitVec.xor_assoc, BitVec.xor_self,
          BitVec.xor_zero, Prod.mk.eta, Equiv.symm_apply_apply]
      right_inv := fun pair => by
        obtain ⟨entry, byte, high⟩ := pair
        simp only [Exception.writeEntry, Vector.get_eq_getElem, Vector.set_set,
          Vector.getElem_set_self, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero,
          Equiv.apply_symm_apply, Vector.set_getElem_self] }

theorem gadgetEquiv_fst (slot : Option (Fin 12)) (code : BitVec 8) (visibleDigest : Block)
    (pair : Exception.Entry × Block) :
    (gadgetEquiv slot code visibleDigest pair).1 = gadgetEntry slot code visibleDigest pair.1 pair.2 := by
  cases slot <;> rfl

/-- How the two digests of a digit share their hidden coins: `(later, shared)`. The digest solved
second (the sign-zero digest when `later = true`, else the doubling digest) also reads the other
digest's hidden coin when `shared = true`; the one solved first reads only its own. -/
abbrev GadgetMix := Bool × Bool

/-- The two hidden coins as the two digests read them: the triangular mix `mixCoins`. -/
def mixCoins (mix : GadgetMix) (coins : Block × Block) : Block × Block :=
  if mix.1 then (coins.1, coins.2 ^^^ (if mix.2 then coins.1 else 0))
  else (coins.1 ^^^ (if mix.2 then coins.2 else 0), coins.2)

/-- The triangular mix is its own inverse. -/
def mixEquiv (mix : GadgetMix) : (Block × Block) ≃ (Block × Block) where
  toFun := mixCoins mix
  invFun := mixCoins mix
  left_inv coins := by
    obtain ⟨first, second⟩ := coins
    obtain ⟨later, shared⟩ := mix
    cases later <;> cases shared <;>
      simp [mixCoins, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  right_inv coins := by
    obtain ⟨first, second⟩ := coins
    obtain ⟨later, shared⟩ := mix
    cases later <;> cases shared <;>
      simp [mixCoins, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- **The published gadget entry** of a digit (`FieldMacToECMac.garbleEntry`): the pad, with the
doubling slot and then the sign-zero slot (if the digit is non-zero) overwritten by their digests'
low bytes XOR the digit code. Each digest is its evaluator-visible part XOR its hidden part, the
two hidden parts being the mixed coins. -/
def gadgetEntry2 (slots : Option (Fin 12 × Fin 12)) (mix : GadgetMix) (code : BitVec 8)
    (visibleDigests : Block × Block) (pad : Exception.Entry) (hidden : Block × Block) :
    Exception.Entry :=
  gadgetEntry (slots.map Prod.snd) code visibleDigests.2
    (gadgetEntry (slots.map Prod.fst) code visibleDigests.1 pad (mixCoins mix hidden).1)
    (mixCoins mix hidden).2

/-- **The gadget bijection** of one digit: the mix, then the doubling slot, then the sign-zero
slot, against the entry and two residual bytes and 120-bit remainders. -/
def gadgetEquiv2 (slots : Option (Fin 12 × Fin 12)) (mix : GadgetMix) (code : BitVec 8)
    (visibleDigests : Block × Block) :
    (Exception.Entry × (Block × Block)) ≃
      (Exception.Entry × ((BitVec 8 × BitVec 120) × (BitVec 8 × BitVec 120))) :=
  ((Equiv.refl Exception.Entry).prodCongr (mixEquiv mix)).trans
    ((Equiv.prodAssoc _ _ _).symm.trans
      (((gadgetEquiv (slots.map Prod.fst) code visibleDigests.1).prodCongr (Equiv.refl Block)).trans
        ((Equiv.prodAssoc _ _ _).trans
          (((Equiv.refl Exception.Entry).prodCongr (Equiv.prodComm _ _)).trans
            ((Equiv.prodAssoc _ _ _).symm.trans
              (((gadgetEquiv (slots.map Prod.snd) code visibleDigests.2).prodCongr
                  (Equiv.refl (BitVec 8 × BitVec 120))).trans
                ((Equiv.prodAssoc _ _ _).trans
                  ((Equiv.refl Exception.Entry).prodCongr (Equiv.prodComm _ _)))))))))

theorem gadgetEquiv2_fst (slots : Option (Fin 12 × Fin 12)) (mix : GadgetMix) (code : BitVec 8)
    (visibleDigests : Block × Block) (pair : Exception.Entry × (Block × Block)) :
    (gadgetEquiv2 slots mix code visibleDigests pair).1 =
      gadgetEntry2 slots mix code visibleDigests pair.1 pair.2 := by
  obtain ⟨pad, hidden⟩ := pair
  simp only [gadgetEquiv2, gadgetEntry2, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map, id, Equiv.prodAssoc_symm_apply, Equiv.prodAssoc_apply, Equiv.prodComm_apply,
    Prod.swap, mixEquiv, Equiv.coe_fn_mk]
  rw [gadgetEquiv_fst, gadgetEquiv_fst]

/-! ## All components at once -/

/-- Everything the simulator does not sample and the proof holds fixed: the true row coefficients
(offsets, digits, `ρ`), the evaluator-visible remainders of the fold joins and gadget digests (as
functions of the bridge key), and each gadget entry's slot and digit code. The labels and `Δ` enter
only through these remainders: they are deferred, as the note says. -/
structure JointContext where
  /-- The true row coefficients of each digit (`FieldMacToECMac.rowsForOutputKeys`). -/
  rows : Fin digitCount → Coordinates.Rows
  /-- Each digit's `ρ` (read by the construction's `RowRandomness`; it enters the rows only). -/
  rho : Fin digitCount → NonZeroBase
  /-- The visible remainder of each fold join, given the bridge key. -/
  foldVisible : BaseField → Lane → Fin foldStepCount → Block
  /-- The visible parts of each digit's two gadget digests, given the bridge key. -/
  gadgetVisible : BaseField → Fin digitCount → Block × Block
  /-- The two exceptional slots of each digit's entry (`none` for digit zero). -/
  gadgetSlot : Fin digitCount → Option (Fin 12 × Fin 12)
  /-- How each digit's two digests share their hidden coins. -/
  gadgetMix : Fin digitCount → GadgetMix
  /-- Each digit's code (`Exception.digitCode`). -/
  gadgetCode : Fin digitCount → BitVec 8

/-- The gadget coins: each digit's pad and the hidden parts of its two digests. -/
abbrev GadgetCoins := Fin digitCount → Exception.Entry × (Block × Block)

/-- **The G1U coins**, all components. -/
abbrev JointCoins := (Fin digitCount → DigitCoins) × (CurveCoins × (FoldCells × GadgetCoins))

/-- **The published cells**, all components. -/
abbrev PublicCells := (Fin digitCount → DigitJoins × RowGamma) ×
  (CurveJoins × CurveMembership.Table) × FoldCells × (Fin digitCount → Exception.Entry)

/-- **The visible masks**, all components. -/
abbrev VisibleCells (shape : JointShape) := (Fin digitCount → DigitVisible shape) × CurveVisible shape

/-- What the bijection sets aside: the curve mask and, per digit, two pad bytes and 120 digest bits
each. -/
abbrev Residual := NonZeroBaseField ×
  (Fin digitCount → (BitVec 8 × BitVec 120) × (BitVec 8 × BitVec 120))

instance : Nonempty NonZeroBaseField := ⟨⟨1, by decide⟩⟩
instance : Nonempty Exception.Entry := ⟨Vector.replicate 12 0⟩

/-- The bridge key among the coins. -/
def bridgeKeyOf (coins : JointCoins) : BaseField := coins.2.1.2.1

section Joint

variable [FieldCertificate] (shape : JointShape) (context : JointContext)

/-- **The published cells** of the G1U coins, component by component, by the construction's own
formulas. -/
def publicOf (coins : JointCoins) : PublicCells :=
  (fun digit => (digitJoins (context.rows digit) (coins.1 digit),
      digitGamma (context.rows digit) (coins.1 digit)),
   (curveJoins coins.2.1.1 coins.2.1.2.2.2.1 coins.2.1.2.2.2.2,
      curveTable coins.2.1.1 coins.2.1.2.1 coins.2.1.2.2.1 coins.2.1.2.2.2.1 coins.2.1.2.2.2.2),
   fun lane c => coins.2.2.1 lane c ^^^ context.foldVisible (bridgeKeyOf coins) lane c,
   fun digit => gadgetEntry2 (context.gadgetSlot digit) (context.gadgetMix digit)
      (context.gadgetCode digit) (context.gadgetVisible (bridgeKeyOf coins) digit)
      (coins.2.2.2 digit).1 (coins.2.2.2 digit).2)

/-- **The visible masks** of the G1U coins. -/
def visibleOf (coins : JointCoins) : VisibleCells shape :=
  (fun digit => digitVisible shape (coins.1 digit), curveVisible shape coins.2.1.1)

/-- The 91 digits at once. -/
def digitsEquiv : (Fin digitCount → DigitCoins) ≃
    (Fin digitCount → DigitJoins × RowGamma) × (Fin digitCount → DigitVisible shape) :=
  (Equiv.piCongrRight fun digit => digitEquiv shape (context.rows digit)).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

/-- The 91 gadget entries at once, given the bridge key. -/
def gadgetsEquiv (bridgeKey : BaseField) :
    GadgetCoins ≃ (Fin digitCount → Exception.Entry) ×
      (Fin digitCount → (BitVec 8 × BitVec 120) × (BitVec 8 × BitVec 120)) :=
  (Equiv.piCongrRight fun digit => gadgetEquiv2 (context.gadgetSlot digit)
      (context.gadgetMix digit) (context.gadgetCode digit)
      (context.gadgetVisible bridgeKey digit)).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

/-- The curve, then — sheared over its bridge key — the folds and the gadgets. -/
def restEquiv : CurveCoins × (FoldCells × GadgetCoins) ≃
    (((CurveJoins × CurveMembership.Table) × CurveVisible shape) × NonZeroBaseField) ×
      (FoldCells × ((Fin digitCount → Exception.Entry) ×
        (Fin digitCount → (BitVec 8 × BitVec 120) × (BitVec 8 × BitVec 120)))) :=
  Equiv.prodShear (curveEquiv shape) fun curve =>
    (foldEquiv (context.foldVisible curve.2.1)).prodCongr (gadgetsEquiv context curve.2.1)

/-- The final reassociation into (published, visible) and residual. -/
def jointShuffle {A V₁ C V₂ N F E R : Type} :
    ((A × V₁) × (((C × V₂) × N) × (F × (E × R)))) ≃ (((A × C × F × E) × (V₁ × V₂)) × (N × R)) where
  toFun x := (((x.1.1, x.2.1.1.1, x.2.2.1, x.2.2.2.1), (x.1.2, x.2.1.1.2)), (x.2.1.2, x.2.2.2.2))
  invFun y := ((y.1.1.1, y.1.2.1), (((y.1.1.2.1, y.1.2.2), y.2.1), (y.1.1.2.2.1, (y.1.1.2.2.2, y.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The joint bijection**: all G1U coins against (published cells, visible masks) and a residual,
assembled from `digitEquiv` (per digit, both lanes), `curveEquiv`, `foldEquiv` and `gadgetEquiv` by
`Equiv.piCongrRight`, `Equiv.prodShear` and `Equiv.prodCongr`. -/
def jointEquiv : JointCoins ≃ (PublicCells × VisibleCells shape) × Residual :=
  ((digitsEquiv shape context).prodCongr (restEquiv shape context)).trans jointShuffle

/-- The joint bijection's first component is exactly (published cells, visible masks). -/
theorem jointEquiv_fst (coins : JointCoins) :
    (jointEquiv shape context coins).1 = (publicOf context coins, visibleOf shape coins) := by
  obtain ⟨digits, curve, folds, gadgets⟩ := coins
  refine Prod.ext (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))) rfl
  funext digit
  exact gadgetEquiv2_fst _ _ _ _ (gadgets digit)

/-- The coin space is finite (assembled stepwise: the one-shot instance search exceeds its size
bound on this product). -/
noncomputable instance jointCoinsFintype : Fintype JointCoins :=
  @instFintypeProd _ _ (inferInstance : Fintype (Fin digitCount → DigitCoins))
    (inferInstance : Fintype (CurveCoins × (FoldCells × GadgetCoins)))

noncomputable instance publicCellsFintype : Fintype PublicCells := inferInstance

noncomputable instance visibleCellsFintype : Fintype (VisibleCells shape) :=
  @instFintypeProd _ _ (inferInstance : Fintype (Fin digitCount → DigitVisible shape))
    (inferInstance : Fintype (CurveVisible shape))

noncomputable instance publicVisibleFintype : Fintype (PublicCells × VisibleCells shape) :=
  @instFintypeProd _ _ publicCellsFintype (visibleCellsFintype shape)

noncomputable instance residualFintype : Fintype Residual := inferInstance

/-- **F4: THE JOINT EXACTNESS OF `G1U → H`.** Under the G1U coins, the published cells of every
component (both lanes of every digit, all 52 chunks, the row constants, the curve joins and
constants, every fold join, every gadget entry) together with every visible mask are **exactly**
uniform. -/
theorem jointExactness :
    (PMF.uniformOfFintype JointCoins).map (fun coins => (publicOf context coins, visibleOf shape coins))
      = PMF.uniformOfFintype (PublicCells × VisibleCells shape) := by
  have factor : (fun coins => (publicOf context coins, visibleOf shape coins))
      = Prod.fst ∘ jointEquiv shape context :=
    funext fun coins => (jointEquiv_fst shape context coins).symm
  rw [factor, ← PMF.map_comp, uniformOfFintype_map_equiv (jointEquiv shape context),
    Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_fst]

/-! ### The simulator's other quantities are functions of the published and visible cells -/

/-- **The row values `W` the three published rows evaluate to** at the input: the true rows (for
sparse rows they are `FieldMacToECMac.evaluateRow`, `rowTarget_eq_evaluateRow`, whose law given the
output is `Opening`'s theorem). -/
def rowTarget (rows : Coordinates.Rows) (input : AffineInput) : HomogeneousValue :=
  ⟨rows.x.constant + rows.x.x * input.x + rows.x.y * input.y + rows.x.xSquared * input.x ^ 2,
   rows.y.constant + rows.y.y * input.y + rows.y.xSquared * input.x ^ 2
     + rows.y.ySquared * input.y ^ 2,
   rows.z.constant + rows.z.x * input.x⟩

theorem rowTarget_eq_evaluateRow (rows : Coordinates.Rows) (input : AffineInput)
    (sparse : SparseRow rows) : rowTarget rows input = evaluateRow rows input := by
  obtain ⟨xXY, xY2, yX, yXY, zY, zXY, zX2, zY2⟩ := sparse
  simp only [rowTarget, evaluateRow, Coordinates.evaluate, xXY, xY2, yX, yXY, zY, zXY, zX2, zY2]
  congr 1 <;> ring

/-- The true delivered values of a digit are the construction's `Biquadratic.delivered`. -/
theorem digitDelivered_eq (rows : Coordinates.Rows) (masks : DigitMasks) :
    (fun element => digitOffsets masks element + digitSlopes rows masks element * digitSigma shape element)
      = Biquadratic.delivered rows (digitOffsets masks) shape.input := by
  funext element
  rw [Biquadratic.delivered, digitSigma]
  rcases element with element | element <;>
    simp only [JointShape.digitAlpha, JointShape.sigmaOf_alphaX, JointShape.sigmaOf_alphaY,
      Biquadratic.coordValue_inl, Biquadratic.coordValue_inr, digitSlopes] <;> ring

/-- At the true delivered values the published rows hit the true row values, on the curve (the
`Y` row is exact there, `Biquadratic.evaluateEncodedY`). -/
theorem evaluateGamma_delivered (rows : Coordinates.Rows) (masks : DigitMasks)
    (onCurve : OnCurve shape.input) :
    evaluateGamma (digitGamma rows masks) shape.input
        (Biquadratic.delivered rows (digitOffsets masks) shape.input)
      = rowTarget rows shape.input := by
  have hx := Biquadratic.evaluateEncodedX rows (digitOffsets masks) shape.input
  have hy := Biquadratic.evaluateEncodedY rows (digitOffsets masks) shape.input onCurve
  have hz := Biquadratic.evaluateEncodedZ rows (digitOffsets masks) shape.input
  rw [evaluateGamma, rowTarget, HomogeneousValue.mk.injEq]
  exact ⟨hx, hy, hz⟩

/-- The component of a collector triple a collector controls. -/
def collectorComponent (element : Biquadratic.Element) (triple : BaseField × BaseField × BaseField) :
    BaseField :=
  if element = collectorX then triple.1 else if element = collectorY then triple.2.1 else triple.2.2

/-- **The simulator's designated mask** (note §1.4): the collector solve at the target rows, from
the published constants and the four free delivered values, minus the visible running sum, over `κ`
(P3 writes `κ · (…)`; `κ = ±1` for `j* = α₀ xor 1`). -/
def simDesignated (target : HomogeneousValue) (joins : DigitJoins) (gamma : RowGamma)
    (visible : DigitVisible shape) (element : Biquadratic.Element) : BaseField :=
  shape.kappa⁻¹ * (collectorComponent element
      (collectorSolve gamma shape.input (fun e => digitPartial shape joins visible e) target)
    - digitPartial shape joins visible element)

/-- **The designated masks are the simulator's collector solve at the true rows.** -/
theorem designated_eq_solve (rows : Coordinates.Rows) (masks : DigitMasks)
    (element : Biquadratic.Element) (collector : IsCollector element)
    (onCurve : OnCurve shape.input) :
    masks element shape.designated
      = simDesignated shape (rowTarget rows shape.input) (digitJoins rows masks)
          (digitGamma rows masks) (digitVisible shape masks) element := by
  set values := Biquadratic.delivered rows (digitOffsets masks) shape.input
    with valuesDef
  have evalParts := digitPartial_forward shape rows masks
  have trueValues : ∀ e, values e
      = digitOffsets masks e + digitSlopes rows masks e * digitSigma shape e :=
    fun e => (congrFun (digitDelivered_eq shape rows masks) e).symm
  have freeValues : ∀ e, ¬ IsCollector e →
      digitPartial shape (digitJoins rows masks) (digitVisible shape masks) e = values e := by
    intro e notCollector
    rw [evalParts, if_neg notCollector, sub_zero, trueValues]
  have solve := collectorsOf_eq_solve (digitGamma rows masks) shape.input values
    (rowTarget rows shape.input) (onCurve_x_ne_zero shape.input onCurve)
    (evaluateGamma_delivered shape rows masks onCurve)
  have sameSolve : collectorSolve (digitGamma rows masks) shape.input values
      (rowTarget rows shape.input)
      = collectorSolve (digitGamma rows masks) shape.input
          (fun e => digitPartial shape (digitJoins rows masks) (digitVisible shape masks) e)
          (rowTarget rows shape.input) := by
    simp only [collectorSolve]
    rw [freeValues (.inl .rowX_x7) (by simp [IsCollector]),
      freeValues (.inr .rowX_y10) (by simp [IsCollector]),
      freeValues (.inr .rowY_y8) (by simp [IsCollector]),
      freeValues (.inr .rowY_y10) (by simp [IsCollector])]
  have collectorValue : values element
      = digitPartial shape (digitJoins rows masks) (digitVisible shape masks) element
        + shape.kappa * masks element shape.designated := by
    rw [evalParts, if_pos collector, trueValues]; ring
  have component : collectorComponent element
      (collectorSolve (digitGamma rows masks) shape.input values (rowTarget rows shape.input))
      = values element := by
    rw [← solve]
    rcases collector with rfl | rfl | rfl <;> simp [collectorComponent, collectorsOf]
  rw [simDesignated, ← sameSolve, component, collectorValue, add_sub_cancel_left, ← mul_assoc,
    inv_mul_cancel₀ shape.kappa_ne_zero, one_mul]

/-- The designated masks of the coins (collectors only). -/
def designatedOf (coins : JointCoins) : Fin digitCount → Biquadratic.Element → BaseField :=
  fun digit element => if IsCollector element then coins.1 digit element shape.designated else 0

/-- The simulator's designated masks, from the published and visible cells and the true rows. -/
def simulatorDesignated (cells : PublicCells × VisibleCells shape) :
    Fin digitCount → Biquadratic.Element → BaseField :=
  fun digit element => if IsCollector element then
    simDesignated shape (rowTarget (context.rows digit) shape.input) (cells.1.1 digit).1
      (cells.1.1 digit).2 (cells.2.1 digit) element
  else 0

/-- The simulator's bridge key: the evaluator's curve value on the published and visible cells. -/
def simulatorKey (cells : PublicCells × VisibleCells shape) : BaseField :=
  CurveMembership.evaluate cells.1.2.1.2 shape.input (curveDelivered shape cells.1.2.1.1 cells.2.2)

/-- **The joint law the simulator uses** (F4 with its consequences). For a valid input, jointly
over all components: the published cells and visible masks are uniform, the designated masks are
the simulator's collector solve at the true rows `W`, and the bridge key is the evaluator's curve
value — one `PMF` equation. -/
theorem jointLaw (onCurve : OnCurve shape.input) :
    (PMF.uniformOfFintype JointCoins).map (fun coins =>
        ((publicOf context coins, visibleOf shape coins), designatedOf shape coins,
          bridgeKeyOf coins))
      = (PMF.uniformOfFintype (PublicCells × VisibleCells shape)).map (fun cells =>
        (cells, simulatorDesignated shape context cells, simulatorKey shape cells)) := by
  have factor : (fun coins : JointCoins =>
      ((publicOf context coins, visibleOf shape coins), designatedOf shape coins, bridgeKeyOf coins))
      = (fun cells => (cells, simulatorDesignated shape context cells, simulatorKey shape cells))
        ∘ (fun coins => (publicOf context coins, visibleOf shape coins)) := by
    funext coins
    obtain ⟨digits, ⟨masks, bridgeKey, mask, r1, r2⟩, folds, gadgets⟩ := coins
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext digit element
      show (if IsCollector element then digits digit element shape.designated else 0)
        = if IsCollector element then _ else 0
      by_cases collector : IsCollector element
      · rw [if_pos collector, if_pos collector]
        exact designated_eq_solve shape (context.rows digit) (digits digit) element collector
          onCurve
      · rw [if_neg collector, if_neg collector]
    · exact (bridgeKey_eq_eval shape onCurve masks bridgeKey mask r1 r2).symm
  rw [factor, ← PMF.map_comp, jointExactness]

/-- The same, for **any** law of the context (the true rows, `ρ`, the deferred labels): the
simulator's cells are drawn independently of the context. -/
theorem jointLaw_context (contextLaw : PMF JointContext) (onCurve : OnCurve shape.input) :
    contextLaw.bind (fun context => (PMF.uniformOfFintype JointCoins).map (fun coins =>
        (context, (publicOf context coins, visibleOf shape coins), designatedOf shape coins,
          bridgeKeyOf coins)))
      = contextLaw.bind (fun context => (PMF.uniformOfFintype (PublicCells × VisibleCells shape)).map
        (fun cells => (context, cells, simulatorDesignated shape context cells,
          simulatorKey shape cells))) := by
  refine congrArg _ (funext fun context => ?_)
  have joint := congrArg (PMF.map (Prod.mk context)) (jointLaw shape context onCurve)
  simpa only [PMF.map_comp, Function.comp_def] using joint

end Joint

/-! ## The coins' masks are exactly `MaskSwap`'s masks, reorganised by digit

`MaskSwap.swappedTape_garblerMasks` makes the construction's `6,352` switch-mask vectors iid uniform
on `MaskVectors`, which `MaskSwap.maskCoordEquiv` flattens to `MaskCoord → F_p` (vector site, lane
element slot: `1,588 · 642 = 1,019,496` masks). `maskSiteEquiv` reorganises them by digit
— the `pointX` slot `4d + slot(e)` and the `pointY` slot `3d + slot(e)` become digit `d`'s element
`e` (`Pipeline.pointXAssemble_digit`) — and by curve element, which is the mask component of
`JointCoins`. -/

theorem card_xElement : Fintype.card XElement = xSlotsPerDigit := by decide

theorem card_yElement : Fintype.card YElement = ySlotsPerDigit := by decide

/-- The `pointX` lane's slots are the digits' x-type elements (`Elements.xElementIndex`). -/
def pointXSlots : Fin digitCount × XElement ≃ Fin pointElementCountX :=
  Equiv.ofBijective (fun pair => xElementIndex pair.1 pair.2)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨xElementIndex_injective, by
      rw [Fintype.card_prod, Fintype.card_fin, card_xElement, Fintype.card_fin]; rfl⟩)

/-- The `pointY` lane's slots are the digits' y-type elements. -/
def pointYSlots : Fin digitCount × YElement ≃ Fin pointElementCountY :=
  Equiv.ofBijective (fun pair => yElementIndex pair.1 pair.2)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨yElementIndex_injective, by
      rw [Fintype.card_prod, Fintype.card_fin, card_yElement, Fintype.card_fin]; rfl⟩)

/-- The `curveX` lane's slots. -/
def curveXSlots : CurveXElement ≃ Fin curveElementCountX :=
  Equiv.ofBijective curveXElementIndex
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨curveXElementIndex_injective, by decide⟩)

/-- The `curveY` lane's slots. -/
def curveYSlots : CurveYElement ≃ Fin curveElementCountY :=
  Equiv.ofBijective curveYElementIndex
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨curveYElementIndex_injective, by decide⟩)

/-- Every lane element slot is a digit element or a curve element. -/
def laneSlots : (Σ lane : Lane, Fin (laneCount lane))
    ≃ (Fin digitCount × Biquadratic.Element) ⊕ CurveMembership.Element where
  toFun
    | ⟨.curveX, slot⟩ => .inr (.inl (curveXSlots.symm slot))
    | ⟨.curveY, slot⟩ => .inr (.inr (curveYSlots.symm slot))
    | ⟨.pointX, slot⟩ => .inl ((pointXSlots.symm slot).1, .inl (pointXSlots.symm slot).2)
    | ⟨.pointY, slot⟩ => .inl ((pointYSlots.symm slot).1, .inr (pointYSlots.symm slot).2)
  invFun
    | .inl (digit, .inl element) => ⟨.pointX, pointXSlots (digit, element)⟩
    | .inl (digit, .inr element) => ⟨.pointY, pointYSlots (digit, element)⟩
    | .inr (.inl element) => ⟨.curveX, curveXSlots element⟩
    | .inr (.inr element) => ⟨.curveY, curveYSlots element⟩
  left_inv := by
    rintro ⟨lane, slot⟩
    cases lane <;> exact congrArg (Sigma.mk _) (Equiv.apply_symm_apply _ _)
  right_inv := by
    rintro ((⟨digit, element | element⟩) | (element | element)) <;> simp

/-- A mask coordinate is a lane slot and a (chunk, switch) pair. -/
def maskSiteSplit : MaskCoord ≃ (Σ lane : Lane, Fin (laneCount lane)) × ChunkSwitch where
  toFun coord := (⟨coord.1.lane, coord.2⟩, ⟨coord.1.chunk, coord.1.switch⟩)
  invFun pair := ⟨⟨pair.1.1, pair.2.1, pair.2.2⟩, pair.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`MaskSwap`'s mask family, reorganised** into the per-digit (both lanes) and curve masks of the
G1U coins. -/
def maskSiteEquiv : (MaskCoord → BaseField) ≃ (Fin digitCount → DigitMasks) × CurveMasks :=
  (Equiv.arrowCongr (maskSiteSplit.trans (Equiv.prodCongr laneSlots (Equiv.refl _)))
      (Equiv.refl BaseField)).trans
    ((Equiv.curry _ _ _).trans
      ((Equiv.sumArrowEquivProdArrow _ _ _).trans
        (Equiv.prodCongr (Equiv.curry _ _ _) (Equiv.refl _))))

/-- Digit `d`'s x-type element `e` reads the `pointX` lane's slot `4d + slot(e)`. -/
theorem maskSiteEquiv_pointX (masks : MaskCoord → BaseField) (digit : Fin digitCount)
    (element : XElement) (cs : ChunkSwitch) :
    (maskSiteEquiv masks).1 digit (.inl element) cs
      = masks ⟨⟨.pointX, cs.1, cs.2⟩, xElementIndex digit element⟩ := by
  simp [maskSiteEquiv, maskSiteSplit, laneSlots, Equiv.arrowCongr_apply, pointXSlots]

/-- Digit `d`'s y-type element `e` reads the `pointY` lane's slot `3d + slot(e)`. -/
theorem maskSiteEquiv_pointY (masks : MaskCoord → BaseField) (digit : Fin digitCount)
    (element : YElement) (cs : ChunkSwitch) :
    (maskSiteEquiv masks).1 digit (.inr element) cs
      = masks ⟨⟨.pointY, cs.1, cs.2⟩, yElementIndex digit element⟩ := by
  simp [maskSiteEquiv, maskSiteSplit, laneSlots, Equiv.arrowCongr_apply, pointYSlots]

/-- **`MaskSwap`'s uniform masks are the G1U coins' uniform masks.** -/
theorem maskSiteEquiv_uniform :
    (PMF.uniformOfFintype (MaskCoord → BaseField)).map maskSiteEquiv
      = PMF.uniformOfFintype ((Fin digitCount → DigitMasks) × CurveMasks) :=
  uniformOfFintype_map_equiv maskSiteEquiv

end

end Kriterion.ArgoMAC.Security.Phase3
