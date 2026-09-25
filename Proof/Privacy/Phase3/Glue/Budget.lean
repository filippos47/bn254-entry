/-
Phase 3 glue, step 4a: **the error terms of the Plan B chain and the closing inequality.**

Each term is the formula of design note B §5, with the corrections of the review and of P1, for
the phase-4 batched hash-vector sampler (brief A1 §3) at the phase-5 chunk profile. Each switch
mask is one lane vector `sampleLane n k` of `k` hash answers; the garbler draws one vector per
(lane, chunk, switch), `1,588` per lane.

| hop | term | value |
|---|---|---|
| `G0 → G0U` | `maskSwapError = 1588 · Σ_lane laneDelta lane`, with the per-vector bias `laneDelta` = `2^-142`, `2^-290`, `2^-262`, `2^-260` (pointX, pointY, curveX, curveY) | `≤ 1589/2^142 ≈ 2^-131.37` |
| `G0U → G1U` | `hiddenPointError q = 3q/2^128 + 2q/(p−1)` (`L1`; the bridge guess `bridgeInput t = key` has mass `≤ 2/(p−1)`, since `bridgeInput` is at most 2-to-1) | linear |
| `G1U → HW` | `stageOneHitError q₁ + exceptionalError + maskSwapError + coincidenceError`: `L2 = 4q₁/2^128`, plus the exceptional mass `364/(r−1)` (both exceptional kinds; the gadget goes from real to lazy in this hop; P1d, `PublicFirst.gadget_counterShape_refutes`), plus one more mask swap, plus the label-coincidence allowance `2^16/2^128` of the designed sub-hop `G1U → G1U°` (P1j, `PublicFirst.LiftHop`). The mask swap is needed because off the curve `G1U` installs the system-A vectors with `G0U`'s uniform values while `HW` makes no call, so the adversary's own vectors are `sampleLane` of fresh hash answers (P1g; the middle game `M'` of `PublicFirst/MiddleOff.lean` carries the swap). | linear + `2^-112` |
| `HW → H` | `outputKernelError = 455/(r−1)` (`ε_pt`; P1's lemmas give `≤ 455/#Point`) | `2^-244.8` |
| `H → I^U` | `abortError q₁ = q₁·abortQueryCharge q₁`, `abortQueryCharge q₁ = 1/(2^128−q₁)` (per stage-1 query at a candidate designated input: input freshness through `E*`'s min-entropy; hash programming needs only a fresh input, so there is no output part; see `AbortBound`) | linear |
| `I^U → I` | `maskSwapError + idealRefillError q₁`, `idealRefillError q₁ = 0` (lazy hash answers are exactly uniform) | `2^-131.37` |
| `I → M` | `machineCutoffError = 2^-128` (`ε_cut`; the machine's samplers cut off far below it: the designated preimage's `t` sampler, 80 attempts each rejecting with mass `≤ 3/10`, aborts with mass `≤ 2^-138`, and the source, tail, lift and free-coordinate samplers with less) | constant |

`chainError_budget`: for `q₁ + q₂ < 2^100`, `chainError q₁ q₂ · 2^100 ≤ q₁ + q₂ + 1`. Every term
is bounded by a thousandth of its unit, so the budget closes with the constant `≤ 7/1000` (seven
terms: three mask swaps, `364/(r−1)`, `455/(r−1)`, the cutoff and the coincidence allowance; the
value is ≈ `2^-112.0`, so `2^-12.0` in units of `2^-100`, dominated by `coincidenceError`) and the
linear coefficient `≤ 4/1000` (per query, in units of `2^-100`; the value is
`≤ 9/2^128 + 2/(p−1)`, so `≤ 2^-24.8`).
-/

import Proof.Privacy.Phase3.Glue.AbstractSimulator
import Proof.Privacy.Phase3.Basic

namespace Kriterion.ArgoMAC.Phase3.Glue

open BN254
open Kriterion.ArgoMAC.PlanB (Lane two_pow_150_lt_baseFieldModulus)
open Kriterion.ArgoMAC.Security.Phase3 (laneDelta laneDeltaExponent laneDelta_le laneDelta_ne_top)
open scoped ENNReal

noncomputable section

/-- The mask vectors the garbler draws **per lane**: one per (chunk, switch of that chunk),
`Σ_c 2^{w_c} = 4 + 48·32 + 3·16 = 1,588` under the phase-5 profile (chunk widths
`[2, 5 × 48, 4 × 3]`, 52 chunks); `6,352` over the four lanes. It is stated as a numeral; the
`Params`-level identity `Σ_c 2^{w_c} = laneVectorCount` belongs with the mask swap, which counts
the vector sites. -/
def laneVectorCount : ℕ := 1588

/-- One copy of the global mask swap: every lane's `1,588` vectors, each at its lane's proof bias
`laneDelta` (`Security.Phase3.laneDelta_le`: `2^-142` pointX, `2^-290` pointY, `2^-262` curveX,
`2^-260` curveY). Its value is `≤ 1589/2^142 ≈ 2^-131.37` (`maskSwapError_le_pow`). -/
def maskSwapError : ℝ := ((laneVectorCount : ℝ≥0∞) * ∑ lane : Lane, laneDelta lane).toReal

/-- `L1`: hidden-point hits (`Δ` guesses, hidden outputs, hidden hash inputs). A hash query reaches
either one scale site (label mass `≤ 1/2^128`) or the bridge input, and the remapped bridge input is
at most 2-to-1 in `t`, so `Pr[bridgeInput t = key | view] ≤ 2/(p−1)`. -/
def hiddenPointError (queries : ℕ) : ℝ :=
  3 * (queries : ℝ) / 2 ^ 128 + 2 * (queries : ℝ) / ((baseFieldModulus : ℝ) - 1)

/-- `L2`: stage-1 hits on a garbler point. -/
def stageOneHitError (first : ℕ) : ℝ := 4 * (first : ℝ) / 2 ^ 128

/-- `ε_exc`: the exceptional mass at the adversary's input, both exceptional kinds of every digit
(the doubling input `Q = K` and the sign-zero input `Q = 2K`), with the collision extension:
`≤ (3/2) · 182/#Point · (1 − 91/#Point)⁻¹ ≤ 364/(r−1)`. It is charged in `G1U → HW`, where the gadget
switches from the garbler's entries (which unlock the true digit at an exceptional input) to uniform
published bytes. -/
def exceptionalError : ℝ := 364 / ((scalarFieldModulus : ℝ) - 1)

/-- `ε_coin`: the label-coincidence allowance of `G1U → HW`, `2^16/2^128 = 2^-112`. The hop runs
through `G1U°` (P1j, `PublicFirst.LiftHop`): the identical-until-bad sub-hop `G1U → G1U°`, which
installs the designed garbler entries instead of the reach's, costs the mass of the coincidence
event, at most `2^16` label-coincidence groups of `2^-128` each. It does not depend on `q₁`.
Phase 3 hid it in the slack of its mask swap `N·δ₃ = 2^-111.86`; the batched sampler's
`maskSwapError` (`2^-131.37`) is too small for that, so it is its own term. -/
def coincidenceError : ℝ := 2 ^ 16 / 2 ^ 128

/-- `ε_pt`: the offset restriction, the doubling rows and the tail restriction of the output
kernel. P1's opening lemmas give `≤ 455/#Point`, which is `≤ 455/(r−1)` since `#Point ≥ r`. -/
def outputKernelError : ℝ := 455 / ((scalarFieldModulus : ℝ) - 1)

/-- The abort charge of **one stage-1 query at a candidate designated input**: the designated label
`E*` equals the query's recorded domain, `≤ max_e Pr[E* = e | view] ≤ 1/(2^128 − q₁)`. There is
no output part: programming the hash oracle needs only a fresh input. A hash input decodes to at
most one scale site (`PlanB.scaleInput_injective`), so the query is charged to one candidate site
only; summed over the distinct candidate inputs the coefficient is `1` (no factor for the four
candidate switches). -/
def abortQueryCharge (first : ℕ) : ℝ := 1 / (2 ^ 128 - (first : ℝ))

/-- `ε_abort`: the per-query charge over the `q₁` stage-1 queries. -/
def abortError (first : ℕ) : ℝ := (first : ℝ) * abortQueryCharge first

/-- `L3`: the lazy-refill charge of `I^U → I`, which is `0`. Its only charge was answer exclusion,
and the lazy hash answers are exactly uniform (`HashTable.query`), so refilling the derived mask
vectors costs nothing beyond the mask swap. -/
def idealRefillError (_first : ℕ) : ℝ := 0

/-- The whole chain `G0 → G0U → G1U → HW → H → I^U → I → M`. -/
def chainError (first second : ℕ) : ℝ :=
  maskSwapError + hiddenPointError (first + second) +
    (stageOneHitError first + exceptionalError + maskSwapError + coincidenceError) +
    outputKernelError + abortError first + (maskSwapError + idealRefillError first) +
    machineCutoffError

/-! ### Each term against its unit

No power above `2^256` is evaluated: the lane biases stay exponents, and `p` enters only through
`2^150 < p`. -/

/-- A sum over the four lanes, written out. -/
theorem sum_lane {M : Type*} [AddCommMonoid M] (f : Lane → M) :
    ∑ lane : Lane, f lane = f .curveX + f .curveY + f .pointX + f .pointY := by
  rw [show (Finset.univ : Finset Lane) = {.curveX, .curveY, .pointX, .pointY} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide),
    add_assoc, add_assoc]

/-- `laneDelta_le`, in `ℝ`. -/
theorem laneDelta_toReal_le (lane : Lane) :
    (laneDelta lane).toReal ≤ 1 / 2 ^ laneDeltaExponent lane := by
  have bound := ENNReal.toReal_mono (ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero))
    (laneDelta_le lane)
  simpa [ENNReal.toReal_inv, ENNReal.toReal_pow] using bound

/-- `maskSwapError` in `ℝ`: every lane bias is finite (`laneDelta_ne_top`). -/
theorem maskSwapError_eq_sum :
    maskSwapError = (laneVectorCount : ℝ) * ∑ lane : Lane, (laneDelta lane).toReal := by
  unfold maskSwapError
  rw [ENNReal.toReal_mul, ENNReal.toReal_sum fun lane _ => laneDelta_ne_top lane,
    ENNReal.toReal_natCast]

/-- **The mask-swap value**, `1588·(2^-142 + 2^-290 + 2^-262 + 2^-260) ≤ 1589/2^142 ≈ 2^-131.37`:
the three smaller lanes are each `≤ 2^-260 = 2^-142·2^-118`, and `3·1588·2^-118 ≤ 1`. -/
theorem maskSwapError_le_pow : maskSwapError ≤ 1589 / 2 ^ 142 := by
  have smaller (lane : Lane) (big : 260 ≤ laneDeltaExponent lane) :
      (laneDelta lane).toReal ≤ 1 / 2 ^ 142 * (1 / 2 ^ 118) := by
    calc _ ≤ 1 / (2 : ℝ) ^ laneDeltaExponent lane := laneDelta_toReal_le lane
      _ ≤ 1 / 2 ^ 260 := one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ one_le_two big)
      _ = _ := by rw [one_div_mul_one_div, ← pow_add]
  have pointX : (laneDelta .pointX).toReal ≤ 1 / 2 ^ 142 := laneDelta_toReal_le .pointX
  have pointY := smaller .pointY (by decide)
  have curveX := smaller .curveX (by decide)
  have curveY := smaller .curveY (by decide)
  have tail : (1 : ℝ) / 2 ^ 142 * (4764 * (1 / 2 ^ 118)) ≤ 1 / 2 ^ 142 * 1 :=
    mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
  rw [maskSwapError_eq_sum, sum_lane, div_eq_mul_one_div (1589 : ℝ)]
  unfold laneVectorCount
  generalize (1 : ℝ) / 2 ^ 142 = unit at *
  generalize (1 : ℝ) / 2 ^ 118 = gap at *
  push_cast
  linarith

theorem maskSwapError_le : maskSwapError * 2 ^ 100 ≤ 1 / 1000 := by
  calc maskSwapError * 2 ^ 100 ≤ 1589 / 2 ^ 142 * 2 ^ 100 :=
        mul_le_mul_of_nonneg_right maskSwapError_le_pow (by positivity)
    _ ≤ 1 / 1000 := by norm_num

theorem exceptionalError_nonneg : 0 ≤ exceptionalError := by
  unfold exceptionalError scalarFieldModulus
  norm_num

theorem exceptionalError_le : exceptionalError * 2 ^ 100 ≤ 1 / 1000 := by
  unfold exceptionalError scalarFieldModulus
  norm_num

theorem outputKernelError_le : outputKernelError * 2 ^ 100 ≤ 1 / 1000 := by
  unfold outputKernelError scalarFieldModulus
  norm_num

theorem machineCutoffError_le : machineCutoffError * 2 ^ 100 ≤ 1 / 1000 := by
  unfold machineCutoffError
  norm_num

/-- `2^16/2^128 · 2^100 = 2^-12 ≈ 0.000244`. -/
theorem coincidenceError_le : coincidenceError * 2 ^ 100 ≤ 1 / 1000 := by
  unfold coincidenceError
  norm_num

theorem hiddenPointError_le (queries : ℕ) :
    hiddenPointError queries * 2 ^ 100 ≤ (queries : ℝ) / 1000 := by
  have split : hiddenPointError queries * 2 ^ 100 =
      (queries : ℝ) * ((3 / 2 ^ 128 + 2 / ((baseFieldModulus : ℝ) - 1)) * 2 ^ 100) := by
    unfold hiddenPointError
    ring
  have room : (2 : ℝ) ^ 149 ≤ (baseFieldModulus : ℝ) - 1 := by
    have big : (2 : ℝ) ^ 150 < baseFieldModulus := by exact_mod_cast two_pow_150_lt_baseFieldModulus
    have double : (2 : ℝ) ^ 150 = 2 ^ 149 * 2 := pow_succ 2 149
    have one : (1 : ℝ) ≤ 2 ^ 149 := one_le_pow₀ one_le_two
    linarith
  have bridge : 2 / ((baseFieldModulus : ℝ) - 1) ≤ 2 / 2 ^ 149 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) room
  have coefficient : (3 / 2 ^ 128 + 2 / ((baseFieldModulus : ℝ) - 1)) * 2 ^ 100 ≤ 1 / 1000 := by
    calc _ ≤ (3 / 2 ^ 128 + 2 / 2 ^ 149) * (2 : ℝ) ^ 100 :=
          mul_le_mul_of_nonneg_right (add_le_add le_rfl bridge) (by positivity)
      _ ≤ 1 / 1000 := by norm_num
  rw [split, div_eq_mul_one_div (queries : ℝ) 1000]
  exact mul_le_mul_of_nonneg_left coefficient (Nat.cast_nonneg _)

theorem stageOneHitError_le (first : ℕ) :
    stageOneHitError first * 2 ^ 100 ≤ (first : ℝ) / 1000 := by
  have split : stageOneHitError first * 2 ^ 100 = (first : ℝ) * (4 * 2 ^ 100 / 2 ^ 128) := by
    unfold stageOneHitError
    ring
  rw [split, div_eq_mul_one_div (first : ℝ) 1000]
  exact mul_le_mul_of_nonneg_left (by norm_num) (Nat.cast_nonneg _)

/-- Below `2^100` queries, `2^128 − q₁ ≥ 2^127`. -/
theorem room_le (first : ℕ) (small : first < 2 ^ 100) : (2 : ℝ) ^ 127 ≤ 2 ^ 128 - (first : ℝ) := by
  have firstSmall : (first : ℝ) ≤ 2 ^ 100 := by exact_mod_cast small.le
  have : (2 : ℝ) ^ 100 ≤ 2 ^ 127 := by norm_num
  have : (2 : ℝ) ^ 128 = 2 ^ 127 + 2 ^ 127 := by norm_num
  linarith

/-- The per-query abort charge is non-negative below `2^100` queries. -/
theorem abortQueryCharge_nonneg (first : ℕ) (small : first < 2 ^ 100) :
    0 ≤ abortQueryCharge first := by
  have room := room_le first small
  unfold abortQueryCharge
  have : (0 : ℝ) < 2 ^ 128 - (first : ℝ) := lt_of_lt_of_le (by positivity) room
  positivity

/-- The refill charge is `0`, so it is trivially within its unit. -/
theorem idealRefillError_le (first : ℕ) :
    idealRefillError first * 2 ^ 100 ≤ (first : ℝ) / 1000 := by
  unfold idealRefillError
  rw [zero_mul]
  positivity

theorem abortError_le (first : ℕ) (small : first < 2 ^ 100) :
    abortError first * 2 ^ 100 ≤ (first : ℝ) / 1000 := by
  have room := room_le first small
  have fresh : 1 / (2 ^ 128 - (first : ℝ)) ≤ 1 / 2 ^ 127 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) room
  have coefficient : abortQueryCharge first * 2 ^ 100 ≤ 1 / 1000 := by
    unfold abortQueryCharge
    calc _ ≤ 1 / 2 ^ 127 * (2 : ℝ) ^ 100 := mul_le_mul_of_nonneg_right fresh (by positivity)
      _ ≤ 1 / 1000 := by norm_num
  have split : abortError first * 2 ^ 100 = (first : ℝ) * (abortQueryCharge first * 2 ^ 100) := by
    unfold abortError
    ring
  rw [split, div_eq_mul_one_div (first : ℝ) 1000]
  exact mul_le_mul_of_nonneg_left coefficient (Nat.cast_nonneg _)

/-- **The closing inequality.** Below `2^100` queries the whole chain costs at most
`(q₁ + q₂ + 1) / 2^100`: the constant part (three mask swaps, the doubling exception, the output
kernel, the cutoff, the coincidence allowance) is below one unit and the linear part below one
unit per query. -/
theorem chainError_budget (first second : ℕ) (small : first + second < 2 ^ 100) :
    chainError first second * 2 ^ 100 ≤ (first : ℝ) + (second : ℝ) + 1 := by
  have swap := maskSwapError_le
  have kernel := outputKernelError_le
  have exceptional := exceptionalError_le
  have cutoff := machineCutoffError_le
  have coincidence := coincidenceError_le
  have hidden := hiddenPointError_le (first + second)
  have hit := stageOneHitError_le first
  have abort := abortError_le first (by omega)
  have refill := idealRefillError_le first
  have firstNonneg : (0 : ℝ) ≤ first := Nat.cast_nonneg _
  have secondNonneg : (0 : ℝ) ≤ second := Nat.cast_nonneg _
  push_cast at hidden
  unfold chainError
  nlinarith

end

end Kriterion.ArgoMAC.Phase3.Glue
