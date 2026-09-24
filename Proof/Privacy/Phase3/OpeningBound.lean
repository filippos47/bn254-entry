/-
**Phase 3, P1b — `OpeningBound`: `HW → H` at `outputKernelError = 364/(r−1)`.**

`HW` and `H` (`Opened.lean`) are one abstract simulator with two rows kernels: the construction's
true rows under the coins' law (`realRows`) and the tail/head-clamp/lift sampler (`simulatedRows`,
whose tail is the construction's own offset law). Everything else is shared, so the game distance
is at most the kernels' distance at the adversary's (valid) input and its output (§1, data
processing through `abstractIdealGame`). §2–§4 bound that kernel distance by `364 / #Point`, from
P1's `Opening.lean`: the real rows are lifts of the real digit points at uniform `λ` off the doubling
event (`realRow_*`, `lifts_law`), the doubling mass is `≤ 182/#Point` (`bn254_doubling_real_le`),
and the two point laws are within `91/#Point + 91/#Point` (`bn254_digitPoints_good_etvDist_le`, and
the good-tail restriction of the simulator's tail). §5 proves `#Point ≥ r` from the certificates
(the point `(1, 2)` has order exactly `r`), so `364/#Point ≤ 364/(r−1)`.
-/

import Proof.Privacy.Phase3.Opened
import Proof.Privacy.Phase3.Opening
import Proof.Correctness.Base7Termination

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Phase3.Glue (HybridGame PlanBAdversary Stage1Source LazyAbstractSimulator
  abstractIdealGame idealSamplers)
open scoped ENNReal

noncomputable section

/-! ## §1. The game distance is at most the rows kernels' distance -/

/-- The abstract ideal game, unfolded into `PMF` binds. -/
def stagedGame [FieldCertificate] {FixedIndex EncIndex Randomness Public Key Oracle Aux : Type}
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      Key LamportSignature Oracle)
    (simulator : LazyAbstractSimulator FixedIndex EncIndex Public)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedIndex EncIndex)
      AffineInput Public LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  (simulator.stage1 parameter LazyOracle.empty).bind fun first => match first with
  | none => PMF.pure false
  | some (circuit, state, oracle) =>
    (LazyOracle.run (adversary.chooseInput parameter circuit auxiliary) oracle).bind fun selected =>
      (simulator.stage2 state selected.1.1 (scheme.function scalar selected.1.1) selected.2).bind
        fun second => match second with
        | none => PMF.pure false
        | some (labels, updated) =>
          (LazyOracle.run (adversary.decide parameter circuit labels auxiliary selected.1.2)
            updated).map Prod.fst

/-- `abstractIdealGame` is `stagedGame`. -/
theorem abstractIdealGame_eq_staged [FieldCertificate]
    {FixedIndex EncIndex Randomness Public Key Oracle Aux : Type}
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      Key LamportSignature Oracle)
    (simulator : LazyAbstractSimulator FixedIndex EncIndex Public)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedIndex EncIndex)
      AffineInput Public LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    abstractIdealGame scheme simulator adversary parameter scalar auxiliary =
      stagedGame scheme simulator adversary parameter scalar auxiliary := by
  unfold abstractIdealGame stagedGame
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, liftM, monadLift,
    MonadLift.monadLift, OptionT.lift, Option.elimM, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.map_bind, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext first
  rcases first with _ | ⟨circuit, state, oracle⟩
  · simp [PMF.pure_map]
  · simp only [Option.elim, PMF.map_bind]
    congr 1
    funext selected
    congr 1
    funext second
    rcases second with _ | ⟨labels, updated⟩
    · simp [PMF.pure_map]
    · simp only [Option.elim, PMF.map_bind, PMF.pure_map, Option.getD_some]
      exact PMF.bind_pure_comp Prod.fst _

/-- **Data processing through the opened games.** Two opened simulators with the same installation
and different rows kernels give games within the kernels' largest distance at the adversary's input
and its output (`none` outputs are shared). -/
theorem openedGame_etvDist_le [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (first second : RowsKernel) (install : Installation)
    (adversary : PlanBAdversary Unit) (parameter : Nat) (scalar : NonZeroScalar) (bound : ℝ≥0∞)
    (close : ∀ input target, Scheme.scheme.function scalar input = some target →
      (first input target).etvDist (second input target) ≤ bound) :
    (abstractIdealGame Scheme.scheme (openedSimulator first install) adversary parameter scalar
        ()).etvDist
      (abstractIdealGame Scheme.scheme (openedSimulator second install) adversary parameter
        scalar ()) ≤ bound := by
  rw [abstractIdealGame_eq_staged, abstractIdealGame_eq_staged]
  unfold stagedGame
  refine etvDist_bind_left_le_const _ _ _ bound fun stageOne => ?_
  rcases stageOne with _ | ⟨circuit, state, oracle⟩
  · simp
  refine etvDist_bind_left_le_const _ _ _ bound fun selected => ?_
  refine le_trans (PMF.etvDist_bind_right_le _ _ _) ?_
  show ((openedSimulator first install).stage2 state selected.1.1
      (Scheme.scheme.function scalar selected.1.1) selected.2).etvDist
    ((openedSimulator second install).stage2 state selected.1.1
      (Scheme.scheme.function scalar selected.1.1) selected.2) ≤ bound
  unfold openedSimulator
  dsimp only
  cases output : Scheme.scheme.function scalar selected.1.1 with
  | none => simp
  | some target =>
    dsimp only
    refine le_trans (etvDist_map_le' _ _ _) ?_
    unfold openedOpening
    dsimp only
    refine etvDist_bind_left_le_const _ _ _ bound fun ran => ?_
    rcases ran with _ | ran
    · simp
    unfold openedCont
    exact le_trans (PMF.etvDist_bind_right_le _ _ _) (close _ _ output)

/-! ## §2. A true row is the lift of `T + K`, or the doubling row -/

/-- `2 ≠ 0` in the base field. -/
theorem two_ne_zero_base : (2 : BaseField) ≠ 0 := by decide

section Rows

variable [FieldCertificate] [GroupCertificate]

/-- The lift multiplier of a real row, from the digit multiple `T` and the offset `K`: `x_T − k_x`,
or `2 k_y` in the inverse case (P1's `realRow_xNe`, `realRow_neg`); `1` otherwise. -/
def pointMultiplier : Point → Point → BaseField
  | .some (x := tx) (y := ty) _, .some (x := kx) (y := ky) _ =>
      if tx = kx then (if ty = ky then 1 else 2 * ky) else tx - kx
  | _, _ => 1

/-- **The real row** of a digit multiple `T`, an offset `K` and a randomiser `ρ`: the doubling row
`(0, 0, 0)` when `T = K`, and otherwise the lift of `T + K` at `ρ · pointMultiplier T K`. -/
def realRowOf (T K : Point) (rho : BaseField) : FieldMacToECMac.HomogeneousValue :=
  if T = K then ⟨0, 0, 0⟩ else lift (T + K) (rho * pointMultiplier T K)

/-- Off the doubling case the multiplier is non-zero. -/
theorem pointMultiplier_ne_zero (T K : Point) (different : T ≠ K) : pointMultiplier T K ≠ 0 := by
  cases T with
  | zero => exact one_ne_zero
  | some tx ty tValid =>
    cases K with
    | zero => exact one_ne_zero
    | some kx ky kValid =>
      show (if tx = kx then (if ty = ky then (1 : BaseField) else 2 * ky) else tx - kx) ≠ 0
      by_cases sameX : tx = kx
      · rw [if_pos sameX]
        by_cases sameY : ty = ky
        · exact absurd (by subst sameX; subst sameY; rfl) different
        · rw [if_neg sameY]
          have onCurve : OnCurve ⟨kx, ky⟩ :=
            (equation_iff_onCurve ⟨kx, ky⟩).mp
              ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mpr kValid)
          exact mul_ne_zero two_ne_zero_base (JacobianMixed.noAffineYZero ⟨kx, ky⟩ onCurve)
      · rw [if_neg sameX]
        exact sub_ne_zero.mpr sameX

/-- **A true row is `realRowOf`.** For a valid input `P`, the construction's row of an output key
(`FieldMacToECMac.evaluateRow` of `Coordinates.rows`) is `realRowOf (digit • P) K ρ`. -/
theorem trueRow_eq (key : FieldMacToECMac.OutputKey) (rho : NonZeroBase) (input : AffineInput)
    (point : Point) (decoded : decodePoint input = some point) :
    FieldMacToECMac.evaluateRow
        (Coordinates.rows key.offset.coordinates (digitEndomorphismBase key.digit) rho.value) input
      = realRowOf (digitScalar key.digit • point) key.offset.point rho.value := by
  have inputOnCurve : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
  have pointEq := JacobianMixed.affinePoint_eq_of_decode input point decoded inputOnCurve
  have offsetEq := JacobianMixed.affineOffsetPoint_eq key.offset
  cases selected : digitEndomorphismBase key.digit with
  | none =>
    have digitZero : key.digit = .zero := by
      cases digitCase : key.digit
      case zero => rfl
      all_goals rw [digitCase] at selected; simp [digitEndomorphismBase] at selected
    rw [realRow_digitZero key.offset.coordinates key.offset.onCurve input rho.value, digitZero]
    have zeroSmul : (0 : ScalarField) • point = 0 := Module.zero_smul point
    simp only [digitScalar]
    rw [zeroSmul, offsetEq]
    unfold realRowOf
    rw [if_neg (by
      intro same
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ same.symm), zero_add]
    simp [JacobianMixed.affinePoint, pointMultiplier]
  | some phi =>
    have phiSix : phi ^ 6 = 1 := digitEndomorphismBasePowSix key.digit phi selected
    have tOnCurve : OnCurve (FieldMacToECMac.transformedInput phi input) := by
      simpa [FieldMacToECMac.transformedInput] using
        Coordinates.transformedOnCurve phi phiSix input inputOnCurve
    have digitPoint :
        JacobianMixed.affinePoint (FieldMacToECMac.transformedInput phi input) tOnCurve =
          digitScalar key.digit • point := by
      rw [JacobianMixed.transformedInputPoint_eq_digitEndomorphism key.digit phi selected input
        point decoded tOnCurve, digitEndomorphismAction]
    rw [FieldMacToECMac.evaluateRowsSome, ← digitPoint, offsetEq]
    generalize FieldMacToECMac.transformedInput phi input = t at tOnCurve ⊢
    unfold realRowOf
    by_cases xEq : t.x = key.offset.coordinates.x
    · have squares : t.y ^ 2 = key.offset.coordinates.y ^ 2 := by
        have transformedEquation := tOnCurve
        have offsetEquation := key.offset.onCurve
        simp only [OnCurve] at transformedEquation offsetEquation
        rw [xEq] at transformedEquation
        linear_combination transformedEquation - offsetEquation
      have product : (t.y - key.offset.coordinates.y) * (t.y + key.offset.coordinates.y) = 0 := by
        linear_combination squares
      rcases mul_eq_zero.mp product with equalY | oppositeY
      · have sameY : t.y = key.offset.coordinates.y := sub_eq_zero.mp equalY
        rw [realRow_double key.offset.coordinates t key.offset.onCurve tOnCurve xEq sameY,
          if_pos (by
            simp only [JacobianMixed.affinePoint, WeierstrassCurve.Affine.Point.some.injEq]
            exact ⟨xEq, sameY⟩)]
      · have negativeY : t.y = -key.offset.coordinates.y := eq_neg_of_add_eq_zero_left oppositeY
        have yNe : key.offset.coordinates.y ≠ 0 :=
          JacobianMixed.noAffineYZero _ key.offset.onCurve
        have differentY : t.y ≠ key.offset.coordinates.y := by
          rw [negativeY]
          intro same
          have : (2 : BaseField) * key.offset.coordinates.y = 0 := by linear_combination -same
          exact mul_ne_zero two_ne_zero_base yNe this
        rw [realRow_neg key.offset.coordinates t key.offset.onCurve tOnCurve xEq negativeY,
          if_neg (by
            simp only [JacobianMixed.affinePoint, WeierstrassCurve.Affine.Point.some.injEq,
              not_and]
            exact fun _ => differentY)]
        have sum : JacobianMixed.affinePoint t tOnCurve
            + JacobianMixed.affinePoint key.offset.coordinates key.offset.onCurve = 0 := by
          have negated : JacobianMixed.affinePoint t tOnCurve
              = -JacobianMixed.affinePoint key.offset.coordinates key.offset.onCurve := by
            simp only [JacobianMixed.affinePoint, WeierstrassCurve.Affine.Point.neg_some,
              WeierstrassCurve.Affine.Point.some.injEq, WeierstrassCurve.Affine.negY]
            refine ⟨xEq, ?_⟩
            rw [negativeY]
            simp [curve]
          rw [negated, neg_add_cancel]
        rw [sum]
        simp only [JacobianMixed.affinePoint, pointMultiplier, if_pos xEq, if_neg differentY]
        congr 1
        ring
    · rw [realRow_xNe key.offset.coordinates t key.offset.onCurve tOnCurve xEq rho.value
        rho.nonzero, if_neg (by
          simp only [JacobianMixed.affinePoint, WeierstrassCurve.Affine.Point.some.injEq,
            not_and]
          exact fun same => absurd same xEq)]
      simp only [JacobianMixed.affinePoint, pointMultiplier, if_neg xEq]

end Rows

/-! ## §3. The coins' law of the offsets' tail and the row randomisers -/

/-- Points are finite data. -/
instance pointFinite [FieldCertificate] : Finite Point :=
  Finite.of_injective (fun point : Point => match point with
      | .zero => (none : Option (BaseField × BaseField))
      | .some x y _ => some (x, y)) (by
    intro first second same
    cases first <;> cases second <;> simp_all)

/-- The finite instance of the points used throughout (any two are equal). -/
noncomputable instance pointFintype [FieldCertificate] : Fintype Point := Fintype.ofFinite _

section Law

variable [FieldCertificate] [GroupCertificate]

/-- A clamped family is clamped at every certificate instance (the certificates are `Prop`s). -/
theorem clamped_all {field₀ : FieldCertificate} {group₀ : @GroupCertificate field₀}
    (offsets : FieldMacToECMac.SuccessfulOffsets)
    (clamped : @FieldMacToECMac.SuccessfulOffsets.IsClamped field₀ group₀ offsets) :
    ∀ [field : FieldCertificate] [group : @GroupCertificate field], offsets.IsClamped := by
  intro field group
  obtain rfl : field = field₀ := Subsingleton.elim _ _
  obtain rfl : group = group₀ := Subsingleton.elim _ _
  exact clamped

/-- An affine offset is never the identity. -/
theorem offset_point_ne_zero (offset : FieldMacToECMac.AffineOffset) : offset.point ≠ 0 := by
  rw [JacobianMixed.affineOffsetPoint_eq]
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- The affine offset of a non-identity point. -/
def offsetOfPoint : (point : Point) → point ≠ 0 → FieldMacToECMac.AffineOffset
  | .zero, nonzero => absurd rfl nonzero
  | .some x y valid, _ => ⟨⟨x, y⟩, (equation_iff_onCurve ⟨x, y⟩).mp
      ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mpr valid)⟩

theorem offsetOfPoint_point (point : Point) (nonzero : point ≠ 0) :
    (offsetOfPoint point nonzero).point = point := by
  cases point with
  | zero => exact absurd rfl nonzero
  | some x y valid =>
    rw [JacobianMixed.affineOffsetPoint_eq]
    rfl

theorem offsetOfPoint_congr {first second : Point} (same : first = second) (firstNonzero : first ≠ 0)
    (secondNonzero : second ≠ 0) :
    offsetOfPoint first firstNonzero = offsetOfPoint second secondNonzero := by
  subst same
  rfl

theorem offsetOfPoint_offset (offset : FieldMacToECMac.AffineOffset) :
    offsetOfPoint offset.point (offset_point_ne_zero offset) = offset := by
  obtain ⟨coordinates, onCurve⟩ := offset
  rw [offsetOfPoint_congr (JacobianMixed.affineOffsetPoint_eq ⟨coordinates, onCurve⟩) _
    (WeierstrassCurve.Affine.Point.some_ne_zero _)]
  rfl

/-- The points of the free offsets. -/
def tailPoints (offsets : FieldMacToECMac.SuccessfulOffsets) : Fin 90 → Point :=
  fun index => (offsets.free.get index).point

theorem freeOffsetPoints_eq (free : Vector FieldMacToECMac.AffineOffset 90) :
    FieldMacToECMac.freeOffsetPoints free = List.ofFn fun index => (free.get index).point := by
  unfold FieldMacToECMac.freeOffsetPoints
  apply List.ext_getElem
  · simp only [List.length_map, Vector.length_toList, List.length_ofFn]
  · intro index first second
    rw [List.getElem_map, List.getElem_ofFn, Vector.getElem_toList]
    rfl

/-- `radix • pointHorner radix (points of free)` is `radixMap (horner (tailPoints))`. -/
theorem clampedFirst_eq (offsets : FieldMacToECMac.SuccessfulOffsets) :
    FieldMacToECMac.clampedFirst offsets.free
      = -radixMap (horner radixMap 90 (tailPoints offsets)) := by
  rw [FieldMacToECMac.clampedFirst, freeOffsetPoints_eq, pointHorner_ofFn]
  rfl

/-- A clamped offset family has a good tail. -/
theorem goodTail_tailPoints (offsets : FieldMacToECMac.SuccessfulOffsets)
    (clamped : offsets.IsClamped) : GoodTail radixMap (tailPoints offsets) := by
  refine ⟨fun index => offset_point_ne_zero _, fun zero => ?_⟩
  have first := offset_point_ne_zero offsets.first
  rw [clamped, clampedFirst_eq, zero, neg_zero] at first
  exact first rfl

/-- The offsets of a good tail: the free offsets are its points, the first is the clamp. -/
def offsetsOfTail (tail : Fin 90 → Point) (good : GoodTail radixMap tail) :
    FieldMacToECMac.SuccessfulOffsets where
  first := offsetOfPoint (-radixMap (horner radixMap 90 tail)) (neg_ne_zero.mpr good.2)
  free := Vector.ofFn fun index => offsetOfPoint (tail index) (good.1 index)

theorem tailPoints_offsetsOfTail (tail : Fin 90 → Point) (good : GoodTail radixMap tail) :
    tailPoints (offsetsOfTail tail good) = tail := by
  funext index
  simp [tailPoints, offsetsOfTail, offsetOfPoint_point]

theorem offsetsOfTail_clamped (tail : Fin 90 → Point) (good : GoodTail radixMap tail) :
    (offsetsOfTail tail good).IsClamped := by
  unfold FieldMacToECMac.SuccessfulOffsets.IsClamped
  rw [clampedFirst_eq, tailPoints_offsetsOfTail]
  exact offsetOfPoint_point _ _

theorem offsetsOfTail_tailPoints (offsets : FieldMacToECMac.SuccessfulOffsets)
    (clamped : offsets.IsClamped) :
    offsetsOfTail (tailPoints offsets) (goodTail_tailPoints offsets clamped) = offsets := by
  obtain ⟨first, free⟩ := offsets
  have headSame : -radixMap (horner radixMap 90 (tailPoints ⟨first, free⟩)) = first.point := by
    rw [← clampedFirst_eq]
    exact clamped.symm
  simp only [offsetsOfTail, FieldMacToECMac.SuccessfulOffsets.mk.injEq]
  constructor
  · rw [offsetOfPoint_congr headSame _ (offset_point_ne_zero first), offsetOfPoint_offset]
  · apply Vector.ext
    intro index bound
    simp only [Vector.getElem_ofFn]
    exact offsetOfPoint_offset (free.get ⟨index, bound⟩)

/-- The offset of every digit is the construction's clamp of the tail. -/
theorem values_point (offsets : FieldMacToECMac.SuccessfulOffsets) (clamped : offsets.IsClamped)
    (digit : Fin FieldMacToECMac.outputMacCount) :
    (offsets.values.get digit).point = clampOffsets radixMap (tailPoints offsets) digit := by
  refine Fin.cases ?_ (fun place => ?_) digit
  · show offsets.first.point = _
    rw [clamped, clampedFirst_eq]
    rfl
  · show (offsets.free.get place).point = _
    rfl

/-- The row randomisers of a row randomness vector. -/
def rhoOf (randomness : FieldMacToECMac.Randomness) : Fin FieldMacToECMac.outputMacCount → NonZeroBase :=
  fun digit => (randomness.get digit).rho

/-- Replace the row randomisers. -/
def setRho (randomness : FieldMacToECMac.Randomness) (rho : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    FieldMacToECMac.Randomness :=
  Vector.ofFn fun digit => { randomness.get digit with rho := rho digit }

theorem rhoOf_setRho (randomness : FieldMacToECMac.Randomness)
    (rho : Fin FieldMacToECMac.outputMacCount → NonZeroBase) : rhoOf (setRho randomness rho) = rho := by
  funext digit
  unfold rhoOf setRho
  rw [Vector.get_ofFn]

theorem setRho_rhoOf (randomness : FieldMacToECMac.Randomness)
    (rho : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    setRho (setRho randomness rho) (rhoOf randomness) = randomness := by
  apply Vector.ext
  intro index bound
  unfold setRho rhoOf
  rw [Vector.getElem_ofFn, Vector.get_ofFn]
  rfl

/-- The good tails. -/
abbrev GoodTails := {tail : Fin 90 → Point // GoodTail radixMap tail}

/-- The coins' offset tail and row randomisers. -/
def tailRho (coins : Coins) : GoodTails × (Fin FieldMacToECMac.outputMacCount → NonZeroBase) :=
  (⟨tailPoints coins.offsets, goodTail_tailPoints coins.offsets coins.offsetsClamped⟩,
    rhoOf coins.pointRandomness)

/-- Move a coin to another fibre of `tailRho`. -/
def moveCoins (target : GoodTails × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)) (coins : Coins) : Coins :=
  { coins with
    offsets := offsetsOfTail target.1.1 target.1.2
    offsetsClamped := clamped_all _ (offsetsOfTail_clamped target.1.1 target.1.2)
    pointRandomness := setRho coins.pointRandomness target.2 }

theorem moveCoins_offsets (target : GoodTails × (Fin FieldMacToECMac.outputMacCount → NonZeroBase))
    (coins : Coins) : (moveCoins target coins).offsets = offsetsOfTail target.1.1 target.1.2 := rfl

theorem moveCoins_pointRandomness
    (target : GoodTails × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)) (coins : Coins) :
    (moveCoins target coins).pointRandomness = setRho coins.pointRandomness target.2 := rfl

theorem tailRho_moveCoins (target : GoodTails × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)) (coins : Coins) :
    tailRho (moveCoins target coins) = target := by
  obtain ⟨⟨tail, good⟩, rho⟩ := target
  have first : tailPoints (moveCoins ⟨⟨tail, good⟩, rho⟩ coins).offsets = tail := by
    rw [moveCoins_offsets]
    exact tailPoints_offsetsOfTail tail good
  have second : rhoOf (moveCoins ⟨⟨tail, good⟩, rho⟩ coins).pointRandomness = rho := by
    rw [moveCoins_pointRandomness]
    exact rhoOf_setRho _ _
  rw [tailRho, Prod.mk.injEq, Subtype.mk.injEq]
  exact ⟨first, second⟩

theorem moveCoins_moveCoins (target : GoodTails × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)) (coins : Coins)
    (inFibre : tailRho coins = target) (other : GoodTails × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)) :
    moveCoins target (moveCoins other coins) = coins := by
  subst inFibre
  apply Scheme.Coins.data_injective
  have offsetsSame : (moveCoins (tailRho coins) (moveCoins other coins)).offsets
      = coins.offsets := by
    rw [moveCoins_offsets]
    exact offsetsOfTail_tailPoints coins.offsets coins.offsetsClamped
  have rhoSame : (moveCoins (tailRho coins) (moveCoins other coins)).pointRandomness
      = coins.pointRandomness := by
    rw [moveCoins_pointRandomness, moveCoins_pointRandomness]
    exact setRho_rhoOf _ _
  rw [Scheme.Coins.data, Scheme.Coins.data, offsetsSame, rhoSame]
  rfl

instance goodTailsNonempty : Nonempty GoodTails :=
  ⟨⟨tailPoints Scheme.witness.offsets,
    goodTail_tailPoints _ Scheme.witness.offsetsClamped⟩⟩

noncomputable instance goodTailsFintype : Fintype GoodTails := Fintype.ofFinite _

instance coinsNonempty' : Nonempty Coins := ⟨Scheme.witness⟩

/-- **The coins' law of (offset tail, row randomisers)**: uniform good tails, independent uniform
randomisers. -/
theorem tailRho_law :
    letI : Fintype Coins := Fintype.ofFinite Coins
    (PMF.uniformOfFintype Coins).map tailRho
      = productPMF (PMF.uniformOfFintype GoodTails)
          (PMF.uniformOfFintype (Fin FieldMacToECMac.outputMacCount → NonZeroBase)) := by
  letI : Fintype Coins := Fintype.ofFinite Coins
  classical
  rw [← uniformOfFintype_productPMF]
  refine uniform_map_of_fibre_equiv tailRho fun first second =>
    { toFun := fun coins => ⟨moveCoins second coins.1, tailRho_moveCoins second coins.1⟩
      invFun := fun coins => ⟨moveCoins first coins.1, tailRho_moveCoins first coins.1⟩
      left_inv := fun coins => Subtype.ext (moveCoins_moveCoins first coins.1 coins.2 second)
      right_inv := fun coins => Subtype.ext (moveCoins_moveCoins second coins.1 coins.2 first) }

end Law

/-! ## §4. The rows kernels are within `364 / #Point` -/

/-- Two kernels behind one law differ by at most the mass where they differ. -/
theorem etvDist_bind_le_differ {α β : Type} (p : PMF α) (f g : α → PMF β) :
    (p.bind f).etvDist (p.bind g) ≤ p.toOuterMeasure {a | f a ≠ g a} := by
  classical
  refine le_trans (etvDist_bind_left_le p f g) ?_
  rw [PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases same : f a = g a
  · rw [same, PMF.etvDist_self, zero_mul]
    exact zero_le
  · rw [Set.indicator_of_mem (show a ∈ {a | f a ≠ g a} from same)]
    calc (f a).etvDist (g a) * p a ≤ 1 * p a := by gcongr; exact PMF.etvDist_le_one _ _
      _ = p a := one_mul _

/-- The uniform law does not depend on the finite instance. -/
theorem uniform_instance {α : Type} (first second : Fintype α) [Nonempty α] :
    @PMF.uniformOfFintype α first _ = @PMF.uniformOfFintype α second _ := by
  congr 1
  exact Subsingleton.elim _ _

section Kernel

variable [FieldCertificate] [GroupCertificate]

/-- The two non-zero types of the base field. -/
def nonZeroEquiv : NonZeroBase ≃ NonZeroField where
  toFun value := ⟨value.value, value.nonzero⟩
  invFun value := ⟨value.1, value.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The digits of a scalar, as a vector. -/
def digitsOf (scalar : NonZeroScalar) : Vector Digit FieldMacToECMac.outputMacCount :=
  ⟨(construction.digits scalar.value).toArray,
    by simpa [FieldMacToECMac.outputMacCount] using construction.digitCount scalar.value⟩

/-- The digit multiples `T_d = digit_d • P` of an input point. -/
def multiplesOf (scalar : NonZeroScalar) (point : Point) : Fin 91 → Point :=
  fun digit => digitScalar ((digitsOf scalar).get digit) • point

/-- Horner of scalar multiples of one point. -/
theorem pointHorner_map_smul (point : Point) (digits : List Digit) :
    pointHorner radix (digits.map fun digit => digitScalar digit • point)
      = scalarHorner radix (digits.map digitScalar) • point := by
  induction digits with
  | nil => exact (Module.zero_smul point).symm
  | cons digit rest ih =>
    simp only [List.map_cons, pointHorner, scalarHorner, ih, add_smul, mul_smul]

/-- **The digit multiples recompose the output**: `H(T) = k • P`. -/
theorem horner_multiplesOf (scalar : NonZeroScalar) (point : Point) :
    horner radixMap 91 (multiplesOf scalar point) = scalar.value • point := by
  rw [show radixMap = DistribSMul.toAddMonoidHom Point radix from rfl, ← pointHorner_ofFn]
  have listEq : List.ofFn (multiplesOf scalar point)
      = (construction.digits scalar.value).map fun digit => digitScalar digit • point := by
    apply List.ext_getElem
    · simp [construction.digitCount scalar.value]
    · intro index first second
      rw [List.getElem_ofFn, List.getElem_map]
      rfl
  rw [listEq, pointHorner_map_smul, construction.scalarReconstruction]

/-- The output keys' digits are the scalar's digits. -/
theorem outputKeys_get (scalar : NonZeroScalar) (offsets : FieldMacToECMac.SuccessfulOffsets)
    (digit : Fin FieldMacToECMac.outputMacCount) :
    (FieldMacToECMac.outputKeys construction scalar.value offsets).get digit
      = { digit := (digitsOf scalar).get digit, offset := offsets.values.get digit } := by
  simp [FieldMacToECMac.outputKeys, digitsOf, Vector.get_ofFn]

/-- The real rows of a (tail, randomisers) pair. -/
def realRowsOf (multiples : Fin 91 → Point) (sample : GoodTails × (Fin 91 → NonZeroBase)) :
    Fin 91 → FieldMacToECMac.HomogeneousValue :=
  fun digit => realRowOf (multiples digit) (clampOffsets radixMap sample.1.1 digit)
    (sample.2 digit).value

/-- The true rows of one garbling are `realRowsOf` its (tail, randomisers). -/
theorem trueRows_eq (scalar : NonZeroScalar) (coins : Coins) (input : AffineInput)
    (point : Point) (decoded : decodePoint input = some point) :
    trueRows scalar coins input = realRowsOf (multiplesOf scalar point) (tailRho coins) := by
  funext digit
  unfold trueRows realRowsOf
  rw [FieldMacToECMac.rowsForOutputKeys, Vector.get_ofFn, outputKeys_get,
    trueRow_eq _ _ input point decoded, values_point _ coins.offsetsClamped]
  rfl

/-- The multiplier with the doubling case set to `1`. -/
def safeMultiplier (multiples : Fin 91 → Point) (tail : Fin 90 → Point) (digit : Fin 91) :
    BaseField :=
  if multiples digit = clampOffsets radixMap tail digit then 1
  else pointMultiplier (multiples digit) (clampOffsets radixMap tail digit)

theorem safeMultiplier_ne_zero (multiples : Fin 91 → Point) (tail : Fin 90 → Point)
    (digit : Fin 91) : safeMultiplier multiples tail digit ≠ 0 := by
  unfold safeMultiplier
  split_ifs with same
  · exact one_ne_zero
  · exact pointMultiplier_ne_zero _ _ same

/-- The real rows with the doubling rows replaced by lifts. -/
def liftedRowsOf (multiples : Fin 91 → Point) (sample : GoodTails × (Fin 91 → NonZeroBase)) :
    Fin 91 → FieldMacToECMac.HomogeneousValue :=
  fun digit => lift (realPoints radixMap multiples sample.1.1 digit)
    ((sample.2 digit).value * safeMultiplier multiples sample.1.1 digit)

theorem realRowsOf_eq_lifted (multiples : Fin 91 → Point) (tail : GoodTails)
    (noDouble : ∀ digit, multiples digit ≠ clampOffsets radixMap tail.1 digit)
    (rho : Fin 91 → NonZeroBase) :
    realRowsOf multiples (tail, rho) = liftedRowsOf multiples (tail, rho) := by
  funext digit
  simp only [realRowsOf, liftedRowsOf, realRowOf, safeMultiplier, if_neg (noDouble digit)]
  rfl

/-- The uniform randomisers, lifted at any non-zero multipliers, are uniform lifts. -/
theorem lifts_law' (points : Fin 91 → Point) (multiplier : Fin 91 → BaseField)
    (nonzero : ∀ digit, multiplier digit ≠ 0) :
    (PMF.uniformOfFintype (Fin 91 → NonZeroBase)).map
        (fun rho digit => lift (points digit) ((rho digit).value * multiplier digit))
      = (PMF.uniformOfFintype (Fin 91 → NonZeroBase)).map
        (fun rho digit => lift (points digit) (rho digit).value) := by
  have transport : ∀ (F : (Fin 91 → NonZeroField) → Fin 91 → FieldMacToECMac.HomogeneousValue),
      (PMF.uniformOfFintype (Fin 91 → NonZeroBase)).map
          (fun rho => F (fun digit => nonZeroEquiv (rho digit)))
        = (PMF.uniformOfFintype (Fin 91 → NonZeroField)).map F := by
    intro F
    have equiv := Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv
      (Equiv.piCongrRight fun _ : Fin 91 => nonZeroEquiv)
    rw [← equiv, PMF.map_comp]
    rfl
  have first := transport fun rho digit => lift (points digit) ((rho digit).1 * multiplier digit)
  have second := transport fun rho digit => lift (points digit) (rho digit).1
  simp only [nonZeroEquiv, Equiv.coe_fn_mk] at first second
  rw [first, second]
  exact lifts_law points multiplier nonzero

end Kernel

section KernelLaw

variable [FieldCertificate] [GroupCertificate]

/-- The simulator's rows of a (tail, lifts) pair. -/
def simRowsOf (target : Point) (sample : GoodTails × (Fin 91 → NonZeroBase)) :
    Fin 91 → FieldMacToECMac.HomogeneousValue :=
  fun digit => lift (clampPoints radixMap target sample.1.1 digit) (sample.2 digit).value

/-- The glue's lift is P1's. -/
theorem liftRow_eq_lift (point : Point) (scale : BaseField) :
    Kriterion.ArgoMAC.Phase3.Glue.liftRow point scale = lift point scale := by
  cases point <;> rfl

/-- The glue's digit points are P1's clamp of the offsets' tail to the target. -/
theorem digitPoints_eq (target : Point) (offsets : FieldMacToECMac.SuccessfulOffsets)
    (digit : Fin 91) :
    Kriterion.ArgoMAC.Phase3.Glue.digitPoints target offsets.free digit
      = clampPoints radixMap target (tailPoints offsets) digit := by
  obtain ⟨index, bound⟩ := digit
  cases index with
  | zero =>
    show target - radix • pointHorner radix (FieldMacToECMac.freeOffsetPoints offsets.free)
      = target - radixMap (horner radixMap 90 (tailPoints offsets))
    rw [freeOffsetPoints_eq, pointHorner_ofFn]
    rfl
  | succ index =>
    show (offsets.free.get ⟨index, _⟩).point = clampPoints radixMap target (tailPoints offsets)
      (Fin.succ ⟨index, by omega⟩)
    rw [clampPoints, Fin.cons_succ]
    rfl

/-- `(p ⊗ q).map fst = p`. -/
theorem productPMF_map_fst {A C : Type} (first : PMF A) (second : PMF C) :
    (productPMF first second).map Prod.fst = first := by
  rw [productPMF, PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure first]
  congr 1
  funext value
  rw [PMF.map_comp]
  exact PMF.map_const _ _

/-- **The real rows' law**: the product of uniform good tails and uniform randomisers, through
`realRowsOf` (stated at `Fin 91`, which the glue spells `Fin digitCount`). -/
theorem realRows_law (scalar : NonZeroScalar) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) (target : Point) :
    @Eq (PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue))) (realRows scalar input target)
      ((productPMF (PMF.uniformOfFintype GoodTails)
          (PMF.uniformOfFintype (Fin 91 → NonZeroBase))).map
        fun sample => some (realRowsOf (multiplesOf scalar point) sample)) := by
  letI : Fintype Coins := Fintype.ofFinite Coins
  have factor : (fun coins : Coins => (some fun (digit : Fin 91) =>
        trueRows scalar coins input digit : Option (Fin 91 → FieldMacToECMac.HomogeneousValue)))
      = (fun sample => some (realRowsOf (multiplesOf scalar point) sample)) ∘ tailRho := by
    funext coins
    exact congrArg some (trueRows_eq scalar coins input point decoded)
  show ((PMF.uniformOfFintype Coins).map (fun coins : Coins => (some fun (digit : Fin 91) =>
        trueRows scalar coins input digit : Option (Fin 91 → FieldMacToECMac.HomogeneousValue))) :
      PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue))) = _
  rw [factor, ← PMF.map_comp, tailRho_law]

/-- **The simulator's rows' law**: the same product, through `simRowsOf`. -/
theorem simulatedRows_law (input : AffineInput) (target : Point) :
    @Eq (PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue))) (simulatedRows input target)
      ((productPMF (PMF.uniformOfFintype GoodTails)
          (PMF.uniformOfFintype (Fin 91 → NonZeroBase))).map
        fun sample => some (simRowsOf target sample)) := by
  letI : Fintype Coins := Fintype.ofFinite Coins
  have tails : (PMF.uniformOfFintype Coins).map (fun coins => (tailRho coins).1)
      = PMF.uniformOfFintype GoodTails := by
    have := congrArg (PMF.map Prod.fst) tailRho_law
    rw [PMF.map_comp, productPMF_map_fst] at this
    exact this
  have step : simulatedRows input target
      = ((PMF.uniformOfFintype Coins).bind fun coins =>
          (PMF.uniformOfFintype (Fin 91 → NonZeroBase)).map fun lift =>
            some fun (digit : Fin 91) => Kriterion.ArgoMAC.Phase3.Glue.liftRow
              (Kriterion.ArgoMAC.Phase3.Glue.digitPoints target coins.offsets.free digit)
              (lift digit).value :
          PMF (Option (Fin 91 → FieldMacToECMac.HomogeneousValue))) := by
    unfold simulatedRows idealSamplers Kriterion.ArgoMAC.Phase3.Glue.coinOffsetsLaw
    simp only [PMF.bind_map, Function.comp_def, PMF.map_bind]
    simp only [PMF.bind_map, Function.comp_def, ← PMF.bind_pure_comp]
    rfl
  simp only [liftRow_eq_lift, digitPoints_eq] at step
  rw [step, productPMF, PMF.map_bind, ← tails, PMF.bind_map]
  congr 1
  funext coins
  simp only [Function.comp_apply, PMF.map_comp]
  rfl

end KernelLaw

section KernelBound

variable [FieldCertificate] [GroupCertificate]

theorem noHitNonempty (multiples : Fin 91 → Point) (output : Point)
    (hits : horner radixMap 91 multiples = output) :
    Nonempty {tail : Fin 90 → Point // NoHit radixMap output multiples tail} := by
  obtain ⟨tail, good⟩ := (inferInstance : Nonempty GoodTails)
  exact ⟨⟨Fin.tail multiples + tail, (goodTail_iff_noHit radixMap multiples output hits tail).mp good⟩⟩

/-- **The doubling tails have mass `≤ 182 / #Point`** under the construction's offset law. -/
theorem doubling_mass_le (multiples : Fin 91 → Point) (output : Point)
    (hits : horner radixMap 91 multiples = output) :
    (PMF.uniformOfFintype GoodTails).toOuterMeasure
        {tail | ∃ digit, multiples digit = clampOffsets radixMap tail.1 digit}
      ≤ 182 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  classical
  haveI := noHitNonempty multiples output hits
  have preimage : {tail : GoodTails | ∃ digit, multiples digit = clampOffsets radixMap tail.1 digit}
      = (fun tail : GoodTails => realPoints radixMap multiples tail.1) ⁻¹'
        {points | ∃ digit, points digit = multiples digit + multiples digit} := by
    ext tail
    simp only [Set.mem_setOf_eq, Set.mem_preimage, realPoints, Pi.add_apply, add_right_inj]
    exact exists_congr fun digit => eq_comm
  rw [preimage, ← PMF.toOuterMeasure_map_apply,
    uniform_instance goodTailsFintype (Subtype.fintype _)]
  exact bn254_doubling_real_le multiples output hits

/-- The uniform tails miss the good tails with mass `≤ 91 / #Point`. -/
theorem notGood_mass_le :
    (PMF.uniformOfFintype (Fin 90 → Point)).toOuterMeasure {tail | ¬ GoodTail radixMap tail}
      ≤ 91 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  classical
  have same : {tail : Fin 90 → Point | ¬ GoodTail radixMap tail}
      = {tail | ∃ digit, clampPoints radixMap 0 tail digit = (fun _ : Fin 91 => (0 : Point)) digit} := by
    ext tail
    simp only [Set.mem_setOf_eq, GoodTail, not_and_or, not_forall, not_not]
    constructor
    · rintro (⟨index, zero⟩ | zero)
      · exact ⟨index.succ, by simp [clampPoints, zero]⟩
      · exact ⟨0, by simp [clampPoints, zero]⟩
    · rintro ⟨digit, zero⟩
      refine Fin.cases (fun zero => Or.inr ?_) (fun index zero => Or.inl ⟨index, ?_⟩) digit zero
      · simpa [clampPoints] using zero
      · simpa [clampPoints] using zero
  rw [same]
  have := clamp_anyHit_le (n := 89) radixMap radixMap_injective 0 (fun _ => 0)
  simpa using this

/-- **The two point laws are within `182 / #Point`**: the real points against the uniform-tail
clamp (P1's `bn254_digitPoints_good_etvDist_le`), and the uniform-tail clamp against the good-tail
clamp (the good-tail restriction). -/
theorem points_etvDist_le (multiples : Fin 91 → Point) (output : Point)
    (hits : horner radixMap 91 multiples = output) :
    ((PMF.uniformOfFintype GoodTails).map fun tail => realPoints radixMap multiples tail.1).etvDist
      ((PMF.uniformOfFintype GoodTails).map fun tail => clampPoints radixMap output tail.1)
      ≤ 182 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  classical
  haveI := noHitNonempty multiples output hits
  refine le_trans (PMF.etvDist_triangle _
    ((PMF.uniformOfFintype (Fin 90 → Point)).map (clampPoints radixMap output)) _) ?_
  have first : ((PMF.uniformOfFintype GoodTails).map
        fun tail => realPoints radixMap multiples tail.1).etvDist
      ((PMF.uniformOfFintype (Fin 90 → Point)).map (clampPoints radixMap output))
      ≤ 91 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
    rw [uniform_instance goodTailsFintype (Subtype.fintype _)]
    exact bn254_digitPoints_good_etvDist_le multiples output hits
  have second : ((PMF.uniformOfFintype (Fin 90 → Point)).map (clampPoints radixMap output)).etvDist
      ((PMF.uniformOfFintype GoodTails).map fun tail => clampPoints radixMap output tail.1)
      ≤ 91 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
    rw [PMF.etvDist_comm]
    have factor : (fun tail : GoodTails => clampPoints radixMap output tail.1)
        = clampPoints radixMap output ∘ Subtype.val := rfl
    rw [factor, ← PMF.map_comp]
    refine le_trans (etvDist_map_le' _ _ _) ?_
    rw [uniform_instance goodTailsFintype (Subtype.fintype _)]
    exact le_trans (etvDist_uniform_subtype_le _) notGood_mass_le
  calc _ ≤ 91 * (Fintype.card Point : ℝ≥0∞)⁻¹ + 91 * (Fintype.card Point : ℝ≥0∞)⁻¹ :=
        add_le_add first second
    _ = 182 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by rw [← add_mul]; norm_num

/-- **The rows kernels are within `364 / #Point`** at a valid input and its output. -/
theorem rows_etvDist_le (scalar : NonZeroScalar) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    @PMF.etvDist (Option (Fin 91 → FieldMacToECMac.HomogeneousValue))
        (realRows scalar input (scalar.value • point)) (simulatedRows input (scalar.value • point))
      ≤ 364 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
  classical
  set multiples := multiplesOf scalar point
  have hits := horner_multiplesOf scalar point
  rw [realRows_law scalar input point decoded, simulatedRows_law]
  set tails := PMF.uniformOfFintype GoodTails
  set rhos := PMF.uniformOfFintype (Fin 91 → NonZeroBase)
  -- the lifted rows, doubling replaced by a lift
  refine le_trans (PMF.etvDist_triangle _
    ((productPMF tails rhos).map fun sample => some (liftedRowsOf multiples sample)) _) ?_
  have doubling : ((productPMF tails rhos).map
        fun sample => some (realRowsOf multiples sample)).etvDist
      ((productPMF tails rhos).map fun sample => some (liftedRowsOf multiples sample))
      ≤ 182 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
    simp only [productPMF, PMF.map_bind, PMF.map_comp]
    refine le_trans (etvDist_bind_le_differ _ _ _) ?_
    refine le_trans (PMF.toOuterMeasure_mono _ ?_) (doubling_mass_le multiples _ hits)
    intro tail member
    by_contra noDouble
    apply member.1
    congr 1
    funext rho
    simp only [Function.comp_apply]
    rw [realRowsOf_eq_lifted multiples tail (fun digit same => noDouble ⟨digit, same⟩) rho]
  have lifted : ((productPMF tails rhos).map
        fun sample => some (liftedRowsOf multiples sample))
      = ((tails.map fun tail => realPoints radixMap multiples tail.1).bind fun points =>
          rhos.map fun rho => some fun digit => lift (points digit) (rho digit).value) := by
    simp only [productPMF, PMF.map_bind, PMF.map_comp, PMF.bind_map]
    congr 1
    funext tail
    have law := lifts_law' (realPoints radixMap multiples tail.1)
      (safeMultiplier multiples tail.1) (safeMultiplier_ne_zero multiples tail.1)
    have mapped := congrArg (PMF.map some) law
    simp only [PMF.map_comp] at mapped
    exact mapped
  have simulated : ((productPMF tails rhos).map fun sample => some (simRowsOf (scalar.value • point)
        sample))
      = ((tails.map fun tail => clampPoints radixMap (scalar.value • point) tail.1).bind
          fun points => rhos.map fun rho => some fun digit => lift (points digit) (rho digit).value) := by
    simp only [productPMF, PMF.map_bind, PMF.map_comp, PMF.bind_map]
    rfl
  have kernel : ((productPMF tails rhos).map
        fun sample => some (liftedRowsOf multiples sample)).etvDist
      ((productPMF tails rhos).map fun sample => some (simRowsOf (scalar.value • point) sample))
      ≤ 182 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
    rw [lifted, simulated]
    exact le_trans (PMF.etvDist_bind_right_le _ _ _) (points_etvDist_le multiples _ hits)
  calc _ ≤ 182 * (Fintype.card Point : ℝ≥0∞)⁻¹ + 182 * (Fintype.card Point : ℝ≥0∞)⁻¹ :=
        add_le_add doubling kernel
    _ = 364 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by rw [← add_mul]; norm_num

end KernelBound

/-! ## §5. `#Point ≥ r`, from the certificates -/

section Order

variable [FieldCertificate] [GroupCertificate]

/-- The point `(1, 2)`. -/
def basePoint : Point := JacobianMixed.affinePoint ⟨1, 2⟩ generatorOnCurve

theorem basePoint_ne_zero : basePoint ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _

/-- **`#Point ≥ r`**: the multiples of `(1, 2)` are pairwise distinct, because `r` is prime and the
certificate's `r • P = 0` makes the points an `F_r`-module in which `(1, 2) ≠ 0`. No `#Point = r`
fact is used. -/
theorem scalarFieldModulus_le_card_point : scalarFieldModulus ≤ Fintype.card Point := by
  haveI : Fact (Nat.Prime scalarFieldModulus) := ⟨scalarFieldPrime⟩
  have injective : Function.Injective fun scalar : ScalarField => scalar • basePoint := by
    intro first second same
    by_contra different
    have difference : (first - second) • basePoint = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr same
    have scaled := congrArg (fun point : Point => (first - second)⁻¹ • point) difference
    simp only [smul_zero, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr different), one_smul]
      at scaled
    exact basePoint_ne_zero scaled
  have := Fintype.card_le_of_injective _ injective
  simpa [ZMod.card] using this

/-- `364 / #Point ≤ 364 / (r − 1)`: the budget's `outputKernelError`. -/
theorem kernel_le_outputKernelError :
    (364 * (Fintype.card Point : ℝ≥0∞)⁻¹).toReal ≤ Kriterion.ArgoMAC.Phase3.Glue.outputKernelError := by
  have order := scalarFieldModulus_le_card_point
  have large : (1 : ℝ) < scalarFieldModulus := by
    have : 1 < scalarFieldModulus := by unfold scalarFieldModulus; norm_num
    exact_mod_cast this
  have cardReal : (scalarFieldModulus : ℝ) ≤ (Fintype.card Point : ℝ) := by exact_mod_cast order
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Kriterion.ArgoMAC.Phase3.Glue.outputKernelError]
  norm_num
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

end Order

/-! ## §6. `OpeningBound` -/

/-- **`HW → H` at any instances**: the two opened games are within `outputKernelError`. -/
theorem publicFirst_opened_le [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (adversary : PlanBAdversary Unit) (parameter : Nat)
    (scalar : NonZeroScalar) :
    Assumptions.advantage
        (abstractIdealGame Scheme.scheme (openedSimulator (realRows scalar) skipInstallation)
          adversary parameter scalar ())
        (abstractIdealGame Scheme.scheme (openedSimulator simulatedRows skipInstallation)
          adversary parameter scalar ())
      ≤ Kriterion.ArgoMAC.Phase3.Glue.outputKernelError := by
  rw [advantage_eq_etvDist]
  have close : ∀ input target, Scheme.scheme.function scalar input = some target →
      (realRows scalar input target).etvDist (simulatedRows input target)
        ≤ 364 * (Fintype.card Point : ℝ≥0∞)⁻¹ := by
    intro input target output
    change (decodePoint input).map (scalarMultiplication scalar.value) = some target at output
    obtain ⟨point, decoded, rfl⟩ := Option.map_eq_some_iff.mp output
    exact rows_etvDist_le scalar input point decoded
  have finite : (364 * (Fintype.card Point : ℝ≥0∞)⁻¹) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr
      Fintype.card_ne_zero))
  exact le_trans (ENNReal.toReal_mono finite (openedGame_etvDist_le (realRows scalar)
    simulatedRows skipInstallation adversary parameter scalar _ close))
    kernel_le_outputKernelError

/-- **`OpeningBound.kernel`** (P3's field, verbatim): `HW → H` costs `outputKernelError = 364/(r−1)`,
at the `Solution` instances, for every adversary (the `2^100` budget hypothesis is not needed). -/
theorem openingBound_kernel :
    Kriterion.ArgoMAC.Phase3.Glue.HopBound publicFirstHybrid openedHybrid
      fun _ _ => Kriterion.ArgoMAC.Phase3.Glue.outputKernelError := by
  intro field group adversary parameter scalar _
  exact @publicFirst_opened_le field group (Classical.decEq _) (Classical.decEq _) adversary
    parameter scalar

end

end Kriterion.ArgoMAC.Security.Phase3
