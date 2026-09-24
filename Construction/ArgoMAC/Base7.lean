/-
This file defines the optimized BN254 scalar digits.
-/

import Construction.ArgoMAC.Algebra
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace Kriterion.ArgoMAC

/-- `Digit` is the alphabet in `alg:digits`. -/
inductive Digit where
  | zero
  | one
  | negOne
  | omega
  | negOmega
  | omegaSquared
  | negOmegaSquared
deriving DecidableEq

/-- `omega` is the BN254 G1 endomorphism eigenvalue. -/
def omega : BN254.ScalarField :=
  BN254.endomorphismScalar

/-- The scalar root selects the concrete BN254 curve endomorphism. -/
theorem omegaAction [BN254.FieldCertificate] [BN254.GroupCertificate]
    (point : BN254.Point) : BN254.endomorphism point = omega • point := by
  rw [BN254.GroupCertificate.endomorphismAction]
  rfl

/-- The eigenvalue is a cube root of unity. -/
theorem omegaCube : omega ^ 3 = 1 := by
  decide

/-- The eigenvalue is not the identity root. -/
theorem omegaNeOne : omega ≠ 1 := by
  decide

/-- The concrete root satisfies its quadratic equation. -/
theorem omegaQuadratic : omega ^ 2 + omega + 1 = 0 := by
  decide

/-- The quadratic equation rewrites the square of the root. -/
theorem omegaSquared : omega * omega = -omega - 1 := by
  linear_combination omegaQuadratic

/-- `digitScalar` maps each digit to its scalar value. -/
def digitScalar : Digit → BN254.ScalarField
  | .zero => 0
  | .one => 1
  | .negOne => -1
  | .omega => omega
  | .negOmega => -omega
  | .omegaSquared => omega * omega
  | .negOmegaSquared => -(omega * omega)

/-- This is the selected six-cycle generator for BN254 G1. -/
def endomorphismGenerator : BN254.BaseField :=
  -(BN254.endomorphismBase ^ 2)

/-- This is `EndoScalar::endo_base` for the digit order. -/
def digitEndomorphismBase : Digit → Option BN254.BaseField
  | .zero => none
  | .one => some 1
  | .negOmegaSquared => some endomorphismGenerator
  | .omega => some (endomorphismGenerator ^ 2)
  | .negOne => some (endomorphismGenerator ^ 3)
  | .omegaSquared => some (endomorphismGenerator ^ 4)
  | .negOmega => some (endomorphismGenerator ^ 5)

/-- The coordinate map for `omega` is the Arkworks BN254 endomorphism. -/
theorem omegaEndomorphismBase :
    digitEndomorphismBase .omega = some BN254.endomorphismBase := by
  decide

theorem digitEndomorphismBasePowSix (digit : Digit) (phi : BN254.BaseField)
    (selected : digitEndomorphismBase digit = some phi) : phi ^ 6 = 1 := by
  cases digit <;> simp [digitEndomorphismBase] at selected
  all_goals subst phi
  all_goals decide

/-- This is the protocol endomorphism operation. -/
def digitEndomorphism [BN254.FieldCertificate] : Digit → BN254.Point → BN254.Point
  | .zero, _ => 0
  | .one, point => point
  | .negOne, point => -point
  | .omega, point => BN254.endomorphism point
  | .negOmega, point => -(BN254.endomorphism point)
  | .omegaSquared, point => BN254.endomorphism (BN254.endomorphism point)
  | .negOmegaSquared, point => -(BN254.endomorphism (BN254.endomorphism point))

/-- The coordinate operation equals multiplication by its scalar digit. -/
theorem digitEndomorphismAction [BN254.FieldCertificate] [BN254.GroupCertificate]
    (digit : Digit) (point : BN254.Point) :
    digitEndomorphism digit point = digitScalar digit • point := by
  cases digit
  case zero => exact (Module.zero_smul point).symm
  all_goals simp [digitEndomorphism, digitScalar, omegaAction, smul_smul]

/-- `radix` is the optimized base `2 - omega`. -/
def radix : BN254.ScalarField :=
  2 - omega

/-- `DecompositionState` contains one Eisenstein integer pair. -/
structure DecompositionState where
  a : Int
  b : Int
deriving DecidableEq

/-- `Round` contains one selected digit and its integer coordinates. -/
structure Round where
  digit : Digit
  u : Int
  v : Int
deriving DecidableEq

/-- `selectRound` defines the residue table. -/
def selectRound (residue : Int) : Round :=
  match residue with
  | 0 => ⟨.zero, 0, 0⟩
  | 1 => ⟨.one, 1, 0⟩
  | 2 => ⟨.omega, 0, 1⟩
  | 3 => ⟨.negOmegaSquared, 1, 1⟩
  | 4 => ⟨.omegaSquared, -1, -1⟩
  | 5 => ⟨.negOmega, 0, -1⟩
  | 6 => ⟨.negOne, -1, 0⟩
  | _ => ⟨.zero, 0, 0⟩

/-- `nextRound` selects the next base-seven digit. -/
def nextRound (state : DecompositionState) : Round :=
  selectRound ((state.a + 2 * state.b) % 7)

/-- `nextState` defines the exact division recurrence. -/
def nextState (state : DecompositionState) : DecompositionState :=
  let round := nextRound state
  let a := state.a - round.u
  let b := state.b - round.v
  ⟨(3 * a - b) / 7, (a + 2 * b) / 7⟩

/-- `decompose` runs the fixed digit recurrence. -/
def decompose : Nat → DecompositionState → List Digit
  | 0, _ => []
  | rounds + 1, state => (nextRound state).digit :: decompose rounds (nextState state)

/-- `after` returns the state after the fixed digit recurrence. -/
def after : Nat → DecompositionState → DecompositionState
  | 0, state => state
  | rounds + 1, state => after rounds (nextState state)

/-- `stateValue` maps one Eisenstein integer pair into the scalar field. -/
def stateValue (state : DecompositionState) : BN254.ScalarField :=
  state.a + omega * state.b

/-- `scalarModulus` is the integer form of the BN254 scalar modulus. -/
def scalarModulus : Int := BN254.scalarFieldModulus

/-- These four constants are the BN254 G1 reduced GLV basis. -/
def glvN11 : Int := -147946756881789319000765030803803410728
def glvN12 : Int := 9931322734385697763
def glvN21 : Int := -9931322734385697763
def glvN22 : Int := -147946756881789319010696353538189108491

/-- `truncDiv` implements integer division toward zero. -/
def truncDiv (numerator denominator : Int) : Int :=
  if numerator < 0 then -((-numerator) / denominator) else numerator / denominator

/-- `roundedQuotient` implements the rounding rule in arkworks GLV decomposition. -/
def roundedQuotient (numerator : Int) : Int :=
  let quotient := truncDiv numerator scalarModulus
  let remainder := numerator - quotient * scalarModulus
  if 2 * remainder > scalarModulus then quotient + 1 else quotient

/-- `glvInitial` implements the BN254 G1 reduced-basis split. -/
def glvInitial (scalar : BN254.ScalarField) : DecompositionState :=
  let value : Int := scalar.val
  let betaOne := roundedQuotient (value * glvN22)
  let betaTwo := roundedQuotient (value * -glvN12)
  let latticeOne := betaOne * glvN11 + betaTwo * glvN21
  let latticeTwo := betaOne * glvN12 + betaTwo * glvN22
  ⟨value - latticeOne, -latticeTwo⟩

/-- The first GLV basis vector is zero modulo the scalar modulus. -/
theorem glvBasisOne :
    (glvN11 : BN254.ScalarField) + omega * (glvN12 : BN254.ScalarField) = 0 := by
  decide

/-- The second GLV basis vector is zero modulo the scalar modulus. -/
theorem glvBasisTwo :
    (glvN21 : BN254.ScalarField) + omega * (glvN22 : BN254.ScalarField) = 0 := by
  decide

/-- The fixed GLV split reconstructs the input scalar. -/
theorem glvInitialCorrect (scalar : BN254.ScalarField) :
    stateValue (glvInitial scalar) = scalar := by
  simp only [stateValue, glvInitial]
  push_cast
  rw [ZMod.natCast_zmod_val]
  linear_combination
    -(roundedQuotient ((scalar.val : Int) * glvN22) : BN254.ScalarField) * glvBasisOne -
    (roundedQuotient ((scalar.val : Int) * -glvN12) : BN254.ScalarField) * glvBasisTwo

/-- `shiftedInitial` adds one combination of the two GLV basis vectors. -/
def shiftedInitial (scalar : BN254.ScalarField) (e₁ e₂ : Int) :
    DecompositionState :=
  ⟨(glvInitial scalar).a + e₁ * glvN11 + e₂ * glvN21,
    (glvInitial scalar).b + e₁ * glvN12 + e₂ * glvN22⟩

/-- These four states are the corners of one GLV basis cell. -/
def fourShiftedInitials (scalar : BN254.ScalarField) : List DecompositionState :=
  [shiftedInitial scalar 0 0, shiftedInitial scalar 1 0,
    shiftedInitial scalar 0 1, shiftedInitial scalar 1 1]

/-- `shortInitial` selects the first state that terminates in 91 rounds. -/
def shortInitial (scalar : BN254.ScalarField) : DecompositionState :=
  let state₀ := shiftedInitial scalar 0 0
  let state₁ := shiftedInitial scalar 1 0
  let state₂ := shiftedInitial scalar 0 1
  let state₃ := shiftedInitial scalar 1 1
  if after 91 state₀ = ⟨0, 0⟩ then state₀
  else if after 91 state₁ = ⟨0, 0⟩ then state₁
  else if after 91 state₂ = ⟨0, 0⟩ then state₂
  else state₃

/-- One recurrence step gives the required integer identities. -/
theorem nextStateEquations (state : DecompositionState) :
    state.a = (nextRound state).u + 2 * (nextState state).a + (nextState state).b ∧
    state.b = (nextRound state).v - (nextState state).a + 3 * (nextState state).b := by
  generalize residueEq : (state.a + 2 * state.b) % 7 = residue
  have residueNonnegative : 0 ≤ residue := by
    rw [← residueEq]
    exact Int.emod_nonneg _ (by decide)
  have residueLess : residue < 7 := by
    rw [← residueEq]
    exact Int.emod_lt_of_pos _ (by decide)
  interval_cases residue <;>
    simp [nextState, nextRound, selectRound, residueEq] <;>
    omega

/-- The selected digit equals its integer coordinate pair. -/
theorem nextRoundValue (state : DecompositionState) :
    digitScalar (nextRound state).digit =
      (nextRound state).u + omega * (nextRound state).v := by
  generalize residueEq : (state.a + 2 * state.b) % 7 = residue
  have residueNonnegative : 0 ≤ residue := by
    rw [← residueEq]
    exact Int.emod_nonneg _ (by decide)
  have residueLess : residue < 7 := by
    rw [← residueEq]
    exact Int.emod_lt_of_pos _ (by decide)
  interval_cases residue <;>
    simp [nextRound, selectRound, residueEq, digitScalar, omegaSquared]
  all_goals ring

/-- The fixed recurrence preserves the represented scalar. -/
theorem nextStateCorrect (state : DecompositionState) :
    stateValue state =
      digitScalar (nextRound state).digit + radix * stateValue (nextState state) := by
  rw [nextRoundValue]
  obtain ⟨aEquation, bEquation⟩ := nextStateEquations state
  simp only [stateValue, radix]
  rw [aEquation, bEquation]
  push_cast
  linear_combination ((nextState state).b : BN254.ScalarField) * omegaQuadratic

/-- This certificate records the proved 91-round termination result. -/
class TerminationCertificate : Prop where
  terminal : ∀ scalar, after 91 (shortInitial scalar) = ⟨0, 0⟩
  initialCorrect : ∀ scalar, stateValue (shortInitial scalar) = scalar

/-- The fixed recurrence always returns the requested number of digits. -/
theorem decomposeLength (rounds : Nat) (state : DecompositionState) :
    (decompose rounds state).length = rounds := by
  induction rounds generalizing state with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      simp [decompose, inductionHypothesis]

/-- Each recurrence step preserves the represented scalar. -/
theorem reconstructionWithTail (rounds : Nat)
    (state : DecompositionState) :
    scalarHorner radix ((decompose rounds state).map digitScalar) +
        radix ^ rounds * stateValue (after rounds state) = stateValue state := by
  induction rounds generalizing state with
  | zero =>
      simp [decompose, after, scalarHorner]
  | succ rounds inductionHypothesis =>
      simp only [decompose, List.map_cons, scalarHorner, after, pow_succ]
      calc
        digitScalar (nextRound state).digit +
              radix * scalarHorner radix
                ((decompose rounds (nextState state)).map digitScalar) +
            radix ^ rounds * radix * stateValue (after rounds (nextState state)) =
            digitScalar (nextRound state).digit + radix *
              (scalarHorner radix
                ((decompose rounds (nextState state)).map digitScalar) +
                radix ^ rounds * stateValue (after rounds (nextState state))) := by ring
        _ = digitScalar (nextRound state).digit + radix * stateValue (nextState state) := by
          rw [inductionHypothesis (nextState state)]
        _ = stateValue state := (nextStateCorrect state).symm

/-- `Construction` has no caller-selected algorithm or proof field. -/
abbrev Construction := Unit

/-- `construction` is the one fixed ArgoMAC construction. -/
def construction : Construction := ()

/-- `digits` returns the 91 fixed recurrence digits. -/
def Construction.digits (_construction : Construction)
    (scalar : BN254.ScalarField) : List Digit :=
  decompose 91 (shortInitial scalar)

/-- The fixed recurrence returns 91 digits. -/
theorem Construction.digitCount (construction : Construction)
    (scalar : BN254.ScalarField) : (construction.digits scalar).length = 91 := by
  exact decomposeLength 91 _

/-- The fixed recurrence reconstructs the input scalar. -/
theorem Construction.scalarReconstruction [TerminationCertificate]
    (construction : Construction) (scalar : BN254.ScalarField) :
    scalarHorner radix ((construction.digits scalar).map digitScalar) = scalar := by
  have invariant := reconstructionWithTail 91
    (shortInitial scalar)
  rw [TerminationCertificate.terminal scalar] at invariant
  simp [stateValue] at invariant
  change scalarHorner radix
    ((decompose 91 (shortInitial scalar)).map digitScalar) = scalar
  rw [invariant]
  exact TerminationCertificate.initialCorrect scalar

end Kriterion.ArgoMAC
