/-
This file proves the fixed 91-round BN254 scalar decomposition.
-/

import Construction.ArgoMAC.Base7
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.NormNum.NatSqrt

namespace Kriterion.ArgoMAC.GLV91

def modulus : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

def basisA : Nat := 147946756881789319000765030803803410728
def basisD : Nat := 9931322734385697763
def basisC : Nat := 147946756881789319010696353538189108491

def qnorm (a b : Int) : Int := a * a - a * b + b * b

def stateNorm (state : DecompositionState) : Int := qnorm state.a state.b

def quotientC (k : Nat) : Nat := k * basisC / modulus
def quotientD (k : Nat) : Nat := k * basisD / modulus
def remainderC (k : Nat) : Nat := k * basisC % modulus
def remainderD (k : Nat) : Nat := k * basisD % modulus

def candidate (k : Nat) (e₁ e₂ : Int) : DecompositionState :=
  ⟨(k : Int) - (basisA : Int) * (quotientC k : Int) -
      (basisD : Int) * (quotientD k : Int) - (basisA : Int) * e₁ -
      (basisD : Int) * e₂,
    (basisD : Int) * (quotientC k : Int) -
      (basisC : Int) * (quotientD k : Int) + (basisD : Int) * e₁ -
      (basisC : Int) * e₂⟩

def fourCandidates (k : Nat) : List DecompositionState :=
  [candidate k 0 0, candidate k 1 0, candidate k 0 1, candidate k 1 1]

theorem constants :
    basisC = basisA + basisD ∧
    modulus = basisA * basisA + basisA * basisD + basisD * basisD := by
  norm_num [basisA, basisD, basisC, modulus]

theorem modulus_pos : 0 < modulus := by norm_num [modulus]

theorem scalarModulusEq : scalarModulus = (modulus : Int) := by
  norm_num [scalarModulus, BN254.scalarFieldModulus, modulus]

theorem glvConstants :
    glvN11 = -(basisA : Int) ∧ glvN12 = (basisD : Int) ∧
    glvN21 = -(basisD : Int) ∧ glvN22 = -(basisC : Int) := by
  norm_num [glvN11, glvN12, glvN21, glvN22, basisA, basisD, basisC]

theorem roundedQuotientNegNat (n : Nat) :
    roundedQuotient (-(n : Int)) = -((n / modulus : Nat) : Int) := by
  rw [roundedQuotient, truncDiv, scalarModulusEq]
  by_cases hn : n = 0
  · simp [hn]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnposInt : (0 : Int) < (n : Int) := by exact_mod_cast hnpos
    have hneg : -(n : Int) < 0 := by omega
    simp only [hneg, if_true, neg_neg]
    norm_cast
    have hremainder : -(n : Int) - -((n / modulus : Nat) : Int) * (modulus : Int) ≤ 0 := by
      have hdiv := Nat.div_mul_le_self n modulus
      have hdivInt : ((n / modulus : Nat) : Int) * (modulus : Int) ≤ (n : Int) := by
        exact_mod_cast hdiv
      calc
        -(n : Int) - -((n / modulus : Nat) : Int) * (modulus : Int) =
            -((n : Int) - ((n / modulus : Nat) : Int) * (modulus : Int)) := by ring
        _ ≤ 0 := by omega
    simp only [show ¬2 * (-(n : Int) - -((n / modulus : Nat) : Int) * (modulus : Int)) >
        (modulus : Int) by omega, if_false]

theorem glvInitialEqCandidateZero (scalar : BN254.ScalarField) :
    glvInitial scalar = candidate scalar.val 0 0 := by
  obtain ⟨hn11, hn12, hn21, hn22⟩ := glvConstants
  have hbetaOne : roundedQuotient (-((scalar.val * basisC : Nat) : Int)) =
      -((quotientC scalar.val : Nat) : Int) := by
    rw [roundedQuotientNegNat]
    rfl
  have hbetaTwo : roundedQuotient (-((scalar.val * basisD : Nat) : Int)) =
      -((quotientD scalar.val : Nat) : Int) := by
    rw [roundedQuotientNegNat]
    rfl
  simp only [glvInitial, candidate, hn11, hn12, hn21, hn22]
  rw [show (scalar.val : Int) * -(basisC : Int) =
      -((scalar.val * basisC : Nat) : Int) by push_cast; ring,
    show (scalar.val : Int) * -(basisD : Int) =
      -((scalar.val * basisD : Nat) : Int) by push_cast; ring,
    hbetaOne, hbetaTwo]
  congr 1 <;> ring

theorem candidateEqShiftedInitial (scalar : BN254.ScalarField) (e₁ e₂ : Int) :
    candidate scalar.val e₁ e₂ = shiftedInitial scalar e₁ e₂ := by
  obtain ⟨hn11, hn12, hn21, hn22⟩ := glvConstants
  unfold shiftedInitial
  rw [glvInitialEqCandidateZero]
  simp only [candidate, hn11, hn12, hn21, hn22]
  congr 1 <;> ring

theorem fourCandidatesEqShiftedInitials (scalar : BN254.ScalarField) :
    fourCandidates scalar.val = fourShiftedInitials scalar := by
  simp only [fourCandidates, fourShiftedInitials, candidateEqShiftedInitial]

theorem shiftedInitialCorrect (scalar : BN254.ScalarField) (e₁ e₂ : Int) :
    stateValue (shiftedInitial scalar e₁ e₂) = scalar := by
  have hinitial := glvInitialCorrect scalar
  simp only [stateValue, shiftedInitial]
  simp only [stateValue] at hinitial
  push_cast
  linear_combination hinitial +
    (e₁ : BN254.ScalarField) * glvBasisOne +
    (e₂ : BN254.ScalarField) * glvBasisTwo

theorem qnorm_nonneg (a b : Int) : 0 ≤ qnorm a b := by
  dsimp [qnorm]
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]

theorem scaledCandidateIdentity
    (A d C r k qc qd u v e₁ e₂ : Int)
    (hC : C = A + d)
    (hr : r = A * A + A * d + d * d)
    (hu : k * C = r * qc + u)
    (hv : k * d = r * qd + v) :
    r * qnorm
      (k - A * qc - d * qd - A * e₁ - d * e₂)
      (d * qc - C * qd + d * e₁ - C * e₂) =
    qnorm (r * e₁ - u) (r * e₂ - v) := by
  have ueq : u = k * C - r * qc := by linarith
  have veq : v = k * d - r * qd := by linarith
  rw [ueq, veq, hC, hr]
  simp only [qnorm]
  ring

theorem candidateScaledNorm (k : Nat) (e₁ e₂ : Int) :
    (modulus : Int) * stateNorm (candidate k e₁ e₂) =
      qnorm ((modulus : Int) * e₁ - (remainderC k : Int))
        ((modulus : Int) * e₂ - (remainderD k : Int)) := by
  have huNat := Nat.mod_add_div (k * basisC) modulus
  have hvNat := Nat.mod_add_div (k * basisD) modulus
  have hu : (k : Int) * (basisC : Int) =
      (modulus : Int) * (quotientC k : Int) + (remainderC k : Int) := by
    have hcast : ((k * basisC : Nat) : Int) =
        ((remainderC k : Nat) : Int) +
          ((modulus : Nat) : Int) * ((quotientC k : Nat) : Int) := by
      exact_mod_cast huNat.symm
    simpa [quotientC, remainderC, add_comm] using hcast
  have hv : (k : Int) * (basisD : Int) =
      (modulus : Int) * (quotientD k : Int) + (remainderD k : Int) := by
    have hcast : ((k * basisD : Nat) : Int) =
        ((remainderD k : Nat) : Int) +
          ((modulus : Nat) : Int) * ((quotientD k : Nat) : Int) := by
      exact_mod_cast hvNat.symm
    simpa [quotientD, remainderD, add_comm] using hcast
  obtain ⟨hC, hr⟩ := constants
  have hCInt : (basisC : Int) = (basisA : Int) + (basisD : Int) := by
    exact_mod_cast hC
  have hrInt : (modulus : Int) =
      (basisA : Int) * (basisA : Int) +
      (basisA : Int) * (basisD : Int) +
      (basisD : Int) * (basisD : Int) := by
    exact_mod_cast hr
  simpa [candidate, stateNorm] using
    scaledCandidateIdentity (basisA : Int) (basisD : Int) (basisC : Int)
      (modulus : Int) (k : Int) (quotientC k : Int) (quotientD k : Int)
      (remainderC k : Int) (remainderD k : Int) e₁ e₂ hCInt hrInt hu hv

set_option maxRecDepth 100000 in
/-- The unshifted candidate stays inside one reduced basis cell. -/
theorem candidateZeroBounds (k : Nat) :
    0 ≤ (candidate k 0 0).a ∧
      (candidate k 0 0).a < (basisC : Int) ∧
      -(basisD : Int) < (candidate k 0 0).b ∧
      (candidate k 0 0).b < (basisC : Int) := by
  have modulusPos : 0 < modulus := by
    norm_num [modulus]
  have remainderCEquation : (k : Int) * (basisC : Int) =
      (modulus : Int) * (quotientC k : Int) + (remainderC k : Int) := by
    have equation := Nat.mod_add_div (k * basisC) modulus
    have castEquation : ((k * basisC : Nat) : Int) =
        ((remainderC k : Nat) : Int) +
          ((modulus : Nat) : Int) * ((quotientC k : Nat) : Int) := by
      exact_mod_cast equation.symm
    simpa [quotientC, remainderC, add_comm] using castEquation
  have remainderDEquation : (k : Int) * (basisD : Int) =
      (modulus : Int) * (quotientD k : Int) + (remainderD k : Int) := by
    have equation := Nat.mod_add_div (k * basisD) modulus
    have castEquation : ((k * basisD : Nat) : Int) =
        ((remainderD k : Nat) : Int) +
          ((modulus : Nat) : Int) * ((quotientD k : Nat) : Int) := by
      exact_mod_cast equation.symm
    simpa [quotientD, remainderD, add_comm] using castEquation
  have modulusIdentity : (modulus : Int) =
      (basisA : Int) * (basisC : Int) + (basisD : Int) * (basisD : Int) := by
    norm_num [modulus, basisA, basisC, basisD]
  have aScaled : (modulus : Int) * (candidate k 0 0).a =
      (basisA : Int) * (remainderC k : Int) +
        (basisD : Int) * (remainderD k : Int) := by
    simp only [candidate, Int.mul_zero, sub_zero]
    linear_combination
      (basisA : Int) * remainderCEquation +
      (basisD : Int) * remainderDEquation +
      (k : Int) * modulusIdentity
  have bScaled : (modulus : Int) * (candidate k 0 0).b =
      (basisC : Int) * (remainderD k : Int) -
        (basisD : Int) * (remainderC k : Int) := by
    simp only [candidate, Int.mul_zero, add_zero, sub_zero]
    linear_combination
      (basisC : Int) * remainderDEquation -
      (basisD : Int) * remainderCEquation
  have remainderCNonnegative : 0 ≤ (remainderC k : Int) := Int.ofNat_zero_le _
  have remainderDNonnegative : 0 ≤ (remainderD k : Int) := Int.ofNat_zero_le _
  have remainderCLess : (remainderC k : Int) < (modulus : Int) := by
    exact_mod_cast Nat.mod_lt (k * basisC) modulusPos
  have remainderDLess : (remainderD k : Int) < (modulus : Int) := by
    exact_mod_cast Nat.mod_lt (k * basisD) modulusPos
  have modulusPosInt : (0 : Int) < (modulus : Int) := by
    exact_mod_cast modulusPos
  have basisAPos : (0 : Int) < (basisA : Int) := by
    norm_num [basisA]
  have basisCPos : (0 : Int) < (basisC : Int) := by
    norm_num [basisC]
  have basisDPos : (0 : Int) < (basisD : Int) := by
    norm_num [basisD]
  have basisSum : (basisA : Int) + (basisD : Int) = (basisC : Int) := by
    norm_num [basisA, basisC, basisD]
  have aRightNonnegative :
      0 ≤ (basisA : Int) * (remainderC k : Int) +
        (basisD : Int) * (remainderD k : Int) :=
    add_nonneg (mul_nonneg basisAPos.le remainderCNonnegative)
      (mul_nonneg basisDPos.le remainderDNonnegative)
  have aRightLess :
      (basisA : Int) * (remainderC k : Int) +
          (basisD : Int) * (remainderD k : Int) <
        (modulus : Int) * (basisC : Int) := by
    calc
      (basisA : Int) * (remainderC k : Int) +
          (basisD : Int) * (remainderD k : Int) <
          (basisA : Int) * (modulus : Int) +
            (basisD : Int) * (modulus : Int) :=
        add_lt_add (mul_lt_mul_of_pos_left remainderCLess basisAPos)
          (mul_lt_mul_of_pos_left remainderDLess basisDPos)
      _ = (modulus : Int) * (basisC : Int) := by rw [← basisSum]; ring
  have bRightGreater :
      -((modulus : Int) * (basisD : Int)) <
        (basisC : Int) * (remainderD k : Int) -
          (basisD : Int) * (remainderC k : Int) := by
    calc
      -((modulus : Int) * (basisD : Int)) =
          -((basisD : Int) * (modulus : Int)) := by ring
      _ < -((basisD : Int) * (remainderC k : Int)) :=
        neg_lt_neg (mul_lt_mul_of_pos_left remainderCLess basisDPos)
      _ ≤ (basisC : Int) * (remainderD k : Int) -
          (basisD : Int) * (remainderC k : Int) := by
        linarith [mul_nonneg basisCPos.le remainderDNonnegative]
  have bRightLess :
      (basisC : Int) * (remainderD k : Int) -
          (basisD : Int) * (remainderC k : Int) <
        (modulus : Int) * (basisC : Int) := by
    calc
      (basisC : Int) * (remainderD k : Int) -
          (basisD : Int) * (remainderC k : Int) ≤
          (basisC : Int) * (remainderD k : Int) := by
        exact sub_le_self _ (mul_nonneg basisDPos.le remainderCNonnegative)
      _ < (basisC : Int) * (modulus : Int) :=
        mul_lt_mul_of_pos_left remainderDLess basisCPos
      _ = (modulus : Int) * (basisC : Int) := by ring
  constructor
  · by_contra negative
    have productNegative :
        (modulus : Int) * (candidate k 0 0).a < 0 :=
      mul_neg_of_pos_of_neg modulusPosInt (lt_of_not_ge negative)
    rw [aScaled] at productNegative
    exact (not_lt_of_ge aRightNonnegative) productNegative
  constructor
  · apply (mul_lt_mul_iff_right₀ modulusPosInt).mp
    rw [aScaled]
    exact aRightLess
  constructor
  · apply (mul_lt_mul_iff_right₀ modulusPosInt).mp
    calc
      (modulus : Int) * (-(basisD : Int)) =
          -((modulus : Int) * (basisD : Int)) := by ring
      _ < (basisC : Int) * (remainderD k : Int) -
          (basisD : Int) * (remainderC k : Int) := bRightGreater
      _ = (modulus : Int) * (candidate k 0 0).b := bScaled.symm
  · apply (mul_lt_mul_iff_right₀ modulusPosInt).mp
    rw [bScaled]
    exact bRightLess

set_option maxRecDepth 100000 in
/-- Every corner candidate fits in one signed 128-bit integer pair. -/
theorem fourCandidatesSignedI128 (k : Nat) :
    ∀ state ∈ fourCandidates k,
      -((2 : Int) ^ 127) ≤ state.a ∧ state.a < (2 : Int) ^ 127 ∧
      -((2 : Int) ^ 127) ≤ state.b ∧ state.b < (2 : Int) ^ 127 := by
  obtain ⟨aNonnegative, aLess, bGreater, bLess⟩ := candidateZeroBounds k
  have shiftA (e₁ e₂ : Int) :
      (candidate k e₁ e₂).a = (candidate k 0 0).a -
        (basisA : Int) * e₁ - (basisD : Int) * e₂ := by
    simp [candidate]
  have shiftB (e₁ e₂ : Int) :
      (candidate k e₁ e₂).b = (candidate k 0 0).b +
        (basisD : Int) * e₁ - (basisC : Int) * e₂ := by
    simp [candidate]
  have basisFits : (basisC : Int) + (basisD : Int) < (2 : Int) ^ 127 := by
    norm_num [basisC, basisD]
  have basisSum : (basisC : Int) = (basisA : Int) + (basisD : Int) := by
    norm_num [basisA, basisC, basisD]
  intro state member
  simp only [fourCandidates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals rw [shiftA, shiftB]
  all_goals
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega

theorem upperTriangleCover (u v scale : Int)
    (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u ≤ scale) :
    3 * qnorm u v ≤ scale ^ 2 ∨
    3 * qnorm (u - scale) v ≤ scale ^ 2 ∨
    3 * qnorm (u - scale) (v - scale) ≤ scale ^ 2 := by
  by_contra h
  simp only [not_or, not_le] at h
  rcases h with ⟨h₀, h₁, h₂⟩
  dsimp [qnorm] at h₀ h₁ h₂ ⊢
  have hsu : 0 ≤ scale - u := by omega
  have huv : 0 ≤ u - v := by omega
  nlinarith [sq_nonneg (3 * u - 2 * scale), sq_nonneg (3 * v - scale),
    mul_nonneg hsu huv, mul_nonneg hsu hv, mul_nonneg huv hv]

theorem lowerTriangleCover (u v scale : Int)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ scale) :
    3 * qnorm u v ≤ scale ^ 2 ∨
    3 * qnorm u (v - scale) ≤ scale ^ 2 ∨
    3 * qnorm (u - scale) (v - scale) ≤ scale ^ 2 := by
  by_contra h
  simp only [not_or, not_le] at h
  rcases h with ⟨h₀, h₁, h₂⟩
  dsimp [qnorm] at h₀ h₁ h₂ ⊢
  have hsv : 0 ≤ scale - v := by omega
  have hvu : 0 ≤ v - u := by omega
  nlinarith [sq_nonneg (3 * u - scale), sq_nonneg (3 * v - 2 * scale),
    mul_nonneg hsv hvu, mul_nonneg hsv hu, mul_nonneg hvu hu]

theorem qnorm_neg (a b : Int) : qnorm (-a) (-b) = qnorm a b := by
  simp only [qnorm]
  ring

theorem cancelNormScale (r x : Int) (hr : 0 < r)
    (h : 3 * (r * x) ≤ r ^ 2) : 3 * x ≤ r := by
  apply (mul_le_mul_iff_right₀ hr).mp
  nlinarith

theorem candidateNormOfCornerNorm (k : Nat) (e₁ e₂ : Int)
    (hcorner : 3 * qnorm
      ((modulus : Int) * e₁ - (remainderC k : Int))
      ((modulus : Int) * e₂ - (remainderD k : Int)) ≤ (modulus : Int) ^ 2) :
    3 * stateNorm (candidate k e₁ e₂) ≤ (modulus : Int) := by
  apply cancelNormScale (modulus : Int) _ (by exact_mod_cast modulus_pos)
  rw [candidateScaledNorm]
  exact hcorner

theorem existsCandidateNormBound (k : Nat) :
    ∃ state ∈ fourCandidates k,
      3 * stateNorm state ≤ (modulus : Int) := by
  let u : Int := remainderC k
  let v : Int := remainderD k
  let r : Int := modulus
  have hu0 : 0 ≤ u := by exact Int.ofNat_zero_le _
  have hv0 : 0 ≤ v := by exact Int.ofNat_zero_le _
  have hur : u ≤ r := by
    dsimp [u, r, remainderC]
    exact_mod_cast (Nat.le_of_lt (Nat.mod_lt _ modulus_pos))
  have hvr : v ≤ r := by
    dsimp [v, r, remainderD]
    exact_mod_cast (Nat.le_of_lt (Nat.mod_lt _ modulus_pos))
  rcases le_total v u with hvu | huv
  · rcases upperTriangleCover u v r hv0 hvu hur with h₀ | h₁ | h₃
    · refine ⟨candidate k 0 0, by simp only [fourCandidates, List.mem_cons,
          true_or], ?_⟩
      apply candidateNormOfCornerNorm
      have hcorner : 3 * qnorm (-u) (-v) ≤ r ^ 2 := by
        simpa [qnorm_neg] using h₀
      simpa [u, v, r] using hcorner
    · refine ⟨candidate k 1 0, by simp only [fourCandidates, List.mem_cons,
          true_or, or_true], ?_⟩
      apply candidateNormOfCornerNorm
      have hcorner : 3 * qnorm (r - u) (-v) ≤ r ^ 2 := by
        rw [show r - u = -(u - r) by ring, qnorm_neg]
        exact h₁
      simpa [u, v, r] using hcorner
    · refine ⟨candidate k 1 1, by simp only [fourCandidates, List.mem_cons,
          true_or, or_true], ?_⟩
      apply candidateNormOfCornerNorm
      have hcorner : 3 * qnorm (r - u) (r - v) ≤ r ^ 2 := by
        rw [show r - u = -(u - r) by ring,
          show r - v = -(v - r) by ring, qnorm_neg]
        exact h₃
      simpa [u, v, r] using hcorner
  · rcases lowerTriangleCover u v r hu0 huv hvr with h₀ | h₂ | h₃
    · refine ⟨candidate k 0 0, by simp only [fourCandidates, List.mem_cons,
          true_or], ?_⟩
      apply candidateNormOfCornerNorm
      have hcorner : 3 * qnorm (-u) (-v) ≤ r ^ 2 := by
        simpa [qnorm_neg] using h₀
      simpa [u, v, r] using hcorner
    · refine ⟨candidate k 0 1, by simp only [fourCandidates, List.mem_cons,
          true_or, or_true], ?_⟩
      apply candidateNormOfCornerNorm
      have hcorner : 3 * qnorm (-u) (r - v) ≤ r ^ 2 := by
        rw [show r - v = -(v - r) by ring, qnorm_neg]
        exact h₂
      simpa [u, v, r] using hcorner
    · refine ⟨candidate k 1 1, by simp only [fourCandidates, List.mem_cons,
          true_or, or_true], ?_⟩
      apply candidateNormOfCornerNorm
      have hcorner : 3 * qnorm (r - u) (r - v) ≤ r ^ 2 := by
        rw [show r - u = -(u - r) by ring,
          show r - v = -(v - r) by ring, qnorm_neg]
        exact h₃
      simpa [u, v, r] using hcorner

theorem nextNormIdentity (state : DecompositionState) :
    qnorm (state.a - (nextRound state).u) (state.b - (nextRound state).v) =
      7 * stateNorm (nextState state) := by
  obtain ⟨ha, hb⟩ := nextStateEquations state
  simp only [stateNorm, qnorm]
  rw [ha, hb]
  ring

theorem formOne (a b : Int) :
    (2 * a - b) ^ 2 ≤ 4 * qnorm a b := by
  dsimp [qnorm]
  nlinarith [sq_nonneg b]

theorem formOmega (a b : Int) :
    (2 * b - a) ^ 2 ≤ 4 * qnorm a b := by
  dsimp [qnorm]
  nlinarith [sq_nonneg a]

theorem formOneAddOmega (a b : Int) :
    (a + b) ^ 2 ≤ 4 * qnorm a b := by
  dsimp [qnorm]
  nlinarith [sq_nonneg (a - b)]

theorem absFormLeSqrt (a b x : Int) (m : Nat)
    (hx : x ^ 2 ≤ 4 * qnorm a b) (hm : qnorm a b ≤ (m : Int)) :
    |x| ≤ (Nat.sqrt (4 * m) : Int) := by
  rw [← Int.sqrt_natCast, Int.abs_le_sqrt_iff_sq_le]
  · have hscale : 4 * qnorm a b ≤ (4 : Int) * (m : Int) := by nlinarith
    exact hx.trans (by simpa using hscale)
  · positivity

theorem selectedDigitNormBound (state : DecompositionState) (m : Nat)
    (hm : stateNorm state ≤ (m : Int)) :
    qnorm (state.a - (nextRound state).u) (state.b - (nextRound state).v) ≤
      (m + 1 + Nat.sqrt (4 * m) : Nat) := by
  dsimp [stateNorm, qnorm] at hm
  have h₁ := absFormLeSqrt state.a state.b (2 * state.a - state.b) m
    (formOne state.a state.b) hm
  have h₂ := absFormLeSqrt state.a state.b (2 * state.b - state.a) m
    (formOmega state.a state.b) hm
  have h₃ := absFormLeSqrt state.a state.b (state.a + state.b) m
    (formOneAddOmega state.a state.b) hm
  rw [abs_le] at h₁ h₂ h₃
  rcases h₁ with ⟨h₁l, h₁u⟩
  rcases h₂ with ⟨h₂l, h₂u⟩
  rcases h₃ with ⟨h₃l, h₃u⟩
  generalize residueEq : (state.a + 2 * state.b) % 7 = residue
  have residueNonnegative : 0 ≤ residue := by
    rw [← residueEq]
    exact Int.emod_nonneg _ (by norm_num)
  have residueLess : residue < 7 := by
    rw [← residueEq]
    exact Int.emod_lt_of_pos _ (by norm_num)
  interval_cases residue <;>
    simp [nextRound, selectRound, residueEq, qnorm] <;>
    nlinarith

def growBound (bound : Nat) : Nat :=
  7 * bound + 1 - Nat.sqrt (4 * (7 * bound + 1))

def normBound : Nat → Nat
  | 0 => 2
  | n + 1 => growBound (normBound n)

def iterateGrow : Nat → Nat → Nat
  | 0, bound => bound
  | rounds + 1, bound => growBound (iterateGrow rounds bound)

theorem normBoundAdd (start rounds : Nat) :
    normBound (start + rounds) = iterateGrow rounds (normBound start) := by
  induction rounds with
  | zero => simp [iterateGrow]
  | succ rounds inductionHypothesis =>
      rw [Nat.add_succ, normBound, iterateGrow, inductionHypothesis]

theorem growBoundSpec (b : Nat) (hb : 1 ≤ b) :
    growBound b + 1 + Nat.sqrt (4 * growBound b) ≤ 7 * b := by
  let u := 7 * b + 1
  let s := Nat.sqrt (4 * u)
  have hu : 8 ≤ u := by omega
  have hsFour : 4 ≤ s := by
    rw [Nat.le_sqrt]
    nlinarith
  have hsLeU : s ≤ u := by
    apply Nat.le_of_lt_succ
    rw [Nat.sqrt_lt]
    nlinarith
  have hsUpper : 4 * u < (s + 1) * (s + 1) := Nat.lt_succ_sqrt _
  have hsub : u - s + s = u := Nat.sub_add_cancel hsLeU
  have hfourSub : s - 2 + 2 = s := Nat.sub_add_cancel (by omega)
  have honeSub : s - 1 + 1 = s := Nat.sub_add_cancel (by omega)
  have hradicand : 4 * (u - s) < (s - 1) * (s - 1) := by
    nlinarith
  have hsqrt : Nat.sqrt (4 * (u - s)) ≤ s - 2 := by
    have hlt : Nat.sqrt (4 * (u - s)) < s - 1 := Nat.sqrt_lt.2 hradicand
    omega
  change (u - s) + 1 + Nat.sqrt (4 * (u - s)) ≤ 7 * b
  omega

theorem nextStateNormBound (state : DecompositionState) (b : Nat) (hb : 1 ≤ b)
    (hstate : stateNorm state ≤ (growBound b : Nat)) :
    stateNorm (nextState state) ≤ (b : Nat) := by
  have hselected := selectedDigitNormBound state (growBound b) hstate
  have hgrow := growBoundSpec b hb
  have hid := nextNormIdentity state
  have hnextNonnegative := qnorm_nonneg (nextState state).a (nextState state).b
  dsimp [stateNorm] at hid hnextNonnegative ⊢
  have hgrowInt :
      (growBound b : Int) + 1 + (Nat.sqrt (4 * growBound b) : Int) ≤
        7 * (b : Int) := by
    exact_mod_cast hgrow
  norm_num at hselected
  nlinarith

theorem growBoundPos (b : Nat) (hb : 1 ≤ b) : 1 ≤ growBound b := by
  let u := 7 * b + 1
  let s := Nat.sqrt (4 * u)
  have hu : 8 ≤ u := by omega
  have hsLtU : s < u := by
    rw [Nat.sqrt_lt]
    nlinarith
  change 1 ≤ u - s
  omega

theorem normBoundPos (n : Nat) : 1 ≤ normBound n := by
  induction n with
  | zero => norm_num [normBound]
  | succ n ih =>
      simpa [normBound] using growBoundPos (normBound n) ih

theorem qnormNeTwo (a b : Int) : qnorm a b ≠ 2 := by
  intro h
  have hm := congrArg (fun x : Int => x % 3) h
  have haNonnegative : 0 ≤ a % 3 := Int.emod_nonneg _ (by norm_num)
  have haLess : a % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hbNonnegative : 0 ≤ b % 3 := Int.emod_nonneg _ (by norm_num)
  have hbLess : b % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  generalize haEq : a % 3 = ra at haNonnegative haLess hm
  generalize hbEq : b % 3 = rb at hbNonnegative hbLess hm
  interval_cases ra <;> interval_cases rb <;>
    norm_num [qnorm, Int.add_emod, Int.sub_emod, Int.mul_emod, haEq, hbEq] at hm

theorem smallStateTerminates (state : DecompositionState)
    (h : stateNorm state ≤ 2) : nextState state = ⟨0, 0⟩ := by
  rcases state with ⟨a, b⟩
  have hnonnegative := qnorm_nonneg a b
  have hnotwo : stateNorm ⟨a, b⟩ ≠ 2 := qnormNeTwo a b
  have hone : stateNorm ⟨a, b⟩ ≤ 1 := by omega
  have hid : 2 * stateNorm ⟨a, b⟩ =
      a ^ 2 + b ^ 2 + (a - b) ^ 2 := by
    simp only [stateNorm, qnorm]
    ring
  have haLower : -1 ≤ a := by nlinarith [sq_nonneg b, sq_nonneg (a - b)]
  have haUpper : a ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg (a - b)]
  have hbLower : -1 ≤ b := by nlinarith [sq_nonneg a, sq_nonneg (a - b)]
  have hbUpper : b ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg (a - b)]
  interval_cases a
  all_goals interval_cases b
  all_goals norm_num [stateNorm, qnorm] at hone
  all_goals norm_num [nextState, nextRound, selectRound]

theorem afterSuccEqZeroOfNormLe (n : Nat) (state : DecompositionState)
    (h : stateNorm state ≤ (normBound n : Nat)) :
    after (n + 1) state = ⟨0, 0⟩ := by
  induction n generalizing state with
  | zero =>
      simpa [after, normBound] using smallStateTerminates state h
  | succ n ih =>
      simp only [normBound] at h
      have hnext := nextStateNormBound state (normBound n) (normBoundPos n) h
      simpa [after] using ih (nextState state) hnext

set_option maxHeartbeats 1000000

theorem boundValue10 : normBound 10 = 199169703 := by
  norm_num [normBound, growBound]

theorem boundValue20 : normBound 20 = 56255667269565349 := by
  rw [show 20 = 10 + 10 by norm_num, normBoundAdd, boundValue10]
  norm_num [iterateGrow, growBound]

theorem boundValue30 : normBound 30 = 15890833538216798757541161 := by
  rw [show 30 = 20 + 10 by norm_num, normBoundAdd, boundValue20]
  norm_num [iterateGrow, growBound]

theorem boundValue40 : normBound 40 = 4488767160523972906085238674205697 := by
  rw [show 40 = 30 + 10 by norm_num, normBoundAdd, boundValue30]
  norm_num [iterateGrow, growBound]

theorem boundValue50 :
    normBound 50 = 1267965621372032194118008944447706426444945 := by
  rw [show 50 = 40 + 10 by norm_num, normBoundAdd, boundValue40]
  norm_num [iterateGrow, growBound]

theorem boundValue60 :
    normBound 60 =
      358168904620504515669114390085969197354217985031118 := by
  rw [show 60 = 50 + 10 by norm_num, normBoundAdd, boundValue50]
  norm_num [iterateGrow, growBound]

theorem boundValue70 :
    normBound 70 =
      101173850516734263569257482452744024380534662717230631681180 := by
  rw [show 70 = 60 + 10 by norm_num, normBoundAdd, boundValue60]
  norm_num [iterateGrow, growBound]

theorem boundValue80 :
    normBound 80 =
      28579108617003289768557636100842816155539193671359393469578712780228 := by
  rw [show 80 = 70 + 10 by norm_num, normBoundAdd, boundValue70]
  norm_num [iterateGrow, growBound]

theorem boundValue :
    normBound 90 =
      8072890822786049911192470628436961768360750887255955910449276353626847573707 := by
  rw [show 90 = 80 + 10 by norm_num, normBoundAdd, boundValue80]
  norm_num [iterateGrow, growBound]

theorem boundCertificate : modulus ≤ 3 * normBound 90 := by
  rw [boundValue]
  norm_num [modulus]

/-- Ninety base-seven digits cannot encode every BN254 scalar. -/
theorem digitCountOptimal : 7 ^ 90 < modulus ∧ modulus < 7 ^ 91 := by
  norm_num [modulus]

theorem existsCandidateTerminates91 (k : Nat) :
    ∃ state ∈ fourCandidates k, after 91 state = ⟨0, 0⟩ := by
  obtain ⟨state, hmember, hnorm⟩ := existsCandidateNormBound k
  refine ⟨state, hmember, ?_⟩
  have hcertificateInt : (modulus : Int) ≤ 3 * (normBound 90 : Nat) := by
    exact_mod_cast boundCertificate
  have hbound : stateNorm state ≤ (normBound 90 : Nat) := by
    nlinarith
  simpa using afterSuccEqZeroOfNormLe 90 state hbound

theorem existsShiftedInitialTerminates91 (scalar : BN254.ScalarField) :
    ∃ state ∈ fourShiftedInitials scalar, after 91 state = ⟨0, 0⟩ := by
  rw [← fourCandidatesEqShiftedInitials]
  exact existsCandidateTerminates91 scalar.val

theorem existsCorrectShiftedInitialTerminates91 (scalar : BN254.ScalarField) :
    ∃ state ∈ fourShiftedInitials scalar,
      stateValue state = scalar ∧ after 91 state = ⟨0, 0⟩ := by
  obtain ⟨state, hmember, hterminal⟩ := existsShiftedInitialTerminates91 scalar
  refine ⟨state, hmember, ?_, hterminal⟩
  simp only [fourShiftedInitials, List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with rfl | rfl | rfl | rfl
  all_goals exact shiftedInitialCorrect scalar _ _

theorem shortInitialTerminates91 (scalar : BN254.ScalarField) :
    after 91 (shortInitial scalar) = ⟨0, 0⟩ := by
  by_cases h₀ : after 91 (shiftedInitial scalar 0 0) = ⟨0, 0⟩
  · simp [shortInitial, h₀]
  by_cases h₁ : after 91 (shiftedInitial scalar 1 0) = ⟨0, 0⟩
  · simp [shortInitial, h₀, h₁]
  by_cases h₂ : after 91 (shiftedInitial scalar 0 1) = ⟨0, 0⟩
  · simp [shortInitial, h₀, h₁, h₂]
  obtain ⟨state, hmember, _, hterminal⟩ :=
    existsCorrectShiftedInitialTerminates91 scalar
  simp only [fourShiftedInitials, List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with rfl | rfl | rfl | rfl
  · exact (h₀ hterminal).elim
  · exact (h₁ hterminal).elim
  · exact (h₂ hterminal).elim
  · simpa [shortInitial, h₀, h₁, h₂] using hterminal

theorem shortInitialCorrect (scalar : BN254.ScalarField) :
    stateValue (shortInitial scalar) = scalar := by
  simp only [shortInitial]
  split <;> rename_i h₀
  · exact shiftedInitialCorrect scalar 0 0
  split <;> rename_i h₁
  · exact shiftedInitialCorrect scalar 1 0
  split <;> rename_i h₂
  · exact shiftedInitialCorrect scalar 0 1
  · exact shiftedInitialCorrect scalar 1 1

instance : TerminationCertificate where
  terminal := shortInitialTerminates91
  initialCorrect := shortInitialCorrect

end Kriterion.ArgoMAC.GLV91
