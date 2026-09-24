/-
This file is the Plan B correctness root (plan
`2026-09-17-planB.md`, Task 21).

`PerfectCorrectness` quantifies over **every** security parameter, scalar, tape and input --
there is no "with overwhelming probability" anywhere in it -- and Plan B meets it
structurally (plan D.9):

* no working modulus and no `Z_M` wraparound: every wire is `F_p` and every gate is
  `F_p`-linear, so the one-hot fold `sum_j iota(j) * L_j` is an identity, not an estimate;
* the switch-resolution order is a function of the evaluator's cleartext input alone;
* off-curve inputs are refused *before* the garbled program is touched --
  `Pipeline.evaluate` runs `decodePoint` on the cleartext affine input and returns `none`,
  which `Garbling.evaluate` reports as `some none`. That branch is deterministic and
  tape-independent;
* the two Jacobian degeneracies (`Z = 0` with `X = Y = 0`, and the doubling exception) go
  through the unchanged exception gadget, whose entry is a deterministic function of the tape
  and the input;
* the two switch systems deliver exactly `a_e * coord + K e` for every tape, by
  `PlanB.delivers` (`Proof/Correctness/PGS/Row.lean`), so nothing about the delivery is
  conditional either;
* the four-element `Y` row is exact on the curve (`Biquadratic.evaluateEncodedY`), which is the
  only place the evaluator reaches it; `Proof/Correctness/PGS/NonResidue.lean` adds that every
  curve point has `x ≠ 0` (`3` is not a square), which the simulator's opening needs to divide by
  the `Y` collector's coefficient `x ^ 2`.
-/

import Proof.Correctness.Base7Termination
import Proof.Correctness.CanonicalBits
import Proof.Correctness.JacobianMixed
import Proof.Correctness.PGS.AffineFp
import Proof.Correctness.PGS.EncSlots
import Proof.Correctness.PGS.ExceptionalPoints
import Proof.Correctness.PGS.NonResidue
import Proof.Correctness.PGS.OneHot
import Proof.Correctness.PGS.Row
import Proof.Correctness.PGS.ScaleHot

namespace Kriterion.ArgoMAC

open BN254

/-- The circuit function equals the required scalar multiplication function. -/
theorem functionCorrect [FieldCertificate] [GroupCertificate]
    (scalar : NonZeroScalar) (input : AffineInput) :
    (Garbling.garbledCircuit construction).function scalar input =
      checkedScalarMultiplication scalar.value input := rfl

/-- Every random tape gives the required evaluation result. -/
theorem perfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness (Garbling.garbledCircuit construction)
      (fun randomness =>
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)) :=
  JacobianMixed.perfectCorrectness

/-- **Perfect correctness, unfolded.** For every certificate pair, security parameter, scalar,
tape and input -- including off-curve inputs, where the answer is `some none`, and both
Jacobian degeneracies -- evaluation returns the checked scalar multiplication. -/
theorem evaluateCorrect [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    (parameter : Nat) (scalar : NonZeroScalar) (tape : Garbling.Randomness)
    (input : AffineInput) :
    Garbling.evaluate (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)
        (Garbling.garble construction scalar tape).1
        (Garbling.encode (Garbling.garble construction scalar tape).2
          (BitInput.ofAffine input))
      = checkedScalarMultiplication scalar.value input :=
  JacobianMixed.evaluateCorrect scalar tape input

end Kriterion.ArgoMAC
