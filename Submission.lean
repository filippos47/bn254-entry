/-
The Plan B entry at the query-gated challenge library (`aaf2789`).

* `FixedIndex` is the fixed-key index of `Construction/PGS/Index.lean`: the `bin-to-hot` fold
  gates and the doubling-exception gadget (`117,908` indices), at the ragged-first profile (chunk
  widths `[2, 5 × 32, 4 × 23]`, `chunkCount = 56`). The switch masks are not fixed-key gates:
  each switch mask vector is drawn from one batch of hash queries
  (`Construction/PGS/BatchSampler.lean`);
* `Randomness` is `Scheme.Coins`: a Plan B tape without its three public tables, which the
  library now supplies as a separate oracle;
* `Public` is the eight-field, tag-free public value of design D.5, `1,348,634` bytes (`733`
  elements per chunk word, with the four-element `Y` row);
* `scheme` is `Scheme.scheme`, the Plan B garbler and evaluator on `coins.withOracle oracle`;
* `garbleProgram`/`evaluateProgram` are the query programs of `Construction/OraclePrograms.lean`
  at their exact budgets, `1,077,993` and `1,035,473` queries.

Every field is proved outright. `adaptivePrivacy` is `Phase3.Glue.planB_oracleAdaptivePrivacy_of`
applied to `planB_publicFirst` and `MachineBound.of_law machineLaw_planB`. The hybrid chain
(with the public-first hop `G1U → HW`), the lazy oracle, the abort bound and the closed
simulator machine are all proved.

Elaboration note: each non-trivial field is proved as a standalone theorem below and then
*named* in the structure instance, and the `scheme` field is the constant `@Scheme.scheme`, not
the eta-expanded `fun field group => ...`: the beta-redex that the expansion leaves in the field
types makes the kernel unfold `PlanB.Wire.encoding` when it checks the constructor application.
-/

import Solution
import Construction
import Proof

set_option maxRecDepth 8000

namespace Submission
open Kriterion Kriterion.BN254 Kriterion.ArgoMAC

/-- `Solution.lamportCompatible`: `Encode` selects one label of each of the 508 pairs. -/
def lamportCompatible (field : FieldCertificate) (group : @GroupCertificate field) :
    GarbledCircuit.LamportCompatibility (@Scheme.scheme field group) affineLamportBits where
  keyPairs key := Lamport.keyPairs key
  encodeSelectsLabels key input := Lamport.selectedLabels_eq key input

/-- `Solution.perfectCorrectness`: the evaluator rebuilds its labels from the 508 selected
blocks (`Lamport.restore_selected`), and Plan B is exact for every coins, oracle and input. -/
theorem perfectCorrectness (field : FieldCertificate) (group : @GroupCertificate field) :
    GarbledCircuit.PerfectCorrectness (@Scheme.scheme field group) Prod.snd := by
  letI := field
  letI := group
  intro parameter scalar tape input
  change some (Garbling.evaluate tape.2
      (Garbling.garble construction scalar (tape.1.withOracle tape.2)).1
      (Lamport.restore input
        (Lamport.selectedLabels (tape.1.inputMacKey.encode (BitInput.ofAffine input))))) = _
  rw [Lamport.restore_selected]
  exact congrArg some (JacobianMixed.evaluateCorrect scalar (tape.1.withOracle tape.2) input)

/-- `Solution.garbleProgramCorrect`. -/
theorem garbleProgramCorrect (field : FieldCertificate) (group : @GroupCertificate field)
    (parameter : Nat) (scalar : NonZeroScalar) (coins : Scheme.Coins) (oracle : Scheme.Oracle) :
    (Programs.garbleProgram parameter scalar coins).eval (Cryptography.publicAnswer oracle) =
      (@Scheme.scheme field group).garble parameter scalar (coins, oracle) :=
  @Programs.garbleProgram_correct field group parameter scalar coins oracle

/-- `Solution.evaluateProgramCorrect`. -/
theorem evaluateProgramCorrect (field : FieldCertificate) (group : @GroupCertificate field)
    (table : PlanB.Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature)
    (oracle : Scheme.Oracle) :
    (@Programs.evaluateProgram field group table input labels).eval
        (Cryptography.publicAnswer oracle) =
      (@Scheme.scheme field group).evaluate oracle table input labels :=
  @Programs.evaluateProgram_correct field group table input labels oracle

/-- The Plan B submission at `1,348,634` bytes. -/
def solution : Kriterion.Solution := {
  FixedIndex := PlanB.FixedIndex
  EncIndex := EncPRF.PermutationIndex
  fixedFinite := inferInstance
  encFinite := inferInstance
  Randomness := Scheme.Coins
  randomnessFinite := inferInstance
  randomness := Scheme.witness
  Public := PlanB.Public
  EncodingKey := InputMacKey
  encoding := PlanB.Wire.encoding
  ciphertextBytes := 1348634
  garbleQueries := Programs.garbleQueries
  evaluateQueries := Programs.evaluateQueries
  scheme := @Scheme.scheme
  garbleProgram := fun _ _ => Programs.garbleProgram
  evaluateProgram := @Programs.evaluateProgram
  garbleProgramCorrect := garbleProgramCorrect
  evaluateProgramCorrect := evaluateProgramCorrect
  ciphertextSize := by
    intro field group parameter scalar tape
    exact PlanB.Wire.ciphertextSize _
  lamportCompatible := lamportCompatible
  functionCorrect := fun _ _ _ _ => rfl
  perfectCorrectness := perfectCorrectness
  adaptivePrivacy := Phase3.Glue.planB_oracleAdaptivePrivacy_of
    Security.Phase3.PublicFirst.planB_publicFirst
    (Phase3.Glue.MachineBound.of_law PlanB.SimMachine.machineLaw_planB)
}

end Submission
