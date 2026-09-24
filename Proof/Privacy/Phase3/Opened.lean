/-
**Phase 3, P1b — the opened hybrids `HW` and `H`.**

Design note B §3 and the P3 interface (`Glue/Assembly.lean`). Both games have the shape of P4's
`I^U` (`Lazy.idealUniformHybrid`, `Lazy/Refill.lean`): the glue's ideal game `I` whose honest
evaluation is P4's refill run (`Lazy.refillRun`: every non-designated switch-mask vector the run
asks is programmed from a uniform mask tape at its cell's first stage-2 touch, the `452` designated
hash queries intercepted). They differ from `I^U`, and from each other, only after that run
(`openedCont`):

* **the target rows** come from a kernel (`RowsKernel`): the construction's true rows under the
  coins' law (`realRows scalar`) for `HW`, the simulator's tail/head-clamp/lift sampler
  (`simulatedRows`, drawn exactly as `I`/`I^U` draw it) for `H`; the designated vector's free
  coordinates, collector solve and `452` hash answers follow (`Glue.designatedLimbs`);
* **the designated installation**: `HW` and `H` skip a failed program (`programAllSkip`); `I^U`
  aborts (`Glue.programAll`). `idealUniformHybrid_eq_opened` shows `I^U` *is* the opened game at
  (`simulatedRows`, `abortInstallation`), so `H → I^U` (`AbortBound`) changes the installation only.

| hybrid | rows | installation |
|---|---|---|
| `publicFirstHybrid` (`HW`) | `realRows scalar` | skip |
| `openedHybrid` (`H`) | `simulatedRows` | skip |
| `Lazy.idealUniformHybrid` (`I^U`, P4) | `simulatedRows` | abort |
-/

import Proof.Privacy.Phase3.Lazy.Refill

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Phase3.Glue (HybridGame PlanBAdversary Stage1Source LazyAbstractSimulator
  abstractIdealGame idealSamplers openingQueriesM targetRows designatedLimbs programRequests
  programAll DesignatedRecord)

noncomputable section

/-! ### The target rows -/

/-- A law of the 91 target rows, given the input and its output point; `none` is a sampler
abort. -/
abbrev RowsKernel [FieldCertificate] :=
  AffineInput → Point → PMF (Option (Fin digitCount → FieldMacToECMac.HomogeneousValue))

/-- **The simulator's target rows**: the tail offsets, the head clamp to the output, and the lifts,
drawn exactly as the glue's ideal `I` draws them (`idealSamplers.tail`, `idealSamplers.lift`,
`Glue.targetRows`). -/
def simulatedRows [FieldCertificate] [GroupCertificate] : RowsKernel := fun _ target =>
  idealSamplers.tail.bind fun tail => match tail with
  | none => PMF.pure none
  | some tail => idealSamplers.lift.bind fun lift => match lift with
    | none => PMF.pure none
    | some lift => PMF.pure (some (targetRows target tail lift))

/-- The true rows of one garbling at the input: `FieldMacToECMac.evaluateRow` of the construction's
row coefficients (`rowsForOutputKeys` of the garbler's output keys and row randomness). -/
def trueRows [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (coins : Coins)
    (input : AffineInput) (digit : Fin FieldMacToECMac.outputMacCount) :
    FieldMacToECMac.HomogeneousValue :=
  FieldMacToECMac.evaluateRow ((FieldMacToECMac.rowsForOutputKeys
    (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
      coins.pointRandomness).get digit) input

/-- **The real target rows**: the construction's true rows under the coins' law (the garbler's
offsets and row randomness, uniform). -/
def realRows [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) : RowsKernel :=
  fun input _ =>
    letI : Fintype Coins := Fintype.ofFinite Coins
    (PMF.uniformOfFintype Coins).map fun coins => some fun digit => trueRows scalar coins input digit

/-! ### The designated installation -/

/-- Program every request `hash input := answer`, **skipping** a failed one (and a missing input):
the oracle is left as it was at that request. -/
def programAllSkip [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex] :
    List (Option BaseField × (Block × Block)) →
      LazyOracle.State FixedIndex EncPRF.PermutationIndex →
        LazyOracle.State FixedIndex EncPRF.PermutationIndex
  | [], oracle => oracle
  | (input, answer) :: rest, oracle => match input with
    | none => programAllSkip rest oracle
    | some input => programAllSkip rest
        ((LazyOracle.program (.hash input) answer oracle).getD oracle)

/-- A designated installation: the `452` hash program requests on the oracle, `none` an abort. -/
abbrev Installation [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex] :=
  List (Option BaseField × (Block × Block)) →
    LazyOracle.State FixedIndex EncPRF.PermutationIndex →
      Option (LazyOracle.State FixedIndex EncPRF.PermutationIndex)

/-- `H`'s and `HW`'s installation: never aborts. -/
def skipInstallation [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex] :
    Installation := fun requests oracle => some (programAllSkip requests oracle)

/-- `I^U`'s installation: `I`'s own (`Glue.programAll`). -/
def abortInstallation [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex] :
    Installation := programAll

/-! ### The opened simulators -/

/-- **The opening after its honest run**: the target rows from a kernel, the designated vector's
free coordinates, collector solve and `452` hash answers (`Glue.designatedLimbs`), the installation
(P4's `Lazy.openingCont` with a rows kernel and an installation). -/
def openedCont [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (rows : RowsKernel) (install : Installation)
    (table : Public) (input : AffineInput) (labels : LamportSignature) (target : Point)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LazyOracle.State FixedIndex EncPRF.PermutationIndex × DesignatedRecord) :
    PMF (Option (LazyOracle.State FixedIndex EncPRF.PermutationIndex)) :=
  let restored := Lamport.restore input labels
  (rows input target).bind fun targets => match targets with
  | none => PMF.pure none
  | some targets =>
    (designatedLimbs idealSamplers table restored.input ran.1.1 ran.1.2 targets).bind
      fun answers => match answers with
      | none => PMF.pure none
      | some answers => PMF.pure (install (programRequests restored.input ran.2.2 answers) ran.2.1)

/-- **The opening of the opened hybrids**: P4's refill run, then `openedCont`. -/
def openedOpening [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (rows : RowsKernel) (install : Installation)
    (table : Public) (input : AffineInput) (labels : LamportSignature) (target : Point)
    (oracle : LazyOracle.State FixedIndex EncPRF.PermutationIndex) :
    PMF (Option (LazyOracle.State FixedIndex EncPRF.PermutationIndex)) :=
  let restored := Lamport.restore input labels
  (Kriterion.ArgoMAC.Phase3.Lazy.refillRun restored.input
      (openingQueriesM table restored.input restored.inputMac) oracle).bind fun ran =>
    match ran with
    | none => PMF.pure none
    | some ran => openedCont rows install table input labels target ran

/-- **The opened simulator** of a rows kernel and an installation: `I`'s stage 1, and `I`'s stage 2
with `openedOpening`. -/
def openedSimulator [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (rows : RowsKernel) (install : Installation) :
    LazyAbstractSimulator FixedIndex EncPRF.PermutationIndex Public where
  State := Stage1Source
  stage1 _ oracle :=
    idealSamplers.source.map (Option.map fun source => (source.publicValue, source, oracle))
  stage2 source input output oracle :=
    let labels := Lamport.selectedLabels (source.key.encode (BitInput.ofAffine input))
    match output with
    | none => PMF.pure (some (labels, oracle))
    | some target => (openedOpening rows install source.publicValue input labels target oracle).map
        (Option.map fun updated => (labels, updated))

/-! ### The three hybrids -/

/-- **`HW`**: the public-first game with the real output rows. -/
def publicFirstHybrid : HybridGame := fun adversary parameter scalar =>
  abstractIdealGame Scheme.scheme (openedSimulator (realRows scalar) skipInstallation) adversary
    parameter scalar ()

/-- **`H`**: as `HW`, with the digit rows drawn by the tail/head-clamp/lift sampler. -/
def openedHybrid : HybridGame := fun adversary parameter scalar =>
  abstractIdealGame Scheme.scheme (openedSimulator simulatedRows skipInstallation) adversary
    parameter scalar ()

/-- P4's opening continuation is `openedCont` at the simulator's rows and `I`'s installation. -/
theorem openedCont_simulated_abort [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (table : Public) (input : AffineInput)
    (labels : LamportSignature) (target : Point)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LazyOracle.State FixedIndex EncPRF.PermutationIndex × DesignatedRecord) :
    openedCont simulatedRows abortInstallation table input labels target ran
      = Kriterion.ArgoMAC.Phase3.Lazy.openingCont idealSamplers table input labels target ran := by
  unfold openedCont Kriterion.ArgoMAC.Phase3.Lazy.openingCont simulatedRows
    Kriterion.ArgoMAC.Phase3.Glue.openingLimbs
  simp only [PMF.bind_bind]
  refine congrArg _ (funext fun tail => ?_)
  cases tail with
  | none => simp
  | some tail =>
    simp only [PMF.bind_bind]
    refine congrArg _ (funext fun lift => ?_)
    cases lift with
    | none => simp
    | some lift => simp only [PMF.pure_bind]; rfl

/-- **`I^U` is the opened game at (`simulatedRows`, `abortInstallation`)**, so `H → I^U` changes the
designated installation only (skip against abort). -/
theorem idealUniformHybrid_eq_opened [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
    [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (adversary : PlanBAdversary Unit) (parameter : Nat)
    (scalar : NonZeroScalar) :
    Kriterion.ArgoMAC.Phase3.Lazy.idealUniformHybrid adversary parameter scalar
      = abstractIdealGame Scheme.scheme (openedSimulator simulatedRows abortInstallation) adversary
          parameter scalar () := by
  have same : Kriterion.ArgoMAC.Phase3.Lazy.refillSimulator idealSamplers
      = openedSimulator simulatedRows abortInstallation := by
    unfold Kriterion.ArgoMAC.Phase3.Lazy.refillSimulator openedSimulator
      Kriterion.ArgoMAC.Phase3.Glue.planBAbstractSimulator
    dsimp only
    congr 1
    funext source input output oracle
    unfold Kriterion.ArgoMAC.Phase3.Lazy.refillStage2
    cases output with
    | none => rfl
    | some target =>
      unfold Kriterion.ArgoMAC.Phase3.Lazy.refillOpening openedOpening
      dsimp only
      congr 2
      funext ran
      cases ran with
      | none => rfl
      | some ran => exact (openedCont_simulated_abort _ _ _ _ ran).symm
  unfold Kriterion.ArgoMAC.Phase3.Lazy.idealUniformHybrid
  rw [same]

end

end Kriterion.ArgoMAC.Security.Phase3
