/-
Phase 3 glue, step 3a: **the abstract half of `LazySimulatorProtocol.idealGame`.**

The library's ideal game runs a closed `BoundedMachine.Simulator` twice against the *shared*
lazy oracle (the adversary's queries are answered by `LazyOracle.run`, never by the simulator):

1. stage 1 from the request `[ff] ++ natural n ++ natural bytes`, then the byte parse
   `publicValue`;
2. stage 2 from `[ft] ++ affine u ++ output (f_k u)`, then the label parse `words 128 508`;

any `none` (fuel, parse, failed `program`, invalid point operation) makes the game return
`false`. The baseline splits this into an abstract PMF-level game and an exact machine law
(`CompiledAdaptiveGame.lazyCompiledIdealGame_eqStrict`). This file makes the split generic:

* `LazyAbstractSimulator` is a pair of PMF kernels over the lazy oracle state -- a stage-1 kernel
  producing the public value, a retained state and the oracle, and a stage-2 kernel producing the
  508 labels and the oracle -- each allowed to abort with `none`;
* `abstractIdealGame` is `LazySimulatorProtocol.idealGame` with the two kernels in place of the
  two machine runs;
* `machineAbstract` reads a closed machine as such a pair of kernels (run + parse), and
  `idealGame_eq_machineAbstract` proves the library's game **is** the abstract game of the
  machine's kernels -- so a machine law is a statement about kernels only;
* `abstractIdealGame_eq_of_simulation` compares two abstract simulators through a representation
  of retained states (the kernel-level form in which a machine law is proved).
-/

import Proof.Privacy.Phase3.Glue.LazyReal

namespace Kriterion.ArgoMAC.Phase3.Glue

open BN254 Cryptography GarbledCircuit

noncomputable section

/-- A PMF-level simulator on the shared lazy oracle: the abstract half of
`LazySimulatorProtocol.idealGame`. `none` is an abort, and the game then returns `false`. -/
structure LazyAbstractSimulator [FieldCertificate] (FixedIndex EncIndex Public : Type) where
  /-- The state retained from stage 1 to stage 2. -/
  State : Type
  /-- Stage 1: the public value, the retained state and the oracle. -/
  stage1 : Nat → LazyOracle.State FixedIndex EncIndex →
    PMF (Option (Public × State × LazyOracle.State FixedIndex EncIndex))
  /-- Stage 2: from the selected input and its output, the 508 labels and the oracle. -/
  stage2 : State → AffineInput → Option Point → LazyOracle.State FixedIndex EncIndex →
    PMF (Option (LamportSignature × LazyOracle.State FixedIndex EncIndex))

/-- **The abstract ideal game**: `LazySimulatorProtocol.idealGame` with the two kernels of an
abstract simulator in place of the two machine runs (and their parses). -/
def abstractIdealGame [FieldCertificate]
    {FixedIndex EncIndex Randomness Public Key Oracle Aux : Type}
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      Key LamportSignature Oracle)
    (simulator : LazyAbstractSimulator FixedIndex EncIndex Public)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedIndex EncIndex)
      AffineInput Public LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  let experiment : OptionT PMF Bool := do
    let (circuit, state, oracle) ← OptionT.mk (simulator.stage1 parameter LazyOracle.empty)
    let (selected, chosen) ←
      liftM (LazyOracle.run (adversary.chooseInput parameter circuit auxiliary) oracle)
    let (labels, updated) ← OptionT.mk
      (simulator.stage2 state selected.1 (scheme.function scalar selected.1) chosen)
    let (decision, _) ← liftM (LazyOracle.run
      (adversary.decide parameter circuit labels auxiliary selected.2) updated)
    pure decision
  experiment.run.map (fun result => result.getD false)

/-- A closed machine read as an abstract simulator: each stage is the machine run from the
protocol's request, followed by the protocol's parse. -/
def machineAbstract [FieldCertificate] {FixedIndex EncIndex Public : Type}
    [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (encoding : Encoding Public) (bytes : Nat) (machine : BoundedMachine.Simulator) :
    LazyAbstractSimulator FixedIndex EncIndex Public where
  State := BoundedMachine.Configuration (machine.size + 1)
  stage1 parameter oracle := OptionT.run (do
    let memory : BoundedMachine.Memory := { bits := fun stack =>
      if stack = 0 then [false, false] ++ SimulatorProtocol.natural parameter ++ SimulatorProtocol.natural bytes else [] }
    let (initial, oracle, _) ← OptionT.mk (machine.run machine.firstFuel ⟨0, memory⟩ oracle)
    let circuit ← OptionT.mk
      (PMF.pure (SimulatorProtocol.publicValue encoding bytes (initial.memory.bits 3)))
    pure (circuit, initial, oracle))
  stage2 initial input output oracle := OptionT.run (do
    let request := [false, true] ++ SimulatorProtocol.affine input ++ SimulatorProtocol.output output
    let memory := { initial.memory with
      bits := Function.update (Function.update initial.memory.bits 0 request) 3 [] }
    let (encoded, updated, _) ← OptionT.mk (machine.run machine.secondFuel ⟨0, memory⟩ oracle)
    let labels ← OptionT.mk (PMF.pure (SimulatorProtocol.words 128 508 (encoded.memory.bits 3)))
    pure (labels, updated))

/-- `OptionT.mk` undoes `OptionT.run`. -/
theorem optionT_mk_run {m : Type → Type} {α : Type} (x : OptionT m α) :
    OptionT.mk x.run = x := rfl

/-- **The library's ideal game is the abstract game of the machine's kernels**, exactly. -/
theorem idealGame_eq_machineAbstract [FieldCertificate]
    {FixedIndex EncIndex Randomness Public Key Oracle Aux : Type}
    [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      Key LamportSignature Oracle) (encoding : Encoding Public) (bytes : Nat)
    (machine : BoundedMachine.Simulator)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedIndex EncIndex)
      AffineInput Public LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    LazySimulatorProtocol.idealGame scheme encoding bytes machine adversary parameter scalar
        auxiliary =
      abstractIdealGame scheme (machineAbstract encoding bytes machine) adversary parameter scalar
        auxiliary := by
  unfold LazySimulatorProtocol.idealGame abstractIdealGame machineAbstract
  simp only [optionT_mk_run, bind_assoc, pure_bind]

/-- A mapped abort-or-value kernel is a bind followed by `pure`. -/
theorem optionT_mk_map {α β : Type} (distribution : PMF (Option α)) (f : α → β) :
    OptionT.mk (distribution.map (Option.map f)) =
      (OptionT.mk distribution >>= fun value => pure (f value) : OptionT PMF β) := by
  change _ = OptionT.mk (distribution >>= fun option => match option with
    | some value => (pure (f value) : OptionT PMF β).run
    | none => pure none)
  congr 1
  rw [PMF.monad_bind_eq_bind, ← PMF.bind_pure_comp]
  congr 1
  funext option
  cases option <;> rfl

/-- A bind out of an abort-or-value kernel only reads the values in its support. -/
theorem optionT_bind_congr {α β : Type} (distribution : PMF (Option α))
    (first second : α → OptionT PMF β)
    (agree : ∀ value, some value ∈ distribution.support → first value = second value) :
    (OptionT.mk distribution >>= first) = (OptionT.mk distribution >>= second) := by
  change OptionT.mk (distribution >>= fun option => match option with
      | some value => (first value).run
      | none => pure none) =
    OptionT.mk (distribution >>= fun option => match option with
      | some value => (second value).run
      | none => pure none)
  congr 1
  rw [PMF.monad_bind_eq_bind, PMF.monad_bind_eq_bind]
  apply PMF.bind_congr
  intro option member
  cases option with
  | none => rfl
  | some value =>
    change (first value).run = (second value).run
    rw [agree value ((PMF.mem_support_iff _ _).mpr member)]

/-- **Kernel-level comparison of abstract simulators.** If the second simulator's stage 1 is the
first's up to a representation of retained states, and its stage 2 agrees on every represented
stage-1 state in the support, the two abstract games are equal for every adversary. This is the
form in which a machine's exact law is proved (`idealGame_eq_machineAbstract` turns the library
game into the abstract game of the machine's kernels). -/
theorem abstractIdealGame_eq_of_simulation [FieldCertificate]
    {FixedIndex EncIndex Randomness Public Key Oracle Aux : Type}
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      Key LamportSignature Oracle)
    (first second : LazyAbstractSimulator FixedIndex EncIndex Public)
    (represent : first.State → second.State)
    (stage1 : ∀ parameter, second.stage1 parameter LazyOracle.empty =
      (first.stage1 parameter LazyOracle.empty).map
        (Option.map fun result => (result.1, represent result.2.1, result.2.2)))
    (stage2 : ∀ parameter result,
      some result ∈ (first.stage1 parameter LazyOracle.empty).support →
        ∀ input output oracle, second.stage2 (represent result.2.1) input output oracle =
          first.stage2 result.2.1 input output oracle)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedIndex EncIndex)
      AffineInput Public LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    abstractIdealGame scheme second adversary parameter scalar auxiliary =
      abstractIdealGame scheme first adversary parameter scalar auxiliary := by
  unfold abstractIdealGame
  rw [stage1, optionT_mk_map]
  simp only [bind_assoc, pure_bind]
  congr 2
  apply optionT_bind_congr
  intro result member
  simp only [stage2 parameter result member]

end

end Kriterion.ArgoMAC.Phase3.Glue
