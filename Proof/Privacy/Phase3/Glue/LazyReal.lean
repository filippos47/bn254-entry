/-
Phase 3 glue, step 2 (note C, T04; design note B, theorem 15 `real_eq_G0`): **the lazy real game
is the tape-sampled real game, exactly.**

The challenge scores `lazyRealGame coins garble encode adversary`: private coins, then the
garbler and both adversary stages against one shared *lazy* oracle. The Plan B hybrid chain
starts from the *tape-sampled* game `G0`: a uniform tape (coins and a complete eager oracle), the
garbler's `eval` on it, and both stages against the same eager oracle. This file proves the two
equal, with no error term:

* `tapeRealGame` is `G0` in the challenge's types: `realGame Scheme.scheme` over the uniform law
  on `Coins × Oracle`, with the handler `publicHandler Prod.snd`;
* `planB_lazy_real` : `lazyRealGame (uniformRandomTape Coins w) garbleProgram scheme.encode A n k aux
  = tapeRealGame A n k aux`, for every adversary (so in particular for
  `machineAdversary encoding M`). It is the baseline's `lazy_real_uniform` (ported in
  `OracleLaw.lean`) followed by `Programs.garbleProgram_correct` -- this is where the query
  program's correctness is consumed -- and the product form of the uniform tape;
* `tapeRealGame_eq_wire` : `G0` is also the old eager endpoint of the Plan B proof,
  `realGame Lamport.wireCircuit (uniformRandomTape Garbling.Randomness w) Garbling.oracleHandler`,
  through the randomness split of `RandomnessSplit.lean`.

Every statement takes its `Fintype`/`DecidableEq` instances as arguments, so it holds at the
`Fintype.ofFinite` / `Classical.decEq` instances `Solution.adaptivePrivacy` installs.
-/

import Construction.OraclePrograms
import Proof.Privacy.Phase3.Glue.RandomnessSplit
import Proof.Privacy.Phase3.Glue.OracleLaw

namespace Kriterion.ArgoMAC.Phase3.Glue

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.Scheme (Coins Oracle)

noncomputable section

/-- The adversaries of the Plan B games: public queries, affine input, Plan B public value,
508 Lamport blocks. -/
abbrev PlanBAdversary (Aux : Type) :=
  AdaptiveAdversary (publicOracleSpec PlanB.FixedIndex EncPRF.PermutationIndex) AffineInput
    PlanB.Public LamportSignature Aux

/-- **`G0`**, the tape-sampled real game in the challenge's types: a uniform (coins, oracle)
tape, the Plan B garbler on it, and both adversary stages against the tape's oracle. -/
def tapeRealGame [FieldCertificate] [GroupCertificate] [Fintype PlanB.FixedIndex]
    [Fintype EncPRF.PermutationIndex] [Fintype Coins] {Aux : Type}
    (adversary : PlanBAdversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) : PMF Bool :=
  realGame Scheme.scheme (fun _ => PMF.uniformOfFintype (Coins × Oracle)) (publicHandler Prod.snd)
    adversary parameter scalar auxiliary

/-- An eager run with the identity projection never changes its oracle state. -/
theorem eager_run_state {FixedIndex EncIndex Result : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (oracle : PublicOracle FixedIndex EncIndex) (result : Result × PublicOracle FixedIndex EncIndex)
    (member : result ∈ (program.run (publicHandler id) oracle).support) : result.2 = oracle := by
  rw [public_run_tape (project := id), PMF.support_map] at member
  obtain ⟨value, _, equal⟩ := member
  exact (congrArg Prod.snd equal).symm

/-- **Step 2: the lazy real game is `G0`, exactly.** -/
theorem planB_lazy_real [FieldCertificate] [GroupCertificate] [Fintype PlanB.FixedIndex]
    [Fintype EncPRF.PermutationIndex] [DecidableEq PlanB.FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] [Fintype Coins] {Aux : Type}
    (adversary : PlanBAdversary Aux) (witness : Coins) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) :
    lazyRealGame (uniformRandomTape Coins witness)
        (fun parameter scalar coins => (Programs.garbleProgram parameter scalar coins).toOracleProgram)
        Scheme.scheme.encode adversary parameter scalar auxiliary =
      tapeRealGame adversary parameter scalar auxiliary := by
  rw [lazy_real_uniform]
  simp only [uniformRandomTape_coins, Programs.garbleProgram_correct]
  unfold tapeRealGame realGame
  beta_reduce
  rw [← uniform_product (A := Coins) (B := Oracle), PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  apply PMF.bind_congr
  intro coins _
  apply PMF.bind_congr
  intro oracle _
  rw [public_run_tape (project := Prod.snd)]
  simp only [PMF.bind_map, Function.comp_def]
  apply PMF.bind_congr
  intro selected reached
  rw [public_run_tape (project := Prod.snd), eager_run_state _ _ _ reached]
  simp only [PMF.map_comp, Function.comp_def]

/-- **`G0` is the old eager endpoint.** The tape-sampled game in the challenge's types equals the
Plan B proof's eager real game on the whole tape `Garbling.Randomness`. -/
theorem tapeRealGame_eq_wire [FieldCertificate] [GroupCertificate] [Fintype PlanB.FixedIndex]
    [Fintype EncPRF.PermutationIndex] [Fintype Coins] [Fintype Garbling.Randomness] {Aux : Type}
    (adversary : PlanBAdversary Aux) (witness : Garbling.Randomness) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) :
    tapeRealGame adversary parameter scalar auxiliary =
      realGame Lamport.wireCircuit (uniformRandomTape Garbling.Randomness witness)
        Garbling.oracleHandler adversary parameter scalar auxiliary := by
  unfold tapeRealGame realGame
  rw [uniformRandomTape_randomness, ← uniform_equiv splitCoins.symm, PMF.bind_map]
  apply PMF.bind_congr
  rintro ⟨coins, oracle⟩ _
  simp only [Function.comp_apply, splitCoins_symm_apply, oracleHandler_eq]
  rw [public_run_tape (project := Prod.snd), public_run_tape (project := tapeOracle)]
  simp only [PMF.bind_map, Function.comp_def, tapeOracle_withOracle]
  apply PMF.bind_congr
  intro selected _
  rw [public_run_tape (project := Prod.snd), public_run_tape (project := tapeOracle)]
  simp only [PMF.map_comp, Function.comp_def, tapeOracle_withOracle]
  rfl

/-- The two steps together: the scored lazy game is the Plan B proof's old eager real game. -/
theorem planB_lazy_real_wire [FieldCertificate] [GroupCertificate] [Fintype PlanB.FixedIndex]
    [Fintype EncPRF.PermutationIndex] [DecidableEq PlanB.FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] [Fintype Coins] [Fintype Garbling.Randomness]
    {Aux : Type} (adversary : PlanBAdversary Aux) (witness : Coins)
    (tapeWitness : Garbling.Randomness) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) :
    lazyRealGame (uniformRandomTape Coins witness)
        (fun parameter scalar coins => (Programs.garbleProgram parameter scalar coins).toOracleProgram)
        Scheme.scheme.encode adversary parameter scalar auxiliary =
      realGame Lamport.wireCircuit (uniformRandomTape Garbling.Randomness tapeWitness)
        Garbling.oracleHandler adversary parameter scalar auxiliary := by
  rw [planB_lazy_real, tapeRealGame_eq_wire]

end

end Kriterion.ArgoMAC.Phase3.Glue
