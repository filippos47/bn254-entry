/-
Phase 3 glue, step 1 (note C, T01): **the randomness split.**

A Plan B tape `Garbling.Randomness` is exactly a pair (private coins, public oracle):

* the oracle half is `(fixedKeyOracle, encPRFOracle, hashOracle)` -- `Scheme.Oracle`, i.e.
  `PublicOracle PlanB.FixedIndex EncPRF.PermutationIndex`;
* the coin half is every other field -- `Scheme.Coins`, the challenge's `Solution.Randomness`.

`splitCoins` is that equivalence (its inverse is the construction's own `Coins.withOracle`), and
`uniform_split` transports the uniform tape law through it: a uniform tape is a uniform coin
followed by an independent uniform oracle. The marginals `uniform_tapeOracle` (the challenge's
`StandardAssumptions` form) and `uniform_tapeCoins` follow.

Every statement takes its `Fintype` instances as arguments, so it applies at the
`Fintype.ofFinite` instances `Solution.adaptivePrivacy` installs; nothing here computes a
cardinality (the permutation families have `(2^128)!`-sized factors).
-/

import Construction.Scheme
import Solution
import Proof.Privacy.Phase3.Glue.Uniform

namespace Kriterion.ArgoMAC.Phase3.Glue

open BN254 Cryptography
open Kriterion.ArgoMAC.Scheme (Coins Oracle)

noncomputable section

/-- The public-oracle half of a Plan B tape. -/
def tapeOracle (tape : Garbling.Randomness) : Oracle :=
  (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)

/-- **The randomness split** `Garbling.Randomness ≃ PrivateCoins × PublicOracle`. -/
def splitCoins : Garbling.Randomness ≃ Coins × Oracle where
  toFun tape := (Coins.ofRandomness tape, tapeOracle tape)
  invFun pair := pair.1.withOracle pair.2
  left_inv tape := by cases tape; rfl
  right_inv pair := by
    rcases pair with ⟨coins, fixed, enc, hash⟩
    cases coins
    rfl

@[simp] theorem splitCoins_apply (tape : Garbling.Randomness) :
    splitCoins tape = (Coins.ofRandomness tape, tapeOracle tape) := rfl

@[simp] theorem splitCoins_symm_apply (coins : Coins) (oracle : Oracle) :
    splitCoins.symm (coins, oracle) = coins.withOracle oracle := rfl

/-- The oracle of a rebuilt tape is the oracle it was built from. -/
@[simp] theorem tapeOracle_withOracle (coins : Coins) (oracle : Oracle) :
    tapeOracle (coins.withOracle oracle) = oracle := rfl

/-- The coins of a rebuilt tape are the coins it was built from. -/
@[simp] theorem ofRandomness_withOracle (coins : Coins) (oracle : Oracle) :
    Coins.ofRandomness (coins.withOracle oracle) = coins := by
  cases coins
  rfl

/-- The construction's evaluation handler reads exactly the oracle half. -/
theorem oracleHandler_eq : Garbling.oracleHandler = publicHandler tapeOracle := rfl

/-- The coins are inhabited (the challenge's fixed witness). -/
instance coinsNonempty : Nonempty Coins := ⟨Scheme.witness⟩

/-- A Plan B tape is inhabited. -/
instance randomnessNonempty : Nonempty Garbling.Randomness := ⟨Seed.randomness 0⟩

/-- A Plan B tape is finite: it is a pair of finite types. -/
instance randomnessFinite : Finite Garbling.Randomness := Finite.of_equiv _ splitCoins.symm

/-- **The uniform-law transport.** A uniform tape is a uniform coin and an independent uniform
oracle. -/
theorem uniform_split [Fintype Garbling.Randomness] [Fintype Coins] [Fintype Oracle] :
    (PMF.uniformOfFintype Garbling.Randomness).map splitCoins =
      (PMF.uniformOfFintype Coins).bind fun coins =>
        (PMF.uniformOfFintype Oracle).map fun oracle => (coins, oracle) := by
  rw [uniform_equiv splitCoins, uniform_product]

/-- The inverse transport: a uniform coin completed by a uniform oracle is a uniform tape. -/
theorem uniform_withOracle [Fintype Garbling.Randomness] [Fintype Coins] [Fintype Oracle] :
    ((PMF.uniformOfFintype Coins).bind fun coins =>
        (PMF.uniformOfFintype Oracle).map fun oracle => coins.withOracle oracle) =
      PMF.uniformOfFintype Garbling.Randomness := by
  have law := congrArg (PMF.map splitCoins.symm) uniform_split
  rw [PMF.map_comp] at law
  simp only [Equiv.symm_comp_self, PMF.map_id] at law
  rw [law, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, splitCoins_symm_apply]

/-- The oracle marginal of the uniform tape is the uniform oracle (`StandardAssumptions`). -/
theorem uniform_tapeOracle [Fintype Garbling.Randomness] [Fintype Coins] [Fintype Oracle] :
    (PMF.uniformOfFintype Garbling.Randomness).map tapeOracle = PMF.uniformOfFintype Oracle := by
  have law := congrArg (PMF.map Prod.snd) uniform_split
  rw [PMF.map_comp, uniform_product, uniform_map_snd] at law
  exact law

/-- The coin marginal of the uniform tape is the uniform coin. -/
theorem uniform_tapeCoins [Fintype Garbling.Randomness] [Fintype Coins] [Fintype Oracle] :
    (PMF.uniformOfFintype Garbling.Randomness).map Coins.ofRandomness =
      PMF.uniformOfFintype Coins := by
  have law := congrArg (PMF.map Prod.fst) uniform_split
  rw [PMF.map_comp, uniform_product, uniform_map_fst] at law
  exact law

/-- The tape law of the old eager real game satisfies the challenge's `StandardAssumptions`. -/
theorem standardAssumptions [Fintype PlanB.FixedIndex] [Fintype EncPRF.PermutationIndex]
    [Fintype Garbling.Randomness] [Fintype Coins] (witness : Garbling.Randomness) :
    Assumptions.StandardAssumptions PlanB.FixedIndex EncPRF.PermutationIndex Garbling.Randomness
      witness tapeOracle := by
  rw [Assumptions.StandardAssumptions, uniformTape_eq]
  exact uniform_tapeOracle

/-- The challenge's coin tape is the uniform coin law, at any `Fintype` instance. -/
theorem uniformRandomTape_coins [Fintype Coins] (witness : Coins) (parameter : Nat) :
    uniformRandomTape Coins witness parameter = PMF.uniformOfFintype Coins := by
  rw [uniformRandomTape, uniformTape_eq]

/-- The old eager game's tape law is the uniform tape, at any `Fintype` instance. -/
theorem uniformRandomTape_randomness [Fintype Garbling.Randomness]
    (witness : Garbling.Randomness) (parameter : Nat) :
    uniformRandomTape Garbling.Randomness witness parameter =
      PMF.uniformOfFintype Garbling.Randomness := by
  rw [uniformRandomTape, uniformTape_eq]

end

end Kriterion.ArgoMAC.Phase3.Glue
