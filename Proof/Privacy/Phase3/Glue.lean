/-
Phase 3 glue root (author P3): the pieces that connect the Plan B hybrid chain (P1) and the
bounded-machine simulator (P2) to the challenge's `GarbledCircuit.OracleAdaptivePrivacy`.

This root is the glue's **interface**: the randomness split, the oracle laws, the lazy real and
ideal games, the abstract simulator, the error budget and the chain assembly. None of it imports
the hybrid chain or the simulator machine. The two chain-end modules import the hybrid chain,
which itself imports this interface, so they sit outside this root. `Proof.Privacy` imports
`Glue.Final`, which imports `Glue.AbortBridge`:

* `Glue.AbortBridge`: P4's per-site abort bound (`Lazy.AbortPerQuery'`) as `AbortBound`;
* `Glue.Final`: `planB_oracleAdaptivePrivacy_of`, the assembly with every proved hop plugged in.
-/

import Proof.Privacy.Phase3.Glue.Uniform
import Proof.Privacy.Phase3.Glue.RandomnessSplit
import Proof.Privacy.Phase3.Glue.OracleLaw
import Proof.Privacy.Phase3.Glue.LazyReal
import Proof.Privacy.Phase3.Glue.LazyIdeal
import Proof.Privacy.Phase3.Glue.AbstractSimulator
import Proof.Privacy.Phase3.Glue.Budget
import Proof.Privacy.Phase3.Glue.Assembly
