/-
This file states the Plan B garbling scheme at the challenge's interface.

The pinned library (`aaf2789`) separates the private coins from the public oracle: `Garble`
receives `(coins, oracle)`, the evaluator receives the oracle, and the encoding key is whatever
the garbler hands to `Encode`. Plan B's `Garbling.Randomness` stores the three public tables
next to the private coins, so this file

* names the private part, `Coins` -- every field of a Plan B tape except the three tables;
* rebuilds a full tape from coins and an oracle, `Coins.withOracle`;
* keeps only the 508 Lamport label pairs as the encoding key (`InputMacKey`), because that is
  all `Encode` reads, and a query program cannot output the oracle;
* states `scheme`, the challenge-facing `GarbledCircuit`, as the existing Plan B garbler and
  evaluator run on `coins.withOracle oracle`.
-/

import Construction.Garbling
import Construction.ArgoMAC.Seed

namespace Kriterion.ArgoMAC.Scheme

open BN254 Cryptography

/-- The public oracle interface: fixed-key permutations, EncPRF permutations, the hash. -/
abbrev Oracle := PublicOracle PlanB.FixedIndex EncPRF.PermutationIndex

/-- The private coins of one garbling: a Plan B tape without its three public tables. -/
structure Coins where
  offsets : FieldMacToECMac.SuccessfulOffsets
  offsetsClamped : ∀ [FieldCertificate] [GroupCertificate], offsets.IsClamped
  pointRandomness : FieldMacToECMac.Randomness
  exceptionPad : FieldMacToECMac.ExceptionPad
  bridgeKey : BaseField
  curveMask : NonZeroBase
  curveR1 : BaseField
  curveR2 : BaseField
  inputZero : PlanB.Coord → Fin coordinateBitCount → Block
  inputDelta : PlanB.Coord → Block

/-- The Plan B tape made of these coins and this oracle. -/
def Coins.withOracle (coins : Coins) (oracle : Oracle) : Garbling.Randomness where
  offsets := coins.offsets
  offsetsClamped := coins.offsetsClamped
  pointRandomness := coins.pointRandomness
  exceptionPad := coins.exceptionPad
  bridgeKey := coins.bridgeKey
  curveMask := coins.curveMask
  curveR1 := coins.curveR1
  curveR2 := coins.curveR2
  fixedKeyOracle := oracle.1
  inputZero := coins.inputZero
  inputDelta := coins.inputDelta
  encPRFOracle := oracle.2.1
  hashOracle := oracle.2.2

/-- The private coins of a Plan B tape. -/
def Coins.ofRandomness (tape : Garbling.Randomness) : Coins where
  offsets := tape.offsets
  offsetsClamped := tape.offsetsClamped
  pointRandomness := tape.pointRandomness
  exceptionPad := tape.exceptionPad
  bridgeKey := tape.bridgeKey
  curveMask := tape.curveMask
  curveR1 := tape.curveR1
  curveR2 := tape.curveR2
  inputZero := tape.inputZero
  inputDelta := tape.inputDelta

/-- The 508 Lamport label pairs `(Z_j, Z_j xor Delta)` the coins carry. -/
def Coins.inputMacKey (coins : Coins) : InputMacKey := {
  x := Vector.ofFn fun position =>
    { falseLabel := coins.inputZero .x position
      trueLabel := coins.inputZero .x position ^^^ coins.inputDelta .x }
  y := Vector.ofFn fun position =>
    { falseLabel := coins.inputZero .y position
      trueLabel := coins.inputZero .y position ^^^ coins.inputDelta .y } }

/-- The label pairs do not depend on the oracle. -/
theorem Coins.withOracle_inputMacKey (coins : Coins) (oracle : Oracle) :
    (coins.withOracle oracle).inputMacKey = coins.inputMacKey := rfl

/-- The fixed witness the challenge's tape law needs. -/
def witness : Coins := Coins.ofRandomness (Seed.randomness 0)

/-! ### The coins are finite

Each instance is `Finite.of_injective` into a product of finite types; nothing is enumerated. -/

/-- A vector is determined by its entries. -/
local instance vectorFinite {α : Type} [Finite α] {count : Nat} : Finite (Vector α count) :=
  Finite.of_injective (fun values : Vector α count => fun index : Fin count => values[index])
    (by
      intro first second equal
      apply Vector.ext
      intro index bound
      exact congrFun equal ⟨index, bound⟩)

instance affineInputFinite : Finite AffineInput :=
  Finite.of_injective (fun input : AffineInput => (input.x, input.y)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance affineOffsetFinite : Finite FieldMacToECMac.AffineOffset :=
  Finite.of_injective (fun offset : FieldMacToECMac.AffineOffset => offset.coordinates) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance nonZeroBaseFinite : Finite NonZeroBase :=
  Finite.of_injective (fun value : NonZeroBase => value.value) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance xRandomnessFinite : Finite Biquadratic.XRandomness :=
  Finite.of_injective (fun value : Biquadratic.XRandomness => (value.r1, value.r2, value.r4)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance yRandomnessFinite : Finite Biquadratic.YRandomness :=
  Finite.of_injective
    (fun value : Biquadratic.YRandomness => (value.r2, value.r3, value.r4, value.r5)) (by
      intro first second equal
      cases first
      cases second
      simp_all)

instance zRandomnessFinite : Finite Biquadratic.ZRandomness :=
  Finite.of_injective (fun value : Biquadratic.ZRandomness => value.r1) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance rowRandomnessFinite : Finite FieldMacToECMac.RowRandomness :=
  Finite.of_injective
    (fun value : FieldMacToECMac.RowRandomness => (value.rho, value.x, value.y, value.z)) (by
      intro first second equal
      cases first
      cases second
      simp_all)

instance successfulOffsetsFinite : Finite FieldMacToECMac.SuccessfulOffsets :=
  Finite.of_injective
    (fun offsets : FieldMacToECMac.SuccessfulOffsets => (offsets.first, offsets.free)) (by
      intro first second equal
      cases first
      cases second
      simp_all)

/-- The data part of the coins: every field except the `Prop`. -/
abbrev CoinsData :=
  FieldMacToECMac.SuccessfulOffsets × FieldMacToECMac.Randomness ×
    FieldMacToECMac.ExceptionPad × BaseField × NonZeroBase × BaseField × BaseField ×
    (PlanB.Coord → Fin coordinateBitCount → Block) × (PlanB.Coord → Block)

/-- The coins' data part. -/
def Coins.data (coins : Coins) : CoinsData :=
  (coins.offsets, coins.pointRandomness, coins.exceptionPad, coins.bridgeKey, coins.curveMask,
    coins.curveR1, coins.curveR2, coins.inputZero, coins.inputDelta)

/-- `offsetsClamped` is a `Prop`, so the data part determines the coins. -/
theorem Coins.data_injective : Function.Injective Coins.data := by
  intro first second equal
  cases first
  cases second
  cases equal
  rfl

instance coinsFinite : Finite Coins :=
  Finite.of_injective Coins.data Coins.data_injective

/-! ### The scheme at the challenge's interface -/

variable [FieldCertificate] [GroupCertificate]

/-- **The Plan B scheme.** `Garble(n, k, (coins, oracle))` is the Plan B garbler on the tape
`coins.withOracle oracle`, with the 508 label pairs as the key; `Encode` selects one label per
input bit; `Evaluate` restores the internal labels and runs the Plan B evaluator. -/
def scheme :
    GarbledCircuit NonZeroScalar AffineInput (Option Point) (Coins × Oracle) PlanB.Public
      InputMacKey GarbledCircuit.LamportSignature Oracle where
  function scalar input := checkedScalarMultiplication scalar.value input
  garble _ scalar tape :=
    ((Garbling.garble construction scalar (tape.1.withOracle tape.2)).1, tape.1.inputMacKey)
  encode key input := Lamport.selectedLabels (key.encode (BitInput.ofAffine input))
  evaluate oracle table input labels :=
    some (Garbling.evaluate oracle table (Lamport.restore input labels))

end Kriterion.ArgoMAC.Scheme
