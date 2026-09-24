/-
**Phase 3, public-first — the hop `G1U → HW`: the Glue's `publicFirst` field, and why its constant
carries the exceptional mass.**

**The field** (`planB_publicFirst`, §5): `Glue.JointExactnessBound.publicFirst` at `planBHybrids`,
i.e. (by `coreUntilBad_iff`) for every adversary below `2^100` queries

`advantage(G1U, HW) ≤ stageOneHitError q₁ + exceptionalError + maskSwapError + coincidenceError`.

It is proved along the designed route (`LiftHop.planB_publicFirst_of_designed`):

* **`G1U → G1U°`** (identical until a coincidence) costs the coincidence mass, at most
  `coincidenceError = 2^16/2^128` (`LawsGuess.coincidenceGuess`, through
  `LiftGuess.coincidenceBound_of_guess`);
* **`G1U° → HW`** is the overlap with the middle game `M'` of the designed shadow: its F4 lift from
  the two laws (`designedLaws`: `LawOff` off the curve, `LawOn` on it), its flag mass from P1k's
  bounds (`designedBounds`: `4q₁/2^128 + 182/(r−1)`), and its two tape readings within the curve
  lanes' share of the mask swap (`LiftTV`, `LiftHop.curveSwapError_le`: `≤ maskSwapError`).

`LawsGuess.planB_publicFirst_of_laws_bounds` assembles the three.

**Why `exceptionalError` (§1–§4, side results off the chain).** The bare stage-1 constant fails.
By `coreUntilBad_iff`, `GameCoreUntilBad G1U HW (fun q₁ _ => 4q₁/2^128)` would be the bound
`advantage(G1U, HW) ≤ 4q₁/2^128`, and at **`q₁ = 0`** it is exact equality of the two games
(`publicFirst_zeroFirst_exact`, `publicFirst_silent_exact`): an adversary that makes no stage-1
query may do anything in stage 2.

**The distinguisher.** Stage 1: output a fixed valid input `u₀`, no query. Stage 2: evaluate as the
honest evaluator does up to the gadget (system A, the bridge hash, the pads `evalPadsM`), read digit
`d`'s gadget mask on the transformed labels (`gadgetMaskM d`, 508 fixed-key queries at
`FixedIndex.gadget d …`), unlock slot `exceptionIndex u₀` of the published entry
(`Exception.unlock`), and output `true` iff the unlocked digit is `k_d` (a nonzero digit of the
scalar; the hop bound quantifies the adversary before the scalar, so the adversary may know it).

* **`G1U`** (`hiddenDeletedHybrid`): the garbler's gadget queries of digit `d` are
  `gadgetMaskM d (transformKey.encodeAffine exc)` with `exc = exceptionalInput φ K_d`
  (`garbleEntryM`). When `u₀ = exc`, the evaluator's reach (`reachTranscript`, i.e. `onCurveM`,
  which runs `unlockM`) asks exactly those queries, so all 508 of them are **visible** and
  installed with the tape's answers (`visibleEntries`; there is no differing position to hide). The
  adversary's mask is then the garbler's, and the unlocked digit is `k_d` with certainty
  (`garbleEntry_unlock_exceptional`).
  When `u₀ ≠ exc`, the slot is a pad byte (a uniform coin) or the written byte behind a hidden
  Davies–Meyer value (a differing position, never installed): the unlocked byte is uniform.
* **`HW`** (`publicFirstHybrid`): the published entry is `Stage1Source.exception`, uniform and
  never read by the simulator (`openedOpening_exception`: the opening reads the table only through
  its rows), and the opening (`openingQueriesM`: system A, the bridge hash, the pads, system B)
  never touches a gadget index, so the mask is a fresh lazy digest: the unlocked byte is uniform,
  and the digit is `k_d` with mass `1/256`.

So the advantage is `(255/256) · Pr[u₀ = exceptionalInput φ K_d]` (`gadget_counterShape`), and that
mass is positive: `K_d` is the construction's offset (a free tail point, or the clamped head) and
`u₀ = exceptionalInput φ K_d` iff `transformedInput φ u₀ = K_d`
(`Exception.exceptionalInput_transform`), i.e. iff digit `d` **doubles** at `u₀` (P1's
`trueRow_eq`: the true row is then `(0,0,0)`). The bare constant at `q₁ = 0` is `0`
(`stageOneHitError_zero`), so it fails (`gadget_counterShape_refutes`).

**Where the chain charges it.** The gadget changes from real to lazy in `G1U → HW`; `HW → H`
(`OpeningBound`) has the lazy gadget on both sides. Under the public-first coupling (`K` independent
of the view, P1's F4) the two games' doubling events coincide, and they differ only on it, so this
hop carries the doubling mass itself: in the model the extra term is exactly the exceptional mass
(`gadget_honest`), `ε_exc ≤ 182/#Point ≤ 182/(r−1)` (P1's `doubling_mass_le`/
`bn254_doubling_real_le`, `scalarFieldModulus_le_card_point`), the field's `exceptionalError`
(`≈ 2^-246`). §4 shows that the flag must be the whole reveal event, not the doubling event alone.
-/

import Proof.Privacy.Phase3.Hybrids
import Proof.Privacy.Phase3.UntilBadIff
import Proof.Privacy.Phase3.PublicFirst.StageOne
import Proof.Privacy.Phase3.PublicFirst.Count
import Proof.Privacy.Phase3.PublicFirst.FullRel
import Proof.Privacy.Phase3.PublicFirst.Middle
import Proof.Privacy.Phase3.PublicFirst.Mismatch
import Proof.Privacy.Phase3.PublicFirst.Doubling
import Proof.Privacy.Phase3.PublicFirst.MiddleOff
import Proof.Privacy.Phase3.PublicFirst.FlagBound
import Proof.Privacy.Phase3.PublicFirst.Shadow
import Proof.Privacy.Phase3.PublicFirst.Stored
import Proof.Privacy.Phase3.PublicFirst.BoundsRevealBound
import Proof.Privacy.Phase3.PublicFirst.BoundsEncRun
import Proof.Privacy.Phase3.PublicFirst.BoundsDesigned
import Proof.Privacy.Phase3.PublicFirst.BoundsPerPair
import Proof.Privacy.Phase3.PublicFirst.LiftGuess
import Proof.Privacy.Phase3.PublicFirst.LawsPrivate
import Proof.Privacy.Phase3.PublicFirst.LawsGuess
import Proof.Privacy.Phase3.PublicFirst.LawsOnReach
import Proof.Privacy.Phase3.PublicFirst.LawsOnOpening
import Proof.Privacy.Phase3.PublicFirst.LawsOnCJoint
import Proof.Privacy.Phase3.PublicFirst.LawsOff
import Proof.Privacy.Phase3.PublicFirst.LawsOnEFinal

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary atSolution GameCoreUntilBad stageOneHitError)
open scoped ENNReal

noncomputable section

/-! ### 1. What the target asks at `q₁ = 0`: exact equality -/

/-- `L2(0) = 0`. -/
theorem stageOneHitError_zero : stageOneHitError 0 = 0 := by
  simp [stageOneHitError]

/-- Two `PMF Bool` at advantage `≤ 0` are equal. -/
theorem pmf_bool_eq_of_advantage_nonpos {first second : PMF Bool}
    (bound : Assumptions.advantage first second ≤ 0) : first = second := by
  apply pmf_bool_ext
  have zero : |(first true).toReal - (second true).toReal| = 0 :=
    le_antisymm bound (abs_nonneg _)
  have same : (first true).toReal = (second true).toReal := sub_eq_zero.mp (abs_eq_zero.mp zero)
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp same

/-- **At `q₁ = 0` the target is exact equality of `G1U` and `HW`.** -/
theorem publicFirst_zeroFirst_exact
    (target : GameCoreUntilBad hiddenDeletedHybrid publicFirstHybrid fun first _ =>
      stageOneHitError first)
    (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar)
    (noFirst : adversary.firstQueryBudget parameter = 0)
    (small : adversary.secondQueryBudget parameter < 2 ^ 100) :
    atSolution hiddenDeletedHybrid field group adversary parameter scalar
      = atSolution publicFirstHybrid field group adversary parameter scalar := by
  have hop := target field group adversary parameter scalar (by omega)
  rw [coreUntilBad_iff] at hop
  simp only [noFirst, stageOneHitError_zero] at hop
  exact pmf_bool_eq_of_advantage_nonpos hop

/-- **A silent adversary**: stage 1 outputs a fixed input with no query (budget `0`); stage 2 is any
program. -/
def silentAdversary (input : AffineInput) (budget : ℕ)
    (decide : ℕ → Public → LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget) :
    PlanBAdversary Unit where
  State := Unit
  firstQueryBudget _ := 0
  secondQueryBudget _ := budget
  chooseInput _ _ _ := .pure (PMF.pure (input, ()))
  decide parameter table labels _ _ := decide parameter table labels

/-- **The target forces `G1U = HW` against every silent adversary.** -/
theorem publicFirst_silent_exact
    (target : GameCoreUntilBad hiddenDeletedHybrid publicFirstHybrid fun first _ =>
      stageOneHitError first)
    (field : FieldCertificate) (group : @GroupCertificate field) (input : AffineInput)
    (budget : ℕ) (small : budget < 2 ^ 100)
    (decide : ℕ → Public → LamportSignature →
      OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Bool budget)
    (parameter : ℕ) (scalar : NonZeroScalar) :
    atSolution hiddenDeletedHybrid field group (silentAdversary input budget decide) parameter scalar
      = atSolution publicFirstHybrid field group (silentAdversary input budget decide) parameter
          scalar :=
  publicFirst_zeroFirst_exact target field group _ parameter scalar rfl small

/-! ### 2. The construction's gadget at the exceptional input -/

/-- **The real gadget unlocks the digit at the exceptional input**: with the garbler's own
permutations (the visible, installed entries of `G1U` when `u = exc`) the evaluator's mask is the
garbler's, and the written slot returns `k_d`. -/
theorem garbleEntry_unlock_exceptional (perms : FieldMacToECMac.GadgetPermutations)
    (output : Fin FieldMacToECMac.outputMacCount) (key : FieldMacToECMac.OutputKey)
    (inputKey : InputMacKey) (pad : Exception.Entry) (phi : BaseField)
    (selected : digitEndomorphismBase key.digit = some phi) :
    Exception.unlock
        (FieldMacToECMac.gadgetMask perms output
          (inputKey.encodeAffine (Exception.exceptionalInput phi key.offset.coordinates)))
        (FieldMacToECMac.garbleEntry perms output key inputKey pad)
        (Exception.exceptionalInput phi key.offset.coordinates)
      = key.digit := by
  simp only [FieldMacToECMac.garbleEntry, selected]
  exact Exception.unlock_writeEntry _ _ _ _

/-- **`HW` never reads the published gadget**: its opening (the refill run of `openingQueriesM`,
the rows kernel, the collector solve on `evaluateHomogeneous`, the installation) is the same for
every value of the table's `exception` field. So in `HW` the published gadget bytes are read by the
adversary only. -/
theorem openedOpening_exception [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (rows : RowsKernel) (install : Installation)
    (table : Public) (gadget : Vector Exception.Entry digitCount) (input : AffineInput)
    (labels : LamportSignature) (target : Point)
    (oracle : LazyOracle.State FixedIndex EncPRF.PermutationIndex) :
    openedOpening rows install { table with exception := gadget } input labels target oracle
      = openedOpening rows install table input labels target oracle := rfl

/-- A nonzero digit has exactly one code. -/
theorem digitOfCode_eq_iff {digit : Digit} (nonzero : digit ≠ .zero) (code : BitVec 8) :
    Exception.digitOfCode code = digit ↔ code = Exception.digitCode digit := by
  constructor
  · intro decoded
    unfold Exception.digitOfCode at decoded
    split at decoded <;> subst decoded
    all_goals first
      | exact absurd rfl nonzero
      | (apply BitVec.eq_of_toNat_eq; simp_all [Exception.digitCode])
  · rintro rfl
    exact Exception.digitOfCode_digitCode digit

/-! ### 3. The counter-shape: the gadget coordinate of `G1U` and of `HW`

The model keeps the construction's own byte code (`Exception.digitOfCode`) and isolates the one
random fact the two games disagree on: whether the hidden offset makes the selected input the
exceptional one. -/

/-- A uniform gadget byte. -/
def uniformByte : PMF (BitVec 8) := PMF.uniformOfFintype (BitVec 8)

theorem card_byte : Fintype.card (BitVec 8) = 256 :=
  (Fintype.card_congr (⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩ :
    BitVec 8 ≃ Fin (2 ^ 8))).trans (Fintype.card_fin _)

/-- The digit unlocked from a uniform slot byte under a mask. -/
def unlockUniform (mask : BitVec 8) : PMF Digit :=
  uniformByte.map fun byte => Exception.digitOfCode (byte ^^^ mask)

/-- **`HW`'s gadget coordinate**: a uniform published slot behind a fresh mask unlocks a nonzero
digit with mass `1/256`. -/
theorem unlockUniform_apply (mask : BitVec 8) {digit : Digit} (nonzero : digit ≠ .zero) :
    unlockUniform mask digit = (256 : ℝ≥0∞)⁻¹ := by
  classical
  unfold unlockUniform uniformByte
  rw [PMF.map_apply, tsum_eq_single (Exception.digitCode digit ^^^ mask)]
  · rw [if_pos, PMF.uniformOfFintype_apply, card_byte]
    · simp
    · rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, Exception.digitOfCode_digitCode]
  · intro byte different
    refine if_neg fun same => different ?_
    have code := (digitOfCode_eq_iff nonzero _).mp same.symm
    rw [← code, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- **`G1U`'s gadget coordinate**: when the hidden offset makes the selection exceptional, the
installed entries unlock the digit (`garbleEntry_unlock_exceptional`); otherwise the slot is a
uniform byte. -/
def g1uUnlock {X : Type} (offsetLaw : PMF X) (exceptional : X → Prop) [DecidablePred exceptional]
    (digit : Digit) (mask : BitVec 8) : PMF Digit :=
  offsetLaw.bind fun offset => if exceptional offset then PMF.pure digit else unlockUniform mask

/-- The distinguisher: is the unlocked digit `k_d`? -/
def unlocks (digit : Digit) (law : PMF Digit) : PMF Bool :=
  law.map fun unlocked => decide (unlocked = digit)

theorem unlocks_true (digit : Digit) (law : PMF Digit) : unlocks digit law true = law digit := by
  classical
  unfold unlocks
  rw [PMF.map_apply, tsum_eq_single digit]
  · simp
  · intro other different
    exact if_neg fun same => different (of_decide_eq_true same.symm)

/-- The exceptional mass. -/
def exceptionalMass {X : Type} (offsetLaw : PMF X) (exceptional : X → Prop) : ℝ≥0∞ :=
  offsetLaw.toOuterMeasure {offset | exceptional offset}

theorem g1uUnlock_apply {X : Type} (offsetLaw : PMF X) (exceptional : X → Prop)
    [DecidablePred exceptional] (mask : BitVec 8) {digit : Digit} (nonzero : digit ≠ .zero) :
    g1uUnlock offsetLaw exceptional digit mask digit
      = exceptionalMass offsetLaw exceptional
        + offsetLaw.toOuterMeasure {offset | ¬ exceptional offset} * (256 : ℝ≥0∞)⁻¹ := by
  classical
  unfold g1uUnlock exceptionalMass
  rw [PMF.bind_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  refine tsum_congr fun offset => ?_
  by_cases hit : exceptional offset
  · simp [hit, Set.indicator]
  · simp [hit, Set.indicator, unlockUniform_apply mask nonzero]

theorem exceptionalMass_add {X : Type} (offsetLaw : PMF X) (exceptional : X → Prop) :
    exceptionalMass offsetLaw exceptional + offsetLaw.toOuterMeasure {offset | ¬ exceptional offset}
      = 1 := by
  classical
  unfold exceptionalMass
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add, ← offsetLaw.tsum_coe]
  refine tsum_congr fun offset => ?_
  by_cases hit : exceptional offset <;> simp [hit, Set.indicator]

/-- **The counter-shape.** Against the silent distinguisher the two gadget coordinates are at
advantage exactly `(255/256) · Pr[exceptional]`. -/
theorem gadget_counterShape {X : Type} (offsetLaw : PMF X) (exceptional : X → Prop)
    [DecidablePred exceptional] (mask mask' : BitVec 8) {digit : Digit} (nonzero : digit ≠ .zero) :
    Assumptions.advantage (unlocks digit (g1uUnlock offsetLaw exceptional digit mask))
        (unlocks digit (unlockUniform mask'))
      = (exceptionalMass offsetLaw exceptional).toReal * (255 / 256) := by
  unfold Assumptions.advantage
  rw [unlocks_true, unlocks_true, g1uUnlock_apply offsetLaw exceptional mask nonzero,
    unlockUniform_apply mask' nonzero]
  set hit := exceptionalMass offsetLaw exceptional
  set miss := offsetLaw.toOuterMeasure {offset | ¬ exceptional offset}
  have total : hit + miss = 1 := exceptionalMass_add offsetLaw exceptional
  have hitTop : hit ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (total ▸ le_self_add)
  have missTop : miss ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (total ▸ le_add_self)
  have totalReal : hit.toReal + miss.toReal = 1 := by
    rw [← ENNReal.toReal_add hitTop missTop, total, ENNReal.toReal_one]
  have inverse : ((256 : ℝ≥0∞)⁻¹).toReal = 1 / 256 := by
    rw [ENNReal.toReal_inv]
    norm_num
  rw [ENNReal.toReal_add hitTop (ENNReal.mul_ne_top missTop (by norm_num)),
    ENNReal.toReal_mul, inverse]
  have hitNonneg : 0 ≤ hit.toReal := ENNReal.toReal_nonneg
  have missEq : miss.toReal = 1 - hit.toReal := by linarith
  rw [missEq]
  rw [show hit.toReal + (1 - hit.toReal) * (1 / 256) - 1 / 256 = hit.toReal * (255 / 256) by ring]
  exact abs_of_nonneg (by positivity)

/-- **The counter-shape refutes `L2` at `q₁ = 0`**: a positive exceptional mass is a positive
advantage, while the target allows `stageOneHitError 0 = 0`. -/
theorem gadget_counterShape_refutes {X : Type} (offsetLaw : PMF X) (exceptional : X → Prop)
    [DecidablePred exceptional] (mask mask' : BitVec 8) {digit : Digit} (nonzero : digit ≠ .zero)
    (positive : 0 < exceptionalMass offsetLaw exceptional) :
    ¬ Assumptions.advantage (unlocks digit (g1uUnlock offsetLaw exceptional digit mask))
        (unlocks digit (unlockUniform mask')) ≤ stageOneHitError 0 := by
  rw [gadget_counterShape offsetLaw exceptional mask mask' nonzero, stageOneHitError_zero, not_le]
  have finite : exceptionalMass offsetLaw exceptional ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      ((exceptionalMass_add offsetLaw exceptional) ▸ le_self_add)
  have realPositive : 0 < (exceptionalMass offsetLaw exceptional).toReal :=
    ENNReal.toReal_pos positive.ne' finite
  positivity

/-- **The honest constant, in the model**: the extra term is at most the exceptional mass (the
doubling mass, `≤ 182/#Point`). -/
theorem gadget_honest {X : Type} (offsetLaw : PMF X) (exceptional : X → Prop)
    [DecidablePred exceptional] (mask mask' : BitVec 8) {digit : Digit} (nonzero : digit ≠ .zero) :
    Assumptions.advantage (unlocks digit (g1uUnlock offsetLaw exceptional digit mask))
        (unlocks digit (unlockUniform mask')) ≤ (exceptionalMass offsetLaw exceptional).toReal := by
  rw [gadget_counterShape offsetLaw exceptional mask mask' nonzero]
  have nonneg : 0 ≤ (exceptionalMass offsetLaw exceptional).toReal := ENNReal.toReal_nonneg
  linarith

end

end Kriterion.ArgoMAC.Security.Phase3

/-! ### 4. P1e: the plan's flag is too small — the collision counter-shape, in the model

On the construction, at a position whose two Even–Mansour pads differ by `Δ`
(`π_i(k₁) ⊕ π_i(k₁ ⊕ 1) = Δ`: the whitening key `k₂` cancels) the two gadget labels coincide, so an
input `u` that differs from `exc_d` only at such positions makes all of digit `d`'s gadget queries
visible in `G1U` and unlocks `k_d`. In the
gadget model of §3 the reveal event is then a predicate `exceptional` strictly larger than the
doubling event. P1d's plan flags only the doubling event (and stage-1 touches, none at `q₁ = 0`),
and **such a flagged game is not below `G1U`** (`plan_not_flagMono`): on `exceptional ∧ ¬ doubling`
the plan's game keeps the uniform slot, while `G1U` reveals the digit, so the plan's flag-down mass
of `false` exceeds `G1U`'s. The correct flag is the whole reveal event (`fixed_below`, `fixed_mono`):
the honest constant does not move (the true doubling mass is `≈ 91/#Point`, half of `182/(r−1)`),
but `M`'s flag mass must be bounded by a doubling bound sharper than P1's `182/#Point`, whose slack
below `182/(r−1)` is only `182/(r(r−1)) ≈ 2^-500`. -/

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open scoped ENNReal

noncomputable section

theorem toOuterMeasure_le_one {α : Type} (law : PMF α) (set : Set α) : law.toOuterMeasure set ≤ 1 := by
  rw [PMF.toOuterMeasure_apply]
  exact le_trans (ENNReal.tsum_le_tsum fun x => Set.indicator_le_self set law x)
    (le_of_eq law.tsum_coe)

/-- A flagged gadget coordinate: flag an event of the offsets, otherwise the uniform slot. -/
def flaggedGadget {X : Type} (offsetLaw : PMF X) (flag : X → Prop) [DecidablePred flag]
    (digit : Digit) (mask : BitVec 8) : PMF (Option Bool) :=
  offsetLaw.bind fun offset => if flag offset then PMF.pure none
    else (unlocks digit (unlockUniform mask)).map some

theorem unlocks_uniform_false (mask : BitVec 8) {digit : Digit} (nonzero : digit ≠ .zero) :
    unlocks digit (unlockUniform mask) false = 1 - (256 : ℝ≥0∞)⁻¹ := by
  rw [pmf_bool_false, unlocks_true, unlockUniform_apply mask nonzero]

theorem flaggedGadget_some {X : Type} (offsetLaw : PMF X) (flag : X → Prop) [DecidablePred flag]
    (digit : Digit) (mask : BitVec 8) (b : Bool) :
    flaggedGadget offsetLaw flag digit mask (some b)
      = offsetLaw.toOuterMeasure {offset | ¬ flag offset} * unlocks digit (unlockUniform mask) b := by
  classical
  unfold flaggedGadget
  rw [PMF.bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun offset => ?_
  by_cases hit : flag offset
  · simp [hit, Set.indicator]
  · simp [hit, Set.indicator]

theorem mass_not_split {X : Type} (offsetLaw : PMF X) (small large : X → Prop)
    (sub : ∀ offset, small offset → large offset) :
    offsetLaw.toOuterMeasure {offset | ¬ small offset}
      = offsetLaw.toOuterMeasure {offset | ¬ large offset}
        + offsetLaw.toOuterMeasure {offset | large offset ∧ ¬ small offset} := by
  classical
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_add]
  refine tsum_congr fun offset => ?_
  by_cases hs : small offset
  · simp [hs, sub offset hs, Set.indicator]
  · by_cases hl : large offset <;> simp [hs, hl, Set.indicator]

/-- **The plan's flag is too small.** If the reveal event of `G1U`'s gadget is strictly larger (in
mass) than the flagged doubling event, the plan's flagged game is not below `G1U`. -/
theorem plan_not_flagMono {X : Type} (offsetLaw : PMF X) (doubling exceptional : X → Prop)
    [DecidablePred doubling] [DecidablePred exceptional]
    (sub : ∀ offset, doubling offset → exceptional offset)
    (extra : 0 < offsetLaw.toOuterMeasure {offset | exceptional offset ∧ ¬ doubling offset})
    (mask mask' : BitVec 8) {digit : Digit} (nonzero : digit ≠ .zero) :
    ¬ FlagMono ((unlocks digit (g1uUnlock offsetLaw exceptional digit mask)).map some)
        (flaggedGadget offsetLaw doubling digit mask') := by
  intro mono
  have atFalse := mono false
  rw [flaggedGadget_some, unlocks_uniform_false mask' nonzero, map_some_apply, pmf_bool_false,
    unlocks_true, g1uUnlock_apply offsetLaw exceptional mask nonzero,
    mass_not_split offsetLaw doubling exceptional sub] at atFalse
  set a := exceptionalMass offsetLaw exceptional
  set b := offsetLaw.toOuterMeasure {offset | ¬ exceptional offset}
  set e := offsetLaw.toOuterMeasure {offset | exceptional offset ∧ ¬ doubling offset}
  have total : a + b = 1 := exceptionalMass_add offsetLaw exceptional
  have aTop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (total ▸ le_self_add)
  have bTop : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (total ▸ le_add_self)
  have eTop : e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (toOuterMeasure_le_one _ _)
  have cTop : (256 : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have cLe : (256 : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr (by norm_num)
  have innerLe : a + b * (256 : ℝ≥0∞)⁻¹ ≤ 1 := by
    calc a + b * 256⁻¹ ≤ a + b * 1 := add_le_add le_rfl (mul_le_mul' le_rfl cLe)
      _ = 1 := by rw [mul_one, total]
  have real := ENNReal.toReal_mono (ENNReal.sub_ne_top ENNReal.one_ne_top) atFalse
  rw [ENNReal.toReal_mul, ENNReal.toReal_add bTop eTop, ENNReal.toReal_sub_of_le cLe ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le innerLe ENNReal.one_ne_top,
    ENNReal.toReal_add aTop (ENNReal.mul_ne_top bTop cTop), ENNReal.toReal_mul,
    ENNReal.toReal_one] at real
  have totalReal : a.toReal + b.toReal = 1 := by
    rw [← ENNReal.toReal_add aTop bTop, total, ENNReal.toReal_one]
  have ePos : 0 < e.toReal := ENNReal.toReal_pos extra.ne' eTop
  have cReal : ((256 : ℝ≥0∞)⁻¹).toReal = 1 / 256 := by
    rw [ENNReal.toReal_inv]; norm_num
  rw [cReal] at real
  nlinarith

/-- **The corrected flag in the model**: flagging the whole reveal event gives a game below `G1U`'s
gadget coordinate … -/
theorem fixed_mono {X : Type} (offsetLaw : PMF X) (exceptional : X → Prop)
    [DecidablePred exceptional] (mask : BitVec 8) (digit : Digit) :
    FlagMono ((unlocks digit (g1uUnlock offsetLaw exceptional digit mask)).map some)
      (flaggedGadget offsetLaw exceptional digit mask) := by
  classical
  intro b
  rw [flaggedGadget_some, map_some_apply]
  unfold unlocks g1uUnlock
  rw [PMF.map_bind, PMF.bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun offset => ?_
  by_cases hit : exceptional offset
  · simp [hit, Set.indicator]
  · simp only [hit, if_false, Set.indicator, Set.mem_ofPred_eq, not_false_eq_true, if_true]
    rfl

/-- … and below the uniform slot of `HW`, with flag mass exactly the reveal mass. -/
theorem fixed_below {X : Type} (offsetLaw : PMF X) (exceptional : X → Prop)
    [DecidablePred exceptional] (mask : BitVec 8) (digit : Digit) :
    Below (unlocks digit (unlockUniform mask)) (flaggedGadget offsetLaw exceptional digit mask) ∧
      flaggedGadget offsetLaw exceptional digit mask none = exceptionalMass offsetLaw exceptional := by
  classical
  constructor
  · intro b
    rw [flaggedGadget_some]
    calc offsetLaw.toOuterMeasure {offset | ¬ exceptional offset} * unlocks digit (unlockUniform mask) b
        ≤ 1 * unlocks digit (unlockUniform mask) b :=
          mul_le_mul' (toOuterMeasure_le_one _ _) le_rfl
      _ = _ := one_mul _
  · unfold flaggedGadget exceptionalMass
    rw [PMF.bind_apply, PMF.toOuterMeasure_apply]
    refine tsum_congr fun offset => ?_
    by_cases hit : exceptional offset
    · simp [hit, Set.indicator]
    · simp [hit, Set.indicator]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst

/-! ### 5. The Glue's `publicFirst` field -/

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

/-- **The Glue's `publicFirst` field, real**: `G1U → HW` at
`stageOneHitError q₁ + exceptionalError + maskSwapError + coincidenceError`, from the two laws
(`designedLaws`) and P1k's bounds (`designedBounds`). -/
theorem planB_publicFirst :
    Kriterion.ArgoMAC.Phase3.Glue.GameCoreUntilBad
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.hiddenDeleted
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.publicFirst fun first _ =>
        Kriterion.ArgoMAC.Phase3.Glue.stageOneHitError first +
          Kriterion.ArgoMAC.Phase3.Glue.exceptionalError +
            Kriterion.ArgoMAC.Phase3.Glue.maskSwapError +
              Kriterion.ArgoMAC.Phase3.Glue.coincidenceError :=
  planB_publicFirst_of_laws_bounds designedLaws designedBounds

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
