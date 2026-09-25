/-
Phase 3 glue, step 4: **the top-level assembly.**

The chain (design note B §3/§5, B-review), at the instances `Solution.adaptivePrivacy` installs,
for the machine adversary `A = machineAdversary encoding M` with fuels `q₁ = M.firstFuel`,
`q₂ = M.secondFuel`:

```
R = lazyRealGame … A                                   (the scored real game)
  = G0 = tapeRealGame A                                (step 2, `planB_lazy_real`, exact)
  →[H_swap.real,       ε_swap           ] G0U          (P1 MaskSwap: every mask vector uniform)
  →[H_joint.hidden,    L1(q₁+q₂)        ] G1U          (identical until a hidden entry is hit)
  →[H_joint.publicFirst, L2 + ε_exc + ε_swap + ε_coin] HW (until a stage-1 hit or an exceptional input; F4)
  →[H_open.kernel,     ε_pt             ] H            (P1 Opening: the lift sampler)
  →[H_abort.abort,     ε_abort(q₁)      ] I^U          (the 362 programs' abort mass, per query)
  →[H_swap.ideal,      ε_swap + 0       ] I            (lazy refill, per derived mask vector)
  →[H_machine.law,     ε_cut            ] M            (P2: the closed machine)
```

Here `ε_swap = maskSwapError = 1588 · Σ_lane laneDelta lane` (one copy of the vector sampler's
bias over the `6,352` switch-mask vectors), `ε_coin = coincidenceError = 2^16/2^128` (the
label-coincidence allowance of the designed sub-hop `G1U → G1U°`, charged once, in `G1U → HW`),
and the refill charge `idealRefillError` is `0`.

For `q₁ + q₂ < 2^100` the six P1/abort hops bound `advantage R I` by the triangle, the machine hop
bounds `advantage I M`, and `adaptivePrivacyTransfer` gives

```
advantage(R, M) · 2^100 ≤ (advantage(R, I) + advantage(I, M)) · 2^100
                        ≤ chainError q₁ q₂ · 2^100                    (the hypotheses)
                        ≤ q₁ + q₂ + 1                                 (`chainError_budget`)
                        ≤ size + 1 + q₁ + q₂ + 1 = M.steps + 1        (the free unit `size + 1`)
```

For `q₁ + q₂ ≥ 2^100` the advantage is at most `1` and `2^100 ≤ M.steps + 1`.

The hybrids `G0U, G1U, HW, H, I^U` are P1's definitions and enter as data (`Hybrids`); every
hop is a named hypothesis (a structure of `Prop` fields). The endpoints `G0` (step 2) and `I`
(step 3) are this directory's own. The conclusion `planB_oracleAdaptivePrivacy` is literally the
type of `Submission.solution.adaptivePrivacy`.
-/

import Proof.Privacy.Phase3.Glue.Budget

namespace Kriterion.ArgoMAC.Phase3.Glue

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.Phase3 (laneDelta)

noncomputable section

/-! ### The chain games -/

/-- `G0`: the tape-sampled real game (step 2), as a chain game. -/
def realHybrid : HybridGame := fun adversary parameter scalar =>
  letI : Fintype Coins := Fintype.ofFinite Coins
  tapeRealGame adversary parameter scalar ()

/-- **P1's proof-only hybrids** (design note B §3). -/
structure Hybrids where
  /-- `G0U`: every switch-mask vector uniform on `F_p^n`, its hash limbs drawn uniformly on the
  `sampleLane` fibre over it (the global mask swap, before the game starts). -/
  maskSwapped : HybridGame
  /-- `G1U`: at the input choice, the hidden entries (active switches, active fold parents,
  gadget differing positions; the whole of system B off the curve) deleted from the lazy state. -/
  hiddenDeleted : HybridGame
  /-- `HW`: the public-first reparametrisation of `G1U` (C1/C2, fold-join and exception-byte
  bijections, label/`Δ` deferral, lazy reorder of the visible entries), real output rows. -/
  publicFirst : HybridGame
  /-- `H`: as `HW`, with the digit rows drawn by the tail/head-clamp/lift sampler. -/
  opened : HybridGame
  /-- `I^U`: the ideal game with every non-designated switch-mask vector the simulator derives
  uniform (its limbs programmed from the swap kernel). -/
  idealUniform : HybridGame

/-- A hop of the chain: at the `Solution` instances, against every adversary with fewer than
`2^100` queries, the two games are within `error q₁ q₂`. -/
def HopBound (first second : HybridGame) (error : ℕ → ℕ → ℝ) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      Assumptions.advantage (atSolution first field group adversary parameter scalar)
        (atSolution second field group adversary parameter scalar) ≤
        error (adversary.firstQueryBudget parameter) (adversary.secondQueryBudget parameter)

/-! ### Identical-until-bad hops: the game-level wrapping -/

/-- The flag of a flagged game outcome `(outcome, bad)`. -/
def badSet : Set (Bool × Bool) := {outcome | outcome.2 = true}

/-- **An identical-until-bad pair of games.** Both games are the first marginal of a flagged law
`(outcome, bad)`; the two flagged laws agree at every outcome whose flag is down; the first flagged
law raises the flag with mass at most `error`. -/
def UntilBad (first second : PMF Bool) (error : ℝ) : Prop :=
  ∃ firstFlagged secondFlagged : PMF (Bool × Bool),
    firstFlagged.map Prod.fst = first ∧ secondFlagged.map Prod.fst = second ∧
    (∀ outcome, firstFlagged (outcome, false) = secondFlagged (outcome, false)) ∧
    (firstFlagged.toOuterMeasure badSet).toReal ≤ error

/-- The acceptance mass of a first marginal. -/
theorem map_fst_true (flagged : PMF (Bool × Bool)) :
    (flagged.map Prod.fst) true = flagged.toOuterMeasure {outcome | outcome.1 = true} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

/-- **Identical until bad** (the library's `Probability.identical_until_bad`, at game level). -/
theorem UntilBad.advantage_le {first second : PMF Bool} {error : ℝ}
    (bound : UntilBad first second error) : Assumptions.advantage first second ≤ error := by
  obtain ⟨firstFlagged, secondFlagged, firstEq, secondEq, agree, bad⟩ := bound
  have law := Kriterion.Cryptography.Probability.identical_until_bad secondFlagged firstFlagged
    badSet {outcome | outcome.1 = true} (by
      rintro ⟨outcome, flag⟩ notBad
      cases flag
      · exact (agree outcome).symm
      · exact (notBad rfl).elim)
  unfold Assumptions.advantage
  rw [← firstEq, ← secondEq, map_fst_true, map_fst_true, abs_sub_comm]
  exact law.trans bad

/-- **An identical-until-bad pair whose agreement off the bad event is an exact core law.** The
first game's flagged law agrees, flag down, with a continuation of `realCore`; the second game is
the same continuation of `simCore`; the core is exact, `realCore = simCore` (for `G1U → HW` the
core is P1's F4 `jointLaw`: the joint law of the published cells, the visible masks, the
designated masks and the bridge key, as a `PMF` equality). -/
def CoreUntilBad (first second : PMF Bool) (error : ℝ) : Prop :=
  ∃ (Core : Type) (realCore simCore : PMF Core) (continuation : Core → PMF (Bool × Bool))
    (firstFlagged : PMF (Bool × Bool)),
    realCore = simCore ∧ firstFlagged.map Prod.fst = first ∧
    (simCore.bind continuation).map Prod.fst = second ∧
    (∀ outcome, firstFlagged (outcome, false) = (realCore.bind continuation) (outcome, false)) ∧
    (firstFlagged.toOuterMeasure badSet).toReal ≤ error

/-- An exact core closes the off-bad agreement. -/
theorem CoreUntilBad.untilBad {first second : PMF Bool} {error : ℝ}
    (bound : CoreUntilBad first second error) : UntilBad first second error := by
  obtain ⟨Core, realCore, simCore, continuation, firstFlagged, core, firstEq, secondEq, agree,
    bad⟩ := bound
  subst core
  exact ⟨firstFlagged, realCore.bind continuation, firstEq, secondEq, agree, bad⟩

/-- A chain hop in identical-until-bad form, at the `Solution` instances, below `2^100`
queries. -/
def GameUntilBad (first second : HybridGame) (error : ℕ → ℕ → ℝ) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      UntilBad (atSolution first field group adversary parameter scalar)
        (atSolution second field group adversary parameter scalar)
        (error (adversary.firstQueryBudget parameter) (adversary.secondQueryBudget parameter))

/-- A chain hop in exact-core identical-until-bad form. -/
def GameCoreUntilBad (first second : HybridGame) (error : ℕ → ℕ → ℝ) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      CoreUntilBad (atSolution first field group adversary parameter scalar)
        (atSolution second field group adversary parameter scalar)
        (error (adversary.firstQueryBudget parameter) (adversary.secondQueryBudget parameter))

theorem GameUntilBad.hopBound {first second : HybridGame} {error : ℕ → ℕ → ℝ}
    (bound : GameUntilBad first second error) : HopBound first second error :=
  fun field group adversary parameter scalar small =>
    (bound field group adversary parameter scalar small).advantage_le

theorem GameCoreUntilBad.hopBound {first second : HybridGame} {error : ℕ → ℕ → ℝ}
    (bound : GameCoreUntilBad first second error) : HopBound first second error :=
  fun field group adversary parameter scalar small =>
    (bound field group adversary parameter scalar small).untilBad.advantage_le

/-! ### The named hypotheses -/

/-- **`H_swap`** (P1 `Phase3/MaskSwap.lean` for `real`; the lazy refill for `idealPerMask`). -/
structure MaskSwapBound (hybrids : Hybrids) : Prop where
  /-- `G0 → G0U`: `maskSwapError`, the tape-level data-processing swap
  (`maskSwap_bind_etvDist_le`). -/
  real : HopBound realHybrid hybrids.maskSwapped fun _ _ => maskSwapError
  /-- `I^U → I`, **a lazy-oracle statement charged per derived mask vector.** In `I` each
  non-designated switch-mask vector the simulator derives is `sampleLane` of fresh answers of the
  shared lazy hash oracle; in `I^U` it is uniform on `F_p^n`, its limbs programmed from the fibre.
  The sites are the derived vectors, at most `laneVectorCount` of each lane (`lane site`); each
  costs its lane's sampler bias `laneDelta (lane site)`. Lazy hash answers are exactly uniform
  (`HashTable.query`), so no per-query refill charge remains (`idealRefillError = 0`). -/
  idealPerMask : ∀ (field : FieldCertificate) (group : @GroupCertificate field)
    (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      ∃ (Site : Type) (_ : Fintype Site) (lane : Site → Lane),
        (∀ vectorLane : Lane,
          (Finset.univ.filter fun site => lane site = vectorLane).card ≤ laneVectorCount) ∧
        Assumptions.advantage
            (atSolution hybrids.idealUniform field group adversary parameter scalar)
            (atSolution idealHybrid field group adversary parameter scalar) ≤
          ∑ site, (laneDelta (lane site)).toReal

/-- `I^U → I` summed: at most `laneVectorCount` vectors per lane, so at most `maskSwapError`,
and the refill adds `idealRefillError = 0`. -/
theorem MaskSwapBound.ideal {hybrids : Hybrids} (swap : MaskSwapBound hybrids) :
    HopBound hybrids.idealUniform idealHybrid fun first _ =>
      maskSwapError + idealRefillError first := by
  intro field group adversary parameter scalar small
  obtain ⟨Site, _, lane, card, bound⟩ :=
    swap.idealPerMask field group adversary parameter scalar small
  refine bound.trans ?_
  beta_reduce
  unfold idealRefillError
  rw [add_zero, maskSwapError_eq_sum, Finset.mul_sum,
    ← Finset.sum_fiberwise' Finset.univ lane fun vectorLane => (laneDelta vectorLane).toReal]
  refine Finset.sum_le_sum fun vectorLane _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast card vectorLane) ENNReal.toReal_nonneg

/-- **`H_joint`** (P1, `Phase3/JointExactness.lean`, F4): hidden-entry deletion, then the joint
public-first reparametrisation, each an identical-until-bad hop whose bad event is the charged hit
event; the second one's off-bad agreement is F4's exact core. -/
structure JointExactnessBound (hybrids : Hybrids) : Prop where
  /-- `G0U → G1U`, identical until a hidden entry is hit: `L1(q₁ + q₂)`. -/
  hidden : GameUntilBad hybrids.maskSwapped hybrids.hiddenDeleted fun first second =>
    hiddenPointError (first + second)
  /-- `G1U → HW`, identical until a stage-1 hit **or a doubling input** (the adversary's input
  doubles a nonzero digit against the garbler's offset, where `G1U`'s real gadget unlocks the true
  digit and `HW`'s published gadget is uniform), agreeing off it through F4's `jointLaw`, **plus
  one sampler-bias swap `maskSwapError`**. Off the curve, `G1U` installs the system-A vectors with
  `G0U`'s uniform values, while `HW` makes no call and the adversary's vectors are `sampleLane` of
  fresh hash answers (P1g; the middle game `M'` of `PublicFirst/MiddleOff.lean` carries the swap).
  **Plus the label-coincidence allowance
  `coincidenceError`** of the designed sub-hop `G1U → G1U°` (P1j). Total:
  `L2(q₁) + ε_exc + maskSwapError + coincidenceError`. -/
  publicFirst : GameCoreUntilBad hybrids.hiddenDeleted hybrids.publicFirst fun first _ =>
    stageOneHitError first + exceptionalError + maskSwapError + coincidenceError

/-- `G0U → G1U` as a hop bound. -/
theorem JointExactnessBound.hiddenHop {hybrids : Hybrids} (joint : JointExactnessBound hybrids) :
    HopBound hybrids.maskSwapped hybrids.hiddenDeleted fun first second =>
      hiddenPointError (first + second) :=
  joint.hidden.hopBound

/-- `G1U → HW` as a hop bound. -/
theorem JointExactnessBound.publicFirstHop {hybrids : Hybrids}
    (joint : JointExactnessBound hybrids) :
    HopBound hybrids.hiddenDeleted hybrids.publicFirst fun first _ =>
      stageOneHitError first + exceptionalError + maskSwapError + coincidenceError :=
  joint.publicFirst.hopBound

/-- **`H_open`** (P1, `Phase3/Opening.lean`): the output-kernel coupling, real digit rows versus
the tail/head-clamp/lift sampler. -/
structure OpeningBound (hybrids : Hybrids) : Prop where
  /-- `HW → H`: `ε_pt = 364/(r−1)`. -/
  kernel : HopBound hybrids.publicFirst hybrids.opened fun _ _ => outputKernelError

/-- **`H_abort`**: the lazy-abort mass of the 362 designated hash programs, **charged per stage-1
query and per abort site.** The sites are a finite family; `count site ≥ 0` is the expected number
of the adversary's stage-1 entries at the site, so `Σ count ≤ q₁`. Each such entry costs
`abortQueryCharge q₁ = 1/(2^128 − q₁)`: a hash program needs only a fresh *input*, and a stage-1
hash entry blocks a designated program only if its input is a candidate input at the label `E*`
(`candidateIndex site E*`), which has conditional mass `≤ 1/(2^128 − q₁)`. There is no output
part.

The site type is existential so that `AbortBound` does not depend on the lazy-oracle development
(which itself imports this module). P4's instance is `Lazy.AbortSite` (A1 §3):

* the chunk-0 hash cells of lane `pointX`, `4·362` of them: the stage-1 hash entries that decode
  to `(pointX, chunk 0, switch < 4, limb)`, the candidate designated inputs (`CandidateSite`,
  pairwise distinct over (site, label) by `candidateIndex_injective`);
* the chunk-0 hash cells of lane `curveX`, `4·4 = 16` of them: a stage-1 hit there makes system A
  read the chunk-0 labels;
* the level-1 fold indices of chunk 0 of both lanes, on which `E*` itself depends.

The bridge from P4's `Lazy.AbortPerQuery'` is `AbortBound.of_perQuery'` (`Glue/AbortBridge.lean`). -/
structure AbortBound (hybrids : Hybrids) : Prop where
  /-- `H → I^U`, per stage-1 query and per abort site. -/
  perQuery : ∀ (field : FieldCertificate) (group : @GroupCertificate field)
    (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      ∃ (Site : Type) (_ : Fintype Site) (count : Site → ℝ), (∀ site, 0 ≤ count site) ∧
        ∑ site, count site ≤ (adversary.firstQueryBudget parameter : ℝ) ∧
        Assumptions.advantage (atSolution hybrids.opened field group adversary parameter scalar)
            (atSolution hybrids.idealUniform field group adversary parameter scalar) ≤
          ∑ site, count site * abortQueryCharge (adversary.firstQueryBudget parameter)

/-- `H → I^U` summed: `ε_abort(q₁) = q₁/(2^128 − q₁)`. -/
theorem AbortBound.abort {hybrids : Hybrids} (abort : AbortBound hybrids) :
    HopBound hybrids.opened hybrids.idealUniform fun first _ => abortError first := by
  intro field group adversary parameter scalar small
  obtain ⟨Site, _, count, nonneg, total, bound⟩ :=
    abort.perQuery field group adversary parameter scalar small
  have charge := abortQueryCharge_nonneg (adversary.firstQueryBudget parameter) (by omega)
  refine bound.trans ?_
  beta_reduce
  unfold abortError
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right total charge

/-- **`H_machine`** (P2): the closed machine realises the abstract simulator within the sampling
cutoff, at cost `≤ 2^60`. -/
structure MachineBound (simulator : BoundedMachine.Simulator) : Prop where
  /-- `I → M`: `ε_cut = 2^-128`, against every adversary. -/
  law : MachineLaw simulator machineCutoffError
  /-- The code and both fuels within `2^60`. -/
  cost : simulator.size + 1 + simulator.firstFuel + simulator.secondFuel ≤ 2 ^ 60

/-- The cost field of `H_machine` is the simulator's own `within` bound. -/
theorem MachineBound.of_law {simulator : BoundedMachine.Simulator}
    (law : MachineLaw simulator machineCutoffError) : MachineBound simulator :=
  ⟨law, simulator.within⟩

/-! ### The chain -/

/-- An advantage is at most `1`. -/
theorem advantage_le_one (first second : PMF Bool) : Assumptions.advantage first second ≤ 1 := by
  unfold Assumptions.advantage
  have bound (distribution : PMF Bool) : (distribution true).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one distribution true)
  have firstBound := bound first
  have secondBound := bound second
  have firstNonneg : 0 ≤ (first true).toReal := ENNReal.toReal_nonneg
  have secondNonneg : 0 ≤ (second true).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- The six hops from `G0` to `I` sum to all of `chainError` but the machine cutoff. -/
theorem real_ideal_le (simulator : BoundedMachine.Simulator) (hybrids : Hybrids)
    (swap : MaskSwapBound hybrids) (opening : OpeningBound hybrids)
    (joint : JointExactnessBound hybrids) (abort : AbortBound hybrids)
    (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter <
      2 ^ 100) :
    Assumptions.advantage (atSolution realHybrid field group adversary parameter scalar)
        (atSolution idealHybrid field group adversary parameter scalar) +
      Assumptions.advantage (atSolution idealHybrid field group adversary parameter scalar)
        (atSolution (machineHybrid simulator) field group adversary parameter scalar) ≤
      chainError (adversary.firstQueryBudget parameter) (adversary.secondQueryBudget parameter) +
        (Assumptions.advantage (atSolution idealHybrid field group adversary parameter scalar)
          (atSolution (machineHybrid simulator) field group adversary parameter scalar) -
          machineCutoffError) := by
  let game (hybrid : HybridGame) := atSolution hybrid field group adversary parameter scalar
  have s0 := swap.real field group adversary parameter scalar small
  have s1 := joint.hiddenHop field group adversary parameter scalar small
  have s2 := joint.publicFirstHop field group adversary parameter scalar small
  have s3 := opening.kernel field group adversary parameter scalar small
  have s4 := abort.abort field group adversary parameter scalar small
  have s5 := swap.ideal field group adversary parameter scalar small
  have t0 := Assumptions.advantageTriangle (game realHybrid) (game hybrids.maskSwapped)
    (game idealHybrid)
  have t1 := Assumptions.advantageTriangle (game hybrids.maskSwapped) (game hybrids.hiddenDeleted)
    (game idealHybrid)
  have t2 := Assumptions.advantageTriangle (game hybrids.hiddenDeleted) (game hybrids.publicFirst)
    (game idealHybrid)
  have t3 := Assumptions.advantageTriangle (game hybrids.publicFirst) (game hybrids.opened)
    (game idealHybrid)
  have t4 := Assumptions.advantageTriangle (game hybrids.opened) (game hybrids.idealUniform)
    (game idealHybrid)
  unfold chainError
  linarith

/-- **Step 4: the Plan B entry satisfies `OracleAdaptivePrivacy`**, from the five named
hypotheses. The statement is literally the type of `Submission.solution.adaptivePrivacy`; at
merge its open obligation becomes `planB_oracleAdaptivePrivacy simulator hybrids H_swap H_open
H_joint H_machine H_abort`. -/
theorem planB_oracleAdaptivePrivacy (simulator : BoundedMachine.Simulator) (hybrids : Hybrids)
    (H_swap : MaskSwapBound hybrids) (H_open : OpeningBound hybrids)
    (H_joint : JointExactnessBound hybrids) (H_machine : MachineBound simulator)
    (H_abort : AbortBound hybrids) :
    ∀ (field : BN254.FieldCertificate) (group : @BN254.GroupCertificate field),
      letI := field
      letI := @Fintype.ofFinite PlanB.FixedIndex inferInstance
      letI := @Fintype.ofFinite EncPRF.PermutationIndex inferInstance
      letI := Classical.decEq PlanB.FixedIndex
      letI := Classical.decEq EncPRF.PermutationIndex
      GarbledCircuit.OracleAdaptivePrivacy (@Scheme.scheme field group) PlanB.Wire.encoding 1100521
        (@uniformRandomTape Scheme.Coins (@Fintype.ofFinite Scheme.Coins inferInstance)
          Scheme.witness)
        (fun parameter scalar coins =>
          (Programs.garbleProgram parameter scalar coins).toOracleProgram) := by
  intro field group
  letI : Fintype PlanB.FixedIndex := Fintype.ofFinite _
  letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite _
  letI : DecidableEq PlanB.FixedIndex := Classical.decEq _
  letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq _
  letI : Fintype Coins := Fintype.ofFinite _
  refine ⟨simulator, fun machine parameter scalar => ?_⟩
  intro adversary
  have real : lazyRealGame (uniformRandomTape Coins Scheme.witness)
      (fun parameter scalar coins => (Programs.garbleProgram parameter scalar coins).toOracleProgram)
      Scheme.scheme.encode adversary parameter scalar () =
      atSolution realHybrid field group adversary parameter scalar :=
    planB_lazy_real adversary Scheme.witness parameter scalar ()
  show Assumptions.WorkPerAdvantage 100 (machine.steps + 1)
    (Assumptions.advantage (lazyRealGame (uniformRandomTape Coins Scheme.witness)
      (fun parameter scalar coins => (Programs.garbleProgram parameter scalar coins).toOracleProgram)
      Scheme.scheme.encode adversary parameter scalar ())
      (atSolution (machineHybrid simulator) field group adversary parameter scalar))
  rw [real]
  have queries : adversary.firstQueryBudget parameter = machine.firstFuel ∧
      adversary.secondQueryBudget parameter = machine.secondFuel := ⟨rfl, rfl⟩
  have steps : (machine.firstFuel : ℝ) + (machine.secondFuel : ℝ) + 1 ≤
      ((machine.steps + 1 : ℕ) : ℝ) := by
    have work : machine.firstFuel + machine.secondFuel + 1 ≤ machine.steps + 1 := by
      unfold BoundedMachine.Adversary.steps
      omega
    exact_mod_cast work
  by_cases small : machine.firstFuel + machine.secondFuel < 2 ^ 100
  · -- The chain: `adaptivePrivacyTransfer` through `I`, then the hops and the budget.
    apply adaptivePrivacyTransfer (ideal := atSolution idealHybrid field group adversary parameter
      scalar)
    have smallBudget : adversary.firstQueryBudget parameter +
        adversary.secondQueryBudget parameter < 2 ^ 100 := by
      rw [queries.1, queries.2]
      exact small
    have hops := real_ideal_le simulator hybrids H_swap H_open H_joint H_abort field group
      adversary parameter scalar smallBudget
    have cut := H_machine.law field group adversary parameter scalar
    have budget := chainError_budget machine.firstFuel machine.secondFuel small
    rw [queries.1, queries.2] at hops
    unfold Assumptions.WorkPerAdvantage
    calc _ ≤ chainError machine.firstFuel machine.secondFuel * 2 ^ 100 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (machine.firstFuel : ℝ) + (machine.secondFuel : ℝ) + 1 := budget
      _ ≤ ((machine.steps + 1 : ℕ) : ℝ) := steps
  · -- Beyond `2^100` queries every advantage is within the allowance.
    unfold Assumptions.WorkPerAdvantage
    have large : (2 : ℝ) ^ 100 ≤ (machine.firstFuel : ℝ) + (machine.secondFuel : ℝ) := by
      have : 2 ^ 100 ≤ machine.firstFuel + machine.secondFuel := Nat.le_of_not_gt small
      exact_mod_cast this
    calc _ ≤ 1 * (2 : ℝ) ^ 100 :=
          mul_le_mul_of_nonneg_right (advantage_le_one _ _) (by positivity)
      _ ≤ ((machine.steps + 1 : ℕ) : ℝ) := by linarith

end

end Kriterion.ArgoMAC.Phase3.Glue
