/-
**Phase 3, P4 — `H → I^U` reduced to the key-averaged installation-failure mass.**

`H` (P1b's `openedHybrid`) and `I^U` (`idealUniformHybrid`, which is the opened game at
`abortInstallation`, `idealUniformHybrid_eq_opened`) differ only in the designated installation:
`H` skips a failed hash program, `I^U` aborts.

* `programAllSkip_of_programAll` — **`H = I^U` off the abort event**: when every program succeeds,
  skipping installs exactly the same oracle.
* `openedStage2_etvDist_le` — the two stage-2 kernels are within the **installation-failure mass**
  `failMass` (the mass of the installation inputs on which `Glue.programAll` returns `none`).
* `openedGame_etvDist_le` — swapping stage 2 costs the prefix average of a bound that may depend on
  the retained state (the source, hence the Lamport key), the input and the output.
* `key_average` — the prefix average with the key averaged separately: stage 1 publishes
  `publicValue`, which does not read the key, so the key is uniform and independent of the
  adversary's first stage.

**The abort sites** (`AbortSite`) are the stage-1 entries an abort may be billed to: the level-1
fold indices of chunk 0 of lanes `pointX` and `curveX` (fixed-key entries; the fold hit of `E*` and
of the `curveX` chunk-0 labels), and the chunk-0 **hash cells** of `pointX` (the `4 · 362`
candidate designated inputs, `Glue.CandidateSite`) and of `curveX` (`4 · 4`; a stage-1 hit there
makes the curve lane read the chunk-0 labels). A cell's entries are the stored labels at its inputs
(`hashCount`); the cells' inputs are pairwise distinct over (cell, label), so all the sites together
hold at most the stage-1 entries, at most `q₁` on average (`stageOneMean_abortUse_le`).

The per-prefix analysis is the named hypothesis `KeyAveragedFailBound`. Given it,
`abortBound_perQuery'_of` proves the restated `AbortBound.perQuery`
(`AbortPerQuery'`: sites = `AbortSite`, per-query charge `Glue.abortQueryCharge q₁`).
-/

import Proof.Privacy.Phase3.Opened
import Proof.Privacy.Phase3.Lazy.IdealPerMask
import Proof.Privacy.Phase3.Lazy.FoldEntropy

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.Phase3 (openedSimulator openedCont openedOpening skipInstallation
  abortInstallation programAllSkip simulatedRows RowsKernel Installation)
open scoped ENNReal

noncomputable section

/-! ### The abort sites -/

/-- **The fixed-key abort indices**: the level-1 fold indices of chunk `0` of lanes `pointX` and
`curveX`. -/
def IsFoldAbort : FixedIndex → Prop
  | .hot lane chunk fold _ _ => (lane = .pointX ∨ lane = .curveX) ∧ chunk = chunkZero ∧ fold.val = 1
  | .gadget _ _ _ _ => False

/-- **The hash abort cells**: the chunk-`0` cells of lanes `pointX` (the candidate designated
inputs) and `curveX`. -/
def IsCellAbort (cell : Cell) : Prop :=
  (cell.1.lane = .pointX ∨ cell.1.lane = .curveX) ∧ cell.1.chunk = chunkZero

noncomputable instance foldAbortFintype : Fintype {index : FixedIndex // IsFoldAbort index} :=
  Fintype.ofFinite _

noncomputable instance cellAbortFintype : Fintype {cell : Cell // IsCellAbort cell} :=
  Fintype.ofFinite _

/-- **An abort site**: a fixed-key abort index or a hash abort cell. -/
abbrev AbortSite := {index : FixedIndex // IsFoldAbort index} ⊕ {cell : Cell // IsCellAbort cell}

/-- **The restated `AbortBound.perQuery`**: `H → I^U`, charged per stage-1 query at an abort site. -/
def AbortPerQuery' (opened idealUniform : HybridGame) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field)
    (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      ∃ count : AbortSite → ℝ, (∀ site, 0 ≤ count site) ∧
        ∑ site, count site ≤ (adversary.firstQueryBudget parameter : ℝ) ∧
        Assumptions.advantage (atSolution opened field group adversary parameter scalar)
            (atSolution idealUniform field group adversary parameter scalar) ≤
          ∑ site, count site * abortQueryCharge (adversary.firstQueryBudget parameter)

/-! ### `H = I^U` off the abort event -/

section Kernels

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **When every program succeeds, skipping installs the same oracle.** -/
theorem programAllSkip_of_programAll :
    ∀ (requests : List (Option BaseField × (Block × Block))) (oracle updated : LState),
      programAll requests oracle = some updated → programAllSkip requests oracle = updated
  | [], oracle, updated, success => by
      simp only [programAll, Option.some.injEq] at success
      exact success
  | (input, answer) :: rest, oracle, updated, success => by
      cases input with
      | none => simp [programAll] at success
      | some input =>
          simp only [programAll] at success
          obtain ⟨middle, programmed, rest⟩ := Option.bind_eq_some_iff.mp success
          simp only [programAllSkip, programmed, Option.getD_some]
          exact programAllSkip_of_programAll _ _ _ rest

/-- The designated requests and the oracle after the refill run, the rows and the designated
vector's hash answers; `none` is a run or sampler abort. -/
def installInputs [FieldCertificate] [GroupCertificate] (rows : RowsKernel) (table : Public)
    (input : AffineInput) (labels : LamportSignature) (target : Point) (oracle : LState) :
    PMF (Option (List (Option BaseField × (Block × Block)) × LState)) :=
  let restored := Lamport.restore input labels
  (refillRun restored.input (openingQueriesM table restored.input restored.inputMac) oracle).bind
    fun ran => match ran with
    | none => PMF.pure none
    | some ran => (rows input target).bind fun targets => match targets with
      | none => PMF.pure none
      | some targets =>
        (designatedLimbs idealSamplers table restored.input ran.1.1 ran.1.2 targets).bind
          fun answers => match answers with
          | none => PMF.pure none
          | some answers =>
              PMF.pure (some (programRequests restored.input ran.2.2 answers, ran.2.1))

/-- The installation step of an opened opening. -/
def installStep (install : Installation) :
    Option (List (Option BaseField × (Block × Block)) × LState) → PMF (Option LState)
  | none => PMF.pure none
  | some inputs => PMF.pure (install inputs.1 inputs.2)

/-- **The opened opening is its installation inputs, then the installation.** -/
theorem openedOpening_eq [FieldCertificate] [GroupCertificate] (rows : RowsKernel)
    (install : Installation) (table : Public) (input : AffineInput) (labels : LamportSignature)
    (target : Point) (oracle : LState) :
    openedOpening rows install table input labels target oracle =
      (installInputs rows table input labels target oracle).bind (installStep install) := by
  unfold openedOpening installInputs
  dsimp only
  rw [PMF.bind_bind]
  refine congrArg _ (funext fun ran => ?_)
  cases ran with
  | none => simp [installStep]
  | some ran =>
      simp only [openedCont, PMF.bind_bind]
      congr 1
      funext targets
      cases targets with
      | none => simp [installStep]
      | some targets =>
          simp only [PMF.bind_bind]
          congr 1
          funext blocks
          cases blocks with
          | none => simp [installStep]
          | some blocks => simp [installStep]

/-- The installation inputs on which `I^U`'s installation aborts. -/
def FailsInstall (inputs : Option (List (Option BaseField × (Block × Block)) × LState)) : Prop :=
  ∃ requests oracle, inputs = some (requests, oracle) ∧ programAll requests oracle = none

/-- **The installation-failure mass** of the opened opening. -/
def failMass [FieldCertificate] [GroupCertificate] (table : Public) (input : AffineInput)
    (labels : LamportSignature) (target : Point) (oracle : LState) : ℝ≥0∞ :=
  (installInputs simulatedRows table input labels target oracle).toOuterMeasure
    {inputs | FailsInstall inputs}

/-- **The two openings are within the failure mass.** -/
theorem openedOpening_etvDist_le [FieldCertificate] [GroupCertificate] (table : Public)
    (input : AffineInput) (labels : LamportSignature) (target : Point) (oracle : LState) :
    (openedOpening simulatedRows skipInstallation table input labels target oracle).etvDist
        (openedOpening simulatedRows abortInstallation table input labels target oracle) ≤
      failMass table input labels target oracle := by
  classical
  rw [openedOpening_eq, openedOpening_eq]
  refine le_trans (Kriterion.ArgoMAC.Security.Phase3.etvDist_bind_left_le _ _ _) ?_
  rw [failMass, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun inputs => ?_
  rw [mul_comm, Set.indicator_apply]
  cases inputs with
  | none => simp [installStep]
  | some inputs =>
      by_cases fails : programAll inputs.1 inputs.2 = none
      · rw [if_pos ⟨inputs.1, inputs.2, rfl, fails⟩]
        exact mul_le_of_le_one_right zero_le (PMF.etvDist_le_one _ _)
      · rw [if_neg (by rintro ⟨requests, oracle', same, failed⟩; cases same; exact fails failed)]
        obtain ⟨updated, success⟩ := Option.ne_none_iff_exists'.mp fails
        simp only [installStep, skipInstallation, abortInstallation, success,
          programAllSkip_of_programAll _ _ _ success, PMF.etvDist_self, mul_zero]
        exact le_rfl

/-- **The two stage-2 kernels are within the failure mass** (`0` without an output point). -/
theorem openedStage2_etvDist_le [FieldCertificate] [GroupCertificate] (source : Stage1Source)
    (input : AffineInput) (output : Option Point) (oracle : LState) :
    ((openedSimulator simulatedRows skipInstallation).stage2 source input output oracle).etvDist
        ((openedSimulator simulatedRows abortInstallation).stage2 source input output oracle) ≤
      match output with
      | none => 0
      | some target => failMass source.publicValue input
          (Lamport.selectedLabels (source.key.encode (BitInput.ofAffine input))) target oracle := by
  cases output with
  | none => simp [openedSimulator]
  | some target =>
      exact le_trans (PMF.etvDist_map_le _ _ _) (openedOpening_etvDist_le _ _ _ _ _)

end Kernels

/-! ### The key is independent of the stage-1 view -/

/-- A source with its Lamport key replaced. -/
def withKey (source : Stage1Source) (key : InputMacKey) : Stage1Source := { source with key := key }

/-- The published value does not read the key. -/
theorem publicValue_withKey (source : Stage1Source) (key : InputMacKey) :
    (withKey source key).publicValue = source.publicValue := rfl

/-- `(s, k) ↦ (s[key := k], s.key)` is a bijection. -/
def keySwap : (Stage1Source × InputMacKey) ≃ (Stage1Source × InputMacKey) where
  toFun pair := (withKey pair.1 pair.2, pair.1.key)
  invFun pair := (withKey pair.1 pair.2, pair.1.key)
  left_inv pair := by obtain ⟨source, key⟩ := pair; rfl
  right_inv pair := by obtain ⟨source, key⟩ := pair; rfl

noncomputable instance inputMacKeyFintype : Fintype InputMacKey := Fintype.ofFinite _

instance inputMacKeyNonempty : Nonempty InputMacKey := ⟨(Classical.choice inferInstance :
  Stage1Source).key⟩

/-- **A uniform source is a uniform source with an independent uniform key written in.** -/
theorem uniform_withKey :
    (PMF.uniformOfFintype Stage1Source).bind (fun source =>
        (PMF.uniformOfFintype InputMacKey).map (withKey source)) =
      PMF.uniformOfFintype Stage1Source := by
  have product := uniform_product (A := Stage1Source) (B := InputMacKey)
  have swapped : (PMF.uniformOfFintype (Stage1Source × InputMacKey)).map
      (fun pair => withKey pair.1 pair.2) = PMF.uniformOfFintype Stage1Source := by
    have factor : (fun pair : Stage1Source × InputMacKey => withKey pair.1 pair.2) =
        Prod.fst ∘ keySwap := rfl
    rw [factor, ← PMF.map_comp, uniform_equiv keySwap, uniform_map_fst]
  calc (PMF.uniformOfFintype Stage1Source).bind (fun source =>
        (PMF.uniformOfFintype InputMacKey).map (withKey source))
      = ((PMF.uniformOfFintype Stage1Source).bind fun source =>
          (PMF.uniformOfFintype InputMacKey).map fun key => (source, key)).map
            (fun pair => withKey pair.1 pair.2) := by
        rw [PMF.map_bind]
        refine congrArg _ (funext fun source => ?_)
        rw [PMF.map_comp]
        rfl
    _ = PMF.uniformOfFintype Stage1Source := by rw [product, swapped]

/-! ### Stage-1 entries at the abort sites -/

section Budget

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- The stage-1 entries at an abort site: the entries at a fold index, the stored labels at a
cell. -/
def siteEntries (oracle : LState) : AbortSite → ℕ
  | .inl index => (oracle.fixed index.val).used
  | .inr cell => hashCount (cellInput cell.val) oracle

/-- The stage-1 entries at the abort sites. -/
def abortUse (oracle : LState) : ℕ := ∑ site, siteEntries oracle site

/-- The stored labels of the abort cells are the stored inputs of the (abort cell, label) pairs. -/
theorem sum_cell_hashCount (oracle : LState) :
    ∑ cell : {cell : Cell // IsCellAbort cell}, hashCount (cellInput cell.val) oracle =
      hashCount (fun pair : {cell : Cell // IsCellAbort cell} × Block =>
        cellInput pair.1.val pair.2) oracle := by
  classical
  simp only [hashCount, Finset.card_filter]
  rw [Fintype.sum_prod_type]

/-- **The abort sites hold at most the stage-1 entries.** -/
theorem abortUse_le_entryPotential (oracle : LState) :
    abortUse oracle ≤
      entryPotential (Subtype.val : {index : FixedIndex // IsFoldAbort index} → FixedIndex)
        oracle := by
  unfold abortUse entryPotential
  rw [Fintype.sum_sum_type]
  show ∑ index : {index : FixedIndex // IsFoldAbort index}, (oracle.fixed index.val).used +
      ∑ cell : {cell : Cell // IsCellAbort cell}, hashCount (cellInput cell.val) oracle ≤ _
  rw [sum_cell_hashCount]
  refine Nat.add_le_add_left (hashCount_le_length _ ?_ oracle) _
  rintro ⟨first, label⟩ ⟨second, label'⟩ same
  have pair := cellInput_injective (a₁ := (first.val, label)) (a₂ := (second.val, label')) same
  simp only [Prod.mk.injEq] at pair ⊢
  exact ⟨Subtype.ext pair.1, pair.2⟩

end Budget

/-! ### The key-averaged failure bound, and the reduction -/

/-- **The per-prefix analysis** (`FailAssembly.keyAveragedFailBound`). For every stage-1 source
(its key averaged out: the key is uniform and independent of the published value), every selected
input with an output point and every stage-1 oracle in which each fixed-key index carries at most
`q < 2^100` entries, the installation of `I^U` fails with mass at most
`abortQueryCharge q = 1/(2^128 − q)` per stage-1 entry at an abort site. -/
def KeyAveragedFailBound : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (source : Stage1Source) (input : AffineInput)
    (target : Point) (oracle : LState) (queries : ℕ),
    queries < 2 ^ 100 → (∀ index, (oracle.fixed index).used ≤ queries) →
      ∑' key, (PMF.uniformOfFintype InputMacKey) key *
          failMass source.publicValue input
            (Lamport.selectedLabels (key.encode (BitInput.ofAffine input))) target oracle ≤
        ENNReal.ofReal (abortQueryCharge queries) * (abortUse oracle : ℝ≥0∞)

/-! ### The reduction -/

/-- A sum against a bound law is the iterated sum. -/
theorem tsum_bind_mul {α β : Type} (p : PMF α) (f : α → PMF β) (value : β → ℝ≥0∞) :
    ∑' b, (p.bind f) b * value b = ∑' a, p a * ∑' b, f a b * value b := by
  simp only [PMF.bind_apply]
  calc ∑' b, (∑' a, p a * f a b) * value b = ∑' b, ∑' a, p a * f a b * value b :=
        tsum_congr fun b => ENNReal.tsum_mul_right.symm
    _ = ∑' a, ∑' b, p a * f a b * value b := ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, f a b * value b := tsum_congr fun a => by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun b => by ring

/-- A sum against a mapped law is a sum against the law. -/
theorem tsum_map_mul {α β : Type} (p : PMF α) (g : α → β) (value : β → ℝ≥0∞) :
    ∑' b, (p.map g) b * value b = ∑' a, p a * value (g a) := by
  rw [← PMF.bind_pure_comp, tsum_bind_mul]
  refine tsum_congr fun a => ?_
  congr 1
  rw [tsum_eq_single (g a)]
  · simp
  · intro other different
    simp [Function.comp_apply, PMF.pure_apply, different]

section Reduction

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **The stage-1 draw collapses onto the source.** -/
theorem stage1_collapse (parameter : ℕ) (value : Public × Stage1Source × LState → ℝ≥0∞) :
    ∑' first, (planBAbstractSimulator idealSamplers).stage1 parameter LazyOracle.empty
        (some first) * value first =
      ∑' source, PMF.uniformOfFintype Stage1Source source *
        value (source.publicValue, source, LazyOracle.empty) := by
  show ∑' first : Public × Stage1Source × LState,
      (((PMF.uniformOfFintype Stage1Source).map some).map
        (Option.map fun source => (source.publicValue, source, LazyOracle.empty))) (some first) *
          value first = _
  rw [PMF.map_comp]
  let extend : Option (Public × Stage1Source × LState) → ℝ≥0∞ := fun option =>
    match option with
    | none => 0
    | some first => value first
  calc ∑' first : Public × Stage1Source × LState,
        ((PMF.uniformOfFintype Stage1Source).map
          (Option.map (fun source : Stage1Source => (source.publicValue, source,
            (LazyOracle.empty : LState))) ∘ some)) (some first) * value first
      = ∑' option : Option (Public × Stage1Source × LState),
          ((PMF.uniformOfFintype Stage1Source).map
            (Option.map (fun source : Stage1Source => (source.publicValue, source,
              (LazyOracle.empty : LState))) ∘ some)) option * extend option := by
        rw [tsum_option _ ENNReal.summable]
        simp only [extend, mul_zero, zero_add]
    _ = _ := tsum_map_mul _ _ _

/-- The same collapse for the opened simulators (same stage 1). -/
theorem stage1_collapse_opened (rows : RowsKernel) (install : Installation) (parameter : ℕ)
    (value : Public × Stage1Source × LState → ℝ≥0∞) :
    ∑' first : Public × Stage1Source × LState, (openedSimulator rows install).stage1 parameter
        LazyOracle.empty (some first) * value first =
      ∑' source, PMF.uniformOfFintype Stage1Source source *
        value (source.publicValue, source, LazyOracle.empty) :=
  stage1_collapse parameter value

/-- **The key averages out separately.** -/
theorem key_average (value : Stage1Source → ℝ≥0∞) :
    ∑' source, PMF.uniformOfFintype Stage1Source source * value source =
      ∑' source, PMF.uniformOfFintype Stage1Source source *
        ∑' key, PMF.uniformOfFintype InputMacKey key * value (withKey source key) := by
  conv_lhs => rw [← uniform_withKey]
  rw [tsum_bind_mul]
  exact tsum_congr fun source => by rw [tsum_map_mul]

/-- **The prefix average of the entries at the abort sites is at most `q₁`.** -/
theorem stageOneMean_abortUse_le (adversary : PlanBAdversary Unit) (parameter : ℕ) :
    stageOneMean adversary parameter (fun oracle => (abortUse oracle : ℝ≥0∞)) ≤
      (adversary.firstQueryBudget parameter : ℝ≥0∞) := by
  refine le_trans ?_ (stageOneMean_entryPotential_le
    (Subtype.val : {index : FixedIndex // IsFoldAbort index} → FixedIndex) Subtype.val_injective
    adversary parameter)
  unfold stageOneMean
  refine ENNReal.tsum_le_tsum fun first => mul_le_mul_of_nonneg_left
    (ENNReal.tsum_le_tsum fun chosen => mul_le_mul_of_nonneg_left ?_ zero_le) zero_le
  show (abortUse chosen.2 : ℝ≥0∞) ≤ (entryPotential Subtype.val chosen.2 : ℝ≥0∞)
  exact_mod_cast abortUse_le_entryPotential chosen.2

end Reduction

/-- **The opened games at two installations** are within the prefix average of any bound on their
stage-2 kernels (the stage-1 kernels are the same). -/
theorem openedGame_etvDist_le [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (rows : RowsKernel) (first second : Installation)
    (bound : Stage1Source → AffineInput → Option Point → LState → ℝ≥0∞)
    (close : ∀ source input output oracle,
      ((openedSimulator rows first).stage2 source input output oracle).etvDist
        ((openedSimulator rows second).stage2 source input output oracle) ≤
          bound source input output oracle)
    (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar) :
    (abstractIdealGame Scheme.scheme (openedSimulator rows first) adversary parameter scalar
        ()).etvDist
      (abstractIdealGame Scheme.scheme (openedSimulator rows second) adversary parameter scalar
        ()) ≤
      ∑' start : Public × Stage1Source × LState, (openedSimulator rows second).stage1 parameter
          LazyOracle.empty (some start) *
        ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter start.1 ()) start.2.2)
          chosen * bound start.2.1 chosen.1.1 (Scheme.scheme.function scalar chosen.1.1)
            chosen.2 := by
  unfold abstractIdealGame
  refine le_trans (Kriterion.ArgoMAC.Security.Phase3.etvDist_map_le' _ _ _) ?_
  refine le_trans (optionT_bind_etvDist_le _ _ _) ?_
  refine ENNReal.tsum_le_tsum fun start => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  obtain ⟨circuit, state, oracle⟩ := start
  refine le_trans (optionT_lift_bind_etvDist_le _ _ _) ?_
  refine ENNReal.tsum_le_tsum fun chosen => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  obtain ⟨selected, chosen⟩ := chosen
  refine le_trans (optionT_bind_mk_etvDist_le _ _ _) ?_
  exact close _ _ _ _

end

end Kriterion.ArgoMAC.Phase3.Lazy
