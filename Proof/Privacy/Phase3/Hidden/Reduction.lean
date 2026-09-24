/-
**Phase 3, P1c — hop (1), `G0U → G1U`: the reduction to two guessing bounds.**

(Moved from `Hidden.lean` by P1f; `Designed` now also reads the scalar.)

### What is proved here (axiom-clean)

`hidden_of_guess` — **`GameUntilBad G0U G1U L1` from the two remaining obligations**:

* `StageOneGuess ε`: given the stage-1 view `(published value, EncPRF entries)`, every answered query
  touches the garbler's non-EncPRF entries with conditional mass `≤ ε`;
* `StageTwoGuess D ε`: for every input `u`, given the stage-2 view `(stage-1 view, labels of u,
  designed-visible entries at u)`, every answered query touches the remaining (hidden) entries with
  conditional mass `≤ ε`;

with `ε = 3/2^128 + 2/(p−1)` (`hiddenCharge`), L1's per-query constant exactly: the union bound
(`touch_mass_le`) charges `ε` per logged query, `q₁ + q₂` of them. Step 1 — `G0U` equals its lazy form
`plantedHybrid`, the garbler's whole transcript planted before stage 1 — is **real**
(`eagerLazyG0U`, from `fullSwapInvariant`).

### The proof

For every tape (`TwoStage`): `G0U` (via `EagerLazyG0U`, stage 1 from the whole transcript) and
`G1U` (stage 1 from the EncPRF entries, `visibleEntries` installed at the input choice) **both
dominate** one flagged sub-law — the designed game `G1U(D)` (only the entries `D` keeps planted at
the input choice) killed at a stage-1 touch of the non-EncPRF entries or a stage-2 touch of what
`D` hides (`eagerPlanted_ge`, `lateInstalled_ge`; the generic `dominate` twice). Two games
dominating one flagged law are within its missing mass (`advantage_le_of_dominated`), which is the
two touch masses (`flagged_total_ge`), each bounded by the union bound (`touch_mass_le`, stage 2
through `guess_bind` at the adversary's own input).

**Why the designed game `D`, not `G1U` itself.** `visibleEntries` is the evaluator's reach on the
eager tape, so it contains a hidden-type entry whenever the reach *coincides* with it (e.g. a gadget
point at a differing position when `Δ = pad₀ ⊕ pad₁`). Conditioned on such a coincidence the view
determines `Δ`, so the pointwise stage-2 guessing bound is **false** for `D = visibleEntries`: its
rare views break it, and their mass is not linear in `q`. The designed set (the entries at the
points the evaluator is meant to hold: inactive fold parents, the hash inputs of inactive switches,
agreeing gadget positions, and system B and `hash(bridgeInput t)` only on the curve) carries no
coincidence information, and `G1U` still dominates the designed flagged law because it plants a
superset.
-/

import Proof.Privacy.Phase3.Hidden.Guess
import Proof.Privacy.Phase3.Hidden.Resample
import Proof.Privacy.Phase3.Hidden.Masks
import Proof.Privacy.Phase3.Hidden.Deleted
import Proof.Privacy.Phase3.UntilBadIff

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Phase3.Glue (HybridGame PlanBAdversary)
open Hidden
open Kriterion.ArgoMAC.Security.OperationalOracle (SparsePermutation)
open scoped ENNReal

noncomputable section

/-! ### Transcripts are consistent with their oracle -/

theorem transcript_consistent {α : Type} (oracle : Oracle) (computation : FreeQuery Programs.Spec α) :
    Consistent oracle (transcript (publicAnswer oracle) computation) := by
  induction computation with
  | pure value => intro entry member; cases member
  | query request next ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · rfl
      · exact ih _ entry member

theorem isEnc_of_fixedPair {entry : Entry FixedIndex EncPRF.PermutationIndex} {i : FixedIndex}
    {x y : Fin (2 ^ 128)} (pair : fixedPair entry = some (i, x, y)) : entry.IsEnc = false := by
  obtain ⟨request, answer⟩ := entry
  cases request <;> simp_all [fixedPair, Entry.IsEnc]

theorem isEnc_of_hashPair {entry : Entry FixedIndex EncPRF.PermutationIndex} {key : BaseField}
    {value : Block × Block} (pair : hashPair entry = some (key, value)) : entry.IsEnc = false := by
  obtain ⟨request, answer⟩ := entry
  cases request <;> simp_all [hashPair, Entry.IsEnc]

theorem isEnc_of_encPair {entry : Entry FixedIndex EncPRF.PermutationIndex} {i : EncPRF.PermutationIndex}
    {x y : Fin (2 ^ 128)} (pair : encPair entry = some (i, x, y)) : entry.IsEnc = true := by
  obtain ⟨request, answer⟩ := entry
  cases request <;> simp_all [encPair, Entry.IsEnc]

section Instances

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
  [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The empty state -/

theorem look_empty (x : Fin (2 ^ 128)) : look (SparsePermutation.empty (2 ^ 128)) x = none := by
  apply look_eq_none.mpr
  show ¬ (_ : ℕ) < 0
  omega

theorem compat_empty (oracle : Oracle) (entries : List (Entry FixedIndex EncPRF.PermutationIndex))
    (consistent : Consistent oracle entries) :
    Compat oracle entries (LazyOracle.empty : LState FixedIndex EncPRF.PermutationIndex) := by
  refine ⟨consistent, fun _ _ i x y _ => Or.inr ⟨?_, ?_⟩, fun _ _ i x y _ => Or.inr ⟨?_, ?_⟩,
    fun _ _ key value _ => Or.inl rfl⟩
  · show ¬ (_ : ℕ) < 0
    omega
  · show ¬ (_ : ℕ) < 0
    omega
  · show ¬ (_ : ℕ) < 0
    omega
  · show ¬ (_ : ℕ) < 0
    omega

/-! ### The pieces of one tape -/

/-- The garbler's EncPRF entries. -/
def encEntries (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    List (Entry FixedIndex EncPRF.PermutationIndex) :=
  (garblerTranscript scalar tape).filter Entry.IsEnc

/-- The garbler's other entries: fixed-key and hash. -/
def plainEntries (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    List (Entry FixedIndex EncPRF.PermutationIndex) :=
  (garblerTranscript scalar tape).filter fun entry => !entry.IsEnc

/-- The stage-1 view: the published value and the EncPRF entries. -/
def stageOneView (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    Public × List (Entry FixedIndex EncPRF.PermutationIndex) :=
  ((Scheme.scheme.garble parameter scalar tape).1, encEntries scalar tape)

/-- The stage-1 extra entries: every non-EncPRF entry of the garbler. -/
def stageOneExtra (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    Extra FixedIndex EncPRF.PermutationIndex :=
  extraOf tape.2 (plainEntries scalar tape)

/-- A designed-visibility rule: which reached garbler entries count as visible at an input. It
may read the scalar (the gadget's exceptional inputs are the scalar's digits' offsets). -/
abbrev Designed :=
  NonZeroScalar → (Coins × Oracle) → AffineInput → Entry FixedIndex EncPRF.PermutationIndex → Bool

/-- The designed-visible entries at an input. -/
def designedEntries (designed : Designed) (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) (input : AffineInput) : List (Entry FixedIndex EncPRF.PermutationIndex) :=
  let garbled := Scheme.scheme.garble parameter scalar tape
  (visibleEntries scalar tape garbled.1 input (Scheme.scheme.encode garbled.2 input)).filter
    (designed scalar tape input)

/-- The stage-2 view at an input: the stage-1 view, the labels, the designed-visible entries. -/
def stageTwoView (designed : Designed) (parameter : ℕ) (scalar : NonZeroScalar)
    (input : AffineInput) (tape : Coins × Oracle) :
    (Public × List (Entry FixedIndex EncPRF.PermutationIndex)) × LamportSignature ×
      List (Entry FixedIndex EncPRF.PermutationIndex) :=
  (stageOneView parameter scalar tape,
    Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input,
    designedEntries designed parameter scalar tape input)

/-- The stage-2 extra entries at an input: the non-EncPRF entries that are not designed-visible. -/
def stageTwoExtra (designed : Designed) (parameter : ℕ) (scalar : NonZeroScalar)
    (input : AffineInput) (tape : Coins × Oracle) : Extra FixedIndex EncPRF.PermutationIndex :=
  dropAll (stageOneExtra scalar tape) (designedEntries designed parameter scalar tape input)

end Instances

/-! ### `G0U` in lazy form, and the obligations -/

/-- **`G0U`, lazily**: the whole garbler transcript planted into the lazy oracle before stage 1. -/
def plantedHybrid : HybridGame := fun adversary parameter scalar =>
  swappedChallengeTape.bind fun tape =>
    let garbled := Scheme.scheme.garble parameter scalar tape
    (LazyOracle.run (adversary.chooseInput parameter garbled.1 ())
        (installAll (garblerTranscript scalar tape) LazyOracle.empty)).bind fun selected =>
      (LazyOracle.run (adversary.decide parameter garbled.1
          (Scheme.scheme.encode garbled.2 selected.1.1) () selected.1.2) selected.2).map Prod.fst

/-- **Obligation 1 (step 1, eager = lazy)**: `G0U` is its lazy form. -/
def EagerLazyG0U : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
    [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar),
    maskSwappedHybrid adversary parameter scalar = plantedHybrid adversary parameter scalar

/-- **Obligation 2 (stage-1 guessing bound)**: given the stage-1 view, an answered query touches
the garbler's non-EncPRF entries with conditional mass at most `ε`. -/
def StageOneGuess (ε : ℝ≥0∞) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
    [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (parameter : ℕ) (scalar : NonZeroScalar)
    (view : Public × List (Entry FixedIndex EncPRF.PermutationIndex))
    (entry : Entry FixedIndex EncPRF.PermutationIndex),
    swappedChallengeTape.toOuterMeasure
        {tape | stageOneView parameter scalar tape = view ∧ Touches (stageOneExtra scalar tape) entry} ≤
      ε * swappedChallengeTape.toOuterMeasure {tape | stageOneView parameter scalar tape = view}

/-- **Obligation 3 (stage-2 guessing bound, per input)**: given the stage-2 view at `u`, an
answered query touches the entries `designed` hides with conditional mass at most `ε`. -/
def StageTwoGuess (designed : Designed) (ε : ℝ≥0∞) : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
    [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (view : (Public × List (Entry FixedIndex EncPRF.PermutationIndex)) × LamportSignature ×
      List (Entry FixedIndex EncPRF.PermutationIndex))
    (entry : Entry FixedIndex EncPRF.PermutationIndex),
    swappedChallengeTape.toOuterMeasure
        {tape | stageTwoView designed parameter scalar input tape = view ∧
          Touches (stageTwoExtra designed parameter scalar input tape) entry} ≤
      ε * swappedChallengeTape.toOuterMeasure
        {tape | stageTwoView designed parameter scalar input tape = view}

/-- `L1`'s per-query charge, `3/2^128 + 2/(p − 1)`: a hash query pays the larger of one scale
site's label guess (`2^-128`) and the bridge input's guess (`2/(p − 1)`, `bridgeInput` is at most
two-to-one), a fixed-key query its input and output hits (`2 · 2^-128`). -/
def hiddenCharge : ℝ := 3 / 2 ^ 128 + 2 / ((baseFieldModulus : ℝ) - 1)

theorem hiddenCharge_nonneg : 0 ≤ hiddenCharge := by
  have big : (1 : ℝ) ≤ baseFieldModulus := by exact_mod_cast baseFieldModulus_pos
  unfold hiddenCharge
  exact add_nonneg (by positivity) (div_nonneg (by norm_num) (by linarith))

theorem hiddenPointError_eq (queries : ℕ) :
    Kriterion.ArgoMAC.Phase3.Glue.hiddenPointError queries = queries * hiddenCharge := by
  unfold Kriterion.ArgoMAC.Phase3.Glue.hiddenPointError hiddenCharge
  ring

/-! ### The reduction -/

section Reduction

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
  [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

theorem bind_apply_expect {α : Type} (μ : PMF α) (f : α → PMF Bool) (b : Bool) :
    (μ.bind f) b = expect μ (fun a => f a b) := by
  rw [PMF.bind_apply]
  rfl

theorem map_fst_apply (p : PMF (Bool × LState FixedIndex EncPRF.PermutationIndex)) (b : Bool) :
    (p.map Prod.fst) b = atBool p b := by
  rw [PMF.map_apply]
  unfold atBool expect
  refine tsum_congr fun o => ?_
  beta_reduce
  by_cases h : o.1 = b
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

/-- The stage-1 relation: the whole transcript against its EncPRF part. -/
theorem stageOne_rel (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    Rel (plantAll (garblerTranscript scalar tape) LazyOracle.empty)
      (plantAll (encEntries scalar tape) LazyOracle.empty) (stageOneExtra scalar tape) := by
  classical
  have consistent : Consistent tape.2 (garblerTranscript scalar tape) :=
    transcript_consistent tape.2 (Programs.garbleM scalar tape.1)
  have encConsistent : Consistent tape.2 (encEntries scalar tape) :=
    fun e member => consistent e (List.mem_filter.mp member).1
  have compat := compat_empty tape.2 _ consistent
  have encCompat := compat_empty tape.2 _ encConsistent
  have encNoFixed : ∀ i x y, ¬ look (((plantAll (encEntries scalar tape) LazyOracle.empty :
      LState FixedIndex EncPRF.PermutationIndex)).fixed i) x = some y := by
    intro i x y found
    rcases (plantAll_look tape.2 _ _ encCompat i x y).mp found with found | ⟨e, member, pair⟩
    · rw [show (LazyOracle.empty : LState FixedIndex EncPRF.PermutationIndex).fixed i =
        SparsePermutation.empty _ from rfl, look_empty] at found
      cases found
    · have := (List.mem_filter.mp member).2
      rw [isEnc_of_fixedPair pair] at this
      cases this
  refine ⟨fun i => ⟨fun x y => ?_, fun x y _ => ?_, fun x y _ x' found => encNoFixed i x' y found⟩,
    fun i => ⟨fun x y => ?_, fun x y extra => ?_, fun x y extra => ?_⟩,
    fun key absent => ?_, fun key value extra => ?_⟩
  · rw [plantAll_look tape.2 _ _ compat i x y]
    rw [show (LazyOracle.empty : LState FixedIndex EncPRF.PermutationIndex).fixed i =
      SparsePermutation.empty _ from rfl, look_empty]
    constructor
    · rintro (h | ⟨e, member, pair⟩)
      · cases h
      · exact Or.inr ⟨e, List.mem_filter.mpr ⟨member, by simp [isEnc_of_fixedPair pair]⟩, pair⟩
    · rintro (h | ⟨e, member, pair⟩)
      · exact (encNoFixed i x y h).elim
      · exact Or.inr ⟨e, (List.mem_filter.mp member).1, pair⟩
  · rcases h : look ((plantAll (encEntries scalar tape) LazyOracle.empty :
        LState FixedIndex EncPRF.PermutationIndex).fixed i) x with _ | y'
    · rfl
    · exact (encNoFixed i x y' h).elim
  · rw [plantAll_encLook tape.2 _ _ compat i x y, plantAll_encLook tape.2 _ _ encCompat i x y]
    rw [show (LazyOracle.empty : LState FixedIndex EncPRF.PermutationIndex).enc i =
      SparsePermutation.empty _ from rfl, look_empty]
    constructor
    · rintro (h | ⟨e, member, pair⟩)
      · cases h
      · exact Or.inl (Or.inr ⟨e, List.mem_filter.mpr ⟨member, isEnc_of_encPair pair⟩, pair⟩)
    · rintro ((h | ⟨e, member, pair⟩) | ⟨e, member, pair⟩)
      · cases h
      · exact Or.inr ⟨e, (List.mem_filter.mp member).1, pair⟩
      · have := (List.mem_filter.mp member).2
        rw [isEnc_of_encPair pair] at this
        cases this
  · obtain ⟨e, member, pair⟩ := extra
    have := (List.mem_filter.mp member).2
    rw [isEnc_of_encPair pair] at this
    cases this
  · obtain ⟨e, member, pair⟩ := extra
    have := (List.mem_filter.mp member).2
    rw [isEnc_of_encPair pair] at this
    cases this
  · rw [plantAll_hashLookup tape.2 _ _ compat key, plantAll_hashLookup tape.2 _ _ encCompat key]
    have notListed : ¬ ∃ e ∈ plainEntries scalar tape, ∃ value, hashPair e = some (key, value) := by
      intro listed
      simp only [stageOneExtra, extraOf] at absent
      rw [if_pos listed] at absent
      cases absent
    have notInT : ¬ ∃ e ∈ garblerTranscript scalar tape, ∃ value, hashPair e = some (key, value) := by
      rintro ⟨e, member, value, pair⟩
      exact notListed ⟨e, List.mem_filter.mpr ⟨member, by simp [isEnc_of_hashPair pair]⟩, value, pair⟩
    have notInEnc : ¬ ∃ e ∈ encEntries scalar tape, ∃ value, hashPair e = some (key, value) := by
      rintro ⟨e, member, value, pair⟩
      exact notInT ⟨e, (List.mem_filter.mp member).1, value, pair⟩
    rw [if_neg (fun both => notInT both.2), if_neg (fun both => notInEnc both.2)]
  · have listed : ∃ e ∈ plainEntries scalar tape, ∃ value, hashPair e = some (key, value) := by
      by_contra notListed
      simp only [stageOneExtra, extraOf] at extra
      rw [if_neg notListed] at extra
      cases extra
    have storedValue : value = codeOf (tape.2.2.2 key) := by
      simp only [stageOneExtra, extraOf] at extra
      rw [if_pos listed] at extra
      exact (Option.some.inj extra).symm
    obtain ⟨e, member, v, pair⟩ := listed
    have notInEnc : ¬ ∃ e ∈ encEntries scalar tape, ∃ value, hashPair e = some (key, value) := by
      rintro ⟨e', member', value', pair'⟩
      have := (List.mem_filter.mp member').2
      rw [isEnc_of_hashPair pair'] at this
      cases this
    rw [plantAll_hashLookup tape.2 _ _ compat key, plantAll_hashLookup tape.2 _ _ encCompat key,
      if_pos ⟨rfl, e, (List.mem_filter.mp member).1, v, pair⟩, if_neg (fun both => notInEnc both.2),
      storedValue]
    exact ⟨rfl, rfl⟩

/-- The EncPRF-only start state avoids every non-EncPRF entry. -/
theorem stageOne_avoid (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    Avoid (plantAll (encEntries scalar tape) LazyOracle.empty) (stageOneExtra scalar tape) := by
  have rel := stageOne_rel scalar tape
  refine ⟨fun i x y extra => ⟨(rel.fixed i).freshIn x y extra, (rel.fixed i).freshOut x y extra⟩,
    fun i x y extra => ⟨(rel.enc i).freshIn x y extra, (rel.enc i).freshOut x y extra⟩,
    fun key value extra => (rel.hashExtra key value extra).2⟩

/-- **The reduction, per game.** -/
theorem hidden_advantage_le (designed : Designed) (ε : ℝ≥0∞) (finite : ε ≠ ⊤)
    (eager : EagerLazyG0U) (one : StageOneGuess ε) (two : StageTwoGuess designed ε)
    (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar) :
    Assumptions.advantage (maskSwappedHybrid adversary parameter scalar)
        (hiddenDeletedHybrid adversary parameter scalar) ≤
      ((adversary.firstQueryBudget parameter : ℝ≥0∞) * ε +
        (adversary.secondQueryBudget parameter : ℝ≥0∞) * ε).toReal := by
  classical
  let μ : PMF (Coins × Oracle) := swappedChallengeTape
  let first := fun tape : Coins × Oracle =>
    adversary.chooseInput parameter (Scheme.scheme.garble parameter scalar tape).1 ()
  let second := fun (tape : Coins × Oracle) (r : AffineInput × adversary.State) =>
    adversary.decide parameter (Scheme.scheme.garble parameter scalar tape).1
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 r.1) () r.2
  let vis := fun (tape : Coins × Oracle) (r : AffineInput × adversary.State) =>
    visibleEntries scalar tape (Scheme.scheme.garble parameter scalar tape).1 r.1
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 r.1)
  let vis'' := fun (tape : Coins × Oracle) (r : AffineInput × adversary.State) =>
    designedEntries designed parameter scalar tape r.1
  let start := fun tape : Coins × Oracle =>
    (plantAll (encEntries scalar tape) LazyOracle.empty : LState FixedIndex EncPRF.PermutationIndex)
  let A : Bool → ℝ≥0∞ := fun b => expect μ fun tape =>
    flaggedMass (first tape) (second tape) (start tape) (stageOneExtra scalar tape) (vis'' tape) b
  have consistent : ∀ tape : Coins × Oracle, Consistent tape.2 (plainEntries scalar tape) :=
    fun tape e member => transcript_consistent tape.2 (Programs.garbleM scalar tape.1) e
      (List.mem_filter.mp member).1
  have visWithin : ∀ tape r, Within (vis tape r) (plainEntries scalar tape) := by
    intro tape r e member
    obtain ⟨inT, flag⟩ := List.mem_filter.mp member
    refine List.mem_filter.mpr ⟨inT, ?_⟩
    simp only [Bool.and_eq_true] at flag
    exact flag.1
  have designedWithin : ∀ tape r, Within (vis'' tape r) (vis tape r) :=
    fun tape r e member => (List.mem_filter.mp member).1
  -- the two games as averages over the tape
  have g0 : ∀ b, maskSwappedHybrid adversary parameter scalar b = expect μ fun tape =>
      eagerPlanted (first tape) (second tape)
        (plantAll (garblerTranscript scalar tape) LazyOracle.empty) b := by
    intro b
    rw [eager adversary parameter scalar]
    unfold plantedHybrid
    rw [bind_apply_expect]
    refine congrArg (expect μ) (funext fun tape => ?_)
    rw [bind_apply_expect]
    unfold eagerPlanted
    refine congrArg (expect _) (funext fun r => ?_)
    exact map_fst_apply _ b
  have g1 : ∀ b, hiddenDeletedHybrid adversary parameter scalar b = expect μ fun tape =>
      lateInstalled (first tape) (second tape) (start tape) (vis tape) b := by
    intro b
    unfold hiddenDeletedHybrid
    rw [bind_apply_expect]
    refine congrArg (expect μ) (funext fun tape => ?_)
    rw [bind_apply_expect]
    unfold lateInstalled
    refine congrArg (expect _) (funext fun r => ?_)
    exact map_fst_apply _ b
  have ge0 : ∀ b, A b ≤ maskSwappedHybrid adversary parameter scalar b := by
    intro b
    rw [g0]
    exact expect_mono _ fun tape => eagerPlanted_ge (first tape) (second tape) tape.2
      (plainEntries scalar tape) (consistent tape) (stageOne_rel scalar tape) (vis'' tape)
      (fun r e member => visWithin tape r e (designedWithin tape r e member)) b
  have ge1 : ∀ b, A b ≤ hiddenDeletedHybrid adversary parameter scalar b := by
    intro b
    rw [g1]
    exact expect_mono _ fun tape => lateInstalled_ge (first tape) (second tape) tape.2
      (plainEntries scalar tape) (consistent tape) (stageOne_avoid scalar tape) (vis tape)
      (vis'' tape) (visWithin tape) (designedWithin tape) b
  -- the two touch masses
  let run₁ := fun view : Public × List (Entry FixedIndex EncPRF.PermutationIndex) =>
    runLog (adversary.chooseInput parameter view.1 ()) (plantAll view.2 LazyOracle.empty :
      LState FixedIndex EncPRF.PermutationIndex)
  have touch₁ : expect μ (fun tape => expect (runLog (first tape) (start tape))
      (fun o => 1 - cleanWeight (stageOneExtra scalar tape) o.2.2)) ≤
      (adversary.firstQueryBudget parameter : ℝ≥0∞) * ε := by
    have bound := touch_mass_le μ (stageOneView parameter scalar) (stageOneExtra scalar)
      (fun view => (run₁ view).map fun o => ((o.1, o.2.1), o.2.2))
      (adversary.firstQueryBudget parameter)
      (fun view o member => by
        rw [PMF.support_map] at member
        obtain ⟨o', member', rfl⟩ := member
        exact runLog_length _ _ o' member')
      ε (one parameter scalar)
    refine le_trans (le_of_eq ?_) bound
    refine congrArg (expect μ) (funext fun tape => ?_)
    rw [expect_map]
    simp only [run₁, first, start, stageOneView]
  let W := fun (z : (AffineInput × adversary.State) × LState FixedIndex EncPRF.PermutationIndex ×
      List (Entry FixedIndex EncPRF.PermutationIndex)) (tape : Coins × Oracle) =>
    stageTwoView designed parameter scalar z.1.1 tape
  let extra₂ := fun (z : (AffineInput × adversary.State) × LState FixedIndex EncPRF.PermutationIndex ×
      List (Entry FixedIndex EncPRF.PermutationIndex)) (tape : Coins × Oracle) =>
    stageTwoExtra designed parameter scalar z.1.1 tape
  let μ₂ := μ.bind fun tape => (run₁ (stageOneView parameter scalar tape)).map fun z => (tape, z)
  let run₂ := fun (view : ((Public × List (Entry FixedIndex EncPRF.PermutationIndex)) ×
      LamportSignature × List (Entry FixedIndex EncPRF.PermutationIndex)) ×
      ((AffineInput × adversary.State) × LState FixedIndex EncPRF.PermutationIndex ×
        List (Entry FixedIndex EncPRF.PermutationIndex))) =>
    (runLog (adversary.decide parameter view.1.1.1 view.1.2.1 () view.2.1.2)
      (plantAll view.1.2.2 view.2.2.1)).map fun o => ((o.1, o.2.1), o.2.2)
  have touch₂ : expect μ (fun tape => expect (runLog (first tape) (start tape)) (fun o =>
      expect (runLog (second tape o.1) (plantAll (vis'' tape o.1) o.2.1))
        fun o₂ => 1 - cleanWeight (dropAll (stageOneExtra scalar tape) (vis'' tape o.1)) o₂.2.2)) ≤
      (adversary.secondQueryBudget parameter : ℝ≥0∞) * ε := by
    have guess := guess_bind μ (stageOneView parameter scalar) run₁ W Prod.fst (fun _ _ => rfl)
      extra₂ ε (fun z w e => two parameter scalar z.1.1 w e)
    have bound := touch_mass_le μ₂ (fun p => (W p.2 p.1, p.2)) (fun p => extra₂ p.2 p.1) run₂
      (adversary.secondQueryBudget parameter)
      (fun view o member => by
        rw [PMF.support_map] at member
        obtain ⟨o', member', rfl⟩ := member
        exact runLog_length _ _ o' member')
      ε guess
    refine le_trans (le_of_eq ?_) bound
    rw [expect_bind]
    refine congrArg (expect μ) (funext fun tape => ?_)
    rw [expect_map]
    simp only [run₁, first, start, stageOneView]
    refine congrArg (expect _) (funext fun z => ?_)
    rw [expect_map]
    simp only [W, extra₂, second, vis'', stageTwoView, stageTwoExtra, stageOneView]
  -- the missing mass
  have sumLe : ∀ tape, flaggedMass (first tape) (second tape) (start tape) (stageOneExtra scalar tape)
      (vis'' tape) true + flaggedMass (first tape) (second tape) (start tape)
      (stageOneExtra scalar tape) (vis'' tape) false ≤ 1 := by
    intro tape
    rw [flagged_sum]
    exact expect_le_one _ fun o => le_trans (mul_le_mul' (cleanWeight_le_one _ _)
      (expect_le_one _ fun o₂ => cleanWeight_le_one _ _)) (le_of_eq (one_mul 1))
  have missing : 1 - (A true + A false) ≤
      (adversary.firstQueryBudget parameter : ℝ≥0∞) * ε +
        (adversary.secondQueryBudget parameter : ℝ≥0∞) * ε := by
    have sumA : A true + A false = expect μ fun tape =>
        flaggedMass (first tape) (second tape) (start tape) (stageOneExtra scalar tape) (vis'' tape) true +
          flaggedMass (first tape) (second tape) (start tape) (stageOneExtra scalar tape) (vis'' tape) false :=
      (expect_add _ _ _).symm
    rw [sumA, ← expect_one_sub _ sumLe]
    refine le_trans (expect_mono _ fun tape => flagged_total_ge (first tape) (second tape) (start tape)
      (stageOneExtra scalar tape) (vis'' tape)) ?_
    rw [expect_add]
    exact add_le_add touch₁ touch₂
  exact advantage_le_of_dominated _ _ A ge0 ge1 _ missing
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) finite,
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) finite⟩)

end Reduction

/-- **Hop (1) from the three obligations**: `G0U → G1U` is identical until the designed-hidden
entries are touched, at `L1 = hiddenPointError (q₁ + q₂)`, per query `3/2^128 + 2/(p−1)`. -/
theorem hidden_of (designed : Designed) (eager : EagerLazyG0U)
    (one : StageOneGuess (ENNReal.ofReal hiddenCharge))
    (two : StageTwoGuess designed (ENNReal.ofReal hiddenCharge)) :
    Kriterion.ArgoMAC.Phase3.Glue.GameUntilBad maskSwappedHybrid hiddenDeletedHybrid
      fun first second => Kriterion.ArgoMAC.Phase3.Glue.hiddenPointError (first + second) := by
  intro field group adversary parameter scalar _
  apply untilBad_of_advantage_le
  have bound := @hidden_advantage_le field group (Fintype.ofFinite _) (Fintype.ofFinite _)
    (Classical.decEq _) (Classical.decEq _) designed (ENNReal.ofReal hiddenCharge)
    ENNReal.ofReal_ne_top eager one two adversary parameter scalar
  refine le_trans bound (le_of_eq ?_)
  rw [← add_mul, ← Nat.cast_add, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hiddenCharge_nonneg]
  beta_reduce
  rw [hiddenPointError_eq]

/-! ### Step 1, reduced: eager = lazy from the tape's resampling invariance -/

/-- **The swapped tape is invariant under resampling off the garbler's transcript**, jointly with
the garbling: drawing the tape, then an oracle uniformly among the completions of the planted
transcript, has the law of (garbling, the tape's own oracle). This is the only fact step 1 needs;
it mentions no adversary. -/
def SwapInvariant : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
    [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (parameter : ℕ) (scalar : NonZeroScalar),
    swappedChallengeTape.bind (fun tape =>
        (Kriterion.ArgoMAC.Phase3.Glue.publicCompletion
          (installAll (garblerTranscript scalar tape) LazyOracle.empty)).map
          fun oracle => (Scheme.scheme.garble parameter scalar tape, oracle)) =
      swappedChallengeTape.map fun tape => (Scheme.scheme.garble parameter scalar tape, tape.2)

section EagerLazy

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
  [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- Both adversary stages against one eager oracle. -/
def eagerAfter (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (garbled : Public × InputMacKey) (oracle : Oracle) : PMF Bool :=
  ((adversary.chooseInput parameter garbled.1 ()).run (publicHandler id) oracle).bind fun selected =>
    ((adversary.decide parameter garbled.1 (Scheme.scheme.encode garbled.2 selected.1.1) ()
      selected.1.2).run (publicHandler id) selected.2).map Prod.fst

/-- Both adversary stages against the lazy oracle. -/
def lazyAfter (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (garbled : Public × InputMacKey) (state : LState FixedIndex EncPRF.PermutationIndex) : PMF Bool :=
  (LazyOracle.run (adversary.chooseInput parameter garbled.1 ()) state).bind fun selected =>
    (LazyOracle.run (adversary.decide parameter garbled.1
      (Scheme.scheme.encode garbled.2 selected.1.1) () selected.1.2) selected.2).map Prod.fst

/-- The lazy two-stage run is the completion average of the eager one (`lazy_real_uniform`). -/
theorem completion_eagerAfter (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (garbled : Public × InputMacKey) (state : LState FixedIndex EncPRF.PermutationIndex) :
    (Kriterion.ArgoMAC.Phase3.Glue.publicCompletion state).bind
        (eagerAfter adversary parameter garbled) = lazyAfter adversary parameter garbled state := by
  have law := congrArg
    (fun distribution : PMF ((AffineInput × adversary.State) × Oracle) =>
      distribution.bind fun selected =>
        ((adversary.decide parameter garbled.1 (Scheme.scheme.encode garbled.2 selected.1.1) ()
          selected.1.2).run (publicHandler id) selected.2).map Prod.fst)
    (Kriterion.ArgoMAC.Phase3.Glue.public_run (adversary.chooseInput parameter garbled.1 ()) state)
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at law
  unfold eagerAfter lazyAfter
  rw [law]
  congr 1
  funext selected
  exact Kriterion.ArgoMAC.Phase3.Glue.public_run_result _ _

theorem bind_congr_support {α β : Type} (p : PMF α) (f g : α → PMF β)
    (same : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases zero : p a = 0
  · simp [zero]
  · rw [same a ((PMF.mem_support_iff _ _).mpr zero)]

/-- `G0U` is the eager two-stage run on the tape's oracle. -/
theorem maskSwapped_eq_eager (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    maskSwappedHybrid adversary parameter scalar =
      swappedChallengeTape.bind fun tape =>
        eagerAfter adversary parameter (Scheme.scheme.garble parameter scalar tape) tape.2 := by
  unfold maskSwappedHybrid realGame
  congr 1
  funext tape
  unfold eagerAfter
  dsimp only
  rw [Kriterion.ArgoMAC.Phase3.Glue.public_run_tape (project := Prod.snd), PMF.bind_map]
  refine bind_congr_support _ _ _ fun selected member => ?_
  have state := Kriterion.ArgoMAC.Phase3.Glue.eager_run_state _ tape.2 selected member
  simp only [Function.comp_apply]
  rw [Kriterion.ArgoMAC.Phase3.Glue.public_run_tape (project := Prod.snd), PMF.map_comp, state]
  rfl

/-- **Step 1 from the invariance.** -/
theorem eagerLazy_of_invariant (invariant : SwapInvariant) : EagerLazyG0U := by
  intro field group fixedFintype encFintype fixedEq encEq adversary parameter scalar
  rw [maskSwapped_eq_eager]
  unfold plantedHybrid
  have lazy : ∀ tape : Coins × Oracle,
      (LazyOracle.run (adversary.chooseInput parameter (Scheme.scheme.garble parameter scalar tape).1 ())
          (installAll (garblerTranscript scalar tape) LazyOracle.empty)).bind (fun selected =>
        (LazyOracle.run (adversary.decide parameter (Scheme.scheme.garble parameter scalar tape).1
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 selected.1.1) ()
            selected.1.2) selected.2).map Prod.fst) =
        (Kriterion.ArgoMAC.Phase3.Glue.publicCompletion
          (installAll (garblerTranscript scalar tape) LazyOracle.empty)).bind
          (eagerAfter adversary parameter (Scheme.scheme.garble parameter scalar tape)) :=
    fun tape => (completion_eagerAfter adversary parameter _ _).symm
  simp only [lazy]
  have joint := congrArg (fun law : PMF ((Public × InputMacKey) × Oracle) =>
    law.bind fun pair => eagerAfter adversary parameter pair.1 pair.2) (invariant parameter scalar)
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at joint
  exact joint.symm

end EagerLazy

theorem transcript_eq_transcriptOf {α : Type}
    (answer : ∀ query : PublicQuery FixedIndex EncPRF.PermutationIndex, query.Answer)
    (computation : FreeQuery Programs.Spec α) :
    transcript answer computation = transcriptOf answer computation := by
  induction computation with
  | pure value => rfl
  | query request next ih =>
      show _ :: _ = _ :: _
      rw [ih]

/-! ### `SwapInvariant` from the full-tape invariance -/

/-- **The swapped tape is invariant under resampling its oracle off the planted garbler
transcript** (coins kept): the content of step 1 (`fullSwapInvariant`). -/
def FullSwapInvariant : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
    [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex] (scalar : NonZeroScalar),
    swappedChallengeTape.bind (fun tape =>
        (Kriterion.ArgoMAC.Phase3.Glue.publicCompletion
          (installAll (garblerTranscript scalar tape) LazyOracle.empty)).map
          fun oracle => (tape.1, oracle)) = swappedChallengeTape

theorem map_support_congr {α β : Type} (p : PMF α) (f g : α → β)
    (same : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  unfold PMF.map
  exact bind_support_congr _ _ _ fun a member => by rw [Function.comp_apply, same a member]; rfl

theorem swapInvariant_of_full (full : FullSwapInvariant) : SwapInvariant := by
  intro field group fixedFintype encFintype fixedEq encEq parameter scalar
  have sameGarble : ∀ tape : Coins × Oracle, ∀ resampled ∈ (Kriterion.ArgoMAC.Phase3.Glue.publicCompletion
      (installAll (garblerTranscript scalar tape) LazyOracle.empty)).support,
      Scheme.scheme.garble parameter scalar (tape.1, resampled) =
        Scheme.scheme.garble parameter scalar tape := by
    intro tape resampled member
    rw [show garblerTranscript scalar tape = transcriptOf (publicAnswer tape.2)
      (Programs.garbleM scalar tape.1) from transcript_eq_transcriptOf _ _] at member
    have agrees := completion_agrees (Programs.garbleM scalar tape.1) tape.2 resampled member
    have evalSame := (transcriptOf_of_agrees (Programs.garbleM scalar tape.1) tape.2 resampled agrees).2
    rw [← Programs.garbleProgram_correct parameter scalar tape.1 resampled,
      ← Programs.garbleProgram_correct parameter scalar tape.1 tape.2, Programs.garbleProgram,
      FreeQuery.eval_toProgram, FreeQuery.eval_toProgram, evalSame]
  have rewritten : swappedChallengeTape.bind (fun tape =>
      (Kriterion.ArgoMAC.Phase3.Glue.publicCompletion
        (installAll (garblerTranscript scalar tape) LazyOracle.empty)).map
        fun oracle => (Scheme.scheme.garble parameter scalar tape, oracle)) =
      swappedChallengeTape.bind (fun tape =>
      (Kriterion.ArgoMAC.Phase3.Glue.publicCompletion
        (installAll (garblerTranscript scalar tape) LazyOracle.empty)).map
        fun oracle => (Scheme.scheme.garble parameter scalar (tape.1, oracle), oracle)) := by
    refine congrArg (PMF.bind swappedChallengeTape) (funext fun tape => ?_)
    exact map_support_congr _ _ _ fun resampled member => by
      rw [sameGarble tape resampled member]
  rw [rewritten]
  have mapped := congrArg (PMF.map fun tape : Coins × Oracle =>
    (Scheme.scheme.garble parameter scalar tape, tape.2)) (full scalar)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at mapped
  exact mapped

/-! ### `FullSwapInvariant` (real): the swapped tape is a remixture of the uniform one -/

section FullSwap

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
  [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- The resampling kernel on tapes. -/
def resampleKernel (scalar : NonZeroScalar) (tape : Coins × Oracle) : PMF (Coins × Oracle) :=
  (Kriterion.ArgoMAC.Phase3.Glue.publicCompletion
    (installAll (garblerTranscript scalar tape) LazyOracle.empty)).map fun oracle => (tape.1, oracle)

/-- The tape law given the garbler's vectors `m` (the kernel behind both vector laws). -/
def maskComponent (m : MaskVectors) : PMF (Coins × Oracle) :=
  ((restLaw restUniform).bind fun rest =>
    (fibreKernel (limbPoint (garblerLabels rest)) m).map (Prod.mk rest)).map
    fun parts => reassembleEquiv (assemble parts)

theorem swapped_eq_mixture :
    swappedChallengeTape = (PMF.uniformOfFintype MaskVectors).bind maskComponent := by
  unfold swappedChallengeTape swappedTape swapLaw swapKernel maskComponent
  rw [PMF.map_comp]
  simp only [PMF.map_bind]
  rw [PMF.bind_comm]
  simp only [PMF.map_comp, Function.comp_def]

theorem uniform_eq_mixture :
    PMF.uniformOfFintype (Coins × Oracle) =
      ((PMF.uniformOfFintype (LimbSite → Block × Block)).map (masksOf VectorSite.lane)).bind
        maskComponent := by
  rw [uniformTape_eq, realTape_eq, PMF.map_comp]
  unfold realLaw maskComponent
  have split : ∀ rest : RestTape TapeRest,
      (PMF.uniformOfFintype ScaleTable).map (Prod.mk rest) =
        ((PMF.uniformOfFintype (LimbSite → Block × Block)).map (masksOf VectorSite.lane)).bind
          fun m => (fibreKernel (limbPoint (garblerLabels rest)) m).map (Prod.mk rest) := by
    intro rest
    rw [uniform_eq_bind_fibreKernel (limbPoint (garblerLabels rest)), PMF.map_bind]
  simp only [split, PMF.map_bind]
  rw [PMF.bind_comm]
  simp only [PMF.map_comp, Function.comp_def]

theorem maskComponent_supported (m : MaskVectors) (tape : Coins × Oracle)
    (member : tape ∈ (maskComponent m).support) : maskOf tape = m := by
  unfold maskComponent at member
  rw [PMF.support_map] at member
  obtain ⟨⟨rest, scale⟩, member, rfl⟩ := member
  rw [PMF.mem_support_bind_iff] at member
  obtain ⟨rest', _, member⟩ := member
  rw [PMF.support_map] at member
  obtain ⟨scale', inKernel, same⟩ := member
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  have onFibre : maskMap (limbPoint (garblerLabels rest')) scale' = m := by
    have masks := fibreKernel_masks (limbPoint (garblerLabels rest')) m
    have mem : maskMap (limbPoint (garblerLabels rest')) scale' ∈ (PMF.pure m).support := by
      rw [← masks, PMF.support_map]
      exact ⟨scale', inKernel, rfl⟩
    simpa using mem
  show switchMasks (hashOf rest'.2 scale') (garblerLabel rest'.1.2.1
    (garblerKeys rest'.1 (hashOf rest'.2 scale')).1 (garblerKeys rest'.1 (hashOf rest'.2 scale')).2)
      = m
  rw [garblerLabel_hashOf, switchMasks_hashOf, onFibre]

theorem masksOf_full (m : MaskVectors) :
    ((PMF.uniformOfFintype (LimbSite → Block × Block)).map (masksOf VectorSite.lane)) m ≠ 0 := by
  rw [← PMF.mem_support_iff, PMF.support_map]
  obtain ⟨values, same⟩ := masksOf_surjective VectorSite.lane m
  exact ⟨values, by simp [PMF.support_uniformOfFintype], same⟩

theorem resampleKernel_preserves (scalar : NonZeroScalar) (tape tape' : Coins × Oracle)
    (member : tape' ∈ (resampleKernel scalar tape).support) : maskOf tape' = maskOf tape := by
  unfold resampleKernel at member
  rw [PMF.support_map] at member
  obtain ⟨resampled, inCompletion, rfl⟩ := member
  rw [show garblerTranscript scalar tape = transcriptOf (publicAnswer tape.2)
    (Programs.garbleM scalar tape.1) from transcript_eq_transcriptOf _ _] at inCompletion
  exact maskOf_determined tape.1 tape.2 resampled scalar
    (completion_agrees (Programs.garbleM scalar tape.1) tape.2 resampled inCompletion)

theorem map_fun_id {α : Type} (p : PMF α) : p.map (fun x => x) = p := PMF.map_id p

theorem uniform_resample (scalar : NonZeroScalar) :
    (PMF.uniformOfFintype (Coins × Oracle)).bind (resampleKernel scalar) =
      PMF.uniformOfFintype (Coins × Oracle) := by
  rw [← Kriterion.ArgoMAC.Phase3.Glue.uniform_product (A := Coins) (B := Oracle), PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun coins => ?_)
  rw [PMF.bind_map]
  have planted : ∀ oracle : Oracle, installAll (garblerTranscript scalar (coins, oracle))
      LazyOracle.empty = plantAll (transcriptOf (publicAnswer oracle) (Programs.garbleM scalar coins))
        (LazyOracle.empty : LState FixedIndex EncPRF.PermutationIndex) := by
    intro oracle
    rw [garblerTranscript, transcript_eq_transcriptOf]
    rfl
  have marginal := congrArg (PMF.map Prod.snd)
    (resample_joint (Programs.garbleM scalar coins) (LazyOracle.empty : LState FixedIndex EncPRF.PermutationIndex))
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, map_fun_id] at marginal
  rw [Kriterion.ArgoMAC.Phase3.Glue.public_initial] at marginal
  have instances : PMF.uniformOfFintype Oracle =
      PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) := by
    congr 1
  unfold resampleKernel
  simp only [Function.comp_def, planted]
  rw [instances]
  have mapped := congrArg (PMF.map fun oracle : Oracle => (coins, oracle)) marginal
  simp only [PMF.map_bind] at mapped
  exact mapped

end FullSwap

/-- **Step 1's remaining content, real.** -/
theorem fullSwapInvariant : FullSwapInvariant := by
  intro field group fixedFintype encFintype fixedEq encEq scalar
  have invariant := uniform_resample scalar
  rw [uniform_eq_mixture] at invariant
  have result := mixture_invariant (PMF.uniformOfFintype MaskVectors)
    ((PMF.uniformOfFintype (LimbSite → Block × Block)).map (masksOf VectorSite.lane)) maskComponent
    (resampleKernel scalar) maskOf masksOf_full maskComponent_supported
    (resampleKernel_preserves scalar) invariant
  rw [← swapped_eq_mixture] at result
  exact result

/-- **Step 1, real**: `G0U` is its lazy form. -/
theorem eagerLazyG0U : EagerLazyG0U :=
  eagerLazy_of_invariant (swapInvariant_of_full fullSwapInvariant)

/-- **Hop (1) from the two guessing bounds alone.** -/
theorem hidden_of_guess (designed : Designed)
    (one : StageOneGuess (ENNReal.ofReal hiddenCharge))
    (two : StageTwoGuess designed (ENNReal.ofReal hiddenCharge)) :
    Kriterion.ArgoMAC.Phase3.Glue.GameUntilBad maskSwappedHybrid hiddenDeletedHybrid
      fun first second => Kriterion.ArgoMAC.Phase3.Glue.hiddenPointError (first + second) :=
  hidden_of designed eagerLazyG0U one two

end

end Kriterion.ArgoMAC.Security.Phase3
