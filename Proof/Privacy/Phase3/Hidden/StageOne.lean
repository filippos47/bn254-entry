/-
**Phase 3, P1f — `StageOneGuess`, from the bridge-input guess.**

A stage-1 touch of the garbler's non-EncPRF entries (`stageOne_touch`) is

* an input or output hit at one fixed-key index, each at most `2^-128` given the stage-1 view
  (`inputHit_le`, `outputHit_le`): `2 · 2^-128` per fixed-key query;
* a hash query at a scale input `scaleInput ℓ c j i L`, which names one vector site `(ℓ, c, j)` and
  one label `L` (`labelInput_injective`), so it touches only if the garbler's label at that site is
  `L`: at most `2^-128` (`labelHit_le`);
* a hash query at the bridge input `bridgeInput t`: at most `2/p` given the view
  (`StageOneBridgeGuess`, `bridgeInput` being at most two-to-one).

A scale input lies in `[0, 2 ^ 150)` and the bridge input above it, so a hash query pays the larger
of the last two, never their sum. So `StageOneGuess (3/2^128 + 2/(p−1))` follows from one statement
about `t` alone, `StageOneBridgeGuess` (`stageOneGuess_of_bridge`).
-/

import Proof.Privacy.Phase3.Hidden.StageOneFixed

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open scoped ENNReal

noncomputable section

/-- **The stage-1 bridge-input guess**: given the stage-1 view, the bridge input `bridgeInput t`
equals a given key with conditional mass at most `2/p`. -/
def StageOneBridgeGuess : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (view : Public × List (Entry FixedIndex EncPRF.PermutationIndex)) (key : BaseField),
    swappedChallengeTape.toOuterMeasure
        {tape | stageOneView parameter scalar tape = view ∧ bridgeInput tape.1.bridgeKey = key} ≤
      2 * (baseFieldModulus : ℝ≥0∞)⁻¹ *
        swappedChallengeTape.toOuterMeasure {tape | stageOneView parameter scalar tape = view}

/-- `1 < p`, as a real. -/
theorem one_lt_modulus_real : (1 : ℝ) < baseFieldModulus := by
  have big := two_pow_150_lt_baseFieldModulus
  have one : (1 : ℕ) < baseFieldModulus := lt_of_le_of_lt (Nat.one_le_two_pow) big
  exact_mod_cast one

theorem fieldCharge_nonneg : 0 ≤ 2 / ((baseFieldModulus : ℝ) - 1) :=
  div_nonneg (by norm_num) (by linarith [one_lt_modulus_real])

theorem two_block_le_charge : 2 * ((2 : ℝ≥0∞) ^ 128)⁻¹ ≤ ENNReal.ofReal hiddenCharge := by
  have real : (2 : ℝ) / 2 ^ 128 ≤ hiddenCharge := by
    unfold hiddenCharge
    have : (2 : ℝ) / 2 ^ 128 ≤ 3 / 2 ^ 128 := by norm_num
    linarith [fieldCharge_nonneg]
  calc 2 * ((2 : ℝ≥0∞) ^ 128)⁻¹ = ENNReal.ofReal (2 / 2 ^ 128) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_ofNat,
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, div_eq_mul_inv]
    _ ≤ ENNReal.ofReal hiddenCharge := ENNReal.ofReal_le_ofReal real

theorem block_le_charge : ((2 : ℝ≥0∞) ^ 128)⁻¹ ≤ ENNReal.ofReal hiddenCharge :=
  le_trans (le_mul_of_one_le_left' (by norm_num)) two_block_le_charge

theorem field_le_charge : 2 * (baseFieldModulus : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal hiddenCharge := by
  have pos : (0 : ℝ) < (baseFieldModulus : ℝ) - 1 := by linarith [one_lt_modulus_real]
  have real : 2 / (baseFieldModulus : ℝ) ≤ hiddenCharge := by
    unfold hiddenCharge
    have smaller : 2 / (baseFieldModulus : ℝ) ≤ 2 / ((baseFieldModulus : ℝ) - 1) :=
      div_le_div_of_nonneg_left (by norm_num) pos (by linarith)
    have : (0 : ℝ) ≤ 3 / 2 ^ 128 := by positivity
    linarith
  calc 2 * (baseFieldModulus : ℝ≥0∞)⁻¹ = ENNReal.ofReal (2 / (baseFieldModulus : ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos (by linarith [one_lt_modulus_real]), ENNReal.ofReal_ofNat,
          ENNReal.ofReal_natCast, div_eq_mul_inv]
    _ ≤ ENNReal.ofReal hiddenCharge := ENNReal.ofReal_le_ofReal real

/-- **A hash query at a scale-range key touches only through one label.** If the key is a scale
input it names one limb slot and one label; the touch is the garbler's label at that slot's site
being that label (at a site of the given kind). -/
theorem scaleTouch_le {Ω : Type} (μ : PMF Ω) (V : Set Ω) (label : Ω → VectorSite → Block)
    (key : BaseField) (P : VectorSite → Prop) (ε : ℝ≥0∞)
    (hit : ∀ (site : VectorSite) (L : Block), P site →
      μ.toOuterMeasure {ω | ω ∈ V ∧ label ω site = L} ≤ ε * μ.toOuterMeasure V) :
    μ.toOuterMeasure {ω | ω ∈ V ∧ ∃ slot : LimbSite, key = labelInput slot (label ω slot.1) ∧
      P slot.1} ≤ ε * μ.toOuterMeasure V := by
  by_cases named : ∃ slot : LimbSite, ∃ L : Block, labelInput slot L = key ∧ P slot.1
  · obtain ⟨slot, L, same, kind⟩ := named
    refine le_trans (outer_mono_event μ (T := {ω | ω ∈ V ∧ label ω slot.1 = L})
      fun ω member => ⟨member.1, ?_⟩) (hit slot.1 L kind)
    obtain ⟨slot', eq, _⟩ := member.2
    obtain ⟨rfl, rfl⟩ := labelInput_inj (same.trans eq)
    rfl
  · have empty : {ω | ω ∈ V ∧ ∃ slot : LimbSite, key = labelInput slot (label ω slot.1) ∧
        P slot.1} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun ω ⟨_, slot, eq, kind⟩ =>
        named ⟨slot, _, eq.symm, kind⟩
    rw [empty, MeasureTheory.measure_empty]
    exact bot_le

/-- **`StageOneGuess` at L1's constant, from the bridge-input guess.** -/
theorem stageOneGuess_of_bridge (bridge : StageOneBridgeGuess) :
    StageOneGuess (ENNReal.ofReal hiddenCharge) := by
  intro field group fixedFintype encFintype fixedEq encEq parameter scalar view entry
  let μ := swappedChallengeTape
  let V := {tape : Coins × Oracle | stageOneView parameter scalar tape = view}
  have twoHits : ∀ (index : FixedIndex) (x y : Block),
      μ.toOuterMeasure {tape | tape ∈ V ∧
        (InputHit scalar index x tape ∨ OutputHit scalar index y tape)} ≤
        ENNReal.ofReal hiddenCharge * μ.toOuterMeasure V := by
    intro index x y
    refine le_trans (outer_and_or_le μ V {tape | InputHit scalar index x tape}
      {tape | OutputHit scalar index y tape}) ?_
    refine le_trans (add_le_add (inputHit_le parameter scalar view index x)
      (outputHit_le parameter scalar view index y)) ?_
    rw [← add_mul, ← two_mul]
    exact mul_le_mul' two_block_le_charge le_rfl
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x =>
      refine le_trans (outer_mono_event μ
        (T := {tape | tape ∈ V ∧ (InputHit scalar index x tape ∨ OutputHit scalar index answer tape)})
        fun tape member =>
          ⟨member.1, stageOne_touch scalar tape ⟨.fixedForward index x, answer⟩ member.2⟩) ?_
      exact twoHits index x answer
  | fixedInverse index y =>
      refine le_trans (outer_mono_event μ
        (T := {tape | tape ∈ V ∧ (InputHit scalar index answer tape ∨ OutputHit scalar index y tape)})
        fun tape member =>
          ⟨member.1, (stageOne_touch scalar tape ⟨.fixedInverse index y, answer⟩ member.2).symm⟩)
        (twoHits index answer y)
  | encForward index x =>
      refine le_trans (outer_mono_event μ (T := ∅) fun tape member =>
        (stageOne_touch scalar tape ⟨.encForward index x, answer⟩ member.2).elim) ?_
      simp
  | encInverse index y =>
      refine le_trans (outer_mono_event μ (T := ∅) fun tape member =>
        (stageOne_touch scalar tape ⟨.encInverse index y, answer⟩ member.2).elim) ?_
      simp
  | hash key =>
      by_cases low : key.val < scaleRange
      · refine le_trans (outer_mono_event μ
          (T := {tape | tape ∈ V ∧ ∃ slot : LimbSite,
            key = labelInput slot (garblerLabelOf tape slot.1) ∧ True})
          fun tape member => ⟨member.1, ?_⟩) ?_
        · rcases stageOne_touch scalar tape ⟨.hash key, answer⟩ member.2 with bridge | ⟨slot, scale⟩
          · exact absurd (bridge ▸ low) (bridgeInput_not_lt _)
          · exact ⟨slot, scale, trivial⟩
        · exact scaleTouch_le μ V garblerLabelOf key (fun _ => True) _ fun site L _ =>
            le_trans (labelHit_le parameter scalar view site L) (mul_le_mul' block_le_charge le_rfl)
      · refine le_trans (outer_mono_event μ
          (T := {tape | stageOneView parameter scalar tape = view ∧ bridgeInput tape.1.bridgeKey =
              key})
          fun tape member => ⟨member.1, ?_⟩) ?_
        · rcases stageOne_touch scalar tape ⟨.hash key, answer⟩ member.2 with bridge | ⟨slot, scale⟩
          · exact bridge.symm
          · exact absurd (scale ▸ labelInput_val_lt _ _) low
        · exact le_trans (bridge parameter scalar view key) (mul_le_mul' field_le_charge le_rfl)

end

end Kriterion.ArgoMAC.Security.Phase3
