/-
**Phase 3, P1h — `StageTwoGuess designedRule`, from the off-curve bridge-input guess.**

A stage-2 touch (`stageTwo_touch`) is a hidden input or output hit at one fixed-key index, each at
most `2^-128` given the stage-2 view (`hiddenInput_le`, `hiddenOutput_le`); a hash query at a scale
input of a hidden site (an active switch, or off the curve a system-B switch) under the garbler's
label there, at most `2^-128` (`hiddenLabel_le`); or — off the curve only — a hash query at the
bridge input `bridgeInput t`. A hash query pays the larger of the last two (a scale input lies below
`2 ^ 150`, the bridge input above). So `StageTwoGuess designedRule (3/2^128 + 2/(p−1))` follows from
one statement about `t` alone, `StageTwoBridgeGuess`: off the curve, given the stage-2 view,
`bridgeInput t` hits a given key with conditional mass at most `2/(p−1)`
(`stageTwoGuess_of_bridge`).
-/

import Proof.Privacy.Phase3.Hidden.StageTwoFixed

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open scoped ENNReal

noncomputable section

/-- **The stage-2 bridge-input guess**: off the curve, given the stage-2 view, the bridge input
`bridgeInput t` equals a given key with conditional mass at most `2/(p − 1)`. -/
def StageTwoBridgeGuess : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (input : AffineInput)
    (view : (Public × List (Entry FixedIndex EncPRF.PermutationIndex)) × LamportSignature ×
      List (Entry FixedIndex EncPRF.PermutationIndex)) (key : BaseField),
    validate input = false →
    swappedChallengeTape.toOuterMeasure
        {tape | stageTwoView designedRule parameter scalar input tape = view ∧
          bridgeInput tape.1.bridgeKey = key} ≤
      2 * ((baseFieldModulus - 1 : ℕ) : ℝ≥0∞)⁻¹ *
        swappedChallengeTape.toOuterMeasure
          {tape | stageTwoView designedRule parameter scalar input tape = view}

theorem fieldMinusOne_le_charge :
    2 * ((baseFieldModulus - 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal hiddenCharge := by
  have pos : (0 : ℝ) < (baseFieldModulus : ℝ) - 1 := by linarith [one_lt_modulus_real]
  have cast : ((baseFieldModulus - 1 : ℕ) : ℝ) = (baseFieldModulus : ℝ) - 1 := by
    rw [Nat.cast_sub (by exact_mod_cast one_lt_modulus_real.le), Nat.cast_one]
  have real : 2 / ((baseFieldModulus : ℝ) - 1) ≤ hiddenCharge := by
    unfold hiddenCharge
    have : (0 : ℝ) ≤ 3 / 2 ^ 128 := by positivity
    linarith
  calc 2 * ((baseFieldModulus - 1 : ℕ) : ℝ≥0∞)⁻¹ =
        ENNReal.ofReal (2 / ((baseFieldModulus : ℝ) - 1)) := by
        rw [ENNReal.ofReal_div_of_pos pos, ENNReal.ofReal_ofNat, ← cast, ENNReal.ofReal_natCast,
          div_eq_mul_inv]
    _ ≤ ENNReal.ofReal hiddenCharge := ENNReal.ofReal_le_ofReal real

/-- **`StageTwoGuess` at L1's constant, from the off-curve bridge-input guess.** -/
theorem stageTwoGuess_of_bridge (bridge : StageTwoBridgeGuess) :
    StageTwoGuess designedRule (ENNReal.ofReal hiddenCharge) := by
  intro field group fixedFintype encFintype fixedEq encEq parameter scalar input view entry
  let μ := swappedChallengeTape
  let V := {tape : Coins × Oracle | stageTwoView designedRule parameter scalar input tape = view}
  have twoHits : ∀ (index : FixedIndex) (x y : Block),
      μ.toOuterMeasure {tape | tape ∈ V ∧
        (HiddenInput scalar input index x tape ∨ HiddenOutput scalar input index y tape)} ≤
        ENNReal.ofReal hiddenCharge * μ.toOuterMeasure V := by
    intro index x y
    refine le_trans (outer_and_or_le μ V {tape | HiddenInput scalar input index x tape}
      {tape | HiddenOutput scalar input index y tape}) ?_
    refine le_trans (add_le_add (hiddenInput_le parameter scalar input view index x)
      (hiddenOutput_le parameter scalar input view index y)) ?_
    rw [← add_mul, ← two_mul]
    exact mul_le_mul' two_block_le_charge le_rfl
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x =>
      refine le_trans (outer_mono_event μ
        (T := {tape | tape ∈ V ∧ (HiddenInput scalar input index x tape ∨
          HiddenOutput scalar input index answer tape)})
        fun tape member => ⟨member.1, stageTwo_touch parameter scalar input tape
          ⟨.fixedForward index x, answer⟩ member.2⟩) ?_
      exact twoHits index x answer
  | fixedInverse index y =>
      refine le_trans (outer_mono_event μ
        (T := {tape | tape ∈ V ∧ (HiddenInput scalar input index answer tape ∨
          HiddenOutput scalar input index y tape)})
        fun tape member => ⟨member.1, (stageTwo_touch parameter scalar input tape
          ⟨.fixedInverse index y, answer⟩ member.2).symm⟩) (twoHits index answer y)
  | encForward index x =>
      refine le_trans (outer_mono_event μ (T := ∅) fun tape member =>
        (stageTwo_touch parameter scalar input tape ⟨.encForward index x, answer⟩ member.2).elim) ?_
      simp
  | encInverse index y =>
      refine le_trans (outer_mono_event μ (T := ∅) fun tape member =>
        (stageTwo_touch parameter scalar input tape ⟨.encInverse index y, answer⟩ member.2).elim) ?_
      simp
  | hash key =>
      by_cases low : key.val < scaleRange
      · refine le_trans (outer_mono_event μ
          (T := {tape | tape ∈ V ∧ ∃ slot : LimbSite,
            key = labelInput slot (garblerLabelOf tape slot.1) ∧ designedSite input slot.1 = false})
          fun tape member => ⟨member.1, ?_⟩) ?_
        · rcases stageTwo_touch parameter scalar input tape ⟨.hash key, answer⟩ member.2 with
            ⟨_, bridge⟩ | scale
          · exact absurd (bridge ▸ low) (bridgeInput_not_lt _)
          · exact scale
        · exact scaleTouch_le μ V garblerLabelOf key (fun site => designedSite input site = false) _
            fun site L hidden =>
              le_trans (hiddenLabel_le parameter scalar input view site hidden L)
                (mul_le_mul' block_le_charge le_rfl)
      · by_cases valid : validate input = true
        · refine le_trans (outer_mono_event μ (T := ∅) fun tape member => ?_) ?_
          · rcases stageTwo_touch parameter scalar input tape ⟨.hash key, answer⟩ member.2 with
              ⟨invalid, _⟩ | ⟨slot, scale, _⟩
            · rw [valid] at invalid
              cases invalid
            · exact absurd (scale ▸ labelInput_val_lt _ _) low
          · simp
        · have invalid : validate input = false := by simpa using valid
          refine le_trans (outer_mono_event μ
            (T := {tape | stageTwoView designedRule parameter scalar input tape = view ∧
              bridgeInput tape.1.bridgeKey = key}) fun tape member => ⟨member.1, ?_⟩) ?_
          · rcases stageTwo_touch parameter scalar input tape ⟨.hash key, answer⟩ member.2 with
              ⟨_, bridge⟩ | ⟨slot, scale, _⟩
            · exact bridge.symm
            · exact absurd (scale ▸ labelInput_val_lt _ _) low
          · exact le_trans (bridge parameter scalar input view key invalid)
              (mul_le_mul' fieldMinusOne_le_charge le_rfl)

end

end Kriterion.ArgoMAC.Security.Phase3
