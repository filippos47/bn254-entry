/-
**Phase 3, P1o — the coincidence guess, real.**

`coincidenceGuess : CoincidenceGuess (ENNReal.ofReal coincidenceError)`: at every fixed input and
against every weight on the stage-1 view `(P, enc)`, the reach meets a hidden garbler entry with
mass at most `2^16/2^128`.

* **Cover** (`LawsGuessReach.coincide_events`): a coincidence is one of `13813` events —
  per lane, chunk `c`, level `m + 1 ≤ b_c` and entry of that level a label event (`2 + 4 + … +
  2^{b_c} = 2^{b_c+1} − 2` per chunk: `6` for the `2`-bit chunk `0`, `62` for each `5`-bit chunk,
  `30` for each `4`-bit chunk, `2·Σ_c 2^{b_c} − 2·52 = 2·1588 − 104 = 3072` per lane,
  `card_levelSite`), per gadget position and bit a gadget event off the curve, per gadget position
  a collision on the curve, and the bridge event: `4·3072 + 2·254·2 + 2·254 + 1 = 13813`
  (`card_eventIndex`).
* **Each event** has conditional mass `≤ 2/2^128` given the view (`LawsGuessFamily`: the
  `k₂`-family, the transposition family, the `Δ`-family, the curve family).
* **Total**: `13813 · 2/2^128 = 27626/2^128 ≤ 2^16/2^128` (a factor `> 2.3` of room).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsGuessFamily
import Proof.Privacy.Phase3.PublicFirst.LiftGuess

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Phase3.Glue (coincidenceError)
open scoped ENNReal

noncomputable section

namespace Guess

/-! ### The events and their count -/

/-- A label event's place in a lane: a chunk, a level `m + 1 ≤ b_c` and an entry of it. -/
abbrev LevelSite := Σ c : Fin chunkCount, Σ m : Fin (chunkWidth c), Fin (2 ^ (m.val + 1))

/-- The levels of a chunk of width `w` carry `2 + 4 + … + 2^w = 2^(w+1) − 2` entries. -/
theorem levelCount (w : ℕ) : ∑ m : Fin w, 2 ^ (m.val + 1) + 2 = 2 * 2 ^ w := by
  induction w with
  | zero => simp
  | succ w ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have double : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ, mul_comm]
      rw [double]
      omega

/-- **The label events of one lane**: `Σ_c (2^{b_c+1} − 2) = 2·1588 − 2·52 = 3072`. -/
theorem card_levelSite : Fintype.card LevelSite = 3072 := by
  have perChunk : ∀ c : Fin chunkCount,
      Fintype.card (Σ m : Fin (chunkWidth c), Fin (2 ^ (m.val + 1))) + 2 =
        2 * 2 ^ chunkWidth c := by
    intro c
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact levelCount (chunkWidth c)
  have total : ∑ c : Fin chunkCount,
      (Fintype.card (Σ m : Fin (chunkWidth c), Fin (2 ^ (m.val + 1))) + 2) = 2 * 1588 := by
    rw [Finset.sum_congr rfl fun c _ => perChunk c, ← Finset.mul_sum, sum_twoPow_chunkWidth]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at total
  rw [Fintype.card_sigma]
  have chunks : chunkCount * 2 = 104 := rfl
  omega

/-- The coincidence events: a label event per (lane, level site), a gadget event off the curve per
(coordinate, position, bit), a gadget collision on the curve per (coordinate, position), and the
bridge event. -/
abbrev EventIndex :=
  (Lane × LevelSite) ⊕ (Coord × Fin PlanB.coordinateBits × Bool) ⊕
    (Coord × Fin PlanB.coordinateBits) ⊕ Unit

/-- **`13813` events**: `4·3072 + 2·254·2 + 2·254 + 1`. -/
theorem card_eventIndex : Fintype.card EventIndex = 13813 := by
  simp only [EventIndex, Fintype.card_sum, Fintype.card_prod, card_lane, card_levelSite,
    card_coord, Fintype.card_fin, Fintype.card_bool, Fintype.card_unit]
  rfl

section Events

variable [FieldCertificate] [GroupCertificate]

/-- The event of an index. -/
def eventOf (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) :
    EventIndex → Coins × Oracle → Prop
  | .inl (lane, ⟨c, m, r⟩) => fun tape => Hit parameter scalar tape input lane c m r
  | .inr (.inl (κ, position, bit)) => fun tape => GadgetOff tape input κ position bit
  | .inr (.inr (.inl (κ, position))) => fun tape => GadgetOn tape κ position
  | .inr (.inr (.inr ())) => fun tape => BridgeHit tape input

open Classical in
/-- **Each event's guess bound.** -/
theorem event_bound (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (i : EventIndex) (weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
        if eventOf parameter scalar input i tape then 1 else 0) ≤
      (2 / 2 ^ 128 : ℝ≥0∞) *
        ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) := by
  rcases i with ⟨lane, ⟨c, m, r⟩⟩ | ⟨κ, position, bit⟩ | ⟨κ, position⟩ | ⟨⟩
  · exact hit_bound parameter scalar input lane c m r weight
  · exact gadgetOff_bound parameter scalar input κ position bit weight
  · exact gadgetOn_bound parameter scalar input κ position weight
  · exact bridge_bound parameter scalar input weight

/-- **The cover**: a coincidence is one of the events. -/
theorem coincide_cover (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (hit : Coincide parameter scalar tape input) :
    ∃ i, eventOf parameter scalar input i tape := by
  rcases coincide_events parameter scalar tape input hit with
    ⟨lane, c, m, r, one⟩ | ⟨κ, position, bit, off⟩ | ⟨κ, position, on⟩ | bridge
  · exact ⟨.inl (lane, ⟨c, m, r⟩), one⟩
  · exact ⟨.inr (.inl (κ, position, bit)), off⟩
  · exact ⟨.inr (.inr (.inl (κ, position))), on⟩
  · exact ⟨.inr (.inr (.inr ())), bridge⟩

open Classical in
theorem coincideWeight_le (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) :
    coincideWeight parameter scalar tape input ≤
      ∑ i : EventIndex, if eventOf parameter scalar input i tape then 1 else 0 := by
  unfold coincideWeight
  split
  · rename_i hit
    obtain ⟨i, holds⟩ := coincide_cover parameter scalar tape input hit
    calc (1 : ℝ≥0∞) = if eventOf parameter scalar input i tape then 1 else 0 := by
          rw [if_pos holds]
      _ ≤ ∑ j : EventIndex, if eventOf parameter scalar input j tape then 1 else 0 :=
        Finset.single_le_sum
          (f := fun j => if eventOf parameter scalar input j tape then (1 : ℝ≥0∞) else 0)
          (fun _ _ => zero_le) (Finset.mem_univ i)
  · exact zero_le

theorem viewOf_eq_stageOneView (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    viewOf parameter scalar tape = stageOneView parameter scalar tape := rfl

theorem coincidenceError_eq : ENNReal.ofReal coincidenceError = (2 ^ 16 / 2 ^ 128 : ℝ≥0∞) := by
  unfold coincidenceError
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

theorem guess_count_le : (13813 : ℝ≥0∞) * (2 / 2 ^ 128) ≤ 2 ^ 16 / 2 ^ 128 := by
  rw [← mul_div_assoc]
  exact ENNReal.div_le_div_right (by norm_num) _

open Classical in
/-- **The per-input coincidence guess, at a fixed input.** -/
theorem coincidence_guess_at (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape *
        (weight (viewOf parameter scalar tape) * coincideWeight parameter scalar tape input)
      ≤ ENNReal.ofReal coincidenceError *
          ∑' tape, swappedChallengeTape tape * weight (viewOf parameter scalar tape) := by
  simp only [viewOf_eq_stageOneView]
  calc ∑' tape, swappedChallengeTape tape *
        (weight (stageOneView parameter scalar tape) * coincideWeight parameter scalar tape input)
      ≤ ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
          ∑ i : EventIndex, if eventOf parameter scalar input i tape then 1 else 0) :=
        ENNReal.tsum_le_tsum fun tape =>
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (coincideWeight_le parameter scalar tape input))
    _ = ∑ i : EventIndex, ∑' tape, swappedChallengeTape tape *
          (weight (stageOneView parameter scalar tape) *
            if eventOf parameter scalar input i tape then 1 else 0) := by
        simp_rw [Finset.mul_sum]
        exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ _i : EventIndex, (2 / 2 ^ 128 : ℝ≥0∞) *
          ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) :=
        Finset.sum_le_sum fun i _ => event_bound parameter scalar input i weight
    _ = ((13813 : ℝ≥0∞) * (2 / 2 ^ 128)) *
          ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) := by
        rw [Finset.sum_const, Finset.card_univ, card_eventIndex, nsmul_eq_mul, mul_assoc]
        norm_num
    _ ≤ ENNReal.ofReal coincidenceError *
          ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) := by
        rw [coincidenceError_eq]
        exact mul_le_mul' guess_count_le le_rfl

end Events

end Guess

/-- **`CoincidenceGuess` at the allowance `2^16/2^128`, real.** -/
theorem coincidenceGuess : CoincidenceGuess (ENNReal.ofReal coincidenceError) := by
  intro field group parameter scalar input
  exact @Guess.coincidence_guess_at field group parameter scalar input

/-- **The Glue's `publicFirst`, from the two laws and P1k's bounds** (the coincidence guess is
discharged). -/
theorem planB_publicFirst_of_laws_bounds (laws : DesignedLaws) (bounds : DesignedBounds) :
    Kriterion.ArgoMAC.Phase3.Glue.GameCoreUntilBad
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.hiddenDeleted
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.publicFirst fun first _ =>
        Kriterion.ArgoMAC.Phase3.Glue.stageOneHitError first +
          Kriterion.ArgoMAC.Phase3.Glue.exceptionalError +
            Kriterion.ArgoMAC.Phase3.Glue.maskSwapError + coincidenceError :=
  planB_publicFirst_of_guess laws bounds coincidenceGuess

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
