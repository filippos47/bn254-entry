/-
**Phase 3, P4b — the failure observable and the chunk-0 charges.**

`failObs`: given the record of a run, whether some designated hash program collides with a
stage-1 entry: the designated input of a limb at its recorded label is already stored. A hash
program needs only a fresh input, so there is no output part: the failure depends on the recorded
labels only, not on the drawn hash answers.

* `failObs_le` — with every record entry `none` or `E`, the failure is at most the per-limb input
  collisions of `E` (`slotInput`).
* `maskCharge` / `maskHit` — the stage-1 hash entries at the chunk-0 cells of a lane, and whether a
  chunk-0 label hits one (then the lane reads a cached answer); summed over a fresh shift of the
  labels, the hits cost at most the entries (`maskHit_sum_le`).
* `slotCharge` — the stage-1 hash entries at the designated inputs; summed over a fresh shift of
  `E`, the input collisions cost at most those entries (`slotInput_sum`).
-/

import Proof.Privacy.Phase3.Lazy.FailHelpers

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### More expectation algebra -/

section Expect

variable {β γ : Type}

theorem expectO_tsum (μ : PMF (Option β)) (f : γ → β → ℝ≥0∞) :
    expectO μ (fun b => ∑' a, f a b) = ∑' a, expectO μ (f a) := by
  unfold expectO
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun o => ?_
  cases o with
  | none => simp
  | some b => exact ENNReal.tsum_mul_left.symm

theorem expectO_value_eq {α : Type} (μ ν : PMF (Option (α × LState × Record × Set Cell)))
    (law : μ.map (Option.map Prod.fst) = ν.map (Option.map Prod.fst)) (f : α → ℝ≥0∞) :
    expectO μ (fun r => f r.1) = expectO ν (fun r => f r.1) := by
  have first := expectO_map μ Prod.fst f
  have second := expectO_map ν Prod.fst f
  rw [law] at first
  exact first.symm.trans second

end Expect

/-! ### The failure observable -/

section Observable

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- One limb's program collides with the stage-1 oracle: its recorded input is stored there. -/
def SlotCollides (stage : LState) (bits : BitInput) (record : Record)
    (limb : Fin (limbCount .pointX)) : Prop :=
  ∃ label, record limb = some label ∧ stage.hash.lookup (designatedInput bits limb label) ≠ none

open Classical in
/-- **The failure observable** of a run's record: whether some limb's program collides. -/
def failObs (stage : LState) (bits : BitInput) (record : Record) : ℝ≥0∞ :=
  if ∃ limb, SlotCollides stage bits record limb then 1 else 0

theorem failObs_le_one (stage : LState) (bits : BitInput) (record : Record) :
    failObs stage bits record ≤ 1 := by
  unfold failObs
  split <;> simp

open Classical in
/-- The input collision of one limb's designated input at a label `E`. -/
def slotInput (stage : LState) (bits : BitInput) (label : Block)
    (limb : Fin (limbCount .pointX)) : ℝ≥0∞ :=
  if stage.hash.lookup (designatedInput bits limb label) ≠ none then 1 else 0

open Classical in
/-- **With every record entry `none` or `E`, the failure is at most the per-limb input collisions
of `E`.** -/
theorem failObs_le (stage : LState) (bits : BitInput) (record : Record) (label : Block)
    (recorded : ∀ limb, record limb = none ∨ record limb = some label) :
    failObs stage bits record ≤ ∑ limb, slotInput stage bits label limb := by
  unfold failObs
  refine (indicator_exists_le _).trans (Finset.sum_le_sum fun limb _ => ?_)
  split
  · rename_i collides
    obtain ⟨recordedLabel, same, hit⟩ := collides
    rcases recorded limb with none | some
    · rw [none] at same
      cases same
    · rw [some] at same
      cases same
      unfold slotInput
      rw [if_pos hit]
  · exact zero_le

end Observable

/-! ### The chunk-0 fold and labels -/

/-- The cleartext value of chunk 0 of `x`. -/
def chunkZeroValue (bits : BitInput) : Nat :=
  (chunkValue (Pipeline.coordBits bits .x) chunkZero).toNat

/-- The halves of the inactive level-1 fold gate of chunk 0 of a lane. -/
def foldIndex (lane : Lane) (bits : BitInput) (half : Bool) : FixedIndex :=
  hotIndexNat lane chunkZero 1 (inactiveEntry (chunkZeroValue bits)) half

theorem foldIndex_indexAt (lane : Lane) (bits : BitInput) (half : Bool) :
    IndexAt lane chunkZero (foldIndex lane bits half) :=
  hotIndexNat_indexAt _ _ _ _ _

theorem foldIndex_ne (lane : Lane) (bits : BitInput) :
    foldIndex lane bits false ≠ foldIndex lane bits true := by
  simp [foldIndex, hotIndexNat]

/-- The level-1 label of chunk 0 of a lane: `join 0 xor` the bit-0 label. -/
def chunkLabel (joins : Vector Block foldStepCount) (labels : Fin coordinateBitCount → Block) :
    Block :=
  joinAt (hotSlice joins chunkZero) 0 ^^^ labelAt (chunkLabels labels chunkZero) 0

/-- The one-hot labels of chunk 0 of a lane, as a function of the fold material. -/
def chunkHot (bits : BitInput) (joins : Vector Block foldStepCount)
    (labels : Fin coordinateBitCount → Block) (material : Block) : Fin (2 ^ 2) → Block :=
  foldLabels (chunkZeroValue bits) (labelAt (chunkLabels labels chunkZero))
    (joinAt (hotSlice joins chunkZero)) material

/-! ### The chunk-0 charges -/

section Charges

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- The stage-1 hash entries at the chunk-0 cells of a lane. -/
def maskCharge (stage : LState) (lane : Lane) : ℝ≥0∞ :=
  ∑ switch : Fin (2 ^ chunkWidth chunkZero), ∑ limb : Fin (limbCount lane),
    (hashCount (cellInput (maskCell lane chunkZero switch limb)) stage : ℝ≥0∞)

open Classical in
/-- Some chunk-0 label of an inactive switch hits a stage-1 hash entry at one of the switch's
cells. -/
def maskHit (stage : LState) (bits : BitInput) (lane : Lane)
    (hot : Fin (2 ^ chunkWidth chunkZero) → Block) : ℝ≥0∞ :=
  if ∃ switch, switch ≠ chunkOf (Pipeline.coordBits bits .x) chunkZero ∧
      ∃ limb : Fin (limbCount lane),
        stage.hash.lookup (cellInput (maskCell lane chunkZero switch limb) (hot switch)) ≠ none
  then 1 else 0

open Classical in
/-- **The mask hit, summed over the fresh fold answer, is at most the chunk-0 entries.** -/
theorem maskHit_sum_le (stage : LState) (bits : BitInput) (lane : Lane)
    (joins : Vector Block foldStepCount) (labels : Fin coordinateBitCount → Block)
    (first : Block) :
    ∑' a, maskHit stage bits lane (chunkHot bits joins labels (first ^^^ a)) ≤
      maskCharge stage lane := by
  unfold maskHit maskCharge
  calc ∑' a, (if ∃ switch, switch ≠ chunkOf (Pipeline.coordBits bits .x) chunkZero ∧
          ∃ limb : Fin (limbCount lane), stage.hash.lookup (cellInput
            (maskCell lane chunkZero switch limb) (chunkHot bits joins labels (first ^^^ a) switch))
              ≠ none then (1 : ℝ≥0∞) else 0)
      ≤ ∑' a, ∑ switch : Fin (2 ^ chunkWidth chunkZero), ∑ limb : Fin (limbCount lane),
          (if stage.hash.lookup (cellInput (maskCell lane chunkZero switch limb)
            (chunkHot bits joins labels (first ^^^ a) switch)) ≠ none then (1 : ℝ≥0∞) else 0) := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        split
        · rename_i found
          obtain ⟨switch, -, limb, hit⟩ := found
          calc (1 : ℝ≥0∞)
              = if stage.hash.lookup (cellInput (maskCell lane chunkZero switch limb)
                  (chunkHot bits joins labels (first ^^^ a) switch)) ≠ none then 1 else 0 := by
                rw [if_pos hit]
            _ ≤ ∑ limb : Fin (limbCount lane),
                  (if stage.hash.lookup (cellInput (maskCell lane chunkZero switch limb)
                    (chunkHot bits joins labels (first ^^^ a) switch)) ≠ none then
                    (1 : ℝ≥0∞) else 0) :=
                Finset.single_le_sum (f := fun limb : Fin (limbCount lane) =>
                  if stage.hash.lookup (cellInput (maskCell lane chunkZero switch limb)
                    (chunkHot bits joins labels (first ^^^ a) switch)) ≠ none then
                    (1 : ℝ≥0∞) else 0) (fun _ _ => zero_le) (Finset.mem_univ limb)
            _ ≤ _ := Finset.single_le_sum (f := fun switch : Fin (2 ^ chunkWidth chunkZero) =>
                  ∑ limb : Fin (limbCount lane),
                    (if stage.hash.lookup (cellInput (maskCell lane chunkZero switch limb)
                      (chunkHot bits joins labels (first ^^^ a) switch)) ≠ none then
                      (1 : ℝ≥0∞) else 0)) (fun _ _ => zero_le) (Finset.mem_univ switch)
        · exact zero_le
    _ = ∑ switch : Fin (2 ^ chunkWidth chunkZero), ∑ limb : Fin (limbCount lane), ∑' a,
          (if stage.hash.lookup (cellInput (maskCell lane chunkZero switch limb)
            (chunkHot bits joins labels (first ^^^ a) switch)) ≠ none then (1 : ℝ≥0∞) else 0) := by
        rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        refine Finset.sum_congr rfl fun switch _ => ?_
        exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ = _ := by
        refine Finset.sum_congr rfl fun switch _ => Finset.sum_congr rfl fun limb _ => ?_
        have shift : ∀ a, chunkHot bits joins labels (first ^^^ a) switch =
            (chunkHot bits joins labels 0 switch ^^^ first) ^^^ a := by
          intro a
          exact (foldLabels_linear _ _ _ (first ^^^ a) switch).trans (BitVec.xor_assoc _ _ _).symm
        simp only [shift]
        exact sum_stored_xor (cellInput (maskCell lane chunkZero switch limb)) _ stage

/-- The stage-1 hash entries at the designated inputs. -/
def slotCharge (stage : LState) (bits : BitInput) : ℝ≥0∞ :=
  ∑ limb : Fin (limbCount .pointX), (hashCount (designatedInput bits limb) stage : ℝ≥0∞)

/-- **Summed over a fresh shift of `E`, one limb's input collisions are its stage-1 entries.** -/
theorem slotInput_sum (stage : LState) (bits : BitInput) (limb : Fin (limbCount .pointX))
    (base : Block) :
    ∑' a, slotInput stage bits (base ^^^ a) limb = hashCount (designatedInput bits limb) stage :=
  sum_stored_xor (designatedInput bits limb) base stage

end Charges

end

end Kriterion.ArgoMAC.Phase3.Lazy
