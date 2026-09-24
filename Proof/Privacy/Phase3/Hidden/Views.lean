/-
**Phase 3, P1f — the garbler's transcript and the stage-1 view on a shifted tape.**

From `garbler_sim`: the garbler's transcript on `shiftTape T scalar tape` is `shiftEntry` of its
transcript on `tape` (`garblerTranscript_shift`), every garbler entry has the garbler's shape
(`garblerTranscript_good`, at the trivial shift), the published value is the same
(`garble_shift`), so the EncPRF entries and the stage-1 view are the same
(`stageOneView_shift`). A touch of the garbler's non-EncPRF entries is an input hit or an output
hit at one fixed-key index, or a hash query at the bridge input or at a scale input under the
garbler's label of its switch (`stageOne_touch`).
-/

import Proof.Privacy.Phase3.Hidden.Reduction
import Proof.Privacy.Phase3.Hidden.Invariance
import Proof.Privacy.Phase3.Hidden.Symmetry

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden

noncomputable section

/-- The trivial shift. -/
def noShift : TapeShift := ⟨fun _ => 0, fun _ _ => 0, 0, fun _ _ _ _ => 0, fun _ _ _ _ => 0⟩

theorem xorFold_zero {count : Nat} : xorFold (fun _ : Fin count => (0 : Block)) = 0 := by
  induction count with
  | zero => rfl
  | succ n ih =>
      unfold xorFold at ih ⊢
      rw [Fin.foldl_succ_last, ih]
      exact BitVec.xor_self

theorem noShift_valid : noShift.Valid := by
  intro lane c n _ _
  show xorFold (fun _ : Fin (2 ^ n) => (0 : Block)) = labelAt (fun position : Fin (chunkWidth c) =>
    (0 : Block) ^^^ (if laneIsPoint lane then (0 : Block) else 0)) n
  rw [xorFold_zero]
  unfold labelAt
  split <;> simp

section Instances

variable [FieldCertificate] [GroupCertificate]

theorem garblerTranscript_eq (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    garblerTranscript scalar tape = Hidden.transcriptOf (publicAnswer tape.2) (Programs.garbleM scalar tape.1) :=
  transcript_eq_transcriptOf _ _

/-- **The garbler's transcript on a shifted tape.** -/
theorem garblerTranscript_shift (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) :
    garblerTranscript scalar (shiftTape T scalar tape) =
      (garblerTranscript scalar tape).map (shiftEntry T scalar tape.1) := by
  rw [garblerTranscript_eq, garblerTranscript_eq]
  exact (forall₂_map_eq (garbler_sim T valid scalar tape).1).1

/-- **Every garbler entry has the garbler's shape.** -/
theorem garblerTranscript_good (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    ∀ entry ∈ garblerTranscript scalar tape, Good scalar tape entry := by
  rw [garblerTranscript_eq]
  exact (forall₂_map_eq (garbler_sim noShift noShift_valid scalar tape).1).2

theorem garble_eval (parameter : ℕ) (scalar : NonZeroScalar) (coins : Coins) (oracle : Oracle) :
    (Programs.garbleM scalar coins).eval (publicAnswer oracle) =
      Scheme.scheme.garble parameter scalar (coins, oracle) := by
  rw [← Programs.garbleProgram_correct parameter scalar coins oracle, Programs.garbleProgram,
    FreeQuery.eval_toProgram]

/-- **The published value is kept.** -/
theorem garble_shift (T : TapeShift) (valid : T.Valid) (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) :
    (Scheme.scheme.garble parameter scalar (shiftTape T scalar tape)).1 =
      (Scheme.scheme.garble parameter scalar tape).1 := by
  have same := (garbler_sim T valid scalar tape).2
  rw [garble_eval parameter, garble_eval parameter] at same
  exact same

theorem filter_map_eq {α : Type} (P : α → Bool) (g : α → α) :
    ∀ (l : List α), (∀ a ∈ l, P (g a) = P a) → (∀ a ∈ l, P a = true → g a = a) →
      (l.map g).filter P = l.filter P
  | [], _, _ => rfl
  | a :: l, same, fixed => by
      rw [List.map_cons, List.filter_cons, List.filter_cons, same a List.mem_cons_self]
      have rest := filter_map_eq P g l (fun b m => same b (List.mem_cons_of_mem _ m))
        (fun b m => fixed b (List.mem_cons_of_mem _ m))
      by_cases p : P a = true
      · rw [if_pos p, if_pos p, fixed a List.mem_cons_self p, rest]
      · rw [if_neg p, if_neg p, rest]

theorem isEnc_shiftEntry (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins)
    (entry : Entry FixedIndex EncPRF.PermutationIndex) :
    Entry.IsEnc (shiftEntry T scalar coins entry) = entry.IsEnc := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | hash value =>
      by_cases h : value = bridgeInput coins.bridgeKey <;> simp [shiftEntry, h, Entry.IsEnc]
  | _ => rfl

theorem shiftEntry_enc (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins)
    (entry : Entry FixedIndex EncPRF.PermutationIndex) (enc : entry.IsEnc = true) :
    shiftEntry T scalar coins entry = entry := by
  obtain ⟨request, answer⟩ := entry
  cases request <;> first | rfl | (simp [Entry.IsEnc] at enc)

/-- **The EncPRF entries are kept.** -/
theorem encEntries_shift (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) :
    encEntries scalar (shiftTape T scalar tape) = encEntries scalar tape := by
  unfold encEntries
  rw [garblerTranscript_shift T valid]
  exact filter_map_eq _ _ _ (fun e _ => isEnc_shiftEntry T scalar tape.1 e)
    (fun e _ enc => shiftEntry_enc T scalar tape.1 e enc)

/-- **The stage-1 view is kept.** -/
theorem stageOneView_shift (T : TapeShift) (valid : T.Valid) (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) :
    stageOneView parameter scalar (shiftTape T scalar tape) = stageOneView parameter scalar tape := by
  unfold stageOneView
  rw [garble_shift T valid, encEntries_shift T valid]

/-! ### Touches of the garbler's entries -/

/-- The garbler asks index `index` at input `x`. -/
def InputHit (scalar : NonZeroScalar) (index : FixedIndex) (x : Block) (tape : Coins × Oracle) : Prop :=
  ∃ y : Block, (⟨.fixedForward index x, y⟩ : Entry FixedIndex EncPRF.PermutationIndex) ∈
    garblerTranscript scalar tape

/-- The garbler's answer at index `index` is `y`. -/
def OutputHit (scalar : NonZeroScalar) (index : FixedIndex) (y : Block) (tape : Coins × Oracle) : Prop :=
  ∃ x : Block, (⟨.fixedForward index x, y⟩ : Entry FixedIndex EncPRF.PermutationIndex) ∈
    garblerTranscript scalar tape

theorem fixedPair_good (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (entry : Entry FixedIndex EncPRF.PermutationIndex) (member : entry ∈ garblerTranscript scalar tape)
    {index : FixedIndex} {x y : Fin (2 ^ 128)} (pair : fixedPair entry = some (index, x, y)) :
    (⟨.fixedForward index (BitVec.ofFin x), BitVec.ofFin y⟩ : Entry FixedIndex EncPRF.PermutationIndex) ∈
      garblerTranscript scalar tape := by
  have good := garblerTranscript_good scalar tape entry member
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward i input =>
      simp only [fixedPair, Option.some.injEq, Prod.mk.injEq] at pair
      obtain ⟨rfl, rfl, rfl⟩ := pair
      exact member
  | fixedInverse _ _ => exact good.elim
  | encForward _ _ => simp [fixedPair] at pair
  | encInverse _ _ => simp [fixedPair] at pair
  | hash _ => simp [fixedPair] at pair

/-- **A stage-1 touch is a hit.** -/
theorem stageOne_touch (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (entry : Entry FixedIndex EncPRF.PermutationIndex) (touch : Touches (stageOneExtra scalar tape) entry) :
    match entry with
    | ⟨.fixedForward index x, answer⟩ =>
        InputHit scalar index x tape ∨ OutputHit scalar index (show Block from answer) tape
    | ⟨.fixedInverse index y, answer⟩ =>
        OutputHit scalar index y tape ∨ InputHit scalar index (show Block from answer) tape
    | ⟨.hash key, _⟩ => key = bridgeInput tape.1.bridgeKey ∨
        ∃ slot : LimbSite, key = labelInput slot (garblerLabelOf tape slot.1)
    | _ => False := by
  have plain : ∀ e ∈ plainEntries scalar tape, e ∈ garblerTranscript scalar tape :=
    fun e member => (List.mem_filter.mp member).1
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x =>
      rcases touch with ⟨y, e, member, pair⟩ | ⟨x', e, member, pair⟩
      · left
        exact ⟨_, fixedPair_good scalar tape e (plain e member) pair⟩
      · right
        exact ⟨_, fixedPair_good scalar tape e (plain e member) pair⟩
  | fixedInverse index y =>
      rcases touch with ⟨x, e, member, pair⟩ | ⟨y', e, member, pair⟩
      · left
        exact ⟨_, fixedPair_good scalar tape e (plain e member) pair⟩
      · right
        exact ⟨_, fixedPair_good scalar tape e (plain e member) pair⟩
  | encForward index x =>
      rcases touch with ⟨y, e, member, pair⟩ | ⟨x', e, member, pair⟩ <;>
      · have notEnc := (List.mem_filter.mp member).2
        rw [isEnc_of_encPair pair] at notEnc
        cases notEnc
  | encInverse index y =>
      rcases touch with ⟨x, e, member, pair⟩ | ⟨y', e, member, pair⟩ <;>
      · have notEnc := (List.mem_filter.mp member).2
        rw [isEnc_of_encPair pair] at notEnc
        cases notEnc
  | hash key =>
      have listed : ∃ e ∈ plainEntries scalar tape, ∃ value, hashPair e = some (key, value) := by
        by_contra none'
        simp only [Touches, stageOneExtra, extraOf, if_neg none'] at touch
        cases touch
      obtain ⟨e, member, value, pair⟩ := listed
      have good := garblerTranscript_good scalar tape e (plain e member)
      obtain ⟨request', answer'⟩ := e
      cases request' <;> simp only [hashPair, Option.some.injEq, reduceCtorEq] at pair
      obtain ⟨rfl, _⟩ := pair
      exact good

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
