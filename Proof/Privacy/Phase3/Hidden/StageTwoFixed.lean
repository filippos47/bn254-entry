/-
**Phase 3, P1h — stage 2, hidden hits: at most `2^-128` each, given the stage-2 view.**

* `stageTwoView_shift`: a join-keeping tape shift that keeps `u`'s labels and moves no garbler entry
  at a designed index keeps the whole stage-2 view (`designedEntries_eq` makes the designed entries a
  filter of the garbler's transcript, which the shift maps entrywise).
* The three families of `StageTwoShift` move no designed entry (`deltaU_fixed`, `key2_fixed` off
  the curve, `hotOut_fixed` at a hidden gate), and for every hidden index `i` one of them moves the
  garbler's point (`inFamily`) or output (`outFamily`) at `i` by `c`, and for every hidden vector
  site one of them moves the garbler's label there by `c` (`hiddenSiteFamily`).
* `stageTwo_touch`: a touch of the stage-2 extra entries is a hit at a **hidden** index, a hash
  query at a scale input of a **hidden** site under the garbler's label there, or, off the curve,
  the bridge input.
* **`hiddenInput_le`, `hiddenOutput_le`, `hiddenLabel_le`**: `μ{view₂ = v ∧ i hidden ∧ the garbler's
  point (output) at i is x} ≤ 2^-128 · μ{view₂ = v}`, and the same for the garbler's label at a
  hidden site (`event_le_of_symmetry`, `swapped_shift_invariant`).
-/

import Proof.Privacy.Phase3.Hidden.Containment

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open scoped ENNReal

noncomputable section

section Instances

variable [FieldCertificate] [GroupCertificate]

/-! ### The stage-2 view on a shifted tape -/

theorem designedIndex_shift (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (index : FixedIndex) :
    designedIndex scalar (shiftTape T scalar tape) input index = designedIndex scalar tape input index := by
  cases index <;> rfl

theorem designedRule_shiftEntry (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (entry : Entry FixedIndex EncPRF.PermutationIndex) :
    designedRule scalar (shiftTape T scalar tape) input (shiftEntry T scalar tape.1 entry) =
      designedRule scalar tape input entry := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x => exact designedIndex_shift T scalar tape input index
  | fixedInverse index x => exact designedIndex_shift T scalar tape input index
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash value =>
      by_cases h : value = bridgeInput tape.1.bridgeKey
      · simp only [shiftEntry, h, if_true]
        rfl
      · simp only [shiftEntry, h, if_false]
        exact designedHash_relabel input _ value

theorem designedRule_shiftTape (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (entry : Entry FixedIndex EncPRF.PermutationIndex) :
    designedRule scalar (shiftTape T scalar tape) input entry = designedRule scalar tape input entry := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x => exact designedIndex_shift T scalar tape input index
  | fixedInverse index x => exact designedIndex_shift T scalar tape input index
  | _ => rfl

theorem designedRule_shiftEntry' (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (entry : Entry FixedIndex EncPRF.PermutationIndex) :
    designedRule scalar tape input (shiftEntry T scalar tape.1 entry) =
      designedRule scalar tape input entry := by
  rw [← designedRule_shiftTape T scalar tape input, designedRule_shiftEntry]

/-- **The designed entries are kept** by a shift that moves no designed garbler entry. -/
theorem designedEntries_shift (T : TapeShift) (valid : T.Valid) (parameter : ℕ)
    (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (fixed : ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
      designedRule scalar tape input entry = true → shiftEntry T scalar tape.1 entry = entry) :
    designedEntries designedRule parameter scalar (shiftTape T scalar tape) input =
      designedEntries designedRule parameter scalar tape input := by
  rw [designedEntries_eq, designedEntries_eq, garblerTranscript_shift T valid]
  have pred : (fun e : Entry FixedIndex EncPRF.PermutationIndex =>
      !e.IsEnc && designedRule scalar (shiftTape T scalar tape) input e) =
      fun e => !e.IsEnc && designedRule scalar tape input e :=
    funext fun e => by rw [designedRule_shiftTape]
  rw [pred]
  refine filter_map_eq _ _ _ (fun e _ => ?_) (fun e member keep => ?_)
  · rw [isEnc_shiftEntry, designedRule_shiftEntry']
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at keep
    exact fixed e member keep.1 keep.2

/-- **The stage-2 view is kept.** -/
theorem stageTwoView_shift (T : TapeShift) (valid : T.Valid) (parameter : ℕ)
    (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (labels : Scheme.scheme.encode (shiftCoins T tape.1).inputMacKey input =
      Scheme.scheme.encode tape.1.inputMacKey input)
    (fixed : ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
      designedRule scalar tape input entry = true → shiftEntry T scalar tape.1 entry = entry) :
    stageTwoView designedRule parameter scalar input (shiftTape T scalar tape) =
      stageTwoView designedRule parameter scalar input tape := by
  unfold stageTwoView
  rw [stageOneView_shift T valid, designedEntries_shift T valid parameter scalar tape input fixed]
  have key : (Scheme.scheme.garble parameter scalar (shiftTape T scalar tape)).2 =
      (shiftCoins T tape.1).inputMacKey := rfl
  have key' : (Scheme.scheme.garble parameter scalar tape).2 = tape.1.inputMacKey := rfl
  rw [key, key', labels]

/-! ### Moving no designed entry -/

theorem shiftEntry_fixed_zero (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins)
    (index : FixedIndex) (x : Block) (answer : Block) (s : indexShift T scalar coins index = (0,
        0)) :
    shiftEntry T scalar coins ⟨.fixedForward index x, answer⟩ = ⟨.fixedForward index x, answer⟩ := by
  have h1 : (indexShift T scalar coins index).1 = 0 := by rw [s]
  have h2 : (indexShift T scalar coins index).2 = 0 := by rw [s]
  show (⟨.fixedForward index (x ^^^ (indexShift T scalar coins index).1),
    answer ^^^ (indexShift T scalar coins index).2⟩ : Entry FixedIndex EncPRF.PermutationIndex) = _
  rw [h1, h2, bxor_zero, bxor_zero]

/-- A shift moving no `k₂` (at the bridge input) and no site label (at a scale input) keeps a hash
entry. -/
theorem shiftEntry_hash_fixed (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins)
    (value : BaseField) (answer : Block × Block)
    (bridge : value = bridgeInput coins.bridgeKey → T.key2 = 0)
    (scale : value ≠ bridgeInput coins.bridgeKey → relabel (siteShift T) value = value) :
    shiftEntry T scalar coins ⟨.hash value, answer⟩ = ⟨.hash value, answer⟩ := by
  by_cases h : value = bridgeInput coins.bridgeKey
  · show (if value = bridgeInput coins.bridgeKey then (⟨.hash value, (answer.1, answer.2 ^^^
      T.key2)⟩ :
      Entry FixedIndex EncPRF.PermutationIndex) else ⟨.hash (relabel (siteShift T) value), answer⟩)
          = _
    rw [if_pos h, bridge h, bxor_zero]
  · show (if value = bridgeInput coins.bridgeKey then (⟨.hash value, (answer.1, answer.2 ^^^
      T.key2)⟩ :
      Entry FixedIndex EncPRF.PermutationIndex) else ⟨.hash (relabel (siteShift T) value), answer⟩)
          = _
    rw [if_neg h, scale h]

/-- A shift that vanishes at every designed index of the garbler's shape, at every designed site's
label and (on the curve) at the bridge input moves no designed garbler entry. -/
theorem fixed_of_zero (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput)
    (zero : ∀ index, IndexShape scalar tape.1 index → designedIndex scalar tape input index = true →
      indexShift T scalar tape.1 index = (0, 0))
    (sites : ∀ site, designedSite input site = true → siteShift T site = 0)
    (key : validate input = true → T.key2 = 0) :
    ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
      designedRule scalar tape input entry = true → shiftEntry T scalar tape.1 entry = entry := by
  intro entry member _ designed
  have good := garblerTranscript_good scalar tape entry member
  have shape := garblerTranscript_ask scalar tape entry member
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x =>
      exact shiftEntry_fixed_zero T scalar tape.1 index x answer
        (zero index (indexShape_of_ask scalar tape.1 index x shape) designed)
  | fixedInverse _ _ => exact good.elim
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash value =>
      have keep : designedHash input value = true := designed
      refine shiftEntry_hash_fixed T scalar tape.1 value answer (fun bridge => ?_) (fun notBridge
          => ?_)
      · rw [bridge, designedHash_bridgeInput] at keep
        exact key keep
      · rcases (good : value = bridgeInput tape.1.bridgeKey ∨
            ∃ slot : LimbSite, value = labelInput slot (garblerLabelOf tape slot.1)) with
          bridge | ⟨slot, rfl⟩
        · exact absurd bridge notBridge
        · rw [designedHash_labelInput] at keep
          rw [relabel_labelInput, sites slot.1 keep, bxor_zero]

theorem indexShift_hot (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) (ℓ : Lane)
    (k : Fin chunkCount) (fold : Fin chunkBits) (r : Fin (2 ^ chunkBits)) (half : Bool) :
    indexShift T scalar coins (.hot ℓ k fold r half) = ((T.lane ℓ).fold k).hot fold.val r.val
        half :=
  rfl

/-- **The Δ-family moves no designed entry.** -/
theorem deltaU_fixed (κ : Coord) (c : Block) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) :
    ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
      designedRule scalar tape input entry = true →
        shiftEntry (familyDeltaU κ input c) scalar tape.1 entry = entry := by
  refine fixed_of_zero _ scalar tape input (fun index shape designed => ?_) (fun site designed =>
      ?_)
    (fun _ => rfl)
  · cases index with
    | hot ℓ k fold r half =>
        obtain ⟨_, small, rSmall⟩ := shape
        simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq] at designed
        rw [indexShift_hot]
        exact deltaU_hot_off κ input c ℓ k fold.val r.val half small rSmall designed.1
    | gadget o κ' position bit =>
        simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq] at designed
        show (gadgetShift _ scalar tape.1 o κ' position bit,
          gadgetShift _ scalar tape.1 o κ' position bit) = _
        rw [deltaU_gadget, if_neg (fun h => h.2 designed.2)]
  · simp only [designedSite, Bool.and_eq_true, decide_eq_true_eq] at designed
    exact deltaU_level_off κ input c site designed.1

theorem curve_of_designed (ℓ : Lane) (input : AffineInput) (invalid : validate input = false)
    (laneOk : (laneIsCurve ℓ || validate input) = true) : laneIsPoint ℓ = false := by
  cases ℓ <;> simp_all [laneIsCurve, laneIsPoint]

/-- **Off the curve the `k₂`-family moves no designed entry.** -/
theorem key2_fixed (t : Nat) (c : Block) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (invalid : validate input = false) :
    ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
      designedRule scalar tape input entry = true →
        shiftEntry (familyKey2 t c) scalar tape.1 entry = entry := by
  refine fixed_of_zero _ scalar tape input (fun index shape designed => ?_) (fun site designed =>
      ?_)
    (fun valid => by rw [invalid] at valid; cases valid)
  · cases index with
    | hot ℓ k fold r half =>
        obtain ⟨_, small, rSmall⟩ := shape
        simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq] at designed
        rw [indexShift_hot]
        exact key2_hot_curve t c ℓ k (curve_of_designed ℓ input invalid designed.2) _ _ half small
          rSmall
    | gadget o κ position bit =>
        simp only [designedIndex, invalid, Bool.false_and] at designed
        cases designed
  · simp only [designedSite, Bool.and_eq_true] at designed
    exact key2_level_curve t c site.lane site.chunk (curve_of_designed _ input invalid designed.2)
      _ le_rfl _ site.switch.isLt

/-- **At a hidden gate the hot-output family moves no designed entry.** -/
theorem hotOut_fixed (ℓ : Lane) (k : Fin chunkCount) (n r : Nat) (c : Block)
    (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (hidden : ∀ (fold : Fin chunkBits) (entry : Fin (2 ^ chunkBits)) (half : Bool), fold.val = n →
      entry.val = r → designedIndex scalar tape input (.hot ℓ k fold entry half) = false) :
    ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
      designedRule scalar tape input entry = true →
        shiftEntry (familyHotOut ℓ k n r c) scalar tape.1 entry = entry := by
  refine fixed_of_zero _ scalar tape input (fun index shape designed => ?_)
    (fun site _ => hotOut_level ℓ k n r c _ _ _ le_rfl _ site.switch.isLt) (fun _ => rfl)
  cases index with
  | hot ℓ' k' fold r' half =>
      obtain ⟨_, small, rSmall⟩ := shape
      rw [indexShift_hot, hotOut_hot ℓ k n r c ℓ' k' fold.val r'.val half small rSmall]
      by_cases same : ℓ' = ℓ ∧ k' = k ∧ fold.val = n ∧ r'.val = r
      · obtain ⟨rfl, rfl, hn, hr⟩ := same
        rw [hidden fold r' half hn hr] at designed
        cases designed
      · rw [if_neg same]
  | gadget o κ position bit =>
      show (gadgetShift _ scalar tape.1 o κ position bit,
        gadgetShift _ scalar tape.1 o κ position bit) = _
      rw [hotOut_gadget]

/-! ### The families at a hidden index and at a hidden site -/

/-- **The family moving the garbler's point at `i`.** -/
def inFamily (input : AffineInput) : FixedIndex → Block → TapeShift
  | .hot ℓ _ _ r _, c =>
      if laneIsCurve ℓ || validate input then familyDeltaU ℓ.coord input c else familyKey2 r.val c
  | .gadget _ κ _ _, c => if validate input then familyDeltaU κ input c else familyKey2 0 c

/-- **The family moving the garbler's output at `i`.** -/
def outFamily (input : AffineInput) : FixedIndex → Block → TapeShift
  | .hot ℓ k fold r _, c => familyHotOut ℓ k fold.val r.val c
  | index, c => inFamily input index c

/-- **The family moving the garbler's label at a vector site.** -/
def hiddenSiteFamily (input : AffineInput) (site : VectorSite) (c : Block) : TapeShift :=
  if laneIsCurve site.lane || validate input then familyDeltaU site.lane.coord input c
  else familyKey2 site.switch.val c

theorem inFamily_valid (input : AffineInput) (index : FixedIndex) (c : Block) :
    (inFamily input index c).Valid := by
  cases index with
  | hot ℓ k fold r half =>
      show TapeShift.Valid (if (laneIsCurve ℓ || validate input) = true then
        familyDeltaU ℓ.coord input c else familyKey2 r.val c)
      split
      · exact familyDeltaU_valid _ _ _
      · exact familyKey2_valid _ _
  | gadget o κ position bit =>
      show TapeShift.Valid (if validate input = true then familyDeltaU κ input c else familyKey2 0
          c)
      split
      · exact familyDeltaU_valid _ _ _
      · exact familyKey2_valid _ _

theorem outFamily_valid (input : AffineInput) (index : FixedIndex) (c : Block) :
    (outFamily input index c).Valid := by
  cases index with
  | hot ℓ k fold r half => exact familyHotOut_valid _ _ _ _ _
  | gadget o κ position bit => exact inFamily_valid _ _ _

theorem hiddenSiteFamily_valid (input : AffineInput) (site : VectorSite) (c : Block) :
    (hiddenSiteFamily input site c).Valid := by
  unfold hiddenSiteFamily
  split
  · exact familyDeltaU_valid _ _ _
  · exact familyKey2_valid _ _

/-- A family that is the Δ-family on the curve (or at a curve lane) and a `k₂`-family otherwise
keeps the labels of `u`. -/
theorem choice_coins (condition : Bool) (κ : Coord) (input : AffineInput) (t : Nat) (c : Block)
    (coins : Coins) :
    Scheme.scheme.encode (shiftCoins (if condition = true then familyDeltaU κ input c
        else familyKey2 t c) coins).inputMacKey input =
      Scheme.scheme.encode coins.inputMacKey input := by
  split
  · exact deltaU_encode _ _ _ _
  · rw [key2_coins]

theorem inFamily_coins (input : AffineInput) (index : FixedIndex) (c : Block) (coins : Coins) :
    Scheme.scheme.encode (shiftCoins (inFamily input index c) coins).inputMacKey input =
      Scheme.scheme.encode coins.inputMacKey input := by
  cases index with
  | hot ℓ k fold r half => exact choice_coins _ _ _ _ _ _
  | gadget o κ position bit => exact choice_coins _ _ _ _ _ _

theorem outFamily_coins (input : AffineInput) (index : FixedIndex) (c : Block) (coins : Coins) :
    Scheme.scheme.encode (shiftCoins (outFamily input index c) coins).inputMacKey input =
      Scheme.scheme.encode coins.inputMacKey input := by
  cases index with
  | hot ℓ k fold r half =>
      show Scheme.scheme.encode (shiftCoins (familyHotOut ℓ k fold.val r.val c) coins).inputMacKey
        input = _
      rw [hotOut_coins]
  | gadget o κ position bit => exact inFamily_coins _ _ _ _

theorem not_or_valid (ℓ : Lane) (input : AffineInput) (h : ¬ (laneIsCurve ℓ || validate input) = true) :
    validate input = false := by
  cases hv : validate input
  · rfl
  · rw [hv, Bool.or_true] at h
    exact absurd rfl h

theorem point_of_not_curve (ℓ : Lane) (input : AffineInput)
    (h : ¬ (laneIsCurve ℓ || validate input) = true) : laneIsPoint ℓ = true := by
  cases ℓ <;> simp_all [laneIsCurve, laneIsPoint]

/-- A family chosen as the Δ-family on the curve (or at a curve lane of `κ`) and a `k₂`-family
otherwise moves no designed entry. -/
theorem choice_fixed (ℓ : Lane) (input : AffineInput) (t : Nat) (c : Block)
    (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
      designedRule scalar tape input entry = true →
        shiftEntry (if (laneIsCurve ℓ || validate input) = true then familyDeltaU ℓ.coord input c
          else familyKey2 t c) scalar tape.1 entry = entry := by
  split
  · exact deltaU_fixed _ _ scalar tape input
  · rename_i h
    exact key2_fixed _ _ scalar tape input (not_or_valid ℓ input h)

/-- **`inFamily` keeps the stage-2 view.** -/
theorem inFamily_view (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (index : FixedIndex) (c : Block) (tape : Coins × Oracle) :
    stageTwoView designedRule parameter scalar input (shiftTape (inFamily input index c) scalar tape) =
      stageTwoView designedRule parameter scalar input tape := by
  refine stageTwoView_shift _ (inFamily_valid input index c) parameter scalar tape input
    (inFamily_coins input index c tape.1) ?_
  cases index with
  | hot ℓ k fold r half => exact choice_fixed ℓ input r.val c scalar tape
  | gadget o κ position bit =>
      show ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
        designedRule scalar tape input entry = true →
          shiftEntry (if validate input = true then familyDeltaU κ input c else familyKey2 0 c)
            scalar tape.1 entry = entry
      split
      · exact deltaU_fixed _ _ scalar tape input
      · rename_i h
        exact key2_fixed _ _ scalar tape input (by simpa using h)

/-- **`hiddenSiteFamily` keeps the stage-2 view.** -/
theorem hiddenSiteFamily_view (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (site : VectorSite) (c : Block) (tape : Coins × Oracle) :
    stageTwoView designedRule parameter scalar input
        (shiftTape (hiddenSiteFamily input site c) scalar tape) =
      stageTwoView designedRule parameter scalar input tape :=
  stageTwoView_shift _ (hiddenSiteFamily_valid input site c) parameter scalar tape input
    (choice_coins _ _ _ _ _ _) (choice_fixed site.lane input site.switch.val c scalar tape)

/-- **`inFamily` moves the garbler's point at a hidden index by `c`.** -/
theorem inFamily_moves (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (index : FixedIndex) (c : Block) (shape : IndexShape scalar tape.1 index)
    (hidden : designedIndex scalar tape input index = false) :
    (indexShift (inFamily input index c) scalar tape.1 index).1 = c := by
  cases index with
  | hot ℓ k fold r half =>
      obtain ⟨one, small, rSmall⟩ := shape
      rw [indexShift_hot]
      show ((((if (laneIsCurve ℓ || validate input) = true then familyDeltaU ℓ.coord input c
        else familyKey2 r.val c).lane ℓ).fold k).hot fold.val r.val half).1 = c
      by_cases h : (laneIsCurve ℓ || validate input) = true
      · rw [if_pos h]
        have on : r.val = activeOf input ℓ.coord k % 2 ^ fold.val := by
          by_contra ne
          have designed : designedIndex scalar tape input (.hot ℓ k fold r half) = true := by
            simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨ne, h⟩
          rw [hidden] at designed
          cases designed
        rw [on]
        exact deltaU_hot_on ℓ.coord input c ℓ k fold.val half rfl small
      · rw [if_neg h, fold_hot]
        show (((familyKey2 r.val c).lane ℓ).fold k).level fold.val r.val = c
        have level := key2_level_point r.val c ℓ k (point_of_not_curve ℓ input h) fold.val one
          small.le
        rwa [Nat.mod_eq_of_lt rSmall] at level
  | gadget o κ position bit =>
      show gadgetShift (inFamily input (.gadget o κ position bit) c) scalar tape.1 o κ position bit = c
      show gadgetShift (if validate input = true then familyDeltaU κ input c else familyKey2 0 c)
        scalar tape.1 o κ position bit = c
      by_cases h : validate input = true
      · rw [if_pos h, deltaU_gadget]
        have differ : (inputBits input κ).getLsb position ≠ bit := by
          intro same
          have designed : designedIndex scalar tape input (.gadget o κ position bit) = true := by
            simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨h, same⟩
          rw [hidden] at designed
          cases designed
        rw [if_pos ⟨rfl, differ⟩]
      · rw [if_neg h]
        exact key2_gadget 0 c scalar tape.1 o κ position bit

/-- **`hiddenSiteFamily` moves the garbler's label at a hidden site by `c`.** -/
theorem hiddenSiteFamily_moves (input : AffineInput) (site : VectorSite) (c : Block)
    (hidden : designedSite input site = false) : siteShift (hiddenSiteFamily input site c) site =
        c := by
  unfold hiddenSiteFamily
  by_cases h : (laneIsCurve site.lane || validate input) = true
  · rw [if_pos h]
    have on : site.switch = chunkOf (inputBits input site.lane.coord) site.chunk := by
      by_contra ne
      have designed : designedSite input site = true := by
        simp only [designedSite, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨ne, h⟩
      rw [hidden] at designed
      cases designed
    exact deltaU_level_on _ input c site rfl on
  · rw [if_neg h]
    have level := key2_level_point site.switch.val c site.lane site.chunk
      (point_of_not_curve site.lane input h) (chunkWidth site.chunk) (chunkWidth_pos _) le_rfl
    rwa [Nat.mod_eq_of_lt site.switch.isLt] at level

/-- **`outFamily` keeps the stage-2 view at a hidden index of the garbler's shape.** -/
theorem outFamily_view (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (index : FixedIndex) (c : Block) (tape : Coins × Oracle) (tape₀ : Coins × Oracle)
    (hidden : designedIndex scalar tape₀ input index = false) :
    stageTwoView designedRule parameter scalar input (shiftTape (outFamily input index c) scalar tape) =
      stageTwoView designedRule parameter scalar input tape := by
  cases index with
  | hot ℓ k fold r half =>
      refine stageTwoView_shift _ (outFamily_valid input _ c) parameter scalar tape input
        (outFamily_coins input _ c tape.1) ?_
      refine hotOut_fixed ℓ k fold.val r.val c scalar tape input fun fold' entry half' same same'
          => ?_
      have eq : designedIndex scalar tape input (.hot ℓ k fold' entry half') =
          designedIndex scalar tape₀ input (.hot ℓ k fold r half) := by
        simp only [designedIndex, same, same']
      rw [eq]
      exact hidden
  | gadget o κ position bit => exact inFamily_view parameter scalar input _ c tape

theorem outFamily_moves (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (index : FixedIndex) (c : Block) (shape : IndexShape scalar tape.1 index)
    (hidden : designedIndex scalar tape input index = false) :
    (indexShift (outFamily input index c) scalar tape.1 index).2 = c := by
  cases index with
  | hot ℓ k fold r half =>
      obtain ⟨_, small, rSmall⟩ := shape
      show ((((familyHotOut ℓ k fold.val r.val c).lane ℓ).fold k).hot fold.val r.val half).2 = c
      rw [hotOut_hot ℓ k fold.val r.val c ℓ k fold.val r.val half small rSmall]
      simp
  | gadget o κ position bit =>
      exact inFamily_moves scalar tape input (.gadget o κ position bit) c shape hidden

/-! ### Touches of the stage-2 extra entries -/

/-- The garbler asks the **hidden** index `i` at `x`. -/
def HiddenInput (scalar : NonZeroScalar) (input : AffineInput) (index : FixedIndex) (x : Block)
    (tape : Coins × Oracle) : Prop :=
  designedIndex scalar tape input index = false ∧ InputHit scalar index x tape

/-- The garbler's answer at the **hidden** index `i` is `y`. -/
def HiddenOutput (scalar : NonZeroScalar) (input : AffineInput) (index : FixedIndex) (y : Block)
    (tape : Coins × Oracle) : Prop :=
  designedIndex scalar tape input index = false ∧ OutputHit scalar index y tape

theorem designed_mem (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (entry : Entry FixedIndex EncPRF.PermutationIndex)
    (member : entry ∈ garblerTranscript scalar tape) (plain : entry.IsEnc = false)
    (designed : designedRule scalar tape input entry = true) :
    entry ∈ designedEntries designedRule parameter scalar tape input := by
  rw [designedEntries_eq]
  exact List.mem_filter.mpr ⟨member, by simp [plain, designed]⟩

theorem designedRule_of_fixedPair (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (entry : Entry FixedIndex EncPRF.PermutationIndex)
    (member : entry ∈ garblerTranscript scalar tape) {index : FixedIndex} {x y : Fin (2 ^ 128)}
    (pair : fixedPair entry = some (index, x, y)) :
    designedRule scalar tape input entry = designedIndex scalar tape input index := by
  have good := garblerTranscript_good scalar tape entry member
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward i input' =>
      simp only [fixedPair, Option.some.injEq, Prod.mk.injEq] at pair
      obtain ⟨rfl, _, _⟩ := pair
      rfl
  | fixedInverse _ _ => exact good.elim
  | encForward _ _ => simp [fixedPair] at pair
  | encInverse _ _ => simp [fixedPair] at pair
  | hash _ => simp [fixedPair] at pair

/-- A stage-2 extra fixed-key pair is a garbler pair at a hidden index. -/
theorem stageTwo_fixed (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (tape : Coins × Oracle) {index : FixedIndex} {x y : Fin (2 ^ 128)}
    (extra : (stageTwoExtra designedRule parameter scalar input tape).fixed index x y) :
    designedIndex scalar tape input index = false ∧
      (⟨.fixedForward index (BitVec.ofFin x), BitVec.ofFin y⟩ :
        Entry FixedIndex EncPRF.PermutationIndex) ∈ garblerTranscript scalar tape := by
  obtain ⟨⟨e, member, pair⟩, notDesigned⟩ := extra
  have inT : e ∈ garblerTranscript scalar tape := (List.mem_filter.mp member).1
  refine ⟨?_, fixedPair_good scalar tape e inT pair⟩
  by_contra designed
  have d : designedIndex scalar tape input index = true := by simpa using designed
  have plain : Entry.IsEnc e = false := isEnc_of_fixedPair pair
  exact notDesigned ⟨e, designed_mem parameter scalar tape input e inT plain
    ((designedRule_of_fixedPair scalar tape input e inT pair).trans d), pair⟩

/-- **A stage-2 touch is a hidden hit, a hidden site's label, or the bridge input off the
curve.** -/
theorem stageTwo_touch (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (tape : Coins × Oracle) (entry : Entry FixedIndex EncPRF.PermutationIndex)
    (touch : Touches (stageTwoExtra designedRule parameter scalar input tape) entry) :
    match entry with
    | ⟨.fixedForward index x, answer⟩ =>
        HiddenInput scalar input index x tape ∨
          HiddenOutput scalar input index (show Block from answer) tape
    | ⟨.fixedInverse index y, answer⟩ =>
        HiddenOutput scalar input index y tape ∨
          HiddenInput scalar input index (show Block from answer) tape
    | ⟨.hash key, _⟩ => (validate input = false ∧ key = bridgeInput tape.1.bridgeKey) ∨
        ∃ slot : LimbSite, key = labelInput slot (garblerLabelOf tape slot.1) ∧
          designedSite input slot.1 = false
    | _ => False := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x =>
      rcases touch with ⟨y, extra⟩ | ⟨x', extra⟩
      · obtain ⟨hidden, member⟩ := stageTwo_fixed parameter scalar input tape extra
        exact Or.inl ⟨hidden, _, member⟩
      · obtain ⟨hidden, member⟩ := stageTwo_fixed parameter scalar input tape extra
        exact Or.inr ⟨hidden, _, member⟩
  | fixedInverse index y =>
      rcases touch with ⟨x, extra⟩ | ⟨y', extra⟩
      · obtain ⟨hidden, member⟩ := stageTwo_fixed parameter scalar input tape extra
        exact Or.inl ⟨hidden, _, member⟩
      · obtain ⟨hidden, member⟩ := stageTwo_fixed parameter scalar input tape extra
        exact Or.inr ⟨hidden, _, member⟩
  | encForward index x =>
      rcases touch with ⟨y, extra⟩ | ⟨x', extra⟩ <;>
      · obtain ⟨⟨e, member, pair⟩, _⟩ := extra
        have notEnc := (List.mem_filter.mp member).2
        rw [isEnc_of_encPair pair] at notEnc
        cases notEnc
  | encInverse index y =>
      rcases touch with ⟨x, extra⟩ | ⟨y', extra⟩ <;>
      · obtain ⟨⟨e, member, pair⟩, _⟩ := extra
        have notEnc := (List.mem_filter.mp member).2
        rw [isEnc_of_encPair pair] at notEnc
        cases notEnc
  | hash key =>
      have notDesigned : ¬ ∃ d ∈ designedEntries designedRule parameter scalar tape input, ∃ value,
          hashPair d = some (key, value) := by
        intro found
        simp only [Touches, stageTwoExtra, dropAll, if_pos found] at touch
        cases touch
      have listed : ∃ e ∈ plainEntries scalar tape, ∃ value, hashPair e = some (key, value) := by
        by_contra none'
        simp only [Touches, stageTwoExtra, dropAll, if_neg notDesigned, stageOneExtra, extraOf,
          if_neg none'] at touch
        cases touch
      obtain ⟨e, member, value, pair⟩ := listed
      have inT : e ∈ garblerTranscript scalar tape := (List.mem_filter.mp member).1
      have good := garblerTranscript_good scalar tape e inT
      obtain ⟨request', answer'⟩ := e
      cases request' <;> simp only [hashPair, Option.some.injEq, reduceCtorEq] at pair
      obtain ⟨rfl, _⟩ := pair
      rcases good with bridge | ⟨slot, scale⟩
      · refine Or.inl ⟨?_, bridge⟩
        by_contra valid
        exact notDesigned ⟨_, designed_mem parameter scalar tape input _ inT rfl (by
          show designedHash input _ = true
          rw [bridge, designedHash_bridgeInput]
          simpa using valid), _, rfl⟩
      · refine Or.inr ⟨slot, scale, ?_⟩
        by_contra kept
        exact notDesigned ⟨_, designed_mem parameter scalar tape input _ inT rfl (by
          show designedHash input _ = true
          rw [scale, designedHash_labelInput]
          simpa using kept), _, rfl⟩

/-! ### The bounds -/

/-- **Stage 2: a hidden input hit, at most `2^-128` given the view.** -/
theorem hiddenInput_le (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (view : (Public × List (Entry FixedIndex EncPRF.PermutationIndex)) × LamportSignature ×
      List (Entry FixedIndex EncPRF.PermutationIndex)) (index : FixedIndex) (x : Block) :
    swappedChallengeTape.toOuterMeasure
        {tape | stageTwoView designedRule parameter scalar input tape = view ∧
          HiddenInput scalar input index x tape} ≤
      ((2 : ℝ≥0∞) ^ 128)⁻¹ * swappedChallengeTape.toOuterMeasure
        {tape | stageTwoView designedRule parameter scalar input tape = view} := by
  have bound := event_le_of_symmetry swappedChallengeTape
    (stageTwoView designedRule parameter scalar input)
    (HiddenInput scalar input index x) (fun c tape => shiftTape (inFamily input index c) scalar tape)
    (fun c => swapped_shift_invariant _ (inFamily_valid input index c) scalar)
    (fun c tape => inFamily_view parameter scalar input index c tape)
    (fun tape c c' first second => by
      have moves : ∀ d, HiddenInput scalar input index x
          (shiftTape (inFamily input index d) scalar tape) →
          garblerPointOf scalar tape index ^^^ d = x := by
        intro d hit
        have hidden : designedIndex scalar tape input index = false := by
          rw [← designedIndex_shift (inFamily input index d)]
          exact hit.1
        have shape := inputHit_shape _ (inFamily_valid input index d) scalar tape index x hit.2
        have shifted := inputHit_shift _ (inFamily_valid input index d) scalar tape index x hit.2
        rwa [inFamily_moves scalar tape input index d shape hidden] at shifted
      have := (moves c first).trans (moves c' second).symm
      rwa [BitVec.xor_right_inj] at this) view
  rwa [card_block', Nat.cast_pow, Nat.cast_ofNat] at bound

/-- **Stage 2: a hidden output hit, at most `2^-128` given the view.** -/
theorem hiddenOutput_le (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (view : (Public × List (Entry FixedIndex EncPRF.PermutationIndex)) × LamportSignature ×
      List (Entry FixedIndex EncPRF.PermutationIndex)) (index : FixedIndex) (y : Block) :
    swappedChallengeTape.toOuterMeasure
        {tape | stageTwoView designedRule parameter scalar input tape = view ∧
          HiddenOutput scalar input index y tape} ≤
      ((2 : ℝ≥0∞) ^ 128)⁻¹ * swappedChallengeTape.toOuterMeasure
        {tape | stageTwoView designedRule parameter scalar input tape = view} := by
  by_cases some : ∃ tape₀, HiddenOutput scalar input index y tape₀
  · obtain ⟨tape₀, hidden₀, _⟩ := some
    have bound := event_le_of_symmetry swappedChallengeTape
      (stageTwoView designedRule parameter scalar input)
      (HiddenOutput scalar input index y) (fun c tape => shiftTape (outFamily input index c) scalar tape)
      (fun c => swapped_shift_invariant _ (outFamily_valid input index c) scalar)
      (fun c tape => outFamily_view parameter scalar input index c tape tape₀ hidden₀)
      (fun tape c c' first second => by
        have moves : ∀ d, HiddenOutput scalar input index y
            (shiftTape (outFamily input index d) scalar tape) →
            tape.2.1.permutation index (garblerPointOf scalar tape index) ^^^ d = y := by
          intro d hit
          have hidden : designedIndex scalar tape input index = false := by
            rw [← designedIndex_shift (outFamily input index d)]
            exact hit.1
          have shape := outputHit_shape _ (outFamily_valid input index d) scalar tape index y hit.2
          have shifted := outputHit_shift _ (outFamily_valid input index d) scalar tape index y hit.2
          rwa [outFamily_moves scalar tape input index d shape hidden] at shifted
        have := (moves c first).trans (moves c' second).symm
        rwa [BitVec.xor_right_inj] at this) view
    rwa [card_block', Nat.cast_pow, Nat.cast_ofNat] at bound
  · have empty : {tape | stageTwoView designedRule parameter scalar input tape = view ∧
        HiddenOutput scalar input index y tape} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun tape member => some ⟨tape, member.2⟩
    rw [empty, MeasureTheory.measure_empty]
    exact bot_le

/-- **Stage 2: a hidden site's label, at most `2^-128` given the view.** -/
theorem hiddenLabel_le (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (view : (Public × List (Entry FixedIndex EncPRF.PermutationIndex)) × LamportSignature ×
      List (Entry FixedIndex EncPRF.PermutationIndex)) (site : VectorSite)
    (hidden : designedSite input site = false) (label : Block) :
    swappedChallengeTape.toOuterMeasure
        {tape | stageTwoView designedRule parameter scalar input tape = view ∧
          garblerLabelOf tape site = label} ≤
      ((2 : ℝ≥0∞) ^ 128)⁻¹ * swappedChallengeTape.toOuterMeasure
        {tape | stageTwoView designedRule parameter scalar input tape = view} := by
  have bound := event_le_of_symmetry swappedChallengeTape
    (stageTwoView designedRule parameter scalar input)
    (fun tape => garblerLabelOf tape site = label)
    (fun c tape => shiftTape (hiddenSiteFamily input site c) scalar tape)
    (fun c => swapped_shift_invariant _ (hiddenSiteFamily_valid input site c) scalar)
    (fun c tape => hiddenSiteFamily_view parameter scalar input site c tape)
    (fun tape c c' first second => by
      have moves : ∀ d, garblerLabelOf (shiftTape (hiddenSiteFamily input site d) scalar tape) site
          =
          label → garblerLabelOf tape site ^^^ d = label := by
        intro d hit
        simp only [garblerLabelOf_shift _ (hiddenSiteFamily_valid input site d),
          hiddenSiteFamily_moves input site d hidden] at hit
        exact hit
      have := (moves c first).trans (moves c' second).symm
      rwa [BitVec.xor_right_inj] at this) view
  rwa [card_block', Nat.cast_pow, Nat.cast_ofNat] at bound

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
