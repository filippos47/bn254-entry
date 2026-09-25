/-
**Phase 3, P1f — stage 1, hits: at most `2^-128` each, given the stage-1 view.**

For every fixed-key index `i` of the garbler's shape and for every vector site, a one-parameter
family of join-keeping tape shifts (`familyZeros`) moves the garbler's point and output at `i`,
respectively the garbler's one-hot label at the site, by `c`:

* a fold gate at step `n` and parent `r` of chunk `k` (`1 ≤ n < b_k`, `r < 2 ^ n`), and a switch `j`
  of chunk `k` (`familyPath`): every zero label of the chunk moves by `c` and, at every paid step,
  one parent's material absorbs it along the path of the target `r` (`j`) (`pathRoute`), so the
  level label of the target moves by `c` at every level (`FoldShift.level_path`), whatever the
  chunk's width `b_k ∈ {2, 4}`;
* a gadget position: its zero label moves by `c`, absorbed in one parent's material when it is a
  paid step's.

None of these touches the published value or the EncPRF entries, so by `event_le_of_symmetry`:

* `inputHit_le`, `outputHit_le`: `μ{view₁ = v ∧ the garbler asks i at x (answers y at i)}
  ≤ 2^-128 · μ{view₁ = v}`;
* `labelHit_le`: `μ{view₁ = v ∧ the garbler's label at a vector site is L} ≤ 2^-128 · μ{view₁ = v}`
  (the price of a hash query at a scale input, which names one site and one label).

The generic fold algebra lives here too: `xorFold_single` (a one-hot XOR fold),
`FoldShift.level_path` and `FoldShift.level_active` (the level labels of a path family and of an
active-path family, at every width).
-/

import Proof.Privacy.Phase3.Hidden.GarblerAsk
import Proof.Correctness.PGS.OneHot

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open scoped ENNReal

noncomputable section

/-! ### Blocks and one-hot XOR folds -/

theorem bxor_zero (c : Block) : c ^^^ (0 : Block) = c := BitVec.xor_zero

theorem bzero_xor (c : Block) : (0 : Block) ^^^ c = c := BitVec.zero_xor

theorem block_xor_self (c : Block) : c ^^^ c = 0 := BitVec.xor_self

/-- A one-hot XOR fold is its hot entry. -/
theorem xorFold_single {count : Nat} (r₀ : Fin count) (c : Block) :
    xorFold (fun r : Fin count => if r = r₀ then c else 0) = c := by
  rw [← xorFoldExcept_xor r₀, xorFoldExcept_congr r₀ _ (fun _ => 0) (fun r ne => if_neg ne),
    xorFoldExcept_eq, xorFold_zero, if_pos rfl, bxor_zero, bzero_xor]

/-- A conditionally one-hot XOR fold. -/
theorem xorFold_single_nat (count r₀ : Nat) (small : r₀ < count) (P : Prop) [Decidable P]
    (c : Block) :
    xorFold (fun r : Fin count => if P ∧ r.val = r₀ then c else 0) = if P then c else 0 := by
  by_cases hP : P
  · have same : (fun r : Fin count => if P ∧ r.val = r₀ then c else 0) =
        fun r => if r = ⟨r₀, small⟩ then c else 0 := funext fun r => by
      simp only [hP, true_and, Fin.ext_iff]
    rw [same, xorFold_single, if_pos hP]
  · have same : (fun r : Fin count => if P ∧ r.val = r₀ then c else 0) = fun _ => 0 :=
      funext fun r => by simp [hP]
    rw [same, xorFold_zero, if_neg hP]

/-! ### The level labels of a fold shift, at every width -/

theorem Hidden.FoldShift.level_succ (F : FoldShift) (n j : Nat) :
    F.level (n + 1) j =
      if j < 2 ^ n then F.level n j ^^^ F.stepShift n j else F.stepShift n (j - 2 ^ n) := rfl

theorem Hidden.FoldShift.stepShift_zero (F : FoldShift) (r : Nat) : F.stepShift 0 r = F.zero 0 :=
  rfl

theorem Hidden.FoldShift.stepShift_succ (F : FoldShift) (n r : Nat) :
    F.stepShift (n + 1) r = F.m (n + 1) r := rfl

/-- **The route of a target at a step**: the target's own parent when the target's bit there is
set, another parent otherwise. -/
def pathRoute (t n : Nat) : Nat :=
  if t / 2 ^ n % 2 = 1 then t % 2 ^ n else if t % 2 ^ n = 0 then 1 else 0

theorem pathRoute_lt (t n : Nat) (one : 1 ≤ n) : pathRoute t n < 2 ^ n := by
  have two : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) one
  have low := Nat.mod_lt t (Nat.two_pow_pos n)
  unfold pathRoute
  split_ifs <;> omega

/-- A target below `2 ^ n` is not routed through itself at step `n`. -/
theorem pathRoute_ne (t n : Nat) (small : t < 2 ^ n) : t ≠ pathRoute t n := by
  have bit : ¬ t / 2 ^ n % 2 = 1 := by
    rw [Nat.div_eq_of_lt small]
    omega
  unfold pathRoute
  rw [if_neg bit, Nat.mod_eq_of_lt small]
  split_ifs <;> omega

/-- **A path family moves the target's level label by `c` at every level**: no `Δ` shift, every
zero label of the chunk moved by `c`, and at every paid step the material of the routed parent. -/
theorem Hidden.FoldShift.level_path (F : FoldShift) (t width : Nat) (c : Block)
    (delta : F.delta = 0) (zero : ∀ n, n < width → F.zero n = c)
    (m : ∀ n r, 1 ≤ n → n < width → F.m n r = if r = pathRoute t n then c else 0) :
    ∀ n, 1 ≤ n → n ≤ width → F.level n (t % 2 ^ n) = c
  | 0, one, _ => absurd one (by omega)
  | 1, _, small => by
      rw [F.level_succ]
      split
      · show F.delta ^^^ F.zero 0 = c
        rw [delta, zero 0 (by omega), bzero_xor]
      · exact zero 0 (by omega)
  | n + 1 + 1, _, small => by
      have previous := F.level_path t width c delta zero m (n + 1) (by omega) (by omega)
      rw [F.level_succ, Nat.mod_pow_succ]
      have low := Nat.mod_lt t (Nat.two_pow_pos (n + 1))
      rcases Nat.mod_two_eq_zero_or_one (t / 2 ^ (n + 1)) with bit | bit
      · rw [bit, mul_zero, add_zero, if_pos low, previous, F.stepShift_succ,
          m (n + 1) _ (by omega) (by omega)]
        have ne : t % 2 ^ (n + 1) ≠ pathRoute t (n + 1) := by
          unfold pathRoute
          rw [if_neg (by omega)]
          split_ifs <;> omega
        rw [if_neg ne, bxor_zero]
      · rw [bit, mul_one, if_neg (by omega), Nat.add_sub_cancel, F.stepShift_succ,
          m (n + 1) _ (by omega) (by omega)]
        have eq : t % 2 ^ (n + 1) = pathRoute t (n + 1) := by
          unfold pathRoute
          rw [if_pos bit]
        rw [if_pos eq]

theorem Hidden.FoldShift.stepShift_active (F : FoldShift) (a width : Nat) (c : Block)
    (zero : ∀ n, n < width → F.zero n = if a / 2 ^ n % 2 = 1 then c else 0)
    (m : ∀ n r, 1 ≤ n → n < width →
      F.m n r = if r = a % 2 ^ n ∧ a / 2 ^ n % 2 = 1 then c else 0)
    (n r : Nat) (small : n < width) (entry : r < 2 ^ n) :
    F.stepShift n r = if r = a % 2 ^ n ∧ a / 2 ^ n % 2 = 1 then c else 0 := by
  cases n with
  | zero =>
      rw [F.stepShift_zero, zero 0 small]
      have r0 : r = a % 2 ^ 0 := by
        rw [pow_zero] at entry ⊢
        omega
      simp only [r0, true_and]
  | succ n => rw [F.stepShift_succ, m (n + 1) r (by omega) small]

/-- **An active-path family moves exactly the active path by `c`**: `Δ` and the zero label of every
set bit of `a` moved by `c`, and at every paid step whose bit is set the material of the active
parent. At every level only the active entry `a mod 2 ^ n` moves. -/
theorem Hidden.FoldShift.level_active (F : FoldShift) (a width : Nat) (c : Block)
    (delta : F.delta = c)
    (zero : ∀ n, n < width → F.zero n = if a / 2 ^ n % 2 = 1 then c else 0)
    (m : ∀ n r, 1 ≤ n → n < width →
      F.m n r = if r = a % 2 ^ n ∧ a / 2 ^ n % 2 = 1 then c else 0) :
    ∀ n, n ≤ width → ∀ j, j < 2 ^ n → F.level n j = if j = a % 2 ^ n then c else 0
  | 0, _, j, small => by
      show F.delta = _
      rw [pow_zero] at small
      rw [delta, if_pos (by rw [pow_zero]; omega)]
  | n + 1, le, j, small => by
      have step := F.stepShift_active a width c zero m n
      rw [F.level_succ, Nat.mod_pow_succ]
      have low := Nat.mod_lt a (Nat.two_pow_pos n)
      have twice : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ n) with bit | bit
      · rw [bit, mul_zero, add_zero]
        by_cases jLow : j < 2 ^ n
        · rw [if_pos jLow, F.level_active a width c delta zero m n (by omega) j jLow,
            step j (by omega) jLow]
          by_cases hj : j = a % 2 ^ n <;> simp [hj, bit]
        · rw [if_neg jLow, step (j - 2 ^ n) (by omega) (by omega),
            if_neg (show ¬ (j - 2 ^ n = a % 2 ^ n ∧ a / 2 ^ n % 2 = 1) by omega),
            if_neg (show ¬ j = a % 2 ^ n by omega)]
      · rw [bit, mul_one]
        by_cases jLow : j < 2 ^ n
        · rw [if_pos jLow, F.level_active a width c delta zero m n (by omega) j jLow,
            step j (by omega) jLow, if_neg (show ¬ j = a % 2 ^ n + 2 ^ n by omega)]
          by_cases hj : j = a % 2 ^ n
          · rw [if_pos hj, if_pos ⟨hj, bit⟩, block_xor_self]
          · rw [if_neg hj, if_neg (fun h => hj h.1), bxor_zero]
        · rw [if_neg jLow, step (j - 2 ^ n) (by omega) (by omega)]
          by_cases hj : j - 2 ^ n = a % 2 ^ n
          · rw [if_pos ⟨hj, bit⟩, if_pos (show j = a % 2 ^ n + 2 ^ n by omega)]
          · rw [if_neg (fun h => hj h.1), if_neg (show ¬ j = a % 2 ^ n + 2 ^ n by omega)]

/-! ### A lane's fold shift -/

theorem lane_fold_zero (T : TapeShift) (ℓ : Lane) (k : Fin chunkCount) (n : Nat)
    (small : n < chunkWidth k) :
    ((T.lane ℓ).fold k).zero n =
      T.zero ℓ.coord (chunkBitIndex k ⟨n, small⟩) ^^^ (if laneIsPoint ℓ then T.key2 else 0) := by
  simp only [LaneShift.fold, TapeShift.lane]
  unfold labelAt
  rw [dif_pos small]

theorem lane_fold_m (T : TapeShift) (ℓ : Lane) (k : Fin chunkCount) :
    ((T.lane ℓ).fold k).m = T.m ℓ k := rfl

theorem lane_fold_o (T : TapeShift) (ℓ : Lane) (k : Fin chunkCount) :
    ((T.lane ℓ).fold k).o = T.o ℓ k := rfl

theorem fold_hot (F : FoldShift) (n r : Nat) (half : Bool) :
    F.hot n r half = (F.level n r, F.level n r ^^^ F.o n r ^^^ (if half then 0 else F.m n r)) := rfl

/-! ### The zero-label families -/

/-- **Move the zero labels of coordinate `κ` at the positions `P` by `c`.** At every paid step
whose zero label moves, one parent's material (`route`) absorbs it, so every join is kept. -/
def familyZeros (κ : Coord) (P : Nat → Prop) [DecidablePred P]
    (route : Fin chunkCount → Nat → Nat) (c : Block) : TapeShift where
  delta _ := 0
  zero κ' p := if κ' = κ ∧ P p.val then c else 0
  key2 := 0
  m ℓ k n r := if (ℓ.coord = κ ∧ P (chunkOffset k + n)) ∧ r = route k n % 2 ^ n then c else 0
  o _ _ _ _ := 0

theorem familyZeros_valid (κ : Coord) (P : Nat → Prop) [DecidablePred P]
    (route : Fin chunkCount → Nat → Nat) (c : Block) : (familyZeros κ P route c).Valid := by
  intro ℓ k n _ small
  rw [lane_fold_zero _ _ _ _ small]
  show xorFold (fun r : Fin (2 ^ n) =>
      if (ℓ.coord = κ ∧ P (chunkOffset k + n)) ∧ r.val = route k n % 2 ^ n then c else 0) =
    (if ℓ.coord = κ ∧ P (chunkOffset k + n) then c else 0) ^^^ (if laneIsPoint ℓ then 0 else 0)
  rw [xorFold_single_nat _ _ (Nat.mod_lt _ (Nat.two_pow_pos n)), ite_self, bxor_zero]

/-- The positions of a chunk. -/
def InChunk (k : Fin chunkCount) (p : Nat) : Prop := chunkOffset k ≤ p ∧ p < chunkOffset k +
    chunkWidth k

instance (k : Fin chunkCount) : DecidablePred (InChunk k) := fun _ => by
  unfold InChunk
  infer_instance

/-- **The path family** of chunk `k` of coordinate `κ` towards the target `t`. -/
def familyPath (κ : Coord) (k : Fin chunkCount) (t : Nat) (c : Block) : TapeShift :=
  familyZeros κ (InChunk k) (fun k' n => if k' = k then pathRoute t n else 0) c

theorem familyPath_valid (κ : Coord) (k : Fin chunkCount) (t : Nat) (c : Block) :
    (familyPath κ k t c).Valid :=
  familyZeros_valid _ _ _ _

/-- **The path family moves the target's level label by `c` at every level** of its chunk, at every
lane of its coordinate. -/
theorem familyPath_level (κ : Coord) (k : Fin chunkCount) (t : Nat) (c : Block) (ℓ : Lane)
    (hκ : ℓ.coord = κ) :
    ∀ n, 1 ≤ n → n ≤ chunkWidth k → (((familyPath κ k t c).lane ℓ).fold k).level n (t % 2 ^ n) =
        c := by
  refine FoldShift.level_path _ t (chunkWidth k) c rfl (fun n small => ?_) (fun n r one small => ?_)
  · rw [lane_fold_zero _ _ _ _ small]
    show (if ℓ.coord = κ ∧ InChunk k (chunkOffset k + n) then c else 0) ^^^
      (if laneIsPoint ℓ then 0 else 0) = c
    rw [if_pos ⟨hκ, by unfold InChunk; omega⟩, ite_self, bxor_zero]
  · rw [lane_fold_m]
    show (if (ℓ.coord = κ ∧ InChunk k (chunkOffset k + n)) ∧
        r = (if k = k then pathRoute t n else 0) % 2 ^ n then c else 0) = _
    rw [if_pos rfl, Nat.mod_eq_of_lt (pathRoute_lt t n one)]
    by_cases hr : r = pathRoute t n
    · rw [if_pos ⟨⟨hκ, by unfold InChunk; omega⟩, hr⟩, if_pos hr]
    · rw [if_neg (fun h => hr h.2), if_neg hr]

/-! ### The families at an index and at a vector site -/

/-- **The family moving the garbler's point and output at a fixed-key index.** -/
def familyAt : FixedIndex → Block → TapeShift
  | .hot ℓ k _ entry _, c => familyPath ℓ.coord k entry.val c
  | .gadget _ κ position _, c => familyZeros κ (fun p => p = position.val) (fun _ _ => 0) c

theorem familyAt_valid (index : FixedIndex) (c : Block) : (familyAt index c).Valid := by
  cases index with
  | hot ℓ k fold entry half => exact familyPath_valid _ _ _ _
  | gadget o κ position bit => exact familyZeros_valid κ (fun p => p = position.val) (fun _ _ => 0) c

/-- **The family moving the garbler's one-hot label at a vector site.** -/
def siteFamily (site : VectorSite) (c : Block) : TapeShift :=
  familyPath site.lane.coord site.chunk site.switch.val c

theorem siteFamily_valid (site : VectorSite) (c : Block) : (siteFamily site c).Valid :=
  familyPath_valid _ _ _ _

/-- **The site family moves the site's label by `c`.** -/
theorem siteFamily_moves (site : VectorSite) (c : Block) : siteShift (siteFamily site c) site =
    c := by
  have level := familyPath_level site.lane.coord site.chunk site.switch.val c site.lane rfl
    (chunkWidth site.chunk) (chunkWidth_pos _) le_rfl
  rwa [Nat.mod_eq_of_lt site.switch.isLt] at level

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- The garbler's index shapes. -/
def IndexShape (scalar : NonZeroScalar) (coins : Coins) (index : FixedIndex) : Prop :=
  GarblerAsk scalar coins (.fixedForward index 0)

theorem indexShape_of_ask (scalar : NonZeroScalar) (coins : Coins) (index : FixedIndex) (x : Block)
    (ask : GarblerAsk scalar coins (.fixedForward index x)) : IndexShape scalar coins index := by
  cases index <;> exact ask

/-- **The family moves its index's point and output by `c`**, at every index of the garbler's
shape. -/
theorem familyAt_moves (scalar : NonZeroScalar) (coins : Coins) (index : FixedIndex) (c : Block)
    (shape : IndexShape scalar coins index) : indexShift (familyAt index c) scalar coins index =
        (c, c) := by
  cases index with
  | hot ℓ k fold entry half =>
      obtain ⟨one, small, entrySmall⟩ := shape
      have level := familyPath_level ℓ.coord k entry.val c ℓ rfl fold.val one small.le
      rw [Nat.mod_eq_of_lt entrySmall] at level
      show (((familyPath ℓ.coord k entry.val c).lane ℓ).fold k).hot fold.val entry.val half = (c, c)
      rw [fold_hot, level, lane_fold_o, lane_fold_m]
      show (c, c ^^^ 0 ^^^ (if half then 0 else
        if (ℓ.coord = ℓ.coord ∧ InChunk k (chunkOffset k + fold.val)) ∧
          entry.val = (if k = k then pathRoute entry.val fold.val else 0) % 2 ^ fold.val then c
        else 0)) = (c, c)
      have ne : ¬ ((ℓ.coord = ℓ.coord ∧ InChunk k (chunkOffset k + fold.val)) ∧
          entry.val = pathRoute entry.val fold.val) :=
        fun h => pathRoute_ne entry.val fold.val entrySmall h.2
      rw [if_pos rfl, Nat.mod_eq_of_lt (pathRoute_lt _ _ one), if_neg ne, ite_self, bxor_zero,
        bxor_zero]
  | gadget o κ position bit =>
      show (gadgetShift _ scalar coins o κ position bit,
        gadgetShift _ scalar coins o κ position bit) = (c, c)
      have shift : gadgetShift (familyAt (.gadget o κ position bit) c) scalar coins o κ position bit
          = c := by
        show (0 : Block) ^^^ (if κ = κ ∧ position.val = position.val then c else 0) ^^^
          (if bit then 0 else 0) = c
        rw [if_pos ⟨rfl, rfl⟩, ite_self, bzero_xor, bxor_zero]
      rw [shift]

theorem shiftEntry_fst_hash (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins)
    (value : BaseField) (answer : (PublicQuery.hash (FixedIndex := FixedIndex)
      (EncIndex := EncPRF.PermutationIndex) value).Answer) :
    ∃ value', (shiftEntry T scalar coins ⟨.hash value, answer⟩).1 = .hash value' := by
  by_cases h : value = bridgeInput coins.bridgeKey
  · exact ⟨value, by simp [shiftEntry, h]⟩
  · exact ⟨relabel (siteShift T) value, by simp [shiftEntry, h]⟩

theorem inputHit_shift (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) (index : FixedIndex) (x : Block)
    (hit : InputHit scalar index x (shiftTape T scalar tape)) :
    garblerPointOf scalar tape index ^^^ (indexShift T scalar tape.1 index).1 = x := by
  obtain ⟨y, member⟩ := hit
  rw [garblerTranscript_shift T valid] at member
  obtain ⟨e, eMember, same⟩ := List.mem_map.mp member
  have good := garblerTranscript_good scalar tape e eMember
  obtain ⟨request, answer⟩ := e
  cases request with
  | fixedForward i input =>
      simp only [shiftEntry] at same
      obtain ⟨⟨rfl, rfl⟩, _⟩ := same
      rw [show input = garblerPointOf scalar tape index from good]
  | fixedInverse _ _ => unfold shiftEntry at same; cases same
  | encForward _ _ => unfold shiftEntry at same; cases same
  | encInverse _ _ => unfold shiftEntry at same; cases same
  | hash value =>
      obtain ⟨value', fst⟩ := shiftEntry_fst_hash T scalar tape.1 value answer
      rw [same] at fst
      cases fst

theorem outputHit_shift (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) (index : FixedIndex) (y : Block)
    (hit : OutputHit scalar index y (shiftTape T scalar tape)) :
    tape.2.1.permutation index (garblerPointOf scalar tape index) ^^^
      (indexShift T scalar tape.1 index).2 = y := by
  obtain ⟨x, member⟩ := hit
  rw [garblerTranscript_shift T valid] at member
  obtain ⟨e, eMember, same⟩ := List.mem_map.mp member
  have good := garblerTranscript_good scalar tape e eMember
  have consistent := transcript_consistent tape.2 (Programs.garbleM scalar tape.1) e eMember
  obtain ⟨request, answer⟩ := e
  cases request with
  | fixedForward i input =>
      simp only [shiftEntry] at same
      obtain ⟨⟨rfl, _⟩, answerSame⟩ := same
      have answerEq : answer = tape.2.1.permutation index input := consistent
      rw [← show input = garblerPointOf scalar tape index from good, ← answerEq]
  | fixedInverse _ _ => unfold shiftEntry at same; cases same
  | encForward _ _ => unfold shiftEntry at same; cases same
  | encInverse _ _ => unfold shiftEntry at same; cases same
  | hash value =>
      obtain ⟨value', fst⟩ := shiftEntry_fst_hash T scalar tape.1 value answer
      rw [same] at fst
      cases fst

/-- An input hit on a shifted tape comes from a garbler entry of the garbler's shape. -/
theorem inputHit_shape (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) (index : FixedIndex) (x : Block)
    (hit : InputHit scalar index x (shiftTape T scalar tape)) : IndexShape scalar tape.1 index := by
  obtain ⟨y, member⟩ := hit
  rw [garblerTranscript_shift T valid] at member
  obtain ⟨e, eMember, same⟩ := List.mem_map.mp member
  have shape := garblerTranscript_ask scalar tape e eMember
  obtain ⟨request, answer⟩ := e
  cases request with
  | fixedForward i input' =>
      simp only [shiftEntry] at same
      obtain ⟨⟨rfl, _⟩, _⟩ := same
      exact indexShape_of_ask scalar tape.1 _ _ shape
  | fixedInverse _ _ => unfold shiftEntry at same; cases same
  | encForward _ _ => unfold shiftEntry at same; cases same
  | encInverse _ _ => unfold shiftEntry at same; cases same
  | hash value =>
      obtain ⟨value', fst⟩ := shiftEntry_fst_hash T scalar tape.1 value answer
      rw [same] at fst
      cases fst

theorem outputHit_shape (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) (index : FixedIndex) (y : Block)
    (hit : OutputHit scalar index y (shiftTape T scalar tape)) : IndexShape scalar tape.1 index :=
        by
  obtain ⟨x, member⟩ := hit
  exact inputHit_shape T valid scalar tape index x ⟨y, member⟩

theorem card_block' : Fintype.card Block = 2 ^ 128 := Kriterion.ArgoMAC.Security.PGS.card_block

/-- **Stage 1: an input hit, at most `2^-128` given the view.** -/
theorem inputHit_le (parameter : ℕ) (scalar : NonZeroScalar)
    (view : Public × List (Entry FixedIndex EncPRF.PermutationIndex)) (index : FixedIndex) (x : Block) :
    swappedChallengeTape.toOuterMeasure
        {tape | stageOneView parameter scalar tape = view ∧ InputHit scalar index x tape} ≤
      ((2 : ℝ≥0∞) ^ 128)⁻¹ *
        swappedChallengeTape.toOuterMeasure {tape | stageOneView parameter scalar tape = view} := by
  have bound := event_le_of_symmetry swappedChallengeTape (stageOneView parameter scalar)
    (InputHit scalar index x) (fun c tape => shiftTape (familyAt index c) scalar tape)
    (fun c => swapped_shift_invariant _ (familyAt_valid index c) scalar)
    (fun c tape => stageOneView_shift _ (familyAt_valid index c) parameter scalar tape)
    (fun tape c c' first second => by
      have moves : ∀ d, InputHit scalar index x (shiftTape (familyAt index d) scalar tape) →
          garblerPointOf scalar tape index ^^^ d = x := by
        intro d hit
        have shifted := inputHit_shift _ (familyAt_valid index d) scalar tape index x hit
        rwa [familyAt_moves scalar tape.1 index d
          (inputHit_shape _ (familyAt_valid index d) scalar tape index x hit)] at shifted
      have := (moves c first).trans (moves c' second).symm
      rwa [BitVec.xor_right_inj] at this) view
  rwa [card_block', Nat.cast_pow, Nat.cast_ofNat] at bound

/-- **Stage 1: an output hit, at most `2^-128` given the view.** -/
theorem outputHit_le (parameter : ℕ) (scalar : NonZeroScalar)
    (view : Public × List (Entry FixedIndex EncPRF.PermutationIndex)) (index : FixedIndex) (y : Block) :
    swappedChallengeTape.toOuterMeasure
        {tape | stageOneView parameter scalar tape = view ∧ OutputHit scalar index y tape} ≤
      ((2 : ℝ≥0∞) ^ 128)⁻¹ *
        swappedChallengeTape.toOuterMeasure {tape | stageOneView parameter scalar tape = view} := by
  have bound := event_le_of_symmetry swappedChallengeTape (stageOneView parameter scalar)
    (OutputHit scalar index y) (fun c tape => shiftTape (familyAt index c) scalar tape)
    (fun c => swapped_shift_invariant _ (familyAt_valid index c) scalar)
    (fun c tape => stageOneView_shift _ (familyAt_valid index c) parameter scalar tape)
    (fun tape c c' first second => by
      have moves : ∀ d, OutputHit scalar index y (shiftTape (familyAt index d) scalar tape) →
          tape.2.1.permutation index (garblerPointOf scalar tape index) ^^^ d = y := by
        intro d hit
        have shifted := outputHit_shift _ (familyAt_valid index d) scalar tape index y hit
        rwa [familyAt_moves scalar tape.1 index d
          (outputHit_shape _ (familyAt_valid index d) scalar tape index y hit)] at shifted
      have := (moves c first).trans (moves c' second).symm
      rwa [BitVec.xor_right_inj] at this) view
  rwa [card_block', Nat.cast_pow, Nat.cast_ofNat] at bound

/-- **Stage 1: a label hit, at most `2^-128` given the view**: the garbler's one-hot label at a
vector site is any given block with conditional mass at most `2^-128`. -/
theorem labelHit_le (parameter : ℕ) (scalar : NonZeroScalar)
    (view : Public × List (Entry FixedIndex EncPRF.PermutationIndex)) (site : VectorSite)
    (label : Block) :
    swappedChallengeTape.toOuterMeasure
        {tape | stageOneView parameter scalar tape = view ∧ garblerLabelOf tape site = label} ≤
      ((2 : ℝ≥0∞) ^ 128)⁻¹ *
        swappedChallengeTape.toOuterMeasure {tape | stageOneView parameter scalar tape = view} := by
  have bound := event_le_of_symmetry swappedChallengeTape (stageOneView parameter scalar)
    (fun tape => garblerLabelOf tape site = label)
    (fun c tape => shiftTape (siteFamily site c) scalar tape)
    (fun c => swapped_shift_invariant _ (siteFamily_valid site c) scalar)
    (fun c tape => stageOneView_shift _ (siteFamily_valid site c) parameter scalar tape)
    (fun tape c c' first second => by
      have moves : ∀ d, garblerLabelOf (shiftTape (siteFamily site d) scalar tape) site = label →
          garblerLabelOf tape site ^^^ d = label := by
        intro d hit
        simp only [garblerLabelOf_shift _ (siteFamily_valid site d), siteFamily_moves] at hit
        exact hit
      have := (moves c first).trans (moves c' second).symm
      rwa [BitVec.xor_right_inj] at this) view
  rwa [card_block', Nat.cast_pow, Nat.cast_ofNat] at bound

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
