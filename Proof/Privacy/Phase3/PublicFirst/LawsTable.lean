/-
**Phase 3, P1l — the two laws, part 2: the garbler on an answer table.**

On `G1U`'s swapped tape the garbler asks each fixed-key index at most once (`fixedOnce_garbleM`: the
gates of every paid fold level of every chunk, at every chunk width, and the gadget positions),
every EncPRF index at its two pad points, the hash at `bridgeInput t` and at its own switch-mask
limbs' inputs (`Hidden.Good`). Its whole run — transcript and published value — is therefore its
run on an **answer table** (`garbler_tapeAnswer`): the EncPRF permutations, the hash off the scale
range, the fixed-key permutations, and one hash answer per mask limb, read at the garbler's labels.

**The table has an explicit law, independent of the coins** (`swapped_reduce`):

* the limbs are P4's mask tape (`Laws.swapLaw_evalAt`: under the swap kernel the answers at the
  points do not depend on the points);
* the fixed-key answers are uniform, one per index (`Laws.fixedOnce_uniform`), although the
  garbler's inputs at a fold level read the answers of the level below;
* the EncPRF permutations and the hash off the scale range are uniform.

`swapped_reduce`: every function of the garbler's transcript and result, averaged over the swapped
tape, is its average over uniform coins and an independent `tableLaw` table.
-/

import Proof.Privacy.Phase3.PublicFirst.Laws

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape cellOf cellInput uniformMaskTape)
open scoped ENNReal

noncomputable section

/-! ### 1. Answer tables -/

/-- **An answer table**: the EncPRF permutations, the hash off the scale range, one answer per
fixed-key index, one hash answer per switch-mask limb. -/
abbrev Table :=
  PermutationOracle EncPRF.PermutationIndex Block × OtherTable × (FixedIndex → Block) × Tape

/-- **Answers from a table.** A hash question at a limb's input (at any label) returns the limb's
answer; any other hash question the table's hash off the scale range (`(0, 0)` at the scale inputs
no limb has); a fixed-key question its index's entry, whatever the input; EncPRF its
permutation. -/
def tableAnswer (A : Table) : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer
  | .fixedForward index _ => A.2.2.1 index
  | .fixedInverse index _ => A.2.2.1 index
  | .encForward index input => A.1.permutation index input
  | .encInverse index output => (A.1.permutation index).symm output
  | .hash key => (cellOf key).elim (hashOf A.2.1 blankScale key) A.2.2.2

theorem tableAnswer_hash (A : Table) (key : BaseField) :
    tableAnswer A (.hash key) = (cellOf key).elim (hashOf A.2.1 blankScale key) A.2.2.2 := rfl

theorem tableAnswer_cell (A : Table) (cell : Cell) (label : Block) :
    tableAnswer A (.hash (cellInput cell label)) = A.2.2.2 cell := by
  rw [tableAnswer_hash, Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput]
  rfl

/-- Off the scale range no hash input is a limb's. -/
theorem cellOf_of_not_lt (key : BaseField) (high : ¬ key.val < scaleRange) : cellOf key = none := by
  unfold cellOf
  rw [dif_neg]
  rintro ⟨cell, label, same⟩
  exact high (same ▸ scaleInput_val_lt_scaleRange _ _ _ _ _)

theorem tableAnswer_other (A : Table) (key : OtherInput) :
    tableAnswer A (.hash key.1) = A.2.1 key := by
  rw [tableAnswer_hash, cellOf_of_not_lt key.1 key.2]
  exact hashOf_other A.2.1 blankScale key

/-- A table with its fixed-key answers replaced. -/
theorem withFixed_tableAnswer (A : Table) (v : FixedIndex → Block) :
    withFixed (tableAnswer A) v = tableAnswer (A.1, A.2.1, v, A.2.2.2) := by
  funext q
  cases q <;> rfl

/-- **The table law**: uniform EncPRF permutations, hash off the scale range and fixed-key answers,
and P4's mask tape, all independent. -/
def tableLaw : PMF Table :=
  productPMF (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block))
    (productPMF (PMF.uniformOfFintype OtherTable)
      (productPMF (PMF.uniformOfFintype (FixedIndex → Block)) uniformMaskTape))

/-! ### 2. Transcripts -/

/-- Every transcript entry carries the answer function's answer. -/
theorem transcript_mem {α : Type}
    (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (computation : FreeQuery Programs.Spec α) :
    ∀ entry ∈ transcript ans computation, ans entry.1 = entry.2 := by
  induction computation with
  | pure value => intro entry member; cases member
  | query request next ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · rfl
      · exact ih _ entry member

/-! ### 3. The garbler asks each fixed-key index once -/

section Once

/-- `FixedOnce` of a computation asking no fixed-key question. -/
theorem FixedOnce.of_queryOnly {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}
    {α : Type} (plain : ∀ q, S q → NotFixed q) (X : Set FixedIndex) {c : FreeQuery Programs.Spec α}
    (only : Hidden.QueryOnly S c) : FixedOnce X c := by
  induction only with
  | pure value => exact .pure X value
  | query request next holds rest ih => exact .other X request next (plain request holds) ih

/-- A dependent loop over pairwise disjoint index sets. -/
theorem FixedOnce.pi : ∀ (count : Nat) {γ : Fin count → Type} (X : Fin count → Set FixedIndex)
    (program : (k : Fin count) → FreeQuery Programs.Spec (γ k)),
    (∀ k, FixedOnce (X k) (program k)) → (∀ k k', k ≠ k' → Disjoint (X k) (X k')) →
      FixedOnce (⋃ k, X k) (FreeQuery.pi count program)
  | 0, _, _, _, _, _ => .pure _ _
  | count + 1, γ, X, program, each, disjoint => by
      have tail := FixedOnce.pi count (fun k => X k.succ) (fun k => program k.succ)
        (fun k => each _) (fun k k' ne => disjoint _ _ fun same => ne (Fin.succ_injective _ same))
      have rest : ∀ head : γ 0, FixedOnce ((⋃ k : Fin count, X k.succ) ∪ ∅)
          (FreeQuery.pi count (fun k => program k.succ) >>= fun tail =>
            Pure.pure (Fin.cons (α := γ) head tail)) :=
        fun head => tail.bind (fun _ => .pure ∅ _) (Set.disjoint_empty _)
      have apart : Disjoint (X 0) ((⋃ k : Fin count, X k.succ) ∪ ∅) := by
        rw [Set.union_empty, Set.disjoint_iUnion_right]
        exact fun k => disjoint _ _ (Fin.succ_ne_zero k).symm
      refine ((each 0).bind rest apart).mono ?_
      rintro i (hi | ⟨_, ⟨k, rfl⟩, hi⟩ | hi)
      · exact Set.mem_iUnion.mpr ⟨0, hi⟩
      · exact Set.mem_iUnion.mpr ⟨k.succ, hi⟩
      · exact hi.elim

theorem hashM_once (index : FixedIndex) (label : Block) :
    FixedOnce {index} (Programs.hashM index label) :=
  .fixed {index} index label _ rfl fun _ => .pure _ _

/-- A hash question asks no fixed-key index. -/
theorem askHash_once (X : Set FixedIndex) (input : BaseField) :
    FixedOnce X (Programs.askHash input) :=
  .other X (.hash input) _ trivial fun _ => .pure _ _

/-- A switch's mask vector asks no fixed-key index. -/
theorem switchMaskM_once (lane : Lane) (chunk : Fin chunkCount) (switch : Nat) (label : Block) :
    FixedOnce ∅ (Programs.switchMaskM lane chunk switch label) := by
  have limbs := FixedOnce.vector (limbCount lane) (fun _ => ∅)
    (fun limb => Programs.askHash (scaleInput lane chunk switch limb.val label))
    (fun _ => askHash_once ∅ _) (fun _ _ _ => Set.disjoint_empty _)
  refine (limbs.bind (fun _ => .pure ∅ _) (Set.disjoint_empty _)).mono ?_
  rintro i (⟨_, ⟨_, rfl⟩, hi⟩ | hi) <;> exact hi.elim

/-- The two halves of one fold gate. -/
def gateSet (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat) : Set FixedIndex :=
  {index | ∃ half, index = hotIndexNat lane chunk step entry half}

/-- The gates of one fold level. -/
def levelSet (lane : Lane) (chunk : Fin chunkCount) (step : Nat) : Set FixedIndex :=
  {index | ∃ entry half, entry < 2 ^ step ∧ index = hotIndexNat lane chunk step entry half}

/-- The gates of the levels below `steps`. -/
def foldSet (lane : Lane) (chunk : Fin chunkCount) (steps : Nat) : Set FixedIndex :=
  {index | ∃ step < steps, index ∈ levelSet lane chunk step}

theorem foldMaskM_once (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat) (label : Block) :
    FixedOnce (gateSet lane chunk step entry) (Programs.foldMaskM lane chunk step entry label) := by
  have apart : Disjoint ({hotIndexNat lane chunk step entry false} : Set FixedIndex)
      ({hotIndexNat lane chunk step entry true} ∪ ∅) := by
    rw [Set.union_empty, Set.disjoint_singleton]
    intro same
    simp only [hotIndexNat, FixedIndex.hot.injEq] at same
    exact Bool.false_ne_true same.2.2.2.2
  refine ((hashM_once _ label).bind (fun _ => (hashM_once _ label).bind (fun _ => .pure ∅ _)
    (Set.disjoint_empty _)) apart).mono ?_
  rintro i (hi | hi | hi)
  · exact ⟨false, hi⟩
  · exact ⟨true, hi⟩
  · exact hi.elim

theorem garbleStepM_once (lane : Lane) (chunk : Fin chunkCount) (step : Nat) (zeroLabel : Block)
    (parent : Fin (2 ^ step) → Block) (small : step < chunkBits) :
    FixedOnce (levelSet lane chunk step) (Programs.garbleStepM lane chunk step zeroLabel parent) := by
  have entryBound : ∀ e : Fin (2 ^ step), e.val < 2 ^ chunkBits := fun e =>
    lt_of_lt_of_le e.isLt (Nat.pow_le_pow_right (by norm_num) small.le)
  unfold Programs.garbleStepM
  split
  · exact .pure _ _
  · have entries := FixedOnce.vector (2 ^ step) (fun e => gateSet lane chunk step e.val)
      (fun e => Programs.foldMaskM lane chunk step e.val (parent e))
      (fun e => foldMaskM_once lane chunk step e.val (parent e)) (fun e e' ne => by
        rw [Set.disjoint_left]
        rintro i ⟨half, rfl⟩ ⟨half', same⟩
        exact ne (Fin.ext (hotIndexNat_inj small small (entryBound e) (entryBound e') same).2.2.2.1))
    refine (entries.bind (fun _ => .pure ∅ _) (Set.disjoint_empty _)).mono ?_
    rintro i (⟨_, ⟨e, rfl⟩, ⟨half, rfl⟩⟩ | hi)
    · exact ⟨e.val, half, e.isLt, rfl⟩
    · exact hi.elim

theorem garbleFoldM_once (lane : Lane) (chunk : Fin chunkCount) (delta : Block)
    (zeroLabel : Nat → Block) :
    ∀ steps, steps ≤ chunkBits →
      FixedOnce (foldSet lane chunk steps) (Programs.garbleFoldM lane chunk delta zeroLabel steps)
  | 0, _ => .pure _ _
  | steps + 1, small => by
      have lower := garbleFoldM_once lane chunk delta zeroLabel steps (by omega)
      have apart : Disjoint (foldSet lane chunk steps) (levelSet lane chunk steps ∪ ∅) := by
        rw [Set.union_empty, Set.disjoint_left]
        rintro i ⟨n, below, e, half, eSmall, rfl⟩ ⟨e', half', eSmall', same⟩
        have eBound : e < 2 ^ chunkBits :=
          lt_of_lt_of_le eSmall (Nat.pow_le_pow_right (by norm_num) (by omega))
        have eBound' : e' < 2 ^ chunkBits :=
          lt_of_lt_of_le eSmall' (Nat.pow_le_pow_right (by norm_num) (by omega))
        have := (hotIndexNat_inj (by omega) (by omega) eBound eBound' same).2.2.1
        omega
      refine (lower.bind (fun previous => (garbleStepM_once lane chunk steps _ previous.1
        (by omega)).bind (fun _ => .pure ∅ _) (Set.disjoint_empty _)) apart).mono ?_
      rintro i (⟨n, below, hi⟩ | hi | hi)
      · exact ⟨n, by omega, hi⟩
      · exact ⟨steps, by omega, hi⟩
      · exact hi.elim

theorem chunkTablesM_once (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) (c : Fin chunkCount) :
    FixedOnce (foldSet lane c (chunkWidth c)) (Programs.chunkTablesM lane delta bitKey c) := by
  have fold := garbleFoldM_once lane c delta (labelAt fun position => (chunkKey bitKey c position).1)
    (chunkWidth c) (chunkWidth_le c)
  have chunk : FixedOnce (foldSet lane c (chunkWidth c) ∪ ∅) (Programs.garbleChunkM lane delta bitKey c) :=
    fold.bind (fun _ => .pure ∅ _) (Set.disjoint_empty _)
  have masks : ∀ tables : HotLabels (chunkWidth c) × Vector Block (chunkWidth c - 1),
      FixedOnce ((⋃ _ : Fin (2 ^ chunkWidth c), (∅ : Set FixedIndex)) ∪ ∅)
        (FreeQuery.vector (2 ^ chunkWidth c) (fun switch =>
          Programs.switchMaskM lane c switch.val (tables.1 switch)) >>= fun masks =>
            Pure.pure (tables, masks)) := fun tables =>
    (FixedOnce.vector _ (fun _ => ∅) _ (fun _ => switchMaskM_once _ _ _ _)
      (fun _ _ _ => Set.disjoint_empty _)).bind (fun _ => .pure ∅ _) (Set.disjoint_empty _)
  refine (chunk.bind masks (Set.disjoint_of_subset_right ?_ (Set.disjoint_empty _))).mono ?_
  · rintro i (⟨_, ⟨_, rfl⟩, hi⟩ | hi) <;> exact hi.elim
  · rintro i ((hi | hi) | (⟨_, ⟨_, rfl⟩, hi⟩ | hi))
    · exact hi
    all_goals exact hi.elim

/-- The fold gates of one lane. -/
def laneSet (lane : Lane) : Set FixedIndex :=
  {index | ∃ c : Fin chunkCount, index ∈ foldSet lane c (chunkWidth c)}

theorem hot_of_foldSet {lane : Lane} {c : Fin chunkCount} {steps : Nat} {index : FixedIndex}
    (member : index ∈ foldSet lane c steps) :
    ∃ (fold : Fin chunkBits) (entry : Fin (2 ^ chunkBits)) (half : Bool),
      index = .hot lane c fold entry half := by
  obtain ⟨n, below, e, half, eSmall, rfl⟩ := member
  exact ⟨⟨n % chunkBits, Nat.mod_lt _ chunkBits_pos⟩,
    ⟨e % 2 ^ chunkBits, Nat.mod_lt _ twoPowChunkBits_pos⟩, half, rfl⟩

theorem laneM_once (lane : Lane) (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block) :
    FixedOnce (laneSet lane) (Programs.laneM lane delta bitKey) := by
  have chunks := FixedOnce.pi chunkCount (fun c => foldSet lane c (chunkWidth c))
    (Programs.chunkTablesM lane delta bitKey) (fun c => chunkTablesM_once lane delta bitKey c)
    (fun c c' ne => by
      rw [Set.disjoint_left]
      intro i first second
      obtain ⟨f, e, h, rfl⟩ := hot_of_foldSet first
      obtain ⟨f', e', h', same⟩ := hot_of_foldSet second
      injection same with sameLane sameChunk
      exact ne sameChunk)
  refine (chunks.bind (fun _ => .pure ∅ _) (Set.disjoint_empty _)).mono ?_
  rintro i (⟨_, ⟨c, rfl⟩, hi⟩ | hi)
  · exact ⟨c, hi⟩
  · exact hi.elim

/-- The gadget positions of one digit. -/
def digitSet (output : Fin FieldMacToECMac.outputMacCount) : Set FixedIndex :=
  {index | ∃ κ position, index = .gadget output κ position}

theorem gadgetDigestM_once (output : Fin FieldMacToECMac.outputMacCount)
    (coordinate : EncPRF.Coordinate) (mac : CoordinateMac) :
    FixedOnce {index | ∃ position, index = .gadget output (Pipeline.gadgetCoord coordinate) position}
      (Programs.gadgetDigestM output coordinate mac) := by
  have positions := FixedOnce.vector coordinateBitCount
    (fun position => {FixedIndex.gadget output (Pipeline.gadgetCoord coordinate) position})
    (fun position => Programs.hashM (.gadget output (Pipeline.gadgetCoord coordinate) position)
      (mac.get position)) (fun position => hashM_once _ _) (fun p p' ne => by
        rw [Set.disjoint_singleton]
        intro same
        injection same with sameOutput sameCoord samePosition
        exact ne samePosition)
  refine (positions.bind (fun _ => .pure ∅ _) (Set.disjoint_empty _)).mono ?_
  rintro i (⟨_, ⟨p, rfl⟩, hi⟩ | hi)
  · exact ⟨p, hi⟩
  · exact hi.elim

theorem garbleEntryM_once (output : Fin FieldMacToECMac.outputMacCount)
    (key : FieldMacToECMac.OutputKey) (inputKey : InputMacKey) (pad : Exception.Entry) :
    FixedOnce (digitSet output) (Programs.garbleEntryM output key inputKey pad) := by
  unfold Programs.garbleEntryM
  split
  · exact .pure _ _
  · have apart : ∀ first second : EncPRF.Coordinate, first ≠ second →
        Disjoint {index | ∃ position, index = FixedIndex.gadget output
            (Pipeline.gadgetCoord first) position}
          {index | ∃ position, index = FixedIndex.gadget output
            (Pipeline.gadgetCoord second) position} := by
      intro first second ne
      rw [Set.disjoint_left]
      rintro i ⟨p, rfl⟩ ⟨p', same⟩
      injection same with sameOutput sameCoord
      cases first <;> cases second <;> first | exact ne rfl | cases sameCoord
    refine ((((gadgetDigestM_once output .x _).bind (fun _ => (gadgetDigestM_once output .y _).bind
      (fun _ => .pure ∅ _) (Set.disjoint_empty _)) ?_).bind (fun _ => .pure ∅ _)
        (Set.disjoint_empty _))).mono ?_
    · rw [Set.union_empty]
      exact apart .x .y (by decide)
    · rintro i ((⟨p, rfl⟩ | ⟨p, rfl⟩ | hi) | hi)
      · exact ⟨_, p, rfl⟩
      · exact ⟨_, p, rfl⟩
      · exact hi.elim
      · exact hi.elim

theorem gadgetM_once (keys : FieldMacToECMac.OutputKeys) (inputKey : InputMacKey)
    (pads : FieldMacToECMac.ExceptionPad) :
    FixedOnce {index | ∃ output, index ∈ digitSet output} (Programs.gadgetM keys inputKey pads) := by
  refine (FixedOnce.vector FieldMacToECMac.outputMacCount digitSet _
    (fun output => garbleEntryM_once output _ _ _) (fun o o' ne => by
      rw [Set.disjoint_left]
      rintro i ⟨κ, p, rfl⟩ ⟨κ', p', same⟩
      injection same with sameOutput
      exact ne sameOutput)).mono ?_
  rintro i ⟨_, ⟨o, rfl⟩, hi⟩
  exact ⟨o, hi⟩

variable [FieldCertificate] [GroupCertificate]

/-- **The garbler asks each fixed-key index at most once.** -/
theorem fixedOnce_garbleM (scalar : NonZeroScalar) (coins : Coins) :
    FixedOnce Set.univ (Programs.garbleM scalar coins) := by
  have laneApart : ∀ first second : Lane, first ≠ second →
      Disjoint (laneSet first) (laneSet second) := by
    intro first second ne
    rw [Set.disjoint_left]
    rintro i ⟨c, hc⟩ ⟨c', hc'⟩
    obtain ⟨f, e, h, rfl⟩ := hot_of_foldSet hc
    obtain ⟨f', e', h', same⟩ := hot_of_foldSet hc'
    injection same with sameLane
    exact ne sameLane
  have gadgetApart : ∀ lane : Lane,
      Disjoint (laneSet lane) {index | ∃ output, index ∈ digitSet output} := by
    intro lane
    rw [Set.disjoint_left]
    rintro i ⟨c, hc⟩ ⟨o, κ, p, same⟩
    obtain ⟨f, e, h, rfl⟩ := hot_of_foldSet hc
    cases same
  unfold Programs.garbleM
  refine (FixedOnce.bind (X := ∅) (askHash_once ∅ _) (fun hashed =>
    FixedOnce.bind (X := ∅) (FixedOnce.of_queryOnly (fun q enc => by
        cases q <;> first | exact enc.elim | trivial) ∅ (Hidden.padsM_encOnly _))
      (fun pads => FixedOnce.bind (laneM_once .curveX _ _) (fun _ =>
        FixedOnce.bind (laneM_once .curveY _ _) (fun _ =>
          FixedOnce.bind (laneM_once .pointX _ _) (fun _ =>
            FixedOnce.bind (laneM_once .pointY _ _) (fun _ =>
              FixedOnce.bind (gadgetM_once _ _ _) (fun _ => .pure ∅ _)
                (Set.disjoint_empty _)) ?_) ?_) ?_) ?_) (Set.empty_disjoint _))
    (Set.empty_disjoint _)).mono (Set.subset_univ _)
  · rw [Set.union_empty]
    exact gadgetApart .pointY
  · rw [Set.disjoint_union_right, Set.union_empty]
    exact ⟨laneApart _ _ (by decide), gadgetApart .pointX⟩
  · rw [Set.disjoint_union_right, Set.disjoint_union_right, Set.union_empty]
    exact ⟨laneApart _ _ (by decide), laneApart _ _ (by decide), gadgetApart .curveY⟩
  · rw [Set.disjoint_union_right, Set.disjoint_union_right, Set.disjoint_union_right,
      Set.union_empty]
    exact ⟨laneApart _ _ (by decide), laneApart _ _ (by decide), laneApart _ _ (by decide),
      gadgetApart .curveX⟩

end Once

/-! ### 4. The garbler on the swapped tape -/

section Tape

variable [FieldCertificate] [GroupCertificate]

/-- **The answers the garbler reads on an assembled tape**: the tape's fixed-key permutations, and
the table of the tape's EncPRF permutations, hash off the scale range and limb answers `T`. -/
def tapeAnswer (rest : RestTape TapeRest) (T : Tape) :
    ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer :=
  withPerms (tableAnswer (rest.1.2.2, rest.2, fun _ => 0, T)) rest.1.2.1.permutation

/-- The garbler's labels on an assembled tape are those of its rest. -/
theorem garblerLabelOf_assemble (rest : RestTape TapeRest) (scale : ScaleTable) :
    Hidden.garblerLabelOf (reassembleEquiv (assemble (rest, scale))) = garblerLabels rest :=
  garblerLabel_hashOf rest.1 rest.2 scale

/-- **On an assembled tape the garbler runs as on its rest and the limb answers at its labels.** -/
theorem garbler_tapeAnswer (scalar : NonZeroScalar) (rest : RestTape TapeRest) (scale : ScaleTable) :
    transcript (tapeAnswer rest (evalAt (limbPoint (garblerLabels rest)) scale))
        (Programs.garbleM scalar rest.1.1) =
      garblerTranscript scalar (reassembleEquiv (assemble (rest, scale))) ∧
    (Programs.garbleM scalar rest.1.1).eval
        (tapeAnswer rest (evalAt (limbPoint (garblerLabels rest)) scale)) =
      (Programs.garbleM scalar rest.1.1).eval
        (publicAnswer (reassembleEquiv (assemble (rest, scale))).2) := by
  let tape := reassembleEquiv (assemble (rest, scale))
  refine transcript_agree (Programs.garbleM scalar tape.1) (publicAnswer tape.2) _ ?_
  intro entry member
  have good := garblerTranscript_good scalar tape entry member
  have answer := transcript_mem (publicAnswer tape.2) (Programs.garbleM scalar tape.1) entry member
  obtain ⟨request, value⟩ := entry
  simp only at answer
  subst answer
  cases request with
  | fixedForward index input => rfl
  | fixedInverse index output => exact good.elim
  | encForward index input => rfl
  | encInverse index output => exact good.elim
  | hash key =>
      have lhs : tapeAnswer rest (evalAt (limbPoint (garblerLabels rest)) scale) (.hash key) =
          tableAnswer (rest.1.2.2, rest.2, fun _ => 0, evalAt (limbPoint (garblerLabels rest)) scale)
            (.hash key) := rfl
      have rhs : publicAnswer tape.2 (.hash key) = hashOf rest.2 scale key := rfl
      rw [lhs, rhs]
      rcases good with bridge | ⟨slot, label⟩
      · have high := bridgeInput_not_lt tape.1.bridgeKey
        rw [← bridge] at high
        rw [tableAnswer_other _ ⟨key, high⟩]
        exact (hashOf_other rest.2 scale ⟨key, high⟩).symm
      · subst label
        have input : Hidden.labelInput slot (Hidden.garblerLabelOf tape slot.1) =
            cellInput slot (garblerLabels rest slot.1) := by
          rw [garblerLabelOf_assemble]
          rfl
        rw [input, tableAnswer_cell]
        exact (hashOf_scale rest.2 scale (limbInput (garblerLabels rest) slot)).symm

end Tape

/-! ### 5. The law of the table -/

section Law

variable [FieldCertificate] [GroupCertificate]

/-- **The garbler on the swapped tape is the garbler on an independent `tableLaw` table.** -/
theorem swapped_reduce (scalar : NonZeroScalar)
    (G : Coins → List (Entry FixedIndex EncPRF.PermutationIndex) → Public × InputMacKey → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape *
        G tape.1 (garblerTranscript scalar tape) ((Programs.garbleM scalar tape.1).eval (publicAnswer tape.2))
      = ∑' coins, PMF.uniformOfFintype Coins coins * ∑' A, tableLaw A *
          G coins (transcript (tableAnswer A) (Programs.garbleM scalar coins))
            ((Programs.garbleM scalar coins).eval (tableAnswer A)) := by
  let K : RestTape TapeRest × Tape → ℝ≥0∞ := fun y =>
    G y.1.1.1 (transcript (tapeAnswer y.1 y.2) (Programs.garbleM scalar y.1.1.1))
      ((Programs.garbleM scalar y.1.1.1).eval (tapeAnswer y.1 y.2))
  have assembled : ∑' tape, swappedChallengeTape tape *
        G tape.1 (garblerTranscript scalar tape)
          ((Programs.garbleM scalar tape.1).eval (publicAnswer tape.2)) =
      ∑' x, swapLaw (restLaw restUniform) (fun rest => limbPoint (garblerLabels rest)) x *
        K (x.1, evalAt (limbPoint (garblerLabels x.1)) x.2) := by
    unfold swappedChallengeTape swappedTape
    rw [tsum_map_mul, tsum_map_mul]
    refine tsum_congr fun x => ?_
    obtain ⟨rest, scale⟩ := x
    have same := garbler_tapeAnswer scalar rest scale
    show _ * G rest.1.1 _ _ = _ * G rest.1.1 _ _
    rw [same.1, same.2]
    rfl
  have law := swapLaw_evalAt (restLaw restUniform) (fun rest => limbPoint (garblerLabels rest))
  rw [assembled, ← tsum_map_mul (swapLaw (restLaw restUniform)
    (fun rest => limbPoint (garblerLabels rest)))
    (fun x => (x.1, evalAt (limbPoint (garblerLabels x.1)) x.2)) K, law, tsum_productPMF]
  unfold restLaw restUniform
  rw [tsum_productPMF, tsum_uniform_prod]
  refine tsum_congr fun coins => congrArg _ ?_
  rw [tsum_uniform_prod]
  unfold tableLaw
  rw [tsum_productPMF, tsum_swap_mul]
  refine tsum_congr fun enc => congrArg _ ?_
  rw [tsum_productPMF, tsum_swap_mul]
  refine tsum_congr fun other => congrArg _ ?_
  simp_rw [tsum_productPMF]
  rw [tsum_swap_mul]
  simp_rw [tsum_swap_mul (PMF.uniformOfFintype (FixedIndex → Block)) (uniformMaskTape : PMF Tape)]
  refine tsum_congr fun T => congrArg _ ?_
  rw [tsum_equiv_uniform (Equiv.mk PermutationOracle.permutation PermutationOracle.mk
    (fun _ => rfl) (fun _ => rfl))]
  have once := fixedOnce_uniform (fixedOnce_garbleM scalar coins)
    (tableAnswer (enc, other, fun _ => 0, T))
    (fun entries value => G coins entries value)
  simp only [withFixed_tableAnswer] at once
  exact once

/-- **A tape realising a table on the garbler's questions**: the table's EncPRF permutations and hash
answers, and fixed-key permutations answering the garbler's one question per index by the table's
block (`FixedOnce.realize`). -/
def tableTape (scalar : NonZeroScalar) (coins : Coins) (A : Table) : Coins × Oracle :=
  (coins, (⟨((fixedOnce_garbleM scalar coins).realize (tableAnswer A) A.2.2.1).choose⟩, A.1,
    fun key => tableAnswer A (.hash key)))

/-- The public answers of an oracle, as an answer function with its fixed-key permutations
replaced. -/
theorem publicAnswer_withPerms (π : FixedIndex → Equiv.Perm Block)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : BaseField → Block × Block)
    (answer : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (encEq : ∀ index input, answer (.encForward index input) = enc.permutation index input)
    (encInverseEq : ∀ index output, answer (.encInverse index output) = (enc.permutation index).symm output)
    (hashEq : ∀ key, answer (.hash key) = hash key) :
    publicAnswer ((⟨π⟩, enc, hash) : Oracle) = withPerms answer π := by
  funext q
  cases q with
  | fixedForward _ _ => rfl
  | fixedInverse _ _ => rfl
  | encForward index input => exact (encEq index input).symm
  | encInverse index output => exact (encInverseEq index output).symm
  | hash key =>
      show randomOracleAnswer hash key = answer (.hash key)
      rw [randomOracleAnswer_eq, hashEq]

theorem tableTape_garbler (scalar : NonZeroScalar) (coins : Coins) (A : Table) :
    garblerTranscript scalar (tableTape scalar coins A) =
      transcript (tableAnswer A) (Programs.garbleM scalar coins) := by
  have realized := ((fixedOnce_garbleM scalar coins).realize (tableAnswer A) A.2.2.1).choose_spec
  show transcript (publicAnswer (tableTape scalar coins A).2) (Programs.garbleM scalar coins) = _
  rw [show (tableTape scalar coins A).2 = ((⟨((fixedOnce_garbleM scalar coins).realize (tableAnswer A)
      A.2.2.1).choose⟩, A.1, fun key => tableAnswer A (.hash key)) : Oracle) from rfl,
    publicAnswer_withPerms _ A.1 _ (tableAnswer A) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl),
    realized.1, withFixed_tableAnswer]

/-- **A tape functional determined by the coins and the garbler's transcript, averaged over the
swapped tape**, is its average over uniform coins and an independent `tableLaw` table, at the
table's tape. -/
theorem swapped_tableTape (scalar : NonZeroScalar) (F : Coins × Oracle → ℝ≥0∞)
    (congr : ∀ first second : Coins × Oracle, first.1 = second.1 →
      garblerTranscript scalar first = garblerTranscript scalar second → F first = F second) :
    ∑' tape, swappedChallengeTape tape * F tape =
      ∑' coins, PMF.uniformOfFintype Coins coins * ∑' A, tableLaw A * F (tableTape scalar coins A) := by
  classical
  let G : Coins → List (Entry FixedIndex EncPRF.PermutationIndex) → Public × InputMacKey → ℝ≥0∞ :=
    fun coins entries _ =>
      if h : ∃ tape : Coins × Oracle, tape.1 = coins ∧ garblerTranscript scalar tape = entries then
        F h.choose else 0
  have atTape : ∀ tape : Coins × Oracle, G tape.1 (garblerTranscript scalar tape)
      ((Programs.garbleM scalar tape.1).eval (publicAnswer tape.2)) = F tape := by
    intro tape
    have h : ∃ t : Coins × Oracle, t.1 = tape.1 ∧ garblerTranscript scalar t = garblerTranscript scalar tape :=
      ⟨tape, rfl, rfl⟩
    dsimp only [G]
    rw [dif_pos h]
    exact congr _ _ h.choose_spec.1 h.choose_spec.2
  have atTable : ∀ coins A, G coins (transcript (tableAnswer A) (Programs.garbleM scalar coins))
      ((Programs.garbleM scalar coins).eval (tableAnswer A)) = F (tableTape scalar coins A) := by
    intro coins A
    have h : ∃ t : Coins × Oracle, t.1 = coins ∧
        garblerTranscript scalar t = transcript (tableAnswer A) (Programs.garbleM scalar coins) :=
      ⟨tableTape scalar coins A, rfl, tableTape_garbler scalar coins A⟩
    dsimp only [G]
    rw [dif_pos h]
    exact congr _ _ h.choose_spec.1 (h.choose_spec.2.trans (tableTape_garbler scalar coins A).symm)
  have reduced := swapped_reduce scalar G
  simp only [atTape, atTable] at reduced
  exact reduced

end Law

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
