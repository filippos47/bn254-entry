/-
**Phase 3, P1n — the off-curve law, step (i): the garbler's entries on an answer table.**

After `LawsTable.swapped_reduce` the garbler of `G1U°` runs on an answer table `A`. Off the curve
the entries `LawOff` plants are its EncPRF entries and its designed entries; on a table both are
transcripts of the evaluator's own programs:

* **the EncPRF entries are the pads' transcript at `k₁`** (`garbler_enc`): the EncPRF part of the
  garbler's transcript is `padsM`'s at the hash value of the bridge input (`enc_split'` for any
  answer function), and the pads' questions read only the first whitening key (`padsM_first`);
* **the designed entries are system A's transcript** (`garbler_designed`): off the curve the
  designed entries are the curve lanes' fold gates off the active parent, at every paid step of
  every chunk, and the hash limbs of their inactive switches (the filter of the two curve lanes'
  transcripts), and on a table the evaluator run on the published fold joins and the selected
  labels asks exactly those questions, in the same order, at the same inputs (correctness on the
  table, `fold_filter` by induction on the step, at every chunk width).

Correctness on a table is read off the real-oracle lemmas (`Reach.evalFold_off`,
`evalHot_agrees_off_active`) through **the table's oracles** (`tableOracle`, `tableHash`): at every
fixed-key index the translation by its entry, and the table's hash. Their Davies–Meyer values are
the table's entries, so the fold materials and the switch masks are the table's
(`foldMaskM_table`, `switchMaskM_table`), whatever the labels.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsPrivate
import Proof.Privacy.Phase3.Hidden.Reach
import Proof.Privacy.Phase3.Hidden.CurveDesigned

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape)
open scoped ENNReal

noncomputable section

/-! ### 1. Transcripts of binds and loops -/

section Loops

variable (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)

theorem transcript_bind' {α β : Type} (P : FreeQuery Programs.Spec α)
    (f : α → FreeQuery Programs.Spec β) :
    transcript ans (P >>= f) = transcript ans P ++ transcript ans (f (P.eval ans)) := by
  rw [transcript_eq_transcriptOf, transcript_eq_transcriptOf, transcript_eq_transcriptOf]
  exact Hidden.transcriptOf_bind ans P f

theorem transcript_pure' {α : Type} (value : α) :
    transcript ans (Pure.pure value : FreeQuery Programs.Spec α) = [] := rfl

theorem transcript_vector' {α : Type} : ∀ (count : Nat) (P : Fin count → FreeQuery Programs.Spec α),
    transcript ans (FreeQuery.vector count P) = (List.ofFn fun i => transcript ans (P i)).flatten
  | 0, _ => rfl
  | count + 1, P => by
      show transcript ans (FreeQuery.vector count (fun index => P index.castSucc) >>= fun values =>
          P (Fin.last count) >>= fun value => Pure.pure (values.push value)) = _
      rw [transcript_bind', transcript_bind', transcript_pure', transcript_vector' count,
        List.ofFn_succ', List.concat_eq_append, List.flatten_append, List.append_nil]
      simp

theorem transcript_pi' : ∀ (count : Nat) {β : Fin count → Type}
    (P : (index : Fin count) → FreeQuery Programs.Spec (β index)),
    transcript ans (FreeQuery.pi count P) = (List.ofFn fun i => transcript ans (P i)).flatten
  | 0, _, _ => rfl
  | count + 1, _, P => by
      show transcript ans (P 0 >>= fun head => FreeQuery.pi count (fun index => P index.succ) >>=
          fun tail => Pure.pure (Fin.cons head tail)) = _
      rw [transcript_bind', transcript_bind', transcript_pure', transcript_pi' count,
        List.ofFn_succ, List.flatten_cons, List.append_nil]

/-- A filter of a flattened family is the flattened family of filters. -/
theorem filter_flatten_ofFn {α : Type} {count : Nat} (keep : α → Bool) (f : Fin count → List α) :
    (List.ofFn f).flatten.filter keep = (List.ofFn fun i => (f i).filter keep).flatten := by
  rw [List.filter_flatten, List.map_ofFn]
  rfl

/-- Two flattened families agree if they agree entrywise. -/
theorem flatten_ofFn_congr {α : Type} {count : Nat} {f g : Fin count → List α}
    (same : ∀ i, f i = g i) : (List.ofFn f).flatten = (List.ofFn g).flatten := by
  rw [funext same]

end Loops

/-! ### 2. The table's oracles -/

/-- Translation by a block, as a permutation. -/
def xorPerm (c : Block) : Equiv.Perm Block where
  toFun x := x ^^^ c
  invFun x := x ^^^ c
  left_inv x := by
    show (x ^^^ c) ^^^ c = x
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  right_inv x := by
    show (x ^^^ c) ^^^ c = x
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- **The table's fixed-key oracle**: at every index the translation by its entry. -/
def tableOracle (A : Table) : PermutationOracle FixedIndex Block :=
  ⟨fun index => xorPerm (A.2.2.1 index)⟩

/-- **The table's hash oracle**: its answers to hash questions. -/
abbrev tableHash (A : Table) : EncPRF.HashOracle := fun key => tableAnswer A (.hash key)

/-- A hash question asks its input. -/
theorem eval_askHash_ans (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (key : BaseField) : (Programs.askHash key).eval ans = ans (.hash key) := rfl

theorem xor_xor_cancel (a b : Block) : (a ^^^ b) ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem xor_cancel_pair (a b x : Block) : (a ^^^ x) ^^^ (b ^^^ x) = a ^^^ b := by
  rw [BitVec.xor_assoc, BitVec.xor_comm b x, ← BitVec.xor_assoc x x b, BitVec.xor_self,
    BitVec.zero_xor]

theorem hash_tableOracle (A : Table) (index : FixedIndex) (x : Block) :
    hash (tableOracle A) index x = A.2.2.1 index := by
  show (x ^^^ A.2.2.1 index) ^^^ x = _
  rw [BitVec.xor_comm x, xor_xor_cancel]

/-- **On a table the fold material is the table's, whatever the label.** -/
theorem foldMaskM_table (A : Table) (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat)
    (label : Block) :
    (Programs.foldMaskM lane chunk step entry label).eval (tableAnswer A) =
      foldMask (tableOracle A) lane chunk step entry label := by
  show (A.2.2.1 (hotIndexNat lane chunk step entry false) ^^^ label) ^^^
      (A.2.2.1 (hotIndexNat lane chunk step entry true) ^^^ label) =
    hash (tableOracle A) (hotIndexNat lane chunk step entry false) label ^^^
      hash (tableOracle A) (hotIndexNat lane chunk step entry true) label
  rw [hash_tableOracle, hash_tableOracle, xor_cancel_pair]

/-- Two answer functions agreeing on a program's questions evaluate it alike. -/
theorem eval_agree {α : Type} {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}
    {P : FreeQuery Programs.Spec α} (only : Hidden.QueryOnly S P)
    (a b : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (same : ∀ q, S q → a q = b q) : P.eval a = P.eval b := by
  induction only with
  | pure value => rfl
  | query request next holds rest ih =>
      show (next (a request)).eval a = (next (b request)).eval b
      rw [same request holds]
      exact ih _

set_option maxRecDepth 200000 in
/-- **On a table a switch mask is the sampler of the table's limbs.** (At the phase-5 widths the
rewrite needs a recursion depth between `50,000` and `80,000`.) -/
theorem switchMaskM_table (A : Table) (lane : Lane) (chunk : Fin chunkCount) (switch : Nat)
    (label : Block) :
    (Programs.switchMaskM lane chunk switch label).eval (tableAnswer A) =
      Vector.ofFn (switchMask (tableHash A) lane chunk switch label) := by
  rw [eval_agree (Hidden.switchMaskM_only lane chunk switch label) (tableAnswer A)
    (publicAnswer (tableOracle A, A.1, tableHash A)) (fun q hq => by
      obtain ⟨limb, rfl⟩ := hq
      exact (randomOracleAnswer_eq (tableHash A) _).symm), Programs.eval_switchMaskM]

/-! ### 3. The lanes on a table are the lanes on the table's oracles -/

section Eval

variable (A : Table) (lane : Lane) (chunk : Fin chunkCount)

theorem garbleStepM_table (step : Nat) (zeroLabel : Block) (parent : Fin (2 ^ step) → Block) :
    (Programs.garbleStepM lane chunk step zeroLabel parent).eval (tableAnswer A) =
      garbleStep (tableOracle A) lane chunk step zeroLabel parent := by
  funext entry
  by_cases zero : step = 0
  · rw [Programs.garbleStepM, if_pos zero]
    simp only [garbleStep, if_pos zero, FreeQuery.eval_pure]
  · rw [Programs.garbleStepM, if_neg zero]
    simp only [garbleStep, if_neg zero, FreeQuery.eval_bind, FreeQuery.eval_pure,
      FreeQuery.eval_vector, Vector.get_ofFn, foldMaskM_table]

theorem garbleFoldM_table (delta : Block) (zeroLabel : Nat → Block) (steps : Nat) :
    (Programs.garbleFoldM lane chunk delta zeroLabel steps).eval (tableAnswer A) =
      garbleFold (tableOracle A) lane chunk delta zeroLabel steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [Programs.garbleFoldM, garbleFold, FreeQuery.eval_bind, FreeQuery.eval_pure, ih,
        garbleStepM_table]

theorem garbleChunkM_table (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block) :
    (Programs.garbleChunkM lane delta bitKey chunk).eval (tableAnswer A) =
      garbleChunk (tableOracle A) lane delta bitKey chunk := by
  simp only [Programs.garbleChunkM, FreeQuery.eval_bind, FreeQuery.eval_pure, garbleFoldM_table]
  rfl

/-- **A lane on a table is the lane on the table's oracles.** -/
theorem laneM_table (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block) :
    (Programs.laneM lane delta bitKey).eval (tableAnswer A) =
      Programs.laneTables (tableOracle A) (tableHash A) lane delta bitKey := by
  simp only [Programs.laneM, Programs.chunkTablesM, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_pi, FreeQuery.eval_vector, garbleChunkM_table, switchMaskM_table,
    Vector.get_ofFn, Programs.vector_get_ofFn]
  rfl

theorem evalStepM_table (step : Nat) (bitLabel join : Block) (active : Fin (2 ^ step))
    (parent : Fin (2 ^ step) → Block) :
    (Programs.evalStepM lane chunk step bitLabel join active parent).eval (tableAnswer A) =
      evalStep (tableOracle A) lane chunk step bitLabel join active parent := by
  funext entry
  simp only [Programs.evalStepM, evalStep, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_vector]
  by_cases same : entry = active
  · rw [if_pos same, if_pos same]
    congr 1
    apply Programs.xorFoldExcept_congr
    intro other different
    simp only [Vector.get_ofFn, if_neg different, foldMaskM_table]
  · simp only [if_neg same, Vector.get_ofFn, foldMaskM_table]

theorem evalFoldM_table (value : Nat) (bitLabel join : Nat → Block) (steps : Nat) :
    (Programs.evalFoldM lane chunk value bitLabel join steps).eval (tableAnswer A) =
      evalFold (tableOracle A) lane chunk value bitLabel join steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [Programs.evalFoldM, evalFold, FreeQuery.eval_bind, FreeQuery.eval_pure, ih,
        evalStepM_table]

end Eval

/-! ### 4. The shape of one chunk's transcripts -/

section Shape

variable (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) (lane : Lane)
  (chunk : Fin chunkCount)

theorem transcript_ite {α : Type} (p : Prop) [Decidable p] (a b : FreeQuery Programs.Spec α) :
    transcript ans (if p then a else b) = if p then transcript ans a else transcript ans b := by
  split <;> rfl

theorem transcript_garbleFoldM_succ (delta : Block) (zeroLabel : Nat → Block) (steps : Nat) :
    transcript ans (Programs.garbleFoldM lane chunk delta zeroLabel (steps + 1)) =
      transcript ans (Programs.garbleFoldM lane chunk delta zeroLabel steps) ++
        transcript ans (Programs.garbleStepM lane chunk steps (zeroLabel steps)
          ((Programs.garbleFoldM lane chunk delta zeroLabel steps).eval ans).1) := by
  show transcript ans (Programs.garbleFoldM lane chunk delta zeroLabel steps >>= _) = _
  rw [transcript_bind', transcript_bind', transcript_pure', List.append_nil]

theorem transcript_evalFoldM_succ (value : Nat) (bitLabel join : Nat → Block) (steps : Nat) :
    transcript ans (Programs.evalFoldM lane chunk value bitLabel join (steps + 1)) =
      transcript ans (Programs.evalFoldM lane chunk value bitLabel join steps) ++
        transcript ans (Programs.evalStepM lane chunk steps (bitLabel steps) (join steps)
          (activeAt value steps)
          ((Programs.evalFoldM lane chunk value bitLabel join steps).eval ans)) := by
  show transcript ans (Programs.evalFoldM lane chunk value bitLabel join steps >>= _) = _
  rw [transcript_bind', transcript_bind', transcript_pure', List.append_nil]

/-- The garbler's fold step asks the gates of every parent. -/
theorem transcript_garbleStepM (steps : Nat) (paid : steps ≠ 0) (zeroLabel : Block)
    (parent : Fin (2 ^ steps) → Block) :
    transcript ans (Programs.garbleStepM lane chunk steps zeroLabel parent) =
      (List.ofFn fun r : Fin (2 ^ steps) =>
        transcript ans (Programs.foldMaskM lane chunk steps r.val (parent r))).flatten := by
  unfold Programs.garbleStepM
  rw [if_neg paid, transcript_bind', transcript_vector', transcript_pure', List.append_nil]

/-- The evaluator's fold step asks the gates of every parent off the active one. -/
theorem transcript_evalStepM (steps : Nat) (bitLabel join : Block) (active : Fin (2 ^ steps))
    (parent : Fin (2 ^ steps) → Block) :
    transcript ans (Programs.evalStepM lane chunk steps bitLabel join active parent) =
      (List.ofFn fun r : Fin (2 ^ steps) => if r = active then [] else
        transcript ans (Programs.foldMaskM lane chunk steps r.val (parent r))).flatten := by
  unfold Programs.evalStepM
  rw [transcript_bind', transcript_vector']
  simp only [transcript_pure', List.append_nil, transcript_ite]

theorem hashM_only {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop} (index : FixedIndex)
    (label : Block) (holds : S (.fixedForward index label)) :
    Hidden.QueryOnly S (Programs.hashM index label) :=
  Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ holds) fun _ => Hidden.QueryOnly.pure' _

/-- A transcript all of whose questions a filter decides alike is kept whole or dropped. -/
theorem filter_transcript_const {α : Type}
    {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}
    {P : FreeQuery Programs.Spec α} (only : Hidden.QueryOnly S P)
    (keep : Entry FixedIndex EncPRF.PermutationIndex → Bool) (b : Bool)
    (value : ∀ e : Entry FixedIndex EncPRF.PermutationIndex, S e.1 → keep e = b) :
    (transcript ans P).filter keep = if b = true then transcript ans P else [] := by
  have mem : ∀ e ∈ transcript ans P, keep e = b := fun e member =>
    value e (only.mem ans e (by rw [← transcript_eq_transcriptOf]; exact member))
  cases b
  · rw [if_neg Bool.false_ne_true]
    exact List.filter_eq_nil_iff.mpr fun e member => by simp [mem e member]
  · rw [if_pos rfl]
    exact List.filter_eq_self.mpr fun e member => mem e member

/-- **The garbler's fold, filtered to the non-active parents, is the evaluator's fold**, at every
step: when the filter keeps exactly the non-active parents' gates and the level labels agree off
the active parent. -/
theorem fold_filter (keep : Entry FixedIndex EncPRF.PermutationIndex → Bool) (delta : Block)
    (zeroLabel : Nat → Block) (value : Nat) (bitLabel join : Nat → Block) (width : Nat)
    (keepHot : ∀ n < width, ∀ (r : Fin (2 ^ n)) (half : Bool) (x : Block)
      (y : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex)
        (hotIndexNat lane chunk n r.val half) x).Answer),
      keep ⟨.fixedForward (hotIndexNat lane chunk n r.val half) x, y⟩ =
        decide (r ≠ activeAt value n))
    (level : ∀ n < width, ∀ r : Fin (2 ^ n), r ≠ activeAt value n →
      (Programs.evalFoldM lane chunk value bitLabel join n).eval ans r =
        ((Programs.garbleFoldM lane chunk delta zeroLabel n).eval ans).1 r) :
    ∀ n, n ≤ width →
      (transcript ans (Programs.garbleFoldM lane chunk delta zeroLabel n)).filter keep =
        transcript ans (Programs.evalFoldM lane chunk value bitLabel join n)
  | 0, _ => rfl
  | n + 1, bound => by
      rw [transcript_garbleFoldM_succ, transcript_evalFoldM_succ, List.filter_append,
        fold_filter keep delta zeroLabel value bitLabel join width keepHot level n (by omega)]
      congr 1
      rw [transcript_evalStepM]
      by_cases zero : n = 0
      · subst zero
        unfold Programs.garbleStepM
        rw [if_pos rfl, transcript_pure', List.filter_nil, List.ofFn_succ, List.ofFn_zero,
          if_pos (Fin.ext (by simp [activeAt]))]
        rfl
      · rw [transcript_garbleStepM ans lane chunk n zero, filter_flatten_ofFn]
        refine flatten_ofFn_congr fun r => ?_
        have only : Hidden.QueryOnly (fun q => ∃ half x,
            q = .fixedForward (hotIndexNat lane chunk n r.val half) x)
            (Programs.foldMaskM lane chunk n r.val
              (((Programs.garbleFoldM lane chunk delta zeroLabel n).eval ans).1 r)) :=
          Hidden.QueryOnly.bind (hashM_only _ _ ⟨false, _, rfl⟩) fun _ =>
            Hidden.QueryOnly.bind (hashM_only _ _ ⟨true, _, rfl⟩) fun _ =>
              Hidden.QueryOnly.pure' _
        rw [filter_transcript_const ans only keep (decide (r ≠ activeAt value n)) (by
          rintro ⟨q, y⟩ ⟨half, x, rfl⟩
          exact keepHot n (by omega) r half x y)]
        by_cases active : r = activeAt value n
        · rw [if_pos active]
          simp [active]
        · rw [if_neg active, if_pos (decide_eq_true active), level n (by omega) r active]

end Shape

/-! ### 5. One chunk, one curve lane: the designed entries are the evaluator's questions -/

section Chunk

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (tape : Coins × Oracle)
  (input : AffineInput)

theorem keep_hot (lane : Lane) (curve : laneIsCurve lane = true) (chunk : Fin chunkCount)
    (n r : Nat) (small : n < chunkBits) (entry : r < 2 ^ chunkBits) (half : Bool) (x : Block)
    (y : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex)
      (hotIndexNat lane chunk n r half) x).Answer) :
    designedKeep scalar tape input ⟨.fixedForward (hotIndexNat lane chunk n r half) x, y⟩ =
      decide (r ≠ (chunkOf (inputBits input lane.coord) chunk).val % 2 ^ n) := by
  have shown : designedRule scalar tape input
      ⟨.fixedForward (hotIndexNat lane chunk n r half) x, y⟩ =
      designedIndex scalar tape input (.hot lane chunk ⟨n, small⟩ ⟨r, entry⟩ half) := by
    show designedIndex scalar tape input (hotIndexNat lane chunk n r half) = _
    rw [hotIndexNat_eq lane chunk n r half small entry]
  simp only [designedKeep, Entry.IsEnc, Bool.not_false, Bool.true_and, shown, designedIndex,
    curve, Bool.true_or, Bool.and_true]

theorem keep_scale (lane : Lane) (curve : laneIsCurve lane = true) (chunk : Fin chunkCount)
    (switch : Fin (2 ^ chunkWidth chunk)) (limb : Fin (limbCount lane)) (label : Block)
    (y : (PublicQuery.hash (FixedIndex := FixedIndex) (EncIndex := EncPRF.PermutationIndex)
      (scaleInput lane chunk switch.val limb.val label)).Answer) :
    designedKeep scalar tape input ⟨.hash (scaleInput lane chunk switch.val limb.val label), y⟩ =
      decide (switch ≠ chunkOf (inputBits input lane.coord) chunk) := by
  have shown : designedRule scalar tape input
      ⟨.hash (scaleInput lane chunk switch.val limb.val label), y⟩ =
      designedSite input ⟨lane, chunk, switch⟩ :=
    designedHash_labelInput input ⟨⟨lane, chunk, switch⟩, limb⟩ label
  simp only [designedKeep, Entry.IsEnc, Bool.not_false, Bool.true_and, shown, designedSite,
    curve, Bool.true_or, Bool.and_true]

theorem transcript_chunkTablesM (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex,
    q.Answer) (lane : Lane) (chunk : Fin chunkCount) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) :
    transcript ans (Programs.chunkTablesM lane delta bitKey chunk) =
      transcript ans (Programs.garbleFoldM lane chunk delta
        (labelAt fun position => (chunkKey bitKey chunk position).1) (chunkWidth chunk)) ++
      (List.ofFn fun switch : Fin (2 ^ chunkWidth chunk) =>
        transcript ans (Programs.switchMaskM lane chunk switch.val
          (((Programs.garbleChunkM lane delta bitKey chunk).eval ans).1 switch))).flatten := by
  unfold Programs.chunkTablesM Programs.garbleChunkM
  rw [transcript_bind', transcript_bind', transcript_pure', List.append_nil, transcript_bind',
    transcript_vector', transcript_pure', List.append_nil]

theorem transcript_evalChunkM (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex,
    q.Answer) (lane : Lane) (chunk : Fin chunkCount) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    transcript ans (Programs.evalChunkM lane joins scale bits labels chunk) =
      transcript ans (Programs.evalFoldM lane chunk (chunkValue bits chunk).toNat
        (labelAt (chunkLabels labels chunk)) (joinAt (hotSlice joins chunk))
        (chunkWidth chunk)) ++
      (List.ofFn fun switch : Fin (2 ^ chunkWidth chunk) => if switch = chunkOf bits chunk then []
        else transcript ans (Programs.switchMaskM lane chunk switch.val
          (((Programs.evalFoldM lane chunk (chunkValue bits chunk).toNat
            (labelAt (chunkLabels labels chunk)) (joinAt (hotSlice joins chunk))
            (chunkWidth chunk)).eval ans) switch))).flatten := by
  unfold Programs.evalChunkM Programs.evalMasksM
  rw [transcript_bind', transcript_bind', transcript_bind', transcript_vector']
  simp only [transcript_pure', List.append_nil, transcript_ite]

/-- **One chunk of a curve lane, on a table**: the designed part of the garbler's questions is
the evaluator's questions, run on the lane's published fold joins and the selected labels. -/
theorem chunk_designed (A : Table) (lane : Lane) (curve : laneIsCurve lane = true) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (bitsEq : inputBits input lane.coord = bits) (chunk : Fin chunkCount) :
    (transcript (tableAnswer A) (Programs.chunkTablesM lane delta bitKey chunk)).filter
        (designedKeep scalar tape input) =
      transcript (tableAnswer A) (Programs.evalChunkM lane
        (hotJoins (tableOracle A) lane delta bitKey) scale bits (selectBits bitKey bits)
        chunk) := by
  have value : (chunkValue bits chunk).toNat = (chunkOf bits chunk).val := chunkValue_toNat _ _
  rw [transcript_chunkTablesM, transcript_evalChunkM, List.filter_append, filter_flatten_ofFn]
  congr 1
  · refine fold_filter (tableAnswer A) lane chunk _ delta _ _ _ _ (chunkWidth chunk) ?_ ?_
      (chunkWidth chunk) le_rfl
    · intro n small r half x y
      have nSmall : n < chunkBits := lt_of_lt_of_le small (chunkWidth_le chunk)
      rw [keep_hot scalar tape input lane curve chunk n r.val nSmall
        (lt_of_lt_of_le r.isLt (Nat.pow_le_pow_right (by norm_num) nSmall.le)) half x y, bitsEq]
      congr 1
      simp only [ne_eq, eq_iff_iff]
      rw [Fin.ext_iff]
      show ¬ r.val = (chunkOf bits chunk).val % 2 ^ n ↔
        ¬ r.val = (chunkValue bits chunk).toNat % 2 ^ n
      rw [value]
    · intro n small r off
      rw [evalFoldM_table, garbleFoldM_table]
      refine evalFold_off (tableOracle A) lane delta bitKey correlated bits chunk n small.le r ?_
      intro same
      apply off
      refine Fin.ext ?_
      show r.val = (chunkValue bits chunk).toNat % 2 ^ n
      rw [value]
      exact same
  · refine flatten_ofFn_congr fun switch => ?_
    rw [filter_transcript_const (tableAnswer A) (Hidden.switchMaskM_only lane chunk switch.val _) _
      (decide (switch ≠ chunkOf bits chunk)) (by
        rintro ⟨q, y⟩ ⟨limb, rfl⟩
        rw [keep_scale scalar tape input lane curve chunk switch limb _ y, bitsEq])]
    by_cases active : switch = chunkOf bits chunk
    · rw [if_pos active]
      simp [active]
    · rw [if_neg active, if_pos (decide_eq_true active)]
      congr 2
      rw [garbleChunkM_table, evalFoldM_table]
      show _ = evalHot (tableOracle A) lane chunk (chunkWidth chunk)
        (hotSlice (hotJoins (tableOracle A) lane delta bitKey) chunk)
        (chunkLabels (selectBits bitKey bits) chunk) (chunkValue bits chunk) switch
      have slices := hotSlice_hotJoins (tableOracle A) lane delta bitKey chunk
      have labels := chunkLabels_selectBits bitKey bits chunk
      have agrees := evalHot_agrees_off_active (oracle := tableOracle A) (lane := lane) correlated
        bits chunk switch active
      exact agrees.symm.trans (congrArg₂ (fun joins held => evalHot (tableOracle A) lane chunk
        (chunkWidth chunk) joins held (chunkValue bits chunk) switch) slices.symm labels.symm)

/-- **One curve lane, on a table**: its designed questions are the evaluator's. -/
theorem lane_designed (A : Table) (lane : Lane) (curve : laneIsCurve lane = true) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (bitsEq : inputBits input lane.coord = bits) :
    (transcript (tableAnswer A) (Programs.laneM lane delta bitKey)).filter
        (designedKeep scalar tape input) =
      transcript (tableAnswer A) (Programs.evalLaneM lane
        (hotJoins (tableOracle A) lane delta bitKey) scale bits (selectBits bitKey bits)) := by
  unfold Programs.laneM Programs.evalLaneM
  rw [transcript_bind', transcript_bind', transcript_pi', transcript_vector', transcript_pure',
    transcript_pure', List.append_nil, List.append_nil, filter_flatten_ofFn]
  exact flatten_ofFn_congr fun chunk => chunk_designed scalar tape input A lane curve delta bitKey
    correlated scale bits bitsEq chunk

/-- **Off the curve the designed entries are the curve lanes'**, on any answers. -/
theorem garbler_designed_lanes
    (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (coins : Coins) (invalid : validate input = false) :
    (transcript ans (Programs.garbleM scalar coins)).filter (designedKeep scalar tape input) =
      (transcript ans (Programs.laneM .curveX (coins.inputDelta .x)
          (Pipeline.bitKeyOf coins.inputMacKey .x))).filter (designedKeep scalar tape input) ++
      (transcript ans (Programs.laneM .curveY (coins.inputDelta .y)
          (Pipeline.bitKeyOf coins.inputMacKey .y))).filter (designedKeep scalar tape input) := by
  rw [transcript_eq_transcriptOf, transcript_eq_transcriptOf, transcript_eq_transcriptOf]
  unfold Programs.garbleM
  simp only [Hidden.transcriptOf_bind, List.filter_append]
  have hashNil : (Hidden.transcriptOf ans (Programs.askHash (bridgeInput coins.bridgeKey))).filter
      (designedKeep scalar tape input) = [] := by
    show [(⟨.hash (bridgeInput coins.bridgeKey), ans (.hash (bridgeInput coins.bridgeKey))⟩ :
      Entry FixedIndex EncPRF.PermutationIndex)].filter _ = []
    have hidden : designedHash input (bridgeInput coins.bridgeKey) = false := by
      rw [designedHash_bridgeInput, invalid]
    simp [designedKeep, designedRule, hidden, Entry.IsEnc]
  have padsNil : ∀ keys, (Hidden.transcriptOf ans (Programs.padsM keys)).filter
      (designedKeep scalar tape input) = [] := fun keys =>
    filter_nil_of_only (Hidden.padsM_encOnly keys) _ _ (keep_enc scalar tape input)
  have pointNil : ∀ ℓ delta bitKey, laneIsCurve ℓ = false →
      (Hidden.transcriptOf ans (Programs.laneM ℓ delta bitKey)).filter
        (designedKeep scalar tape input) = [] := fun ℓ delta bitKey point =>
    filter_nil_of_only (laneM_laneOnly ℓ delta bitKey) _ _
      (keep_point scalar tape input invalid ℓ point)
  have gadgetNil : ∀ keys inputKey pads,
      (Hidden.transcriptOf ans (Programs.gadgetM keys inputKey pads)).filter
        (designedKeep scalar tape input) = [] := fun keys inputKey pads =>
    filter_nil_of_only (gadgetM_gadgetOnly keys inputKey pads) _ _
      (keep_gadget scalar tape input invalid)
  have pureNil : ∀ {β : Type} (value : β), (Hidden.transcriptOf ans
      (Pure.pure value : FreeQuery Programs.Spec β)).filter (designedKeep scalar tape input) = [] :=
    fun _ => rfl
  rw [hashNil, padsNil, pointNil .pointX _ _ rfl, pointNil .pointY _ _ rfl, gadgetNil, pureNil]
  simp only [List.nil_append, List.append_nil]

end Chunk

/-! ### 6. The EncPRF entries -/

section Enc

variable [FieldCertificate] [GroupCertificate]
  (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)

/-- The EncPRF part of a hash-then-pads-then-plain program is the pads' transcript, on any
answers. -/
theorem enc_split' {β : Type} (t : BaseField)
    (R : Block × Block → Programs.Pads → FreeQuery Programs.Spec β)
    (only : ∀ h p, Hidden.QueryOnly Hidden.IsPlain (R h p)) :
    (transcript ans (Programs.askHash t >>= fun h =>
        Programs.padsM ⟨h.1, h.2⟩ >>= fun p => R h p)).filter Entry.IsEnc =
      transcript ans (Programs.padsM ⟨((Programs.askHash t).eval ans).1,
        ((Programs.askHash t).eval ans).2⟩) := by
  rw [transcript_eq_transcriptOf, transcript_eq_transcriptOf, Hidden.transcriptOf_bind,
    Hidden.transcriptOf_bind]
  have hashHead : Hidden.transcriptOf ans (Programs.askHash t) = [⟨.hash t, ans (.hash t)⟩] := rfl
  rw [hashHead, List.filter_append, List.filter_append,
    filter_none _ [_] (fun a member => by rcases List.mem_singleton.mp member with rfl; rfl),
    filter_all _ _ fun a member => isEnc_of_encForward a ((Hidden.padsM_encOnly _).mem _ a member),
    filter_none _ _ fun a member => isEnc_of_plain a ((only _ _).mem _ a member),
    List.nil_append, List.append_nil]

theorem transcript_padM (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    transcript ans (Programs.padM keys coordinate index bit) =
      transcript ans (Programs.askEnc (coordinate, index) (encodeBit bit ^^^ keys.first)) := by
  unfold Programs.padM
  rw [transcript_bind', transcript_pure', List.append_nil]

/-- **The pads' questions read only the first whitening key.** -/
theorem padsM_first (keys : WhiteningKeys) :
    transcript ans (Programs.padsM keys) = transcript ans (Programs.padsM ⟨keys.first, 0⟩) := by
  unfold Programs.padsM
  simp only [transcript_bind', transcript_vector', transcript_pure', List.append_nil,
    transcript_padM]

/-- The pads of a table, at the table's hash value of the bridge input. -/
def tablePads (A : Table) (coins : Coins) : Programs.Pads :=
  (Programs.padsM ⟨(tableHash A (bridgeInput coins.bridgeKey)).1,
    (tableHash A (bridgeInput coins.bridgeKey)).2⟩).eval (tableAnswer A)

/-- **The garbler's EncPRF entries are the pads' transcript at `k₁`.** -/
theorem garbler_enc (scalar : NonZeroScalar) (coins : Coins) :
    (transcript ans (Programs.garbleM scalar coins)).filter Entry.IsEnc =
      transcript ans (Programs.padsM
        ⟨((Programs.askHash (bridgeInput coins.bridgeKey)).eval ans).1, 0⟩) := by
  unfold Programs.garbleM
  refine (enc_split' ans (bridgeInput coins.bridgeKey) _ fun _ _ => ?_).trans (padsM_first ans _)
  exact Hidden.QueryOnly.bind (Hidden.laneM_plainOnly _ _ _) fun _ =>
    Hidden.QueryOnly.bind (Hidden.laneM_plainOnly _ _ _) fun _ =>
      Hidden.QueryOnly.bind (Hidden.laneM_plainOnly _ _ _) fun _ =>
        Hidden.QueryOnly.bind (Hidden.laneM_plainOnly _ _ _) fun _ =>
          Hidden.QueryOnly.bind (Hidden.gadgetM_plainOnly _ _ _) fun _ => Hidden.QueryOnly.pure' _

/-- **The garbler on a table**: the assembly of the lanes on the table's oracles, the table's
pads and the gadget on the table. -/
theorem garbleM_table (scalar : NonZeroScalar) (A : Table) (coins : Coins) :
    (Programs.garbleM scalar coins).eval (tableAnswer A) =
      (Programs.assemble (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
        coins.pointRandomness coins.bridgeKey coins.curveMask
        (Programs.laneTables (tableOracle A) (tableHash A) .curveX (coins.inputDelta .x)
          (Pipeline.bitKeyOf coins.inputMacKey .x))
        (Programs.laneTables (tableOracle A) (tableHash A) .curveY (coins.inputDelta .y)
          (Pipeline.bitKeyOf coins.inputMacKey .y))
        (Programs.laneTables (tableOracle A) (tableHash A) .pointX (coins.inputDelta .x)
          (Pipeline.bitKeyOf (Programs.whitenKeyOf (tablePads A coins) coins.inputMacKey) .x))
        (Programs.laneTables (tableOracle A) (tableHash A) .pointY (coins.inputDelta .y)
          (Pipeline.bitKeyOf (Programs.whitenKeyOf (tablePads A coins) coins.inputMacKey) .y))
        ((Programs.gadgetM (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
          (Programs.transformKeyOf (tablePads A coins) coins.inputMacKey) coins.exceptionPad).eval
            (tableAnswer A)),
       coins.inputMacKey) := by
  have cx := laneM_table A .curveX (coins.inputDelta .x) (Pipeline.bitKeyOf coins.inputMacKey .x)
  have cy := laneM_table A .curveY (coins.inputDelta .y) (Pipeline.bitKeyOf coins.inputMacKey .y)
  have px := laneM_table A .pointX (coins.inputDelta .x)
    (Pipeline.bitKeyOf (Programs.whitenKeyOf (tablePads A coins) coins.inputMacKey) .x)
  have py := laneM_table A .pointY (coins.inputDelta .y)
    (Pipeline.bitKeyOf (Programs.whitenKeyOf (tablePads A coins) coins.inputMacKey) .y)
  unfold tablePads at px py ⊢
  have hashEq : (Programs.askHash (bridgeInput coins.bridgeKey)).eval (tableAnswer A) =
      tableHash A (bridgeInput coins.bridgeKey) :=
    eval_askHash_ans (tableAnswer A) (bridgeInput coins.bridgeKey)
  simp only [Programs.garbleM, FreeQuery.eval_bind, FreeQuery.eval_pure]
  rw [hashEq, cx, cy, px, py]

end Enc

/-! ### 7. The garbler's planted entries on a table, off the curve -/

section Designed

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (tape : Coins × Oracle)
  (input : AffineInput)

/-- The coins' label pairs are free-XOR correlated. -/
theorem correlated_coins (coins : Coins) (coord : Coord) :
    ∀ position, (Pipeline.bitKeyOf coins.inputMacKey coord position).2 =
      (Pipeline.bitKeyOf coins.inputMacKey coord position).1 ^^^ coins.inputDelta coord := by
  intro position
  cases coord <;>
    simp [Pipeline.bitKeyOf, Kriterion.ArgoMAC.Scheme.Coins.inputMacKey, Vector.get_ofFn]

/-- **Off the curve, on a table, the designed entries are system A's questions** on the published
value and the selected labels. -/
theorem garbler_designed (A : Table) (coins : Coins) (invalid : validate input = false) :
    (transcript (tableAnswer A) (Programs.garbleM scalar coins)).filter
        (designedKeep scalar tape input) =
      transcript (tableAnswer A) (systemAM ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
        (BitInput.ofAffine input) (coins.inputMacKey.encode (BitInput.ofAffine input))) := by
  rw [garbler_designed_lanes scalar tape input _ coins invalid, garbleM_table]
  unfold systemAM
  rw [transcript_bind', transcript_bind', transcript_pure', List.append_nil,
    Pipeline.macLabels_encode, Pipeline.macLabels_encode]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · exact lane_designed scalar tape input A .curveX rfl (coins.inputDelta .x)
      (Pipeline.bitKeyOf coins.inputMacKey .x) (correlated_coins coins .x) _ _ rfl
  · exact lane_designed scalar tape input A .curveY rfl (coins.inputDelta .y)
      (Pipeline.bitKeyOf coins.inputMacKey .y) (correlated_coins coins .y) _ _ rfl

end Designed

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
