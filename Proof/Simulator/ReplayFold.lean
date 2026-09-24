/-
**The replay, one chunk's fold** (`Replay.foldStep` against the evaluator's `evalStepM`, then
`extendLevel`; design A1 §4 item 1).

The level labels `E_0 .. E_{2^j − 1}` of fold level `j` sit in the cells `hotLabel 0 ..`
(`LevelCells`). Fold step `j ≥ 1`:

* `det_foldPre`: the active entry `a = α mod 2^j` to `tmpActive`, the step-material cells cleared;
* `agree_foldEntries`: every inactive entry asks its two fixed-key halves (`foldPair`, the
  evaluator's `foldMaskM`) and stores the material; the active entry asks nothing and its cell
  stays `0`;
* `det_foldPost`: the active material `J ⊕ L ⊕ (⊕_e M_e)` (`xorFoldExcept`), then the next level
  `E_r ← E_r ⊕ M_r`, `E_{r + 2^j} ← M_r` (`extendLevel`).

`agree_fold`: the `w − 1` fold steps from level `1` (the bit-`0` label twice, `evalFoldM_one`)
against `evalFoldM … w`.
-/

import Proof.Simulator.ReplaySwitch

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Scratch addresses -/

theorem hot_ne {first second : Nat} (firstSmall : first < 49) (secondSmall : second < 49)
    (different : first ≠ second) : word (hotLabelBase + first) ≠ word (hotLabelBase + second) :=
  word_ne (by unfold hotLabelBase; omega) (by unfold hotLabelBase; omega) (by omega)

theorem hot_ne_tmp (first second : Nat) (firstSmall : first < 49) (secondSmall : second < 16) :
    word (hotLabelBase + first) ≠ word (tmpBase + second) :=
  word_ne (by unfold hotLabelBase; omega) (by unfold tmpBase; omega)
    (by unfold hotLabelBase tmpBase; omega)

theorem tmp_ne {first second : Nat} (firstSmall : first < 16) (secondSmall : second < 16)
    (different : first ≠ second) : word (tmpBase + first) ≠ word (tmpBase + second) :=
  word_ne (by unfold tmpBase; omega) (by unfold tmpBase; omega) (by omega)

omit [FieldCertificate] in
theorem stepMask_eq (entry : Nat) : stepMask entry = hotLabelBase + (32 + entry) := by
  unfold stepMask stepMaskBase
  omega

/-- The one-hot labels of a fold level sit in the level cells. -/
def LevelCells {steps : Nat} (level : Fin (2 ^ steps) → Block) (memory : Memory) : Prop :=
  ∀ e : Fin (2 ^ steps), memory.ram (word (hotLabel e.val)) = blockWord (level e)

/-- The cells a fold step may write: the active entry and the level and step-material cells. -/
def FoldFrame (address : Word) : Prop :=
  address ≠ word tmpActive ∧ ∀ index, index < 48 → address ≠ word (hotLabelBase + index)

omit [FieldCertificate] in
theorem hotIdx_eq (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat) (half : Bool) :
    Replay.hotIdx lane chunk.val step entry half = hotIndexNat lane chunk step entry half := by
  unfold Replay.hotIdx
  rw [show Replay.chunkFin chunk.val = chunk from Fin.ext (Nat.mod_eq_of_lt chunk.isLt)]

/-! ### The fold step, split -/

/-- The step's bookkeeping before the questions. -/
def foldPre (step : Nat) : List Prog :=
  [loadAt rA tmpAlpha, cst rB (2 ^ step - 1), ar .and rA rA rB, storeAt tmpActive rA, cst rA 0,
    Prog.rep (2 ^ step) fun entry => storeAt (stepMask entry) rA]

/-- The step's bookkeeping after the questions. -/
def foldPost (spec : Replay.LaneSpec) (chunk step : Nat) : List Prog :=
  [loadAt rC (Replay.hotJoin spec chunk step), loadAt rD (Replay.bitLabel spec chunk step),
    ar .xor rC rC rD, Prog.rep (2 ^ step) Replay.absorbEntry, loadAt rA tmpActive,
    cst rB stepMaskBase, ar .add rA rA rB, .op (.store rA rC),
    Prog.rep (2 ^ step) fun entry => Replay.extendEntry step entry]

omit [FieldCertificate] in
theorem foldStep_split (spec : Replay.LaneSpec) (chunk step : Nat) :
    Replay.foldStep ordF0 spec chunk step = Prog.seqList (foldPre step ++
      (Prog.rep (2 ^ step) (fun entry => Replay.foldEntry ordF0 spec chunk step entry) ::
        foldPost spec chunk step)) := rfl

omit [FieldCertificate] in
theorem plain_foldPre (step : Nat) : BigInt.IsPlain (Prog.seqList (foldPre step)) := by
  unfold foldPre loadAt storeAt cst ar
  plain_split

omit [FieldCertificate] in
theorem plain_foldPost (spec : Replay.LaneSpec) (chunk step : Nat) :
    BigInt.IsPlain (Prog.seqList (foldPost spec chunk step)) := by
  unfold foldPost Replay.absorbEntry Replay.extendEntry loadAt storeAt cst ar
  plain_split

/-! ### Before the questions -/

omit [FieldCertificate] in
theorem and_mask_word (value step : Nat) (valueSmall : value < 32) (stepSmall : step < 5) :
    Arithmetic.and.eval (word value) (word (2 ^ step - 1)) = word (value % 2 ^ step) := by
  apply BitVec.eq_of_toNat_eq
  have powSmall : 2 ^ step ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [Arithmetic.eval, BitVec.toNat_and, word_small (show value < 2 ^ 256 by omega),
    word_small (show 2 ^ step - 1 < 2 ^ 256 by omega)]
  rw [Nat.and_two_pow_sub_one_eq_mod, word_small (lt_of_le_of_lt (Nat.mod_le _ _) (by omega))]

omit [FieldCertificate] in
/-- **Before the questions**: the active entry, and the step-material cells cleared. -/
theorem det_foldPre (step : Nat) (stepSmall : step < 5) (value : Nat) (valueSmall : value < 32)
    (memory : Memory) (alphaCell : memory.ram (word tmpAlpha) = word value) :
    ∃ after, BigInt.det (Prog.seqList (foldPre step)) memory = some after ∧
      after.ram = BigInt.writeCells (Function.update memory.ram (word tmpActive)
        (word (value % 2 ^ step))) stepMaskBase (2 ^ step) (fun _ => 0) ∧
      after.bits = memory.bits := by
  have powSmall : 2 ^ step ≤ 16 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : step ≤ 4)) (by norm_num)
  have split : foldPre step = [loadAt rA tmpAlpha, cst rB (2 ^ step - 1), ar .and rA rA rB,
      storeAt tmpActive rA, cst rA 0] ++
      [Prog.rep (2 ^ step) fun entry => storeAt (stepMask entry) rA] := rfl
  obtain ⟨start, runStart, ramStart, zeroStart, bitsStart⟩ : ∃ start,
      BigInt.det (Prog.seqList [loadAt rA tmpAlpha, cst rB (2 ^ step - 1), ar .and rA rA rB,
        storeAt tmpActive rA, cst rA 0]) memory = some start ∧
      start.ram = Function.update memory.ram (word tmpActive)
        (Arithmetic.and.eval (memory.ram (word tmpAlpha)) (word (2 ^ step - 1))) ∧
      start.registers rA = word 0 ∧ start.bits = memory.bits :=
    ⟨_, rfl, by reg_eval, by reg_eval, by reg_eval⟩
  obtain ⟨cleared, runClear, holds⟩ := BigInt.det_rep_inv
    (fun done current => current.registers rA = word 0 ∧
      current.ram = BigInt.writeCells start.ram stepMaskBase done (fun _ => 0) ∧
      current.bits = start.bits)
    (fun entry => storeAt (stepMask entry) rA) (2 ^ step)
    (fun index bound current holds => by
      obtain ⟨zero, ram, bitsSame⟩ := holds
      refine ⟨_, rfl, by reg_eval; exact zero, ?_, by reg_eval; exact bitsSame⟩
      reg_eval
      rw [ram, zero, BigInt.writeCells_succ _ _ _ _ (by unfold stepMaskBase hotLabelBase; omega)]
      rfl)
    start ⟨zeroStart, by rw [BigInt.writeCells_zero], rfl⟩
  refine ⟨cleared, ?_, by rw [holds.2.1, ramStart, alphaCell, and_mask_word value step valueSmall
    stepSmall], by rw [holds.2.2, bitsStart]⟩
  rw [split, BigInt.det_seqList_append, runStart, Option.bind_some]
  show BigInt.det (Prog.seq _ (Prog.skip 0)) start = some cleared
  rw [BigInt.det_seq_some runClear]
  rfl

/-! ### The questions -/

/-- **The fold pair**: two hashes of the entry's label, their sum stored as the step material. -/
theorem agree_foldPair (spec : Replay.LaneSpec) (chunk : Fin chunkCount) (step entry : Nat)
    (memory : Memory) (label : Block)
    (labelCell : memory.ram (word (hotLabel entry)) = blockWord label) :
    Agree (fun (mask : Block) after =>
        after.ram = Function.update memory.ram (word (stepMask entry)) (blockWord mask) ∧
          after.bits = memory.bits)
      (rtree (Replay.foldPair ordF0 spec chunk.val step entry) memory)
      (Programs.foldMaskM spec.lane chunk step entry label) := by
  unfold Replay.foldPair Programs.foldMaskM
  simp only [Prog.seqList, hotIdx_eq, TreeLaws.monad_bind, TreeLaws.monad_pure]
  rw [rtree_loadAt_seq]
  have input0 : (setReg (setReg memory rAddr (word (hotLabel entry))) rInput
      (memory.ram (word (hotLabel entry)))).registers rInput = blockWord label := by
    rw [reg_same, labelCell]
  refine agree_hashStep _ rC _ _ label input0 _ fun first => ?_
  have input1 : (hashMem (setReg (setReg memory rAddr (word (hotLabel entry))) rInput
      (memory.ram (word (hotLabel entry)))) (ordF0 (hotIndexNat spec.lane chunk step entry false))
      rC first label).registers rInput = blockWord label := by
    rw [hashMem_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide), input0]
  refine agree_hashStep _ rFirst _ _ label input1 _ fun second => ?_
  rw [rtree_ar_seq, rtree_storeAt_seq _ _ _ _ (by decide), rtree_skip]
  refine .leaf ⟨?_, ?_⟩
  · rw [storeRam_ram, reg_same]
    simp only [setReg_ram, hashMem_ram]
    rw [hashMem_target, hashMem_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide),
      hashMem_target, eval_xor, blockWord_xor]
  · simp only [storeRam_bits, setReg_bits, hashMem_bits]

/-- The invariant of the question loop: the materials so far in their cells, the rest cleared,
every other cell unchanged. -/
def EntryInv (start : Memory) (step active : Nat) (count : Nat) (masks : Vector Block count)
    (memory : Memory) : Prop :=
  (∀ e : Fin count, memory.ram (word (stepMask e.val)) = blockWord masks[e]) ∧
    (∀ e : Fin count, e.val = active → masks[e] = 0) ∧
    (∀ e, count ≤ e → e < 2 ^ step → memory.ram (word (stepMask e)) = blockWord 0) ∧
    (∀ address, (∀ e, e < 2 ^ step → address ≠ word (stepMask e)) →
      memory.ram address = start.ram address) ∧
    memory.bits = start.bits

/-- The evaluator's question of one entry. -/
abbrev entryProg (lane : Lane) (chunk : Fin chunkCount) (step : Nat) (active : Fin (2 ^ step))
    (parent : Fin (2 ^ step) → Block) (entry : Fin (2 ^ step)) : Programs.M Block :=
  if entry = active then pure 0 else Programs.foldMaskM lane chunk step entry.val (parent entry)

/-- **The question loop of a fold step.** -/
theorem agree_foldEntries (spec : Replay.LaneSpec) (chunk : Fin chunkCount) (step : Nat)
    (stepSmall : step < 5) (active : Fin (2 ^ step)) (parent : Fin (2 ^ step) → Block)
    (start : Memory) (activeCell : start.ram (word tmpActive) = word active.val)
    (levels : LevelCells parent start)
    (cleared : ∀ e, e < 2 ^ step → start.ram (word (stepMask e)) = blockWord 0) :
    Agree (EntryInv start step active.val (2 ^ step))
      (rtree (Prog.rep (2 ^ step) fun entry => Replay.foldEntry ordF0 spec chunk.val step entry)
        start)
      (FreeQuery.vector (2 ^ step) (entryProg spec.lane chunk step active parent)) := by
  have powSmall : 2 ^ step ≤ 16 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : step ≤ 4)) (by norm_num)
  have activeSmall : active.val < 16 := lt_of_lt_of_le active.isLt powSmall
  have maskNe : ∀ e e', e < 16 → e' < 16 → e ≠ e' → word (stepMask e) ≠ word (stepMask e') :=
    fun e e' small small' different => by
      rw [stepMask_eq, stepMask_eq]
      exact hot_ne (by omega) (by omega) (by omega)
  refine agree_rep_vector' _ (EntryInv start step active.val) _ _
    (fun entry masks memory holds => ?_) start
    ⟨fun e => e.elim0, fun e => e.elim0, fun e _ bound => cleared e bound, fun _ _ => rfl, rfl⟩
  obtain ⟨done, zeros, rest, frame, bitsSame⟩ := holds
  have entrySmall : entry.val < 16 := lt_of_lt_of_le entry.isLt powSmall
  have activeNow : memory.ram (word tmpActive) = word active.val := by
    rw [frame _ fun e bound same => hot_ne_tmp (32 + e) 1 (by omega) (by omega)
      (by rw [stepMask_eq] at same; exact same.symm), activeCell]
  unfold Replay.foldEntry Replay.foldGate
  simp only [Prog.seqList]
  rw [rtree_loadAt_seq, activeNow, rtree_cst_seq,
    rtree_ar_val _ _ _ _ _ _ (word active.val) (word entry.val)
      (by rw [reg_ne _ _ _ _ (by decide), reg_same]) (reg_same _ _ _), eval_xor, rtree_seq,
    rtree_ite, reg_same]
  by_cases atActive : entry = active
  · subst atActive
    rw [if_pos (by rw [BitVec.xor_self]; rfl), rtree_skip]
    show Agree _ (bindOpt (.pure (some _)) _) (if entry = entry then pure 0 else _)
    rw [if_pos rfl, bindOpt_pure, rtree_skip]
    refine .leaf ⟨fun e => ?_, fun e hit => ?_, fun e small bound => ?_, fun address outside => ?_,
      ?_⟩
    · simp only [setReg_ram]
      by_cases last : e.val = entry.val
      · rw [show e = Fin.last entry.val from Fin.ext last]
        simp only [Fin.getElem_fin, Fin.val_last, Vector.getElem_push_eq]
        exact rest entry.val le_rfl entry.isLt
      · have below : e.val < entry.val := by have := e.isLt; omega
        simp only [Fin.getElem_fin, Vector.getElem_push_lt below]
        exact done ⟨e.val, below⟩
    · by_cases last : e.val = entry.val
      · rw [show e = Fin.last entry.val from Fin.ext last]
        simp only [Fin.getElem_fin, Fin.val_last, Vector.getElem_push_eq]
      · have below : e.val < entry.val := by have := e.isLt; omega
        simp only [Fin.getElem_fin, Vector.getElem_push_lt below]
        exact zeros ⟨e.val, below⟩ hit
    · simp only [setReg_ram]
      exact rest e (by omega) bound
    · simp only [setReg_ram]
      exact frame address outside
    · simp only [setReg_bits]
      exact bitsSame
  · have different : entry.val ≠ active.val := fun same => atActive (Fin.ext same)
    rw [if_neg fun zero =>
      different ((word_xor_eq_zero (by omega) (by omega)).mp zero).symm]
    unfold entryProg
    rw [if_neg atActive]
    have labelCell : (setReg (setReg (setReg (setReg memory rAddr (word tmpActive)) rA
        (word active.val)) rB (word entry.val)) rA (word active.val ^^^ word entry.val)).ram
          (word (hotLabel entry.val)) = blockWord (parent entry) := by
      simp only [setReg_ram]
      rw [frame _ fun e bound same => by
        rw [stepMask_eq] at same
        exact hot_ne (by omega) (by omega) (by omega) same, levels entry]
    show Agree _ (bindOpt (rtree (Replay.foldPair ordF0 spec chunk.val step entry.val)
      (setReg (setReg (setReg (setReg memory rAddr (word tmpActive)) rA
        (word active.val)) rB (word entry.val)) rA (word active.val ^^^ word entry.val)))
        (fun after => .pure (some after))) _
    rw [bindOpt_pure_right]
    refine (agree_foldPair spec chunk step entry.val _ (parent entry) labelCell).mono
      fun mask after post => ?_
    obtain ⟨ram, bitsAfter⟩ := post
    refine ⟨fun e => ?_, fun e hit => ?_, fun e small bound => ?_, fun address outside => ?_, ?_⟩
    · rw [ram]
      simp only [setReg_ram]
      by_cases last : e.val = entry.val
      · rw [show e = Fin.last entry.val from Fin.ext last, Fin.val_last, Function.update_self]
        simp only [Fin.getElem_fin, Fin.val_last, Vector.getElem_push_eq]
      · have below : e.val < entry.val := by have := e.isLt; omega
        rw [Function.update_of_ne (maskNe e.val entry.val (by omega) entrySmall (by omega))]
        simp only [Fin.getElem_fin, Vector.getElem_push_lt below]
        exact done ⟨e.val, below⟩
    · have below : e.val < entry.val := by
        have := e.isLt
        have : e.val ≠ entry.val := fun same => different (same ▸ hit)
        omega
      simp only [Fin.getElem_fin, Vector.getElem_push_lt below]
      exact zeros ⟨e.val, below⟩ hit
    · rw [ram]
      simp only [setReg_ram]
      rw [Function.update_of_ne (maskNe e entry.val (by omega) entrySmall (by omega))]
      exact rest e (by omega) bound
    · rw [ram]
      simp only [setReg_ram]
      rw [Function.update_of_ne (outside entry.val entry.isLt)]
      exact frame address outside
    · rw [bitsAfter]
      simp only [setReg_bits]
      exact bitsSame

/-! ### After the questions -/

/-- The XOR of the first `count` values of a family. -/
def xorUpTo (family : Nat → Block) : Nat → Block
  | 0 => 0
  | count + 1 => xorUpTo family count ^^^ family count

omit [FieldCertificate] in
theorem foldl_xor (family : Nat → Block) : ∀ (count : Nat) (start : Block),
    Fin.foldl count (fun acc (entry : Fin count) => acc ^^^ family entry.val) start =
      start ^^^ xorUpTo family count
  | 0, start => by simp [xorUpTo]
  | count + 1, start => by
      rw [Fin.foldl_succ_last]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [foldl_xor family count start, xorUpTo, BitVec.xor_assoc]

omit [FieldCertificate] in
/-- With the skipped entry at `0`, `xorFoldExcept` is the plain XOR. -/
theorem xorFoldExcept_eq {count : Nat} (skip : Fin count) (family : Fin count → Block)
    (zero : family skip = 0) :
    xorFoldExcept skip family =
      xorUpTo (fun e => if inside : e < count then family ⟨e, inside⟩ else 0) count := by
  unfold xorFoldExcept
  have same : (fun (acc : Block) (entry : Fin count) =>
      if entry = skip then acc else acc ^^^ family entry) = fun acc entry =>
        acc ^^^ (fun e => if inside : e < count then family ⟨e, inside⟩ else 0) entry.val := by
    funext acc entry
    simp only [dif_pos entry.isLt, Fin.eta]
    split
    · rename_i hit
      rw [hit, zero]
      exact BitVec.xor_zero.symm
    · rfl
  rw [same]
  exact (foldl_xor (fun e => if inside : e < count then family ⟨e, inside⟩ else 0) count 0).trans
    BitVec.zero_xor

/-- **After the questions**: the active material, then the next level. -/
theorem det_foldPost (spec : Replay.LaneSpec) (chunk : Nat) (step : Nat) (stepPos : 1 ≤ step)
    (stepSmall : step < 5) (active : Fin (2 ^ step)) (parent masks : Fin (2 ^ step) → Block)
    (join label : Block) (memory : Memory)
    (activeCell : memory.ram (word tmpActive) = word active.val)
    (maskCells : ∀ e : Fin (2 ^ step), memory.ram (word (stepMask e.val)) = blockWord (masks e))
    (activeZero : masks active = 0) (levels : LevelCells parent memory)
    (joinCell : memory.ram (word (Replay.hotJoin spec chunk step)) = blockWord join)
    (labelCell : memory.ram (word (Replay.bitLabel spec chunk step)) = blockWord label) :
    ∃ after, BigInt.det (Prog.seqList (foldPost spec chunk step)) memory = some after ∧
      LevelCells (extendLevel step parent fun entry => if entry = active then
        join ^^^ label ^^^ xorFoldExcept active masks else masks entry) after ∧
      (∀ address, FoldFrame address → after.ram address = memory.ram address) ∧
      after.bits = memory.bits := by
  have powSmall : 2 ^ step ≤ 16 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : step ≤ 4)) (by norm_num)
  have powDouble : 2 ^ (step + 1) = 2 ^ step + 2 ^ step := by rw [pow_succ]; omega
  have maskNe : ∀ e e', e < 16 → e' < 16 → e ≠ e' → word (stepMask e) ≠ word (stepMask e') :=
    fun e e' small small' different => by
      rw [stepMask_eq, stepMask_eq]
      exact hot_ne (by omega) (by omega) (by omega)
  have maskHot : ∀ e e', e < 16 → e' < 32 → word (stepMask e) ≠ word (hotLabel e') :=
    fun e e' small small' => by
      rw [stepMask_eq]
      exact hot_ne (by omega) (by omega) (by omega)
  have hotNe : ∀ e e', e < 32 → e' < 32 → e ≠ e' → word (hotLabel e) ≠ word (hotLabel e') :=
    fun e e' small small' different => hot_ne (by omega) (by omega) different
  set right : Fin (2 ^ step) → Block := fun entry => if entry = active then
    join ^^^ label ^^^ xorFoldExcept active masks else masks entry with rightDef
  set cell : Nat → Block := fun e => if inside : e < 2 ^ step then masks ⟨e, inside⟩ else 0
    with cellDef
  have split : foldPost spec chunk step = [loadAt rC (Replay.hotJoin spec chunk step),
      loadAt rD (Replay.bitLabel spec chunk step), ar .xor rC rC rD] ++
      (Prog.rep (2 ^ step) Replay.absorbEntry :: ([loadAt rA tmpActive, cst rB stepMaskBase,
        ar .add rA rA rB, .op (.store rA rC)] ++
      [Prog.rep (2 ^ step) fun entry => Replay.extendEntry step entry])) := rfl
  -- the join and the label
  obtain ⟨m1, run1, ram1, rC1, bits1⟩ : ∃ m1,
      BigInt.det (Prog.seqList [loadAt rC (Replay.hotJoin spec chunk step),
        loadAt rD (Replay.bitLabel spec chunk step), ar .xor rC rC rD]) memory = some m1 ∧
      m1.ram = memory.ram ∧ m1.registers rC = blockWord (join ^^^ label) ∧
      m1.bits = memory.bits := ⟨_, rfl, rfl, by
        reg_eval
        rw [joinCell, labelCell, eval_xor, blockWord_xor], rfl⟩
  -- the absorption
  obtain ⟨m2, run2, holds2⟩ := BigInt.det_rep_inv
    (fun done current => current.ram = memory.ram ∧ current.bits = memory.bits ∧
      current.registers rC = blockWord (join ^^^ label ^^^ xorUpTo cell done))
    Replay.absorbEntry (2 ^ step) (fun index bound current holds => by
      obtain ⟨ram, bitsSame, acc⟩ := holds
      refine ⟨_, rfl, by reg_eval; exact ram, by reg_eval; exact bitsSame, ?_⟩
      reg_eval
      rw [acc, ram, maskCells ⟨index, bound⟩, eval_xor, blockWord_xor, xorUpTo, BitVec.xor_assoc]
      simp only [cellDef, dif_pos bound])
    m1 ⟨ram1, bits1, by rw [rC1]; exact congrArg blockWord BitVec.xor_zero.symm⟩
  obtain ⟨ram2, bits2, rC2⟩ := holds2
  have folded : xorUpTo cell (2 ^ step) = xorFoldExcept active masks :=
    (xorFoldExcept_eq active masks activeZero).symm
  rw [folded] at rC2
  -- the active material
  obtain ⟨m3, run3, ram3, bits3⟩ : ∃ m3,
      BigInt.det (Prog.seqList [loadAt rA tmpActive, cst rB stepMaskBase, ar .add rA rA rB,
        .op (.store rA rC)]) m2 = some m3 ∧
      m3.ram = Function.update memory.ram (word (stepMask active.val))
        (blockWord (join ^^^ label ^^^ xorFoldExcept active masks)) ∧
      m3.bits = memory.bits := ⟨_, rfl, by
        reg_eval
        rw [ram2, activeCell, BigInt.eval_add_word, rC2, Nat.add_comm]
        rfl, by reg_eval; exact bits2⟩
  have rightCells : ∀ e : Fin (2 ^ step), m3.ram (word (stepMask e.val)) = blockWord (right e) := by
    intro e
    rw [ram3]
    simp only [rightDef]
    by_cases hit : e = active
    · subst hit
      rw [Function.update_self, if_pos rfl]
    · rw [Function.update_of_ne (maskNe e.val active.val (by omega) (by omega)
        (fun same => hit (Fin.ext same))), if_neg hit, maskCells e]
  -- the extension
  obtain ⟨m4, run4, holds4⟩ := BigInt.det_rep_inv
    (fun done current =>
      (∀ e (small : e < 2 ^ step), e < done →
        current.ram (word (hotLabel e)) = blockWord (parent ⟨e, small⟩ ^^^ right ⟨e, small⟩) ∧
        current.ram (word (hotLabel (e + 2 ^ step))) = blockWord (right ⟨e, small⟩)) ∧
      (∀ e (small : e < 2 ^ step), done ≤ e →
        current.ram (word (hotLabel e)) = blockWord (parent ⟨e, small⟩)) ∧
      (∀ address, (∀ e, e < 32 → address ≠ word (hotLabel e)) →
        current.ram address = m3.ram address) ∧
      current.bits = memory.bits)
    (fun entry => Replay.extendEntry step entry) (2 ^ step) (fun index bound current holds => by
      obtain ⟨doneCells, restCells, frame, bitsSame⟩ := holds
      have maskNow : current.ram (word (stepMask index)) = blockWord (right ⟨index, bound⟩) := by
        rw [frame _ fun e small => maskHot index e (by omega) small, rightCells ⟨index, bound⟩]
      have parentNow : current.ram (word (hotLabel index)) = blockWord (parent ⟨index, bound⟩) :=
        restCells index bound le_rfl
      have highLow : word (hotLabel index) ≠ word (hotLabel (index + 2 ^ step)) :=
        hotNe _ _ (by omega) (by omega) (by omega)
      refine ⟨_, rfl, ⟨fun e small below => ?_, fun e small above => ?_,
        fun address outside => ?_, ?_⟩⟩
      · reg_eval
        by_cases last : e = index
        · subst last
          refine ⟨?_, ?_⟩
          · rw [Function.update_self, Function.update_of_ne highLow, parentNow, maskNow, eval_xor,
              blockWord_xor]
          · rw [Function.update_of_ne highLow.symm, Function.update_self, maskNow]
        · have earlier : e < index := by omega
          obtain ⟨first, second⟩ := doneCells e small earlier
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (hotNe _ _ (by omega) (by omega) (by omega)),
              Function.update_of_ne (hotNe _ _ (by omega) (by omega) (by omega)), first]
          · rw [Function.update_of_ne (hotNe _ _ (by omega) (by omega) (by omega)),
              Function.update_of_ne (hotNe _ _ (by omega) (by omega) (by omega)), second]
      · reg_eval
        rw [Function.update_of_ne (hotNe _ _ (by omega) (by omega) (by omega)),
          Function.update_of_ne (hotNe _ _ (by omega) (by omega) (by omega))]
        exact restCells e small (by omega)
      · reg_eval
        rw [Function.update_of_ne (outside index (by omega)),
          Function.update_of_ne (outside (index + 2 ^ step) (by omega))]
        exact frame address outside
      · reg_eval
        exact bitsSame)
    m3 ⟨fun e small below => absurd below (Nat.not_lt_zero _), fun e small _ => by
        rw [ram3, Function.update_of_ne (maskHot active.val e (by omega) (by omega)).symm]
        exact levels ⟨e, small⟩,
      fun _ _ => rfl, bits3⟩
  obtain ⟨doneCells, _, frame4, bits4⟩ := holds4
  refine ⟨m4, ?_, fun e => ?_, fun address framed => ?_, bits4⟩
  · rw [split, BigInt.det_seqList_append, run1, Option.bind_some]
    show BigInt.det (Prog.seq _ (Prog.seqList (_ ++ _))) m1 = some m4
    rw [BigInt.det_seq_some run2, BigInt.det_seqList_append, run3, Option.bind_some]
    show BigInt.det (Prog.seq _ (Prog.skip 0)) m3 = some m4
    rw [BigInt.det_seq_some run4]
    rfl
  · unfold extendLevel
    by_cases below : e.val < 2 ^ step
    · rw [dif_pos below]
      exact (doneCells e.val below below).1
    · rw [dif_neg below]
      have inRange : e.val - 2 ^ step < 2 ^ step := by have := e.isLt; omega
      have high := (doneCells (e.val - 2 ^ step) inRange inRange).2
      rw [show e.val - 2 ^ step + 2 ^ step = e.val by omega] at high
      exact high
  · obtain ⟨notActive, notHot⟩ := framed
    rw [frame4 address fun e small => notHot e (by omega), ram3,
      Function.update_of_ne (fun same => notHot (32 + active.val) (by omega)
        (by rw [same, stepMask_eq]))]

/-! ### One fold step -/

/-- **One fold step** against `evalStepM`, then `extendLevel`. -/
theorem agree_foldStep (spec : Replay.LaneSpec) (chunk : Fin chunkCount) (step : Nat)
    (stepPos : 1 ≤ step) (stepSmall : step < 5) (value : Nat) (valueSmall : value < 32)
    (parent : Fin (2 ^ step) → Block) (join label : Block) (memory : Memory)
    (alphaCell : memory.ram (word tmpAlpha) = word value) (levels : LevelCells parent memory)
    (joinCell : memory.ram (word (Replay.hotJoin spec chunk.val step)) = blockWord join)
    (labelCell : memory.ram (word (Replay.bitLabel spec chunk.val step)) = blockWord label)
    (joinFrame : FoldFrame (word (Replay.hotJoin spec chunk.val step)))
    (labelFrame : FoldFrame (word (Replay.bitLabel spec chunk.val step))) :
    Agree (fun (level : Fin (2 ^ (step + 1)) → Block) after => LevelCells level after ∧
        (∀ address, FoldFrame address → after.ram address = memory.ram address) ∧
        after.bits = memory.bits)
      (rtree (Replay.foldStep ordF0 spec chunk.val step) memory)
      (FreeQuery.bind (Programs.evalStepM spec.lane chunk step label join (activeAt value step)
        parent) fun right => .pure (extendLevel step parent right)) := by
  have powSmall : 2 ^ step ≤ 16 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : step ≤ 4)) (by norm_num)
  obtain ⟨m1, run1, ram1, bits1⟩ := det_foldPre step stepSmall value valueSmall memory alphaCell
  have tmpActiveHot : ∀ e, e < 48 → word tmpActive ≠ word (hotLabelBase + e) :=
    fun e small => (hot_ne_tmp e 1 (by omega) (by omega)).symm
  have maskIn : ∀ e, e < 2 ^ step →
      stepMaskBase ≤ (word (stepMask e)).toNat ∧ (word (stepMask e)).toNat < stepMaskBase + 2 ^ step := by
    intro e bound
    rw [word_small (by unfold stepMask stepMaskBase hotLabelBase; omega)]
    unfold stepMask
    omega
  have ram1Off : ∀ address : Word, (∀ e, e < 2 ^ step → address ≠ word (stepMask e)) →
      address ≠ word tmpActive → m1.ram address = memory.ram address := by
    intro address notMask notActive
    rw [ram1, writeCells_off _ _ _ _ _ (by unfold stepMaskBase hotLabelBase; omega)
      fun e bound => by rw [← stepMask]; exact notMask e bound, Function.update_of_ne notActive]
  have activeCell : m1.ram (word tmpActive) = word (activeAt value step).val := by
    rw [ram1, writeCells_off _ _ _ _ _ (by unfold stepMaskBase hotLabelBase; omega)
      fun e bound same => by
        rw [← stepMask, stepMask_eq] at same
        exact hot_ne_tmp (32 + e) 1 (by omega) (by omega) same.symm, Function.update_self]
    rfl
  have levels1 : LevelCells parent m1 := fun e => by
    have small : e.val < 16 := lt_of_lt_of_le e.isLt powSmall
    rw [ram1Off (word (hotLabel e.val)) (fun e' bound same => by
        rw [stepMask_eq] at same
        exact hot_ne (by omega) (by omega) (by omega) same)
      (fun same => tmpActiveHot e.val (by omega) same.symm), levels e]
  have cleared : ∀ e, e < 2 ^ step → m1.ram (word (stepMask e)) = blockWord 0 := by
    intro e bound
    rw [ram1, show stepMask e = stepMaskBase + e from rfl,
      BigInt.writeCells_in _ _ _ _ _ bound (by unfold stepMaskBase hotLabelBase; omega)]
    rfl
  rw [foldStep_split, rtree_seqList_append, rtree_plain_some (plain_foldPre step) run1, bindOpt_pure]
  show Agree _ (bindOpt (rtree (Prog.rep (2 ^ step) _) m1) _) _
  unfold Programs.evalStepM
  simp only [TreeLaws.monad_bind, TreeLaws.monad_pure, TreeLaws.bind_assoc,
    TreeLaws.bind_pure_left]
  refine Agree.bindOpt (fun masks m2 inv => ?_)
    (agree_foldEntries spec chunk step stepSmall (activeAt value step) parent m1 activeCell
      levels1 cleared)
  obtain ⟨maskCells, maskZero, _, frame2, bits2⟩ := inv
  have notMask : ∀ address : Word, (∃ e, e < 32 ∧ address = word (hotLabel e)) ∨
      address = word tmpActive ∨ FoldFrame address →
        ∀ e, e < 2 ^ step → address ≠ word (stepMask e) := by
    rintro address (⟨e', small, rfl⟩ | rfl | ⟨_, notHot⟩) e bound same
    · rw [stepMask_eq] at same
      exact hot_ne (by omega) (by omega) (by omega) same
    · rw [stepMask_eq] at same
      exact hot_ne_tmp (32 + e) 1 (by omega) (by omega) same.symm
    · exact notHot (32 + e) (by omega) (by rw [same, stepMask_eq])
  obtain ⟨m3, run3, levelsAfter, frame3, bits3⟩ := det_foldPost spec chunk.val step stepPos stepSmall
    (activeAt value step) parent masks.get join label m2
    (by rw [frame2 _ (notMask _ (Or.inr (Or.inl rfl))), activeCell])
    (fun e => by rw [maskCells e]; rfl)
    (maskZero (activeAt value step) rfl)
    (fun e => by
      have small : e.val < 16 := lt_of_lt_of_le e.isLt powSmall
      rw [frame2 _ (notMask _ (Or.inl ⟨e.val, by omega, rfl⟩)), levels1 e])
    (by rw [frame2 _ (notMask _ (Or.inr (Or.inr joinFrame))),
      ram1Off _ (notMask _ (Or.inr (Or.inr joinFrame))) joinFrame.1, joinCell])
    (by rw [frame2 _ (notMask _ (Or.inr (Or.inr labelFrame))),
      ram1Off _ (notMask _ (Or.inr (Or.inr labelFrame))) labelFrame.1, labelCell])
  refine agree_plain_leaf (plain_foldPost spec chunk.val step) run3
    ⟨levelsAfter, fun address framed => ?_, by rw [bits3, bits2, bits1]⟩
  rw [frame3 address framed, frame2 _ (notMask _ (Or.inr (Or.inr framed))),
    ram1Off _ (notMask _ (Or.inr (Or.inr framed))) framed.1]

/-! ### The fold -/

omit [FieldCertificate] in
/-- A fixed-key hash is never intercepted. -/
theorem clean_hashM (bits : BitInput) (index : PlanB.FixedIndex) (label : Block) :
    Clean bits (Programs.hashM index label) :=
  (Clean.ask _ rfl).bind fun _ => .pure _

omit [FieldCertificate] in
theorem clean_foldMaskM (bits : BitInput) (lane : Lane) (chunk : Fin chunkCount)
    (step entry : Nat) (label : Block) :
    Clean bits (Programs.foldMaskM lane chunk step entry label) :=
  (clean_hashM bits _ label).bind fun _ => (clean_hashM bits _ label).bind fun _ => .pure _

omit [FieldCertificate] in
/-- **The fold is clean**: it asks fixed-key questions only. -/
theorem clean_evalFoldM (bits : BitInput) (lane : Lane) (chunk : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) : ∀ steps,
      Clean bits (Programs.evalFoldM lane chunk value bitLabel join steps)
  | 0 => .pure _
  | steps + 1 => (clean_evalFoldM bits lane chunk value bitLabel join steps).bind fun previous =>
      ((Clean.vector _ fun entry => by
        by_cases active : entry = activeAt value steps
        · simp only [if_pos active]; exact .pure _
        · simp only [if_neg active]; exact clean_foldMaskM bits lane chunk steps entry.val _).bind
          fun _ => .pure _).bind fun _ => .pure _

omit [FieldCertificate] in
theorem vector_pow_zero {spec : OracleSpec.{0, 0}} {α : Type} (f : Fin (2 ^ 0) → FreeQuery spec α) :
    FreeQuery.vector (2 ^ 0) f = FreeQuery.bind (f 0) fun v => .pure #v[v] := rfl

omit [FieldCertificate] in
/-- The level-1 labels: the bit-`0` label twice (step `0` is free). -/
theorem levelOne (value : Nat) (bitLabel join : Nat → Block) (free : join 0 = 0) :
    extendLevel 0 (fun _ => 0) (fun entry => if entry = activeAt value 0 then
      join 0 ^^^ bitLabel 0 ^^^ xorFoldExcept (activeAt value 0) (#v[(0 : Block)] : Vector Block (2 ^ 0)).get
      else (#v[(0 : Block)] : Vector Block (2 ^ 0)).get entry) = fun _ => bitLabel 0 := by
  funext entry
  have entryZero : ∀ other : Fin (2 ^ 0), other = activeAt value 0 := fun other =>
    Fin.ext (by have := other.isLt; simp [activeAt] at this ⊢)
  unfold extendLevel xorFoldExcept
  dsimp only
  have foldOne : ∀ start : Block, Fin.foldl 1 (fun (acc : Block) (_ : Fin 1) => acc) start = start :=
    fun start => by
      show Fin.foldl (0 + 1) _ start = start
      rw [Fin.foldl_succ, Fin.foldl_zero]
  split <;> (rw [if_pos (entryZero _), free]; simp [entryZero, foldOne])

omit [FieldCertificate] in
/-- **Level `1`** of the evaluator's fold: the bit-`0` label twice, no question. -/
theorem evalFoldM_one (lane : Lane) (chunk : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) (free : join 0 = 0) :
    Programs.evalFoldM lane chunk value bitLabel join 1 = .pure (fun _ => bitLabel 0) := by
  have zeroActive : ∀ other : Fin (2 ^ 0), other = activeAt value 0 := fun other =>
    Fin.ext (by have := other.isLt; simp [activeAt] at this ⊢)
  simp only [Programs.evalFoldM, Programs.evalStepM, vector_pow_zero, TreeLaws.monad_bind,
    TreeLaws.monad_pure, TreeLaws.bind_pure_left, if_pos (zeroActive 0)]
  rw [levelOne value bitLabel join free]

/-- **The fold**: `steps` fold steps from level `1` against `evalFoldM … (steps + 1)`. -/
theorem agree_fold (spec : Replay.LaneSpec) (chunk : Fin chunkCount) (value : Nat)
    (valueSmall : value < 32) (bitLabel join : Nat → Block) (free : join 0 = 0) :
    ∀ (steps : Nat), steps < 5 → ∀ (memory : Memory),
      memory.ram (word tmpAlpha) = word value →
      LevelCells (fun _ : Fin (2 ^ 1) => bitLabel 0) memory →
      (∀ step, 1 ≤ step → step ≤ steps →
        memory.ram (word (Replay.hotJoin spec chunk.val step)) = blockWord (join step) ∧
        memory.ram (word (Replay.bitLabel spec chunk.val step)) = blockWord (bitLabel step) ∧
        FoldFrame (word (Replay.hotJoin spec chunk.val step)) ∧
        FoldFrame (word (Replay.bitLabel spec chunk.val step))) →
      Agree (fun (level : Fin (2 ^ (steps + 1)) → Block) after => LevelCells level after ∧
          (∀ address, FoldFrame address → after.ram address = memory.ram address) ∧
          after.bits = memory.bits)
        (rtree (Prog.rep steps fun step => Replay.foldStep ordF0 spec chunk.val (step + 1)) memory)
        (Programs.evalFoldM spec.lane chunk value bitLabel join (steps + 1))
  | 0, _, memory, _, levels, _ => by
      rw [evalFoldM_one spec.lane chunk value bitLabel join free, Prog.rep, rtree_skip]
      exact .leaf ⟨levels, fun _ _ => rfl, rfl⟩
  | steps + 1, small, memory, alphaCell, levels, cells => by
      rw [Prog.rep, rtree_seq, Programs.evalFoldM]
      simp only [TreeLaws.monad_bind, TreeLaws.monad_pure]
      refine Agree.bindOpt (fun parent middle post => ?_)
        (agree_fold spec chunk value valueSmall bitLabel join free steps (by omega) memory
          alphaCell levels fun step low high => cells step low (by omega))
      obtain ⟨middleLevels, middleFrame, middleBits⟩ := post
      obtain ⟨joinCell, labelCell, joinFrame, labelFrame⟩ := cells (steps + 1) (by omega) le_rfl
      have alphaFrame : FoldFrame (word tmpAlpha) :=
        ⟨tmp_ne (show 0 < 16 by omega) (show 1 < 16 by omega) (by omega), fun index small =>
          (hot_ne_tmp index 0 (by omega) (by omega)).symm⟩
      refine (agree_foldStep spec chunk (steps + 1) (by omega) small value valueSmall parent
        (join (steps + 1)) (bitLabel (steps + 1)) middle
        (by rw [middleFrame _ alphaFrame, alphaCell]) middleLevels
        (by rw [middleFrame _ joinFrame, joinCell]) (by rw [middleFrame _ labelFrame, labelCell])
        joinFrame labelFrame).mono fun level after post => ?_
      obtain ⟨afterLevels, afterFrame, afterBits⟩ := post
      exact ⟨afterLevels, fun address framed => (afterFrame address framed).trans
        (middleFrame address framed), afterBits.trans middleBits⟩

end

end Kriterion.ArgoMAC.PlanB.SimMachine
