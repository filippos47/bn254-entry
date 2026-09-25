/-
**Phase 3, P1m — (B1) the fixed-key part: one chunk's `bin-to-hot` fold along an answer function,
at every chunk width.**

For a lane program `Programs.evalLaneM lane joins scale word labels` and an answer function `ans`,
chunk `c` of width `w = chunkWidth c` (any width; the statements never unfold the profile):

* `levelAt … s` — the evaluator's level-`s` labels (the fold program's value at `s` steps);
  `levelAt_succ` — level `s + 1` is `extendLevel` of level `s` and the step output `stepOut`: the
  xor of the two fold answers of every inactive entry (`foldAns`; the Davies–Meyer feed-forwards
  cancel), the active one recovered from the join;
* `levelAt_node` — **a node of level `t + 1` is a fixed block xor the fold answers of a nonempty
  set of step-`t` indices** (`nodeEntries`: the node's parent if it is inactive, every inactive
  entry if it is the active one), for every `t`: every level `≥ 2` of a chunk carries fresh
  material of the step below it;
* `mem_evalFoldM`, `lane_fold_question` — **the fold questions**: step `s < w`, an inactive entry
  `e`, either half, at the level-`s` label `levelAt … s e`, and nothing else (the masks ask only
  hash questions); `lane_prefix` — the questions of a lane before chunk `c`'s step `t` contain the
  fold up to step `t` and no step-`t` question of chunk `c`;
* the fold indices are pairwise distinct (steps below `chunkBits`, entries below
  `2 ^ chunkBits`): `PlanB.hotIndexNat_inj`, next to `hotIndexNat_eq` in `Construction/PGS/Index`.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedPot
import Proof.Privacy.Phase3.PublicFirst.BoundsOpening

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Request queriesAlong queriesAlong_bind queriesAlong_pure
  queriesAlong_vector mem_queriesAlong_evalMasksM)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Xor folds as `bigXor` -/

section Folds

/-- A xor fold over `Fin n` is the `bigXor` of the whole family. -/
theorem xorFold_eq_bigXor : ∀ {n : ℕ} (family : Fin n → Block),
    xorFold family = bigXor Finset.univ family
  | 0, family => rfl
  | n + 1, family => by
    unfold xorFold
    rw [Fin.foldl_succ_last, Fin.univ_castSuccEmb, bigXor, Finset.fold_cons, Finset.fold_map]
    have previous := xorFold_eq_bigXor (fun entry : Fin n => family entry.castSucc)
    unfold xorFold at previous
    rw [previous, bigXor]
    exact BitVec.xor_comm _ _

/-- A xor fold skipping one entry is the `bigXor` of the others. -/
theorem xorFoldExcept_eq_bigXor {n : ℕ} (skip : Fin n) (family : Fin n → Block) :
    xorFoldExcept skip family = bigXor (Finset.univ.erase skip) family := by
  rw [xorFoldExcept_eq, xorFold_eq_bigXor, bigXor_erase (Finset.mem_univ skip), BitVec.xor_comm,
    xor_left_cancel']

/-- A `bigXor` over entries and both halves. -/
theorem bigXor_product_bool {α : Type} [DecidableEq α] (E : Finset α) (g : α × Bool → Block) :
    bigXor (E ×ˢ Finset.univ) g = bigXor E fun e => g (e, false) ^^^ g (e, true) := by
  induction E using Finset.induction_on with
  | empty => rfl
  | insert e E outside ih =>
    have split : insert e E ×ˢ (Finset.univ : Finset Bool) =
        insert (e, false) (insert (e, true) (E ×ˢ Finset.univ)) := by
      ext p
      obtain ⟨a, b⟩ := p
      cases b <;> simp
    have notTrue : (e, true) ∉ E ×ˢ (Finset.univ : Finset Bool) := fun member =>
      outside (Finset.mem_product.mp member).1
    have notFalse : (e, false) ∉ insert (e, true) (E ×ˢ (Finset.univ : Finset Bool)) := by
      rw [Finset.mem_insert]
      rintro (same | member)
      · cases same
      · exact outside (Finset.mem_product.mp member).1
    rw [split, bigXor_insert notFalse, bigXor_insert notTrue, ih, bigXor_insert outside,
      BitVec.xor_assoc]

end Folds

/-! ### The fold along an answer function -/

section Fold

variable (ans : (request : Request) → request.Answer) (lane : Lane) (c : Fin chunkCount)

/-- A forward fixed-key answer, as a block. -/
def fixedAns (i : FixedIndex) (x : Block) : Block :=
  ans (.fixedForward i x)

/-- **The step material of entry `e` at step `s`**, at a label, along `ans`: the xor of the two fold
answers. -/
def foldAns (s e : ℕ) (x : Block) : Block :=
  fixedAns ans (hotIndexNat lane c s e false) x ^^^
    fixedAns ans (hotIndexNat lane c s e true) x

theorem eval_foldMaskM_ans (s e : ℕ) (x : Block) :
    FreeQuery.eval ans (Programs.foldMaskM lane c s e x) = foldAns ans lane c s e x := by
  show (fixedAns ans (hotIndexNat lane c s e false) x ^^^ x) ^^^
    (fixedAns ans (hotIndexNat lane c s e true) x ^^^ x) = _
  unfold foldAns
  generalize fixedAns ans (hotIndexNat lane c s e false) x = a
  generalize fixedAns ans (hotIndexNat lane c s e true) x = b
  rw [BitVec.xor_assoc, ← BitVec.xor_assoc x, BitVec.xor_comm x b, BitVec.xor_assoc,
    BitVec.xor_self, BitVec.xor_zero]

/-- **The step output along `ans`**: an inactive entry's material, the active one's recovered from
the join. -/
def stepOut (s : ℕ) (bit join : Block) (active : Fin (2 ^ s)) (parent : Fin (2 ^ s) → Block) :
    Fin (2 ^ s) → Block := fun e =>
  if e = active then
    join ^^^ bit ^^^ xorFoldExcept active fun other => foldAns ans lane c s other.val (parent other)
  else foldAns ans lane c s e.val (parent e)

theorem eval_evalStepM_ans (s : ℕ) (bit join : Block) (active : Fin (2 ^ s))
    (parent : Fin (2 ^ s) → Block) :
    FreeQuery.eval ans (Programs.evalStepM lane c s bit join active parent) =
      stepOut ans lane c s bit join active parent := by
  funext entry
  simp only [Programs.evalStepM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    stepOut]
  by_cases same : entry = active
  · rw [if_pos same, if_pos same]
    congr 1
    apply Programs.xorFoldExcept_congr
    intro other different
    simp only [Vector.get_ofFn, if_neg different, eval_foldMaskM_ans]
  · simp only [if_neg same, Vector.get_ofFn, eval_foldMaskM_ans]

theorem queriesAlong_evalStepM (s : ℕ) (bit join : Block) (active : Fin (2 ^ s))
    (parent : Fin (2 ^ s) → Block) :
    queriesAlong ans (Programs.evalStepM lane c s bit join active parent) =
      (List.finRange (2 ^ s)).flatMap fun e => if e = active then [] else
        [.fixedForward (hotIndexNat lane c s e.val false) (parent e),
          .fixedForward (hotIndexNat lane c s e.val true) (parent e)] := by
  unfold Programs.evalStepM
  rw [queriesAlong_bind, queriesAlong_vector, queriesAlong_pure, List.append_nil]
  congr 1
  funext e
  split <;> rfl

variable (value : ℕ) (bitLabel join : ℕ → Block)

/-- **The evaluator's level-`s` labels** of the chunk, along `ans`. -/
abbrev levelAt (s : ℕ) : Fin (2 ^ s) → Block :=
  FreeQuery.eval ans (Programs.evalFoldM lane c value bitLabel join s)

theorem levelAt_succ (s : ℕ) :
    levelAt ans lane c value bitLabel join (s + 1) =
      extendLevel s (levelAt ans lane c value bitLabel join s)
        (stepOut ans lane c s (bitLabel s) (join s) (activeAt value s)
          (levelAt ans lane c value bitLabel join s)) := by
  show FreeQuery.eval ans (Programs.evalFoldM lane c value bitLabel join s >>= fun previous =>
      Programs.evalStepM lane c s (bitLabel s) (join s) (activeAt value s) previous >>=
        fun right => pure (extendLevel s previous right)) = _
  simp only [FreeQuery.eval_bind, FreeQuery.eval_pure, eval_evalStepM_ans]

theorem queriesAlong_evalFoldM_succ (s : ℕ) :
    queriesAlong ans (Programs.evalFoldM lane c value bitLabel join (s + 1)) =
      queriesAlong ans (Programs.evalFoldM lane c value bitLabel join s) ++
        queriesAlong ans (Programs.evalStepM lane c s (bitLabel s) (join s) (activeAt value s)
          (levelAt ans lane c value bitLabel join s)) := by
  show queriesAlong ans (Programs.evalFoldM lane c value bitLabel join s >>= fun previous =>
      Programs.evalStepM lane c s (bitLabel s) (join s) (activeAt value s) previous >>=
        fun right => pure (extendLevel s previous right)) = _
  rw [queriesAlong_bind, queriesAlong_bind, queriesAlong_pure, List.append_nil]

/-- **The fold's questions**: at a step `s < w`, both halves of an inactive entry at its level-`s`
label. -/
theorem mem_evalFoldM (w : ℕ) (q : Request) :
    q ∈ queriesAlong ans (Programs.evalFoldM lane c value bitLabel join w) ↔
      ∃ s < w, ∃ e : Fin (2 ^ s), e ≠ activeAt value s ∧ ∃ h : Bool,
        q = .fixedForward (hotIndexNat lane c s e.val h)
          (levelAt ans lane c value bitLabel join s e) := by
  induction w with
  | zero =>
    constructor
    · intro member
      cases member
    · rintro ⟨s, small, _⟩
      exact absurd small (Nat.not_lt_zero s)
  | succ w ih =>
    rw [queriesAlong_evalFoldM_succ, List.mem_append, ih, queriesAlong_evalStepM]
    constructor
    · rintro (⟨s, small, rest⟩ | member)
      · exact ⟨s, by omega, rest⟩
      · obtain ⟨e, _, inner⟩ := List.mem_flatMap.mp member
        split at inner
        · cases inner
        · rename_i inactive
          refine ⟨w, by omega, e, inactive, ?_⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inner
          rcases inner with same | same
          · exact ⟨false, same⟩
          · exact ⟨true, same⟩
    · rintro ⟨s, small, e, inactive, h, rfl⟩
      by_cases below : s < w
      · exact Or.inl ⟨s, below, e, inactive, h, rfl⟩
      · have same : s = w := by omega
        subst same
        refine Or.inr (List.mem_flatMap.mpr ⟨e, List.mem_finRange e, ?_⟩)
        rw [if_neg inactive]
        cases h <;> simp

/-- **The fold's questions up to step `t` come first.** -/
theorem evalFoldM_prefix (t : ℕ) : ∀ w, t ≤ w → ∃ rest,
    queriesAlong ans (Programs.evalFoldM lane c value bitLabel join w) =
      queriesAlong ans (Programs.evalFoldM lane c value bitLabel join t) ++ rest := by
  intro w
  induction w with
  | zero =>
    intro le
    have zero : t = 0 := by omega
    subst zero
    exact ⟨[], (List.append_nil _).symm⟩
  | succ w ih =>
    intro le
    by_cases same : t = w + 1
    · subst same
      exact ⟨[], (List.append_nil _).symm⟩
    · obtain ⟨rest, eq⟩ := ih (by omega)
      refine ⟨rest ++ queriesAlong ans (Programs.evalStepM lane c w (bitLabel w) (join w)
        (activeAt value w) (levelAt ans lane c value bitLabel join w)), ?_⟩
      rw [queriesAlong_evalFoldM_succ, eq, List.append_assoc]

/-! #### A node of the next level -/

/-- The parent of a node of level `t + 1`. -/
def nodeParent {t : ℕ} (n : Fin (2 ^ (t + 1))) : Fin (2 ^ t) :=
  ⟨n.val % 2 ^ t, Nat.mod_lt _ (Nat.two_pow_pos t)⟩

/-- **The entries whose step material enters step output `r`**: `r` itself if it is inactive,
every inactive entry if it is the active one. -/
def nodeEntries {t : ℕ} (active r : Fin (2 ^ t)) : Finset (Fin (2 ^ t)) :=
  if r = active then Finset.univ.erase active else {r}

theorem nodeEntries_inactive {t : ℕ} {active r e : Fin (2 ^ t)}
    (member : e ∈ nodeEntries active r) : e ≠ active := by
  unfold nodeEntries at member
  split at member
  · exact Finset.ne_of_mem_erase member
  · rename_i different
    rw [Finset.mem_singleton.mp member]
    exact different

theorem nodeEntries_nonempty {t : ℕ} (one : 1 ≤ t) (active r : Fin (2 ^ t)) :
    (nodeEntries active r).Nonempty := by
  unfold nodeEntries
  split
  · refine Finset.Nontrivial.erase_nonempty ?_
    have two : 2 ≤ 2 ^ t := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) one
    refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ⟨1, by omega⟩, Finset.mem_univ _, ?_⟩
    intro same
    exact absurd (congrArg Fin.val same) (by simp)
  · exact Finset.singleton_nonempty _

/-- **A step output is a fixed block xor the fold answers of its entries.** -/
theorem stepOut_eq (s : ℕ) (bit join : Block) (active : Fin (2 ^ s))
    (parent : Fin (2 ^ s) → Block) (r : Fin (2 ^ s)) :
    stepOut ans lane c s bit join active parent r =
      (if r = active then join ^^^ bit else 0) ^^^
        bigXor (nodeEntries active r ×ˢ Finset.univ) fun p =>
          fixedAns ans (hotIndexNat lane c s p.1.val p.2) (parent p.1) := by
  rw [bigXor_product_bool]
  unfold stepOut nodeEntries
  by_cases same : r = active
  · rw [if_pos same, if_pos same, if_pos same, xorFoldExcept_eq_bigXor]
    rfl
  · rw [if_neg same, if_neg same, if_neg same, zero_xor_block, ← Finset.insert_empty,
      bigXor_insert (Finset.notMem_empty r), bigXor, Finset.fold_empty, xor_zero_block]
    rfl

/-- **A node of level `t + 1`**: its parent's label if it is a left child, xor the parent's step
output. -/
theorem levelAt_node (t : ℕ) (n : Fin (2 ^ (t + 1))) :
    levelAt ans lane c value bitLabel join (t + 1) n =
      ((if n.val < 2 ^ t then levelAt ans lane c value bitLabel join t (nodeParent n) else 0) ^^^
        (if nodeParent n = activeAt value t then join t ^^^ bitLabel t else 0)) ^^^
        bigXor (nodeEntries (activeAt value t) (nodeParent n) ×ˢ Finset.univ) fun p =>
          fixedAns ans (hotIndexNat lane c t p.1.val p.2)
            (levelAt ans lane c value bitLabel join t p.1) := by
  rw [levelAt_succ, BitVec.xor_assoc, ← stepOut_eq]
  unfold extendLevel
  by_cases below : n.val < 2 ^ t
  · rw [dif_pos below, if_pos below]
    have same : (⟨n.val, below⟩ : Fin (2 ^ t)) = nodeParent n :=
      Fin.ext (Nat.mod_eq_of_lt below).symm
    rw [same]
  · rw [dif_neg below, if_neg below, zero_xor_block]
    have expand : (2 : ℕ) ^ (t + 1) = 2 ^ t + 2 ^ t := by rw [pow_succ]; omega
    have bound := n.isLt
    have same : (⟨n.val - 2 ^ t, by omega⟩ : Fin (2 ^ t)) = nodeParent n := by
      apply Fin.ext
      show n.val - 2 ^ t = n.val % 2 ^ t
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [same]

end Fold

/-! ### The fold indices -/

section Indices

theorem step_lt_chunkBits {c : Fin chunkCount} {s : ℕ} (small : s < chunkWidth c) :
    s < chunkBits :=
  lt_of_lt_of_le small (chunkWidth_le c)

theorem entry_lt_chunkBits {c : Fin chunkCount} {s : ℕ} (small : s < chunkWidth c)
    (e : Fin (2 ^ s)) : e.val < 2 ^ chunkBits :=
  lt_of_lt_of_le e.isLt (Nat.pow_le_pow_right (by norm_num) (step_lt_chunkBits small).le)

/-- The fold questions of step `t` of one (lane, chunk). -/
def StepAt (lane : Lane) (c : Fin chunkCount) (t : ℕ) : FixedIndex → Prop
  | .hot lane' c' fold _ _ => lane' = lane ∧ c' = c ∧ fold.val = t
  | .gadget _ _ _ _ => False

theorem stepAt_hot {lane : Lane} {c : Fin chunkCount} {t : ℕ} (small : t < chunkBits) (e : ℕ)
    (h : Bool) : StepAt lane c t (hotIndexNat lane c t e h) :=
  ⟨rfl, rfl, Nat.mod_eq_of_lt small⟩

theorem not_stepAt_hot {lane lane' : Lane} {c c' : Fin chunkCount} {t s : ℕ} (small : s < chunkBits)
    (e : ℕ) (h : Bool) (different : lane' ≠ lane ∨ c' ≠ c ∨ s ≠ t) :
    ¬ StepAt lane c t (hotIndexNat lane' c' s e h) := by
  rintro ⟨laneEq, chunkEq, stepEq⟩
  change s % chunkBits = t at stepEq
  rw [Nat.mod_eq_of_lt small] at stepEq
  rcases different with d | d | d
  · exact d laneEq
  · exact d chunkEq
  · exact d stepEq

end Indices

/-! ### One lane -/

section Lane

variable [FieldCertificate] (ans : (request : Request) → request.Answer) (lane : Lane)
  (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
  (word : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block)

/-- **The level-`s` labels of chunk `c` of a lane**, along `ans`. -/
abbrev laneFoldLevel (c : Fin chunkCount) (s : ℕ) : Fin (2 ^ s) → Block :=
  levelAt ans lane c (chunkValue word c).toNat (labelAt (chunkLabels labels c))
    (joinAt (hotSlice joins c)) s

theorem queriesAlong_evalLaneM :
    queriesAlong ans (Programs.evalLaneM lane joins scale word labels) =
      (List.finRange chunkCount).flatMap fun c =>
        queriesAlong ans (Programs.evalChunkM lane joins scale word labels c) := by
  unfold Programs.evalLaneM
  rw [queriesAlong_bind, queriesAlong_vector, queriesAlong_pure, List.append_nil]

theorem queriesAlong_evalChunkM (c : Fin chunkCount) :
    queriesAlong ans (Programs.evalChunkM lane joins scale word labels c) =
      queriesAlong ans (Programs.evalFoldM lane c (chunkValue word c).toNat
          (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c)) (chunkWidth c)) ++
        queriesAlong ans (Programs.evalMasksM lane c (chunkWidth c)
          (laneFoldLevel ans lane joins word labels c (chunkWidth c)) (chunkOf word c)) := by
  unfold Programs.evalChunkM
  rw [queriesAlong_bind, queriesAlong_bind, queriesAlong_pure, List.append_nil]

/-- **A lane's fixed-key questions**: the fold questions of its chunks. -/
theorem lane_fold_question (i : FixedIndex) (x : Block) :
    .fixedForward i x ∈ queriesAlong ans (Programs.evalLaneM lane joins scale word labels) ↔
      ∃ (c : Fin chunkCount) (s : ℕ), s < chunkWidth c ∧ ∃ e : Fin (2 ^ s),
        e ≠ activeAt (chunkValue word c).toNat s ∧ ∃ h : Bool,
          i = hotIndexNat lane c s e.val h ∧
            x = laneFoldLevel ans lane joins word labels c s e := by
  rw [queriesAlong_evalLaneM]
  constructor
  · intro member
    obtain ⟨c, _, inner⟩ := List.mem_flatMap.mp member
    rw [queriesAlong_evalChunkM, List.mem_append] at inner
    rcases inner with fold | masks
    · obtain ⟨s, small, e, inactive, h, same⟩ := (mem_evalFoldM ans lane c _ _ _ _ _).mp fold
      injection same with iEq xEq
      exact ⟨c, s, small, e, inactive, h, iEq, xEq⟩
    · obtain ⟨_, _, _, same⟩ := mem_queriesAlong_evalMasksM ans lane c _ _ _ masks
      cases same
  · rintro ⟨c, s, small, e, inactive, h, rfl, rfl⟩
    refine List.mem_flatMap.mpr ⟨c, List.mem_finRange c, ?_⟩
    rw [queriesAlong_evalChunkM]
    exact List.mem_append_left _
      ((mem_evalFoldM ans lane c _ _ _ _ _).mpr ⟨s, small, e, inactive, h, rfl⟩)

/-- **The questions of a lane before the step-`t` material of chunk `c`**: the other chunks before
`c` and chunk `c`'s fold up to step `t`; none is a step-`t` question of chunk `c`. -/
theorem lane_prefix (c : Fin chunkCount) (t : ℕ) (le : t ≤ chunkWidth c) :
    ∃ front back, queriesAlong ans (Programs.evalLaneM lane joins scale word labels) =
        front ++ back ∧
      (∀ q ∈ queriesAlong ans (Programs.evalFoldM lane c (chunkValue word c).toNat
          (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c)) t), q ∈ front) ∧
      ∀ q ∈ front, ¬ Kriterion.ArgoMAC.Phase3.Lazy.FixedAt (StepAt lane c t) q := by
  obtain ⟨before, after, split⟩ := List.append_of_mem (List.mem_finRange c)
  have beforeOther : ∀ c' ∈ before, c' ≠ c := by
    intro c' member same
    subst same
    have nodup := List.nodup_finRange chunkCount
    rw [split] at nodup
    exact (List.nodup_append.mp nodup).2.2 _ member _ List.mem_cons_self rfl
  obtain ⟨rest, foldSplit⟩ := evalFoldM_prefix ans lane c (chunkValue word c).toNat
    (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c)) t (chunkWidth c) le
  refine ⟨before.flatMap (fun c' => queriesAlong ans
      (Programs.evalChunkM lane joins scale word labels c')) ++
      queriesAlong ans (Programs.evalFoldM lane c (chunkValue word c).toNat
        (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c)) t),
    rest ++ queriesAlong ans (Programs.evalMasksM lane c (chunkWidth c)
      (laneFoldLevel ans lane joins word labels c (chunkWidth c)) (chunkOf word c)) ++
      after.flatMap (fun c' => queriesAlong ans
        (Programs.evalChunkM lane joins scale word labels c')),
    ?_, fun q member => List.mem_append_right _ member, ?_⟩
  · rw [queriesAlong_evalLaneM, split, List.flatMap_append, List.flatMap_cons,
      queriesAlong_evalChunkM, foldSplit]
    simp only [List.append_assoc]
  · intro q member atStep
    rcases List.mem_append.mp member with other | fold
    · obtain ⟨c', inside, inner⟩ := List.mem_flatMap.mp other
      have laneAt := mem_queriesAlong_allQ ans
        (Kriterion.ArgoMAC.Phase3.Lazy.evalChunkM_allQ lane joins scale word labels c') q inner
      cases q with
      | fixedForward i x =>
        rcases laneAt with fixed | hash
        · cases i with
          | hot l cc f e h =>
            exact beforeOther c' inside (fixed.2.symm.trans atStep.2.1)
          | gadget _ _ _ _ => exact fixed.elim
        · exact hash.elim
      | _ => exact atStep.elim
    · obtain ⟨s, small, e, _, h, rfl⟩ := (mem_evalFoldM ans lane c _ _ _ _ _).mp fold
      exact not_stepAt_hot (lt_of_lt_of_le (lt_of_lt_of_le small le) (chunkWidth_le c)) e.val h
        (Or.inr (Or.inr (Nat.ne_of_lt small))) atStep

end Lane

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
