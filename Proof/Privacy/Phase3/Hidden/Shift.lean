/-
**Phase 3, P1f — shifting the tape: one `bin-to-hot` fold, run on a shifted tape.**

The symmetries of hop (1) shift the garbler's labels (`Δ`, the zero labels) and relabel the
fixed-key permutations so that every Davies–Meyer value the garbler reads is kept:
`shiftPerm a b π : x ↦ π (x ⊕ a) ⊕ b` maps the garbler's point `x` to `x ⊕ a` and its image to
`π x ⊕ b`, so the Davies–Meyer value moves by `a ⊕ b` (by nothing when `a = b`).

A `FoldShift` fixes, for one (lane, chunk) fold, the shift of `Δ`, of each step's zero label, of
each step's material `M_r` (`m`) and of each gate's two outputs (`o`). The level shifts follow
(`FoldShift.level`); the shift of the fold-gate permutations is `FoldShift.hot`. When the step
materials' shifts XOR to the zero-label shift (`FoldShift.Valid`), every published join is kept.

`sim_garbleFoldM`: on a tape whose fold-gate permutations are shifted by `FoldShift.hot`, the fold
run on the shifted `Δ` and zero labels asks each gate at the point shifted by `FoldShift.level`,
its level labels are shifted by `FoldShift.level`, and its joins are the same.
-/

import Proof.Privacy.Phase3.Hidden.Sim

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)

noncomputable section

/-! ### XOR bookkeeping -/

theorem xor_cancel_right (x a : Block) : x ^^^ a ^^^ a = x := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem xor_self_left (a b : Block) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem xorFold_xor {count : Nat} (f g : Fin count → Block) :
    xorFold (fun r => f r ^^^ g r) = xorFold f ^^^ xorFold g := by
  induction count with
  | zero =>
      unfold xorFold
      rw [Fin.foldl_zero, Fin.foldl_zero, Fin.foldl_zero]
      exact BitVec.xor_self.symm
  | succ n ih =>
      unfold xorFold at ih ⊢
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last, Fin.foldl_succ_last]
      have := ih (fun r => f r.castSucc) (fun r => g r.castSucc)
      simp only at this ⊢
      rw [this]
      ac_rfl

theorem xorFold_one (f : Fin 1 → Block) : xorFold f = f 0 := by
  unfold xorFold
  rw [Fin.foldl_succ_last, Fin.foldl_zero]
  exact BitVec.zero_xor

/-! ### Shifted permutations -/

/-- `x ↦ π (x ⊕ a) ⊕ b`. -/
def shiftPerm (a b : Block) (π : Equiv.Perm Block) : Equiv.Perm Block where
  toFun x := π (x ^^^ a) ^^^ b
  invFun y := π.symm (y ^^^ b) ^^^ a
  left_inv x := by simp only [xor_cancel_right, Equiv.symm_apply_apply]
  right_inv y := by simp only [xor_cancel_right, Equiv.apply_symm_apply]

theorem shiftPerm_shift (a b : Block) (π : Equiv.Perm Block) (x : Block) :
    shiftPerm a b π (x ^^^ a) = π x ^^^ b := by
  show π (x ^^^ a ^^^ a) ^^^ b = _
  rw [xor_cancel_right]

theorem shiftPerm_involutive (a b : Block) : Function.Involutive (shiftPerm a b) := by
  intro π
  apply Equiv.ext
  intro x
  show π (x ^^^ a ^^^ a) ^^^ b ^^^ b = π x
  rw [xor_cancel_right, xor_cancel_right]

/-! ### The shift of one fold -/

/-- The shift of one (lane, chunk) fold. -/
structure FoldShift where
  /-- The shift of `Δ`. -/
  delta : Block
  /-- The shift of each step's zero label. -/
  zero : Nat → Block
  /-- The shift of each paid step's material `M_r`. -/
  m : Nat → Nat → Block
  /-- The shift of both outputs of a fold gate. -/
  o : Nat → Nat → Block

namespace FoldShift

/-- The shift of a step's material: step `0` is the zero label itself. -/
def stepShift (F : FoldShift) : Nat → Nat → Block
  | 0, _ => F.zero 0
  | n + 1, r => F.m (n + 1) r

/-- The shift of the level labels. -/
def level (F : FoldShift) : Nat → Nat → Block
  | 0, _ => F.delta
  | n + 1, j => if j < 2 ^ n then F.level n j ^^^ F.stepShift n j else F.stepShift n (j - 2 ^ n)

/-- The shift of the fold-gate permutation at `(step, entry, half)`: input by the level shift,
output so that the half's Davies–Meyer value moves by `o ⊕ (m if half = false)`. -/
def hot (F : FoldShift) (n r : Nat) (half : Bool) : Block × Block :=
  (F.level n r, F.level n r ^^^ F.o n r ^^^ (if half then 0 else F.m n r))

/-- The paid materials' shifts XOR to the zero-label shift: every join is kept. -/
def Valid (F : FoldShift) (width : Nat) : Prop :=
  ∀ n, 1 ≤ n → n < width → xorFold (fun r : Fin (2 ^ n) => F.m n r.val) = F.zero n

theorem xorFold_stepShift (F : FoldShift) (width : Nat) (valid : F.Valid width) (n : Nat)
    (small : n < width) : xorFold (fun r : Fin (2 ^ n) => F.stepShift n r.val) = F.zero n := by
  cases n with
  | zero => exact xorFold_one _
  | succ n => exact valid (n + 1) (by omega) small

theorem Valid.mono {F : FoldShift} {width width' : Nat} (valid : F.Valid width) (le : width' ≤ width) :
    F.Valid width' := fun n one small => valid n one (by omega)

end FoldShift

/-! ### One fold, run on the shifted tape -/

variable {rel : Asked FixedIndex EncPRF.PermutationIndex → Asked FixedIndex EncPRF.PermutationIndex → Prop}

/-- One Davies–Meyer gate, asked at the shifted point of the shifted permutation. -/
theorem sim_hashM (O O' : Oracle) (index : FixedIndex) (x a b : Block)
    (oracle : O'.1.permutation index (x ^^^ a) = O.1.permutation index x ^^^ b)
    (entry : rel ⟨.fixedForward index x, O.1.permutation index x⟩
      ⟨.fixedForward index (x ^^^ a), O'.1.permutation index (x ^^^ a)⟩) :
    Sim (publicAnswer O) (publicAnswer O') rel
      (fun v v' => v = PlanB.hash O.1 index x ∧ v' = v ^^^ a ^^^ b)
      (Programs.hashM index x) (Programs.hashM index (x ^^^ a)) := by
  unfold Programs.hashM Programs.askFixed
  refine Sim.bind (R := fun v v' => v = O.1.permutation index x ∧ v' = v ^^^ b)
    (Sim.ask (.fixedForward index x) (.fixedForward index (x ^^^ a))
      (fun (v v' : Block) => v = O.1.permutation index x ∧ v' = v ^^^ b) entry
      ⟨rfl, oracle⟩) fun v v' related => Sim.pure' ?_
  obtain ⟨rfl, rfl⟩ := related
  refine ⟨rfl, ?_⟩
  ac_rfl

/-- The two-half material of one fold gate. -/
theorem sim_foldMaskM (O O' : Oracle) (F : FoldShift) (lane : Lane) (chunk : Fin chunkCount)
    (n r : Nat) (label : Block)
    (oracle : ∀ (half : Bool) (x : Block),
      O'.1.permutation (hotIndexNat lane chunk n r half) (x ^^^ (F.hot n r half).1) =
        O.1.permutation (hotIndexNat lane chunk n r half) x ^^^ (F.hot n r half).2)
    (entry : ∀ half : Bool, rel ⟨.fixedForward (hotIndexNat lane chunk n r half) label,
        O.1.permutation (hotIndexNat lane chunk n r half) label⟩
      ⟨.fixedForward (hotIndexNat lane chunk n r half) (label ^^^ F.level n r),
        O'.1.permutation (hotIndexNat lane chunk n r half) (label ^^^ F.level n r)⟩) :
    Sim (publicAnswer O) (publicAnswer O') rel
      (fun v v' => v = foldMask O.1 lane chunk n r label ∧ v' = v ^^^ F.m n r)
      (Programs.foldMaskM lane chunk n r label)
      (Programs.foldMaskM lane chunk n r (label ^^^ F.level n r)) := by
  unfold Programs.foldMaskM
  refine Sim.bind (sim_hashM O O' _ label _ _ (oracle false label) (entry false))
    fun first first' hfirst => Sim.bind (sim_hashM O O' _ label _ _ (oracle true label) (entry true))
      fun second second' hsecond => Sim.pure' ?_
  obtain ⟨rfl, rfl⟩ := hfirst
  obtain ⟨rfl, rfl⟩ := hsecond
  refine ⟨rfl, ?_⟩
  simp only [FoldShift.hot, Bool.false_eq_true, if_false, if_true]
  ac_nf
  simp only [xor_self_left, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor]

/-- One level of the fold. -/
theorem sim_garbleStepM (O O' : Oracle) (F : FoldShift) (lane : Lane) (chunk : Fin chunkCount)
    (n : Nat) (zeroLabel : Block) (parent : Fin (2 ^ n) → Block)
    (oracle : ∀ (r : Nat) (half : Bool) (x : Block), r < 2 ^ n →
      O'.1.permutation (hotIndexNat lane chunk n r half) (x ^^^ (F.hot n r half).1) =
        O.1.permutation (hotIndexNat lane chunk n r half) x ^^^ (F.hot n r half).2)
    (entry : ∀ (r : Fin (2 ^ n)) (half : Bool), n ≠ 0 →
      rel ⟨.fixedForward (hotIndexNat lane chunk n r.val half) (parent r),
        O.1.permutation (hotIndexNat lane chunk n r.val half) (parent r)⟩
      ⟨.fixedForward (hotIndexNat lane chunk n r.val half) (parent r ^^^ F.level n r.val),
        O'.1.permutation (hotIndexNat lane chunk n r.val half) (parent r ^^^ F.level n r.val)⟩) :
    Sim (publicAnswer O) (publicAnswer O') rel
      (fun right right' => right = garbleStep O.1 lane chunk n zeroLabel parent ∧
        ∀ r : Fin (2 ^ n), right' r = right r ^^^ F.stepShift n r.val)
      (Programs.garbleStepM lane chunk n zeroLabel parent)
      (Programs.garbleStepM lane chunk n (zeroLabel ^^^ F.zero n)
        (fun r => parent r ^^^ F.level n r.val)) := by
  unfold Programs.garbleStepM
  by_cases zero : n = 0
  · subst zero
    rw [if_pos rfl, if_pos rfl]
    refine Sim.pure' ⟨?_, fun r => rfl⟩
    funext r
    show zeroLabel = garbleStep O.1 lane chunk 0 zeroLabel parent r
    unfold garbleStep
    rw [if_pos rfl]
  · simp only [if_neg zero]
    refine Sim.bind (Sim.vector (2 ^ n) _ _
      fun r => sim_foldMaskM O O' F lane chunk n r.val (parent r)
        (fun half x => oracle r.val half x r.isLt) (fun half => entry r half zero))
      fun masks masks' related => Sim.pure' ⟨?_, fun r => ?_⟩
    · funext r
      rw [(related r).1]
      simp [garbleStep, zero]
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      exact (related r).2

/-- **The fold, on the shifted tape.** -/
theorem sim_garbleFoldM (O O' : Oracle) (F : FoldShift) (lane : Lane) (chunk : Fin chunkCount)
    (delta : Block) (zeroLabel : Nat → Block) :
    ∀ steps, F.Valid steps →
      (∀ (n r : Nat) (half : Bool) (x : Block), n < steps → r < 2 ^ n →
        O'.1.permutation (hotIndexNat lane chunk n r half) (x ^^^ (F.hot n r half).1) =
          O.1.permutation (hotIndexNat lane chunk n r half) x ^^^ (F.hot n r half).2) →
      (∀ (n : Nat) (r : Fin (2 ^ n)) (half : Bool), n < steps → n ≠ 0 →
        rel ⟨.fixedForward (hotIndexNat lane chunk n r.val half)
            ((garbleFold O.1 lane chunk delta zeroLabel n).1 r),
          O.1.permutation (hotIndexNat lane chunk n r.val half)
            ((garbleFold O.1 lane chunk delta zeroLabel n).1 r)⟩
          ⟨.fixedForward (hotIndexNat lane chunk n r.val half)
            ((garbleFold O.1 lane chunk delta zeroLabel n).1 r ^^^ F.level n r.val),
          O'.1.permutation (hotIndexNat lane chunk n r.val half)
            ((garbleFold O.1 lane chunk delta zeroLabel n).1 r ^^^ F.level n r.val)⟩) →
      Sim (publicAnswer O) (publicAnswer O') rel
        (fun result result' => result = garbleFold O.1 lane chunk delta zeroLabel steps ∧
          (∀ j : Fin (2 ^ steps), result'.1 j = result.1 j ^^^ F.level steps j.val) ∧
          result'.2 = result.2)
        (Programs.garbleFoldM lane chunk delta zeroLabel steps)
        (Programs.garbleFoldM lane chunk (delta ^^^ F.delta) (fun n => zeroLabel n ^^^ F.zero n)
          steps)
  | 0, _, _, _ => Sim.pure' ⟨rfl, fun _ => rfl, rfl⟩
  | steps + 1, valid, oracle, entry => by
      show Sim _ _ _ _ (Programs.garbleFoldM lane chunk delta zeroLabel steps >>= fun previous =>
          Programs.garbleStepM lane chunk steps (zeroLabel steps) previous.1 >>= fun right =>
            Pure.pure (extendLevel steps previous.1 right,
              fun step => if step = steps then stepJoin steps (zeroLabel steps) right
                else previous.2 step))
        (Programs.garbleFoldM lane chunk (delta ^^^ F.delta) (fun n => zeroLabel n ^^^ F.zero n)
            steps >>= fun previous =>
          Programs.garbleStepM lane chunk steps (zeroLabel steps ^^^ F.zero steps) previous.1
            >>= fun right =>
            Pure.pure (extendLevel steps previous.1 right,
              fun step => if step = steps then stepJoin steps (zeroLabel steps ^^^ F.zero steps) right
                else previous.2 step))
      refine Sim.bind (sim_garbleFoldM O O' F lane chunk delta zeroLabel steps (valid.mono (by omega))
        (fun n r half x small => oracle n r half x (by omega))
        (fun n r half small => entry n r half (by omega))) fun previous previous' hprevious => ?_
      obtain ⟨rfl, levels, joins⟩ := hprevious
      have parent : previous'.1 = fun r => (garbleFold O.1 lane chunk delta zeroLabel steps).1 r ^^^
          F.level steps r.val := funext levels
      rw [parent]
      refine Sim.bind (sim_garbleStepM O O' F lane chunk steps (zeroLabel steps) _
        (fun r half x small => oracle steps r half x (by omega) small)
        (fun r half nonzero => entry steps r half (by omega) nonzero)) fun right right' hright =>
          Sim.pure' ⟨?_, fun j => ?_, ?_⟩
      · rw [hright.1]
        rfl
      · unfold extendLevel
        simp only [FoldShift.level]
        split
        · rw [hright.2]
          ac_rfl
        · rw [hright.2]
      · funext step
        simp only
        split
        · unfold stepJoin
          have shifted : right' = fun r => right r ^^^ F.stepShift steps r.val :=
            funext hright.2
          rw [shifted, xorFold_xor, F.xorFold_stepShift (steps + 1) valid steps (by omega)]
          ac_nf
          simp only [xor_self_left, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor]
        · rw [joins]

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
