/-
**The replay, the `508` whitened labels** (`agree_whiten`): `Replay.whiten` (load `k1`, `k2`, then
`508` times `whitenOne`) against the evaluator's `whitePadsM` (the bit-`false` pads of `x`, then
of `y`), leaving `whiteBase + i` = the whitened label `whitenMacOf pads mac`.
-/

import Proof.Simulator.ReplayWhiten

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

omit [FieldCertificate] in
theorem clean_padM (bits : BitInput) (keys : WhiteningKeys)
    (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) (bit : Bool) :
    Clean bits (Programs.padM keys coordinate index bit) :=
  (Clean.ask _ rfl).bind fun _ => .pure _

/-- The invariant of one half of the whitening loop. -/
def WhiteInv (start : Memory) (base : Nat) (lab : Fin coordinateBitCount → Block)
    (record0 : DesignatedRecord) (count : Nat) (state : Vector Block count × DesignatedRecord)
    (memory : Memory) : Prop :=
  (∀ (i : Fin coordinateBitCount) (bound : i.val < count),
      memory.ram (word (whiteBase + (base + i.val))) = blockWord (state.1[i.val] ^^^ lab i)) ∧
    (∀ address, (∀ i, i < count → address ≠ word (whiteBase + (base + i))) →
      memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧ memory.registers rInput = start.registers rInput ∧
    memory.registers rF = start.registers rF ∧ state.2 = record0

theorem white_ne (base first second : Nat) (baseSmall : base + 254 ≤ 508) (firstSmall : first < 254)
    (secondSmall : second < 254) (different : first ≠ second) :
    word (whiteBase + (base + first)) ≠ word (whiteBase + (base + second)) :=
  word_ne (by unfold whiteBase; omega) (by unfold whiteBase; omega) (by omega)

theorem label_ne_white (position white : Nat) (positionSmall : position < 508) (whiteSmall : white < 508) :
    word (labelBase + position) ≠ word (whiteBase + white) :=
  word_ne (by unfold labelBase; omega) (by unfold whiteBase; omega)
    (by unfold labelBase whiteBase; omega)

/-- **One half of the whitening loop** (`254` labels of one coordinate). -/
theorem agree_whitenHalf (bits : BitInput) (body : Nat → Prog)
    (base : Nat) (coordinate : EncPRF.Coordinate) (lab : Fin coordinateBitCount → Block)
    (keys : WhiteningKeys) (start : Memory) (record0 : DesignatedRecord)
    (bodyIs : ∀ i, body i = Replay.whitenOne ordE0 (base + i))
    (named : ∀ i : Fin coordinateBitCount, Replay.encIdx (base + i.val) = (coordinate, i))
    (baseSmall : base + 254 ≤ 508)
    (firstKey : start.registers rInput = blockWord keys.first)
    (secondKey : start.registers rF = blockWord keys.second)
    (labelCells : ∀ i : Fin coordinateBitCount,
      start.ram (word (labelBase + (base + i.val))) = blockWord (lab i)) :
    Agree (WhiteInv start base lab record0 coordinateBitCount)
      (rtree (Prog.rep coordinateBitCount body) start)
      (interceptT bits (FreeQuery.vector coordinateBitCount fun i =>
        Programs.padM keys coordinate i false) record0) := by
  refine agree_rep_vector bits body (WhiteInv start base lab record0) coordinateBitCount _ ?_ record0
    start ⟨fun i bound => absurd bound (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  intro index values record memory holds
  obtain ⟨cells, frame, bitsSame, inputSame, factorSame, recordSame⟩ := holds
  subst recordSame
  have indexSmall : index.val < 254 := index.isLt
  rw [interceptT_clean bits _ (clean_padM bits keys coordinate index false), bodyIs]
  have labelCell : memory.ram (word (labelBase + (base + index.val))) = blockWord (lab index) := by
    rw [frame (word (labelBase + (base + index.val))) fun i small =>
      label_ne_white (base + index.val) (base + i) (by omega) (by omega), labelCells index]
  have agree := agree_whitenOne (base + index.val) (coordinate, index) (named index) memory keys
    (lab index) (inputSame.trans firstKey) (factorSame.trans secondKey) labelCell
  refine agree.map (fun value => (value, record)) fun pad after post => ?_
  obtain ⟨ram, bitsAfter, inputAfter, factorAfter⟩ := post
  refine ⟨fun i bound => ?_, fun address outside => ?_, bitsAfter.trans bitsSame,
    inputAfter.trans inputSame, factorAfter.trans factorSame, rfl⟩
  · rw [ram]
    by_cases last : i.val = index.val
    · have same : i = index := Fin.ext last
      subst same
      rw [Function.update_self]
      simp only [Vector.getElem_push_eq]
    · rw [Function.update_of_ne (white_ne base i.val index.val baseSmall i.isLt indexSmall last)]
      rw [Vector.getElem_push_lt (by omega)]
      exact cells i (by omega)
  · rw [ram, Function.update_of_ne (outside index.val (by omega)),
      frame address fun other small => outside other (by omega)]

/-- What the whitening leaves: the whitened labels of both coordinates. -/
def WhitenPost (mac : InputMac) (start : Memory) (record0 : DesignatedRecord)
    (result : (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) × DesignatedRecord)
    (after : Memory) : Prop :=
  (∀ i : Fin coordinateBitCount,
      after.ram (word (whiteBase + i.val)) = blockWord ((Programs.whitenMacOf result.1 mac).x.get i)) ∧
    (∀ i : Fin coordinateBitCount, after.ram (word (whiteBase + 254 + i.val)) =
      blockWord ((Programs.whitenMacOf result.1 mac).y.get i)) ∧
    (∀ address, (∀ i, i < 508 → address ≠ word (whiteBase + i)) →
      after.ram address = start.ram address) ∧
    after.bits = start.bits ∧ result.2 = record0

omit [FieldCertificate] in
theorem encIdx_x (i : Fin coordinateBitCount) : Replay.encIdx (0 + i.val) = (.x, i) := by
  have small : i.val < 254 := i.isLt
  unfold Replay.encIdx
  rw [if_pos (by omega)]
  exact Prod.ext rfl (Fin.ext (by simp only [Nat.zero_add]; exact Nat.mod_eq_of_lt small))

omit [FieldCertificate] in
theorem encIdx_y (i : Fin coordinateBitCount) : Replay.encIdx (254 + i.val) = (.y, i) := by
  have small : i.val < 254 := i.isLt
  unfold Replay.encIdx
  rw [if_neg (by omega)]
  exact Prod.ext rfl (Fin.ext (by show (254 + i.val) % 254 = i.val; omega))

theorem white_ne_y (first second : Nat) (firstSmall : first < 254) (secondSmall : second < 254) :
    word (whiteBase + first) ≠ word (whiteBase + (254 + second)) :=
  word_ne (by unfold whiteBase; omega) (by unfold whiteBase; omega) (by omega)

/-- **The whitening.** -/
theorem agree_whiten (bits : BitInput) (memory : Memory)
    (keys : WhiteningKeys) (mac : InputMac) (record0 : DesignatedRecord)
    (k1Cell : memory.ram (word tmpK1) = blockWord keys.first)
    (k2Cell : memory.ram (word tmpK2) = blockWord keys.second)
    (xLabels : ∀ i : Fin coordinateBitCount,
      memory.ram (word (labelBase + i.val)) = blockWord (mac.x.get i))
    (yLabels : ∀ i : Fin coordinateBitCount,
      memory.ram (word (labelBase + 254 + i.val)) = blockWord (mac.y.get i)) :
    Agree (WhitenPost mac memory record0) (rtree (Replay.whiten ordE0) memory)
      (interceptT bits (whitePadsM keys) record0) := by
  have cbc : coordinateBitCount = 254 := rfl
  unfold Replay.whiten
  rw [rtree_loadAt_seq, rtree_loadAt_seq]
  set loaded := setReg (setReg (setReg (setReg memory rAddr (word tmpK1)) rInput
    (memory.ram (word tmpK1))) rAddr (word tmpK2)) rF
    ((setReg (setReg memory rAddr (word tmpK1)) rInput (memory.ram (word tmpK1))).ram (word tmpK2))
    with loadedDef
  have loadedRam : loaded.ram = memory.ram := by simp only [loadedDef, setReg_ram]
  have loadedBits : loaded.bits = memory.bits := by simp only [loadedDef, setReg_bits]
  have firstKey : loaded.registers rInput = blockWord keys.first := by
    simp (config := {decide := true}) only [loadedDef, setReg_registers, setReg_ram, reduceIte]
    exact k1Cell
  have secondKey : loaded.registers rF = blockWord keys.second := by
    simp (config := {decide := true}) only [loadedDef, setReg_registers, setReg_ram, reduceIte]
    exact k2Cell
  rw [show labelCount = coordinateBitCount + coordinateBitCount from rfl, tree_rep_add]
  unfold whitePadsM
  simp only [TreeLaws.monad_bind, TreeLaws.monad_pure, interceptT_bind, interceptT]
  refine Agree.bindOpt (fun state middle firstPost => ?_)
    (agree_whitenHalf bits (Replay.whitenOne ordE0) 0 .x (fun i => mac.x.get i) keys loaded
      record0 (fun i => by rw [Nat.zero_add]) encIdx_x (by omega) firstKey secondKey
      (fun i => by rw [loadedRam, Nat.zero_add]; exact xLabels i))
  obtain ⟨xCells, xFrame, xBits, xInput, xFactor, xRecord⟩ := firstPost
  refine Agree.map _ (fun state' final secondPost => ?_)
    (agree_whitenHalf bits (fun index => Replay.whitenOne ordE0 (coordinateBitCount + index)) 254
      .y (fun i => mac.y.get i) keys middle state.2 (fun i => rfl) encIdx_y (by omega)
      (xInput.trans firstKey) (xFactor.trans secondKey) (fun i => by
        have small : i.val < 254 := i.isLt
        rw [xFrame (word (labelBase + (254 + i.val))) fun other bound =>
            label_ne_white (254 + i.val) (0 + other) (by omega) (by omega),
          loadedRam, ← Nat.add_assoc]
        exact yLabels i))
  obtain ⟨yCells, yFrame, yBits, _, _, yRecord⟩ := secondPost
  refine ⟨fun i => ?_, fun i => ?_, fun address outside => ?_, ?_, yRecord.trans xRecord⟩
  · have small : i.val < 254 := i.isLt
    rw [yFrame (word (whiteBase + i.val)) fun other bound => white_ne_y i.val other small bound]
    have cell := xCells i i.isLt
    rw [Nat.zero_add] at cell
    rw [cell]
    simp only [Programs.whitenMacOf, Vector.get_ofFn, encrypt]
    rfl
  · have cell := yCells i i.isLt
    rw [← Nat.add_assoc] at cell
    rw [cell]
    simp only [Programs.whitenMacOf, Vector.get_ofFn, encrypt]
    rfl
  · rw [yFrame address fun other bound => outside (254 + other) (by omega),
      xFrame address fun other bound => by
        have := outside other (by omega)
        rwa [Nat.zero_add], loadedRam]
  · rw [yBits, xBits, loadedBits]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
