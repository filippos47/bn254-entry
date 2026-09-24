/-
**The replay, the bridge** (`agree_bridge`): the bridge value
`t = c0 + c1 x³ + c2 y² + x3 x² + y4 y + x5 x + y6 + x7` (`CurveMembership.evaluate`) from the curve
constants and the curve lanes' accumulators, moved out of the scale range (`rtree_moveOut`:
`bridgeInput t`), one hash query, and the two keys stored at `tmpK1`, `tmpK2`.
-/

import Proof.Simulator.ReplayLane

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-- What the bridge leaves: the two hash keys. -/
def BridgePost (memory : Memory) (keys : Block × Block) (after : Memory) : Prop :=
  after.ram = Function.update (Function.update memory.ram (word tmpK1) (blockWord keys.1))
    (word tmpK2) (blockWord keys.2) ∧ after.bits = memory.bits

/-- **The move out of the scale range**: `rInput ← t + [t < 2 ^ 150] · 2 ^ 150 = bridgeInput t`. -/
theorem rtree_moveOut (t : BaseField) (rest : Prog) (memory : Memory)
    (input : memory.registers rInput = fieldWord t) :
    rtree (.seq (cst rAcc scaleRange) (.seq (ar .less rSel rInput rAcc)
        (.seq (ar .mul rSel rSel rAcc) (.seq (ar .add rInput rInput rSel) rest)))) memory =
      rtree rest (setReg (setReg (setReg (setReg memory rAcc (word scaleRange)) rSel
        (word (if t.val < scaleRange then 1 else 0))) rSel
        (word ((if t.val < scaleRange then 1 else 0) * scaleRange))) rInput
        (fieldWord (bridgeInput t))) := by
  have small : t.val < 2 ^ 256 := lt_trans t.val_lt (by unfold baseFieldModulus; norm_num)
  have rangeSmall : scaleRange < 2 ^ 256 := by unfold scaleRange; norm_num
  rw [rtree_cst_seq,
    rtree_ar_val _ _ _ _ _ _ (word t.val) (word scaleRange)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte, input]; rfl)
      (reg_same _ _ _),
    BigInt.eval_less_word, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt rangeSmall,
    rtree_ar_val _ _ _ _ _ _ (word (if t.val < scaleRange then 1 else 0)) (word scaleRange)
      (reg_same _ _ _) (by simp (config := {decide := true}) only [setReg_registers, reduceIte]),
    BigInt.eval_mul_word,
    rtree_ar_val _ _ _ _ _ _ (word t.val) (word ((if t.val < scaleRange then 1 else 0) * scaleRange))
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte, input]; rfl)
      (reg_same _ _ _),
    BigInt.eval_add_word]
  have moved : word (t.val + (if t.val < scaleRange then 1 else 0) * scaleRange) =
      fieldWord (bridgeInput t) := by
    unfold fieldWord
    rw [bridgeInput_val]
    split_ifs <;> simp
  rw [moved]

/-- **The bridge.** -/
theorem agree_bridge (memory : Memory) (x y c0 c1 c2 x3 x5 x7 y4 y6 : BaseField)
    (xCell : memory.ram (word reqX) = fieldWord x) (yCell : memory.ram (word reqY) = fieldWord y)
    (c0Cell : memory.ram (word fieldBase) = fieldWord c0)
    (c1Cell : memory.ram (word (fieldBase + 1)) = fieldWord c1)
    (c2Cell : memory.ram (word (fieldBase + 2)) = fieldWord c2)
    (x3Cell : memory.ram (word (accBase + 455)) = fieldWord x3)
    (y4Cell : memory.ram (word (accBase + 731)) = fieldWord y4)
    (x5Cell : memory.ram (word (accBase + 456)) = fieldWord x5)
    (y6Cell : memory.ram (word (accBase + 732)) = fieldWord y6)
    (x7Cell : memory.ram (word (accBase + 457)) = fieldWord x7) :
    Agree (BridgePost memory) (rtree Replay.bridge memory)
      (Programs.askHash (bridgeInput
        (c0 + c1 * x ^ 3 + c2 * y ^ 2 + x3 * x ^ 2 + y4 * y + x5 * x + y6 + x7))) := by
  unfold Replay.bridge
  simp only [Prog.seqList]
  rw [rtree_loadAt_seq, xCell, rtree_loadAt_seq]
  simp only [setReg_ram, yCell]
  rw [rtree_ar_val _ _ _ _ _ _ (fieldWord x) (fieldWord x)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte])
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _ (fieldWord (x * x)) (fieldWord x) (reg_same _ _ _)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _ (fieldWord y) (fieldWord y)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte])
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_loadAt_seq]
  simp only [setReg_ram, c0Cell]
  rw [rtree_loadAt_seq]
  simp only [setReg_ram, c1Cell]
  rw [rtree_ar_val _ _ _ _ _ _ (fieldWord c1) (fieldWord (x * x * x)) (reg_same _ _ _)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _ (fieldWord c0) (fieldWord (c1 * (x * x * x)))
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words, rtree_loadAt_seq]
  simp only [setReg_ram, c2Cell]
  rw [rtree_ar_val _ _ _ _ _ _ (fieldWord c2) (fieldWord (y * y)) (reg_same _ _ _)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _ (fieldWord (c0 + c1 * (x * x * x))) (fieldWord (c2 * (y * y)))
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words, rtree_loadAt_seq]
  simp only [setReg_ram, x3Cell]
  rw [rtree_ar_val _ _ _ _ _ _ (fieldWord x3) (fieldWord (x * x)) (reg_same _ _ _)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _ (fieldWord (c0 + c1 * (x * x * x) + c2 * (y * y))) (fieldWord (x3 * (x * x)))
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words, rtree_loadAt_seq]
  simp only [setReg_ram, y4Cell]
  rw [rtree_ar_val _ _ _ _ _ _ (fieldWord y4) (fieldWord y) (reg_same _ _ _)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _ (fieldWord (c0 + c1 * (x * x * x) + c2 * (y * y) + x3 * (x * x)))
      (fieldWord (y4 * y))
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words, rtree_loadAt_seq]
  simp only [setReg_ram, x5Cell]
  rw [rtree_ar_val _ _ _ _ _ _ (fieldWord x5) (fieldWord x) (reg_same _ _ _)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _
      (fieldWord (c0 + c1 * (x * x * x) + c2 * (y * y) + x3 * (x * x) + y4 * y)) (fieldWord (x5 * x))
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words, rtree_loadAt_seq]
  simp only [setReg_ram, y6Cell]
  rw [rtree_ar_val _ _ _ _ _ _
      (fieldWord (c0 + c1 * (x * x * x) + c2 * (y * y) + x3 * (x * x) + y4 * y + x5 * x))
      (fieldWord y6)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words, rtree_loadAt_seq]
  simp only [setReg_ram, x7Cell]
  rw [rtree_ar_val _ _ _ _ _ _
      (fieldWord (c0 + c1 * (x * x * x) + c2 * (y * y) + x3 * (x * x) + y4 * y + x5 * x + y6))
      (fieldWord x7)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words]
  have same : c0 + c1 * (x * x * x) + c2 * (y * y) + x3 * (x * x) + y4 * y + x5 * x + y6 + x7 =
      c0 + c1 * x ^ 3 + c2 * y ^ 2 + x3 * x ^ 2 + y4 * y + x5 * x + y6 + x7 := by ring
  rw [same, rtree_moveOut _ _ _ (reg_same _ _ _)]
  refine Agree.query 4 rIndex rInput rFirst rSecond _ _
    (by rw [reg_same, query_hash, fieldWord_cast]) _ _
    fun keys => ?_
  refine .leaf ⟨?_, ?_⟩
  · show (storeRam (setReg (storeRam (setReg _ rAddr (word tmpK1)) (word tmpK1) _) rAddr
      (word tmpK2)) (word tmpK2) _).ram = _
    simp only [storeRam_ram, setReg_ram, writePair_ram, writePair_registers, setReg_registers,
      storeRam_registers]
    simp (config := {decide := true}) only [reduceIte]
    rfl
  · show (storeRam (setReg (storeRam (setReg _ rAddr (word tmpK1)) (word tmpK1) _) rAddr
      (word tmpK2)) (word tmpK2) _).bits = _
    simp only [storeRam_bits, setReg_bits, writePair_bits]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
