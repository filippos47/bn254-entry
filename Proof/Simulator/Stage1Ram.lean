/-
**The memory stage 1 leaves.**

`storedMemory memory draw` is the memory after the four blocks of draws (field cells, exception
bytes, fold joins, key); `stage1Final memory draw` is the memory the whole stage-1 program leaves:
the stored RAM, every register zero, and the serialized wire on stack `3`.

`ram_field`, `ram_byte`, `ram_hot`, `ram_key` read the stored cells back, and
`extractSource_final`: the retained RAM reads back as the drawn source.
-/

import Proof.Simulator.Stage1Serialize
import Proof.Simulator.CutoffSource

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-- The stage-1 draws, in the machine's order. -/
abbrev Stage1Draw := (Fin fieldCellCount → BaseField) × (Fin exceptionByteCount → Nat) ×
  (Fin hotBlockCount → Nat) × (Fin keyBlockCount → Nat)

/-- The source a stage-1 draw publishes and retains. -/
def drawSource (draw : Stage1Draw) : Stage1Source :=
  sourceOfDraws (total 0 draw.1) (total 0 draw.2.1) (total 0 draw.2.2.1) (total 0 draw.2.2.2)

section Memory

variable [FieldCertificate]

/-- The memory after the four blocks of draws. -/
def storedMemory (memory : Memory) (draw : Stage1Draw) : Memory :=
  foldStore (wordStep keyBase) keyBlockCount
    (foldStore (wordStep hotBase) hotBlockCount
      (foldStore (wordStep exceptionBase) exceptionByteCount
        (foldStore (cellStep fieldBase) fieldCellCount memory draw.1) draw.2.1) draw.2.2.1)
    draw.2.2.2

/- `storedMemory` is sealed, as `foldStore` is. -/
attribute [irreducible] storedMemory

/-- **The memory stage 1 leaves.** -/
def stage1Final (memory : Memory) (draw : Stage1Draw) : Memory where
  bits := Function.update memory.bits 3 (serialBits (storedMemory memory draw).ram ++ memory.bits 3)
  registers := fun _ => 0
  ram := (storedMemory memory draw).ram

theorem stage1Final_ram (memory : Memory) (draw : Stage1Draw) :
    (stage1Final memory draw).ram = (storedMemory memory draw).ram := by
  unfold stage1Final
  rfl

theorem stage1Final_bits (memory : Memory) (draw : Stage1Draw) :
    (stage1Final memory draw).bits = Function.update memory.bits 3
      (serialBits (storedMemory memory draw).ram ++ memory.bits 3) := by
  unfold stage1Final
  rfl

theorem stage1Final_registers (memory : Memory) (draw : Stage1Draw) :
    (stage1Final memory draw).registers = fun _ => 0 := by
  unfold stage1Final
  rfl

theorem storedMemory_bits (memory : Memory) (draw : Stage1Draw) :
    (storedMemory memory draw).bits = memory.bits := by
  unfold storedMemory
  rw [foldStore_bits _ (wordStep_bits keyBase), foldStore_bits _ (wordStep_bits hotBase),
    foldStore_bits _ (wordStep_bits exceptionBase), foldStore_bits _ (cellStep_bits fieldBase)]

/-! ### The regions -/

theorem regions :
    fieldBase + fieldCellCount ≤ exceptionBase ∧ exceptionBase + exceptionByteCount ≤ hotBase ∧
      hotBase + hotBlockCount ≤ keyBase ∧ keyBase + keyBlockCount < 2 ^ 256 := by
  refine ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.lt_of_succ_le (Nat.le_of_ble_eq_true rfl)⟩

theorem word_ne {first second : Nat} (firstSmall : first < 2 ^ 256) (secondSmall : second < 2 ^ 256)
    (different : first ≠ second) : word first ≠ word second :=
  fun same => different (word_injective firstSmall secondSmall same)

/-- Distinct addresses in a region. -/
theorem region_distinct (base count : Nat) (small : base + count < 2 ^ 256) (first second : Nat)
    (firstBound : first < count) (secondBound : second < count) (different : first ≠ second) :
    word (base + first) ≠ word (base + second) :=
  word_ne (by omega) (by omega) (by omega)

/-- An address below a region's base is outside it. -/
theorem region_away (target base count : Nat) (below : target < base)
    (small : base + count < 2 ^ 256) (index : Nat) (bound : index < count) :
    word target ≠ word (base + index) :=
  word_ne (by omega) (by omega) (by omega)

/-! ### Reading the stored cells -/

/-- A block of stored field cells holds its draws. -/
theorem cells_ram_at (base count : Nat) (small : base + count < 2 ^ 256) (memory : Memory)
    (values : Fin count → BaseField) (index : Fin count) :
    (foldStore (cellStep base) count memory values).ram (word (base + index.val)) =
      BitVec.ofNat 256 (values index).val :=
  foldStore_ram_at (cellStep base) (fun index => word (base + index))
    (fun value : BaseField => BitVec.ofNat 256 value.val) (cellStep_ram base) count
    (region_distinct base count small) memory values index

/-- A block of stored words holds its draws. -/
theorem words_ram_at (base count : Nat) (small : base + count < 2 ^ 256) (memory : Memory)
    (values : Fin count → Nat) (index : Fin count) :
    (foldStore (wordStep base) count memory values).ram (word (base + index.val)) =
      BitVec.ofNat 256 (values index) :=
  foldStore_ram_at (wordStep base) (fun index => word (base + index))
    (fun value => BitVec.ofNat 256 value) (wordStep_ram base) count
    (region_distinct base count small) memory values index

/-- A block of stored words leaves the RAM below its base. -/
theorem words_ram_off (base count : Nat) (small : base + count < 2 ^ 256) (memory : Memory)
    (values : Fin count → Nat) (target : Nat) (below : target < base) :
    (foldStore (wordStep base) count memory values).ram (word target) = memory.ram (word target) :=
  foldStore_ram_off (wordStep base) (fun index => word (base + index))
    (fun value => BitVec.ofNat 256 value) (wordStep_ram base) count memory values (word target)
    (region_away target base count below small)

theorem ram_key (memory : Memory) (draw : Stage1Draw) (index : Fin keyBlockCount) :
    (storedMemory memory draw).ram (word (keyBase + index.val)) =
      BitVec.ofNat 256 (draw.2.2.2 index) := by
  obtain ⟨_, _, _, top⟩ := regions
  unfold storedMemory
  exact words_ram_at keyBase keyBlockCount top _ _ index

theorem ram_hot (memory : Memory) (draw : Stage1Draw) (index : Fin hotBlockCount) :
    (storedMemory memory draw).ram (word (hotBase + index.val)) =
      BitVec.ofNat 256 (draw.2.2.1 index) := by
  obtain ⟨_, _, hotKey, top⟩ := regions
  have bound := index.isLt
  unfold storedMemory
  rw [words_ram_off keyBase keyBlockCount top _ _ _ (by omega)]
  exact words_ram_at hotBase hotBlockCount (by omega) _ _ index

theorem ram_byte (memory : Memory) (draw : Stage1Draw) (index : Fin exceptionByteCount) :
    (storedMemory memory draw).ram (word (exceptionBase + index.val)) =
      BitVec.ofNat 256 (draw.2.1 index) := by
  obtain ⟨_, byteHot, hotKey, top⟩ := regions
  have bound := index.isLt
  unfold storedMemory
  rw [words_ram_off keyBase keyBlockCount top _ _ _ (by omega),
    words_ram_off hotBase hotBlockCount (by omega) _ _ _ (by omega)]
  exact words_ram_at exceptionBase exceptionByteCount (by omega) _ _ index

theorem ram_field (memory : Memory) (draw : Stage1Draw) (index : Fin fieldCellCount) :
    (storedMemory memory draw).ram (word (fieldBase + index.val)) =
      BitVec.ofNat 256 (draw.1 index).val := by
  obtain ⟨fieldByte, byteHot, hotKey, top⟩ := regions
  have bound := index.isLt
  unfold storedMemory
  rw [words_ram_off keyBase keyBlockCount top _ _ _ (by omega),
    words_ram_off hotBase hotBlockCount (by omega) _ _ _ (by omega),
    words_ram_off exceptionBase exceptionByteCount (by omega) _ _ _ (by omega)]
  exact cells_ram_at fieldBase fieldCellCount (by omega) _ _ index

/-! ### The retained source -/

theorem ofNat_mod_256 (width value : Nat) (small : width ≤ 256) :
    BitVec.ofNat width (value % 2 ^ 256) = BitVec.ofNat width value := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 small)

/-- Two readings of draws agree when they agree on the drawn indices. -/
theorem sourceOfDraws_congr (cells cells' : Nat → BaseField) (bytes bytes' hot hot' key key' : Nat → Nat)
    (sameCells : ∀ index, index < fieldCellCount → cells index = cells' index)
    (sameBytes : ∀ index, index < exceptionByteCount →
      BitVec.ofNat 8 (bytes index) = BitVec.ofNat 8 (bytes' index))
    (sameHot : ∀ index, index < hotBlockCount →
      BitVec.ofNat 128 (hot index) = BitVec.ofNat 128 (hot' index))
    (sameKey : ∀ index, index < keyBlockCount →
      BitVec.ofNat 128 (key index) = BitVec.ofNat 128 (key' index)) :
    sourceOfDraws cells bytes hot key = sourceOfDraws cells' bytes' hot' key' := by
  have cellCount := fieldCellCount_eq
  apply stage1Source_ext
  · show (cells 0, cells 1, cells 2) = (cells' 0, cells' 1, cells' 2)
    rw [sameCells 0 (by omega), sameCells 1 (by omega), sameCells 2 (by omega)]
  · apply Vector.ext
    intro digit bound
    have small : digit < 91 := bound
    simp only [sourceOfDraws, Vector.getElem_ofFn]
    rw [sameCells _ (by omega), sameCells (3 + 11 * digit + 1) (by omega),
      sameCells (3 + 11 * digit + 2) (by omega), sameCells (3 + 11 * digit + 3) (by omega),
      sameCells (3 + 11 * digit + 4) (by omega), sameCells (3 + 11 * digit + 5) (by omega),
      sameCells (3 + 11 * digit + 6) (by omega), sameCells (3 + 11 * digit + 7) (by omega),
      sameCells (3 + 11 * digit + 8) (by omega), sameCells (3 + 11 * digit + 9) (by omega),
      sameCells (3 + 11 * digit + 10) (by omega)]
  · apply Vector.ext
    intro digit bound
    apply Vector.ext
    intro slot slotBound
    have small : digit < 91 := bound
    simp only [sourceOfDraws, Vector.getElem_ofFn]
    exact sameBytes _ (by unfold exceptionByteCount; omega)
  · apply Vector.ext
    intro chunk bound
    have small : chunk < 198 := bound
    simp only [sourceOfDraws, Vector.getElem_ofFn]
    exact sameHot _ (by unfold hotBlockCount; omega)
  · apply Vector.ext
    intro chunk bound
    have small : chunk < 198 := bound
    simp only [sourceOfDraws, Vector.getElem_ofFn]
    exact sameHot _ (by unfold hotBlockCount; omega)
  · apply Vector.ext
    intro chunk bound
    have small : chunk < 198 := bound
    simp only [sourceOfDraws, Vector.getElem_ofFn]
    exact sameHot _ (by unfold hotBlockCount; omega)
  · apply Vector.ext
    intro chunk bound
    have small : chunk < 198 := bound
    simp only [sourceOfDraws, Vector.getElem_ofFn]
    exact sameHot _ (by unfold hotBlockCount; omega)
  · funext chunk slot
    have chunkSmall : chunk.val < 56 := chunk.isLt
    have slotSmall : slot.val < 733 := slot.isLt
    exact sameCells _ (by omega)
  · apply inputMacKey_ext
    · apply Vector.ext
      intro bit bound
      have small : bit < 254 := bound
      simp only [sourceOfDraws, Vector.getElem_ofFn]
      rw [sameKey (2 * bit) (by unfold keyBlockCount; omega),
        sameKey (2 * bit + 1) (by unfold keyBlockCount; omega)]
    · apply Vector.ext
      intro bit bound
      have small : bit < 254 := bound
      simp only [sourceOfDraws, Vector.getElem_ofFn]
      rw [sameKey (2 * (254 + bit)) (by unfold keyBlockCount; omega),
        sameKey (2 * (254 + bit) + 1) (by unfold keyBlockCount; omega)]

/-- **The retained RAM reads back as the drawn source.** -/
theorem extractSource_final (memory : Memory) (draw : Stage1Draw) :
    extractSource (stage1Final memory draw) = drawSource draw := by
  unfold extractSource drawSource
  rw [stage1Final_ram]
  apply sourceOfDraws_congr
  · intro index bound
    rw [total_apply _ _ _ bound,
      show fieldBase + index = fieldBase + (⟨index, bound⟩ : Fin fieldCellCount).val from rfl,
      ram_field]
    unfold wordField
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans (draw.1 ⟨index, bound⟩).val_lt
      (by unfold baseFieldModulus; norm_num)), ZMod.natCast_zmod_val]
  · intro index bound
    rw [total_apply _ _ _ bound, show exceptionBase + index =
      exceptionBase + (⟨index, bound⟩ : Fin exceptionByteCount).val from rfl, ram_byte,
      BitVec.toNat_ofNat, ofNat_mod_256 8 _ (by norm_num)]
  · intro index bound
    rw [total_apply _ _ _ bound,
      show hotBase + index = hotBase + (⟨index, bound⟩ : Fin hotBlockCount).val from rfl,
      ram_hot, BitVec.toNat_ofNat, ofNat_mod_256 128 _ (by norm_num)]
  · intro index bound
    rw [total_apply _ _ _ bound,
      show keyBase + index = keyBase + (⟨index, bound⟩ : Fin keyBlockCount).val from rfl,
      ram_key, BitVec.toNat_ofNat, ofNat_mod_256 128 _ (by norm_num)]

end Memory

end

end Kriterion.ArgoMAC.PlanB.SimMachine
