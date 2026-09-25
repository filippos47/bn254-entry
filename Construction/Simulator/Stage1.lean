/-
Stage 1 of the Plan B simulator: sample the complete public value with every scale mask
uniform, keep it in RAM, and emit its canonical `Wire.encoding` bytes.

* `34,295` field cells (curve, rows, the `52 · 642` scale joins), each by constant-time bounded
  rejection over 254 coins with `attempts = 256` tries, aborting on exhaustion;
* `1,092` three-bit exception cells, `808` fold-join blocks and the `1016`-block Lamport key, each
  from fair coins (the key is retained for stage 2, which selects one label per input bit);
* the serializer pushes the `8,804,168` wire bits in reverse, most significant bit of each word
  first, so the response stack reads the encoding least significant bit first; the curve-and-rows
  word and each chunk word are built as base-`p` numbers in a limb scratch and pushed limb by
  limb, and the gadget word's four zero bits are read from that (zero) scratch;
* every register is zeroed at the end, so the retained state is a function of RAM and stacks.

Stage 1 contains no oracle instruction at all.
-/

import Construction.Simulator.BigInt

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine Blocks

namespace Stage1

/-- One uniform field cell at `address`. -/
def fieldCell (address : Nat) : Prog :=
  .seq (bounded fieldWidth (testBelow pNat) attempts (storeAt address rOut)) (zeroRegs samplerScratch)

/-- One uniform word of `width` coins at `address`. -/
def wordCell (width address : Nat) : Prog :=
  .seq (sampleWord width) (.seq (storeAt address rAcc) (zeroRegs [rAcc, rBit, rAddr]))

/-- All field cells, in RAM order. -/
def fields : Prog := Prog.rep fieldCellCount fun index => fieldCell (fieldBase + index)

/-- All exception bytes. -/
def bytes : Prog := Prog.rep exceptionByteCount fun index => wordCell 3 (exceptionBase + index)

/-- All fold-join blocks. -/
def blocks : Prog := Prog.rep hotBlockCount fun index => wordCell 128 (hotBase + index)

/-- The Lamport key: `1016` uniform blocks (P3's `Stage1Source.key`). -/
def key : Prog := Prog.rep keyBlockCount fun index => wordCell 128 (keyBase + index)

/-- Clear the serializer's limb scratch. -/
def clearLimbs : Prog :=
  .seq (cst rAcc 0) (Prog.rep serialLimbCount fun index => storeAt (serialLimbBase + index) rAcc)

/-- The chunk word counted from the top (`chunk = 0` is the last word): its `642` scale cells as
one base-`p` number, built by the big-integer Horner encoder (`BigInt.macPasses`, from zero limbs)
in the limb scratch, then emitted top limb first (`636` limbs of `256` bits from the top down),
then the scratch is cleared. -/
def serializeChunk (chunk : Nat) : Prog :=
  .seq BigInt.setup
    (.seq (BigInt.macPasses serialLimbBase serialLimbCount 642
        (fieldBase + curveCellCount + rowCellCount + 642 * (51 - chunk)))
      (.seq (emitWord (serialLimbBase + (chunkLimbCount - 1)) topLimbBits)
        (.seq (Prog.rep (chunkLimbCount - 1) fun index =>
            emitWord (serialLimbBase + (chunkLimbCount - 2) - index) 256)
          clearLimbs)))

/-- The curve-and-rows word: its `911` cells as one base-`p` number, built by the big-integer
Horner encoder in the limb scratch, then emitted top limb first (`120` bits, then `902` limbs of
`256` bits from the top down), then the scratch is cleared. -/
def serializeFields : Prog :=
  .seq BigInt.setup
    (.seq (BigInt.macPasses serialLimbBase serialLimbCount (curveCellCount + rowCellCount) fieldBase)
      (.seq (emitWord (serialLimbBase + (fieldsLimbCount - 1)) fieldsTopLimbBits)
        (.seq (Prog.rep (fieldsLimbCount - 1) fun index =>
            emitWord (serialLimbBase + (fieldsLimbCount - 2) - index) 256)
          clearLimbs)))

/-- The serializer, in reverse wire order: the `52` scale words, fold joins (128), the gadget
word (its four zero padding bits, read from the zero limb scratch, then its `1092` cells as `3`
bits), then the curve-and-rows word (`serializeFields`). -/
def serialize : Prog :=
  .seq (Prog.rep 52 serializeChunk)
    (.seq (Prog.rep hotBlockCount fun index => emitWord (hotBase + hotBlockCount - 1 - index) 128)
      (.seq (.seq (emitWord serialLimbBase 4)
          (Prog.rep exceptionByteCount fun index =>
            emitWord (exceptionBase + exceptionByteCount - 1 - index) 3))
        serializeFields))

/-- **Stage 1.** -/
def program : Prog :=
  .seq fields (.seq bytes (.seq blocks (.seq key (.seq serialize (zeroRegs allRegisters)))))

/-! ### Sizes and costs -/

theorem size_fieldCell (address : Nat) : (fieldCell address).size = 457231 := by
  simp only [fieldCell, Prog.size]
  rw [size_bounded _ _ _ _ (by rw [cost_storeAt]; omega), size_zeroRegs]
  rfl

theorem cost_fieldCell (address : Nat) : (fieldCell address).cost = 327180 := by
  simp only [fieldCell, Prog.cost]
  rw [cost_bounded _ _ _ _ (by rw [cost_storeAt]; omega), cost_zeroRegs]
  rfl

theorem size_wordCell (width address : Nat) : (wordCell width address).size = 6 + 7 * width := by
  simp only [wordCell, Prog.size, size_sampleWord, size_storeAt, size_zeroRegs, List.length_cons,
    List.length_nil]
  omega

theorem cost_wordCell (width address : Nat) : (wordCell width address).cost = 6 + 5 * width := by
  simp only [wordCell, Prog.cost, cost_sampleWord, cost_storeAt, cost_zeroRegs, List.length_cons,
    List.length_nil]
  omega

theorem size_fields : fields.size = fieldCellCount * 457231 :=
  Prog.size_rep _ _ _ fun _ _ => size_fieldCell _

theorem cost_fields : fields.cost = fieldCellCount * 327180 :=
  Prog.cost_rep _ _ _ fun _ _ => cost_fieldCell _

theorem size_bytes : bytes.size = exceptionByteCount * 27 :=
  Prog.size_rep _ _ _ fun _ _ => size_wordCell _ _

theorem cost_bytes : bytes.cost = exceptionByteCount * 21 :=
  Prog.cost_rep _ _ _ fun _ _ => cost_wordCell _ _

theorem size_blocks : blocks.size = hotBlockCount * 902 :=
  Prog.size_rep _ _ _ fun _ _ => size_wordCell _ _

theorem cost_blocks : blocks.cost = hotBlockCount * 646 :=
  Prog.cost_rep _ _ _ fun _ _ => cost_wordCell _ _

theorem size_key : key.size = keyBlockCount * 902 :=
  Prog.size_rep _ _ _ fun _ _ => size_wordCell _ _

theorem cost_key : key.cost = keyBlockCount * 646 :=
  Prog.cost_rep _ _ _ fun _ _ => cost_wordCell _ _

/-- One chunk word's code: setup, the Horner encoder, the limb emission, the clear. -/
def serializeChunkCount : Nat :=
  4 + BigInt.macPassesCost serialLimbCount 642 + (2 + 3 * topLimbBits) +
    (chunkLimbCount - 1) * (2 + 3 * 256) + (1 + serialLimbCount * 2)

/-- The curve-and-rows word's code: setup, the Horner encoder, the limb emission, the clear. -/
def serializeFieldsCount : Nat :=
  4 + BigInt.macPassesCost serialLimbCount (curveCellCount + rowCellCount) +
    (2 + 3 * fieldsTopLimbBits) + (fieldsLimbCount - 1) * (2 + 3 * 256) +
    (1 + serialLimbCount * 2)

/-- The serializer's size equals its cost: it is straight-line code. -/
def serializeCount : Nat :=
  52 * serializeChunkCount + hotBlockCount * (2 + 3 * 128) +
    ((2 + 3 * 4) + exceptionByteCount * (2 + 3 * 3)) + serializeFieldsCount

theorem size_clearLimbs : clearLimbs.size = 1 + serialLimbCount * 2 := by
  unfold clearLimbs
  rw [Prog.size_seq, size_cst, Prog.size_rep _ _ _ fun _ _ => size_storeAt _ _]

theorem cost_clearLimbs : clearLimbs.cost = 1 + serialLimbCount * 2 := by
  unfold clearLimbs
  rw [Prog.cost_seq, cost_cst, Prog.cost_rep _ _ _ fun _ _ => cost_storeAt _ _]

theorem size_serializeChunk (chunk : Nat) :
    (serializeChunk chunk).size = serializeChunkCount := by
  unfold serializeChunk serializeChunkCount
  rw [Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_seq, BigInt.size_setup,
    BigInt.size_macPasses, size_emitWord, Prog.size_rep _ _ _ fun _ _ => size_emitWord _ _,
    size_clearLimbs]
  omega

theorem cost_serializeChunk (chunk : Nat) :
    (serializeChunk chunk).cost = serializeChunkCount := by
  unfold serializeChunk serializeChunkCount
  rw [Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, BigInt.cost_setup,
    BigInt.cost_macPasses, cost_emitWord, Prog.cost_rep _ _ _ fun _ _ => cost_emitWord _ _,
    cost_clearLimbs]
  omega

theorem size_serializeFields : serializeFields.size = serializeFieldsCount := by
  unfold serializeFields serializeFieldsCount
  rw [Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_seq, BigInt.size_setup,
    BigInt.size_macPasses, size_emitWord, Prog.size_rep _ _ _ fun _ _ => size_emitWord _ _,
    size_clearLimbs]
  omega

theorem cost_serializeFields : serializeFields.cost = serializeFieldsCount := by
  unfold serializeFields serializeFieldsCount
  rw [Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, BigInt.cost_setup,
    BigInt.cost_macPasses, cost_emitWord, Prog.cost_rep _ _ _ fun _ _ => cost_emitWord _ _,
    cost_clearLimbs]
  omega

theorem size_serialize : serialize.size = serializeCount := by
  unfold serialize serializeCount
  rw [Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_seq, size_emitWord,
    Prog.size_rep _ _ _ fun _ _ => size_serializeChunk _,
    Prog.size_rep _ _ _ fun _ _ => size_emitWord _ _,
    Prog.size_rep _ _ _ fun _ _ => size_emitWord _ _, size_serializeFields]
  omega

theorem cost_serialize : serialize.cost = serializeCount := by
  unfold serialize serializeCount
  rw [Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, cost_emitWord,
    Prog.cost_rep _ _ _ fun _ _ => cost_serializeChunk _,
    Prog.cost_rep _ _ _ fun _ _ => cost_emitWord _ _,
    Prog.cost_rep _ _ _ fun _ _ => cost_emitWord _ _, cost_serializeFields]
  omega

theorem size_program : program.size =
    fieldCellCount * 457231 + exceptionByteCount * 27 + hotBlockCount * 902 +
      keyBlockCount * 902 + serializeCount + 16 := by
  unfold program
  rw [Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_seq, size_fields,
    size_bytes, size_blocks, size_key, size_serialize, size_zeroRegs, allRegisters,
    List.length_finRange]
  omega

theorem cost_program : program.cost =
    fieldCellCount * 327180 + exceptionByteCount * 21 + hotBlockCount * 646 +
      keyBlockCount * 646 + serializeCount + 16 := by
  unfold program
  rw [Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, cost_fields,
    cost_bytes, cost_blocks, cost_key, cost_serialize, cost_zeroRegs, allRegisters,
    List.length_finRange]
  omega

end Stage1

end Kriterion.ArgoMAC.PlanB.SimMachine
