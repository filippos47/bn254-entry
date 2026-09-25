/-
Stage 1 of the Plan B simulator: sample the complete public value with every scale mask
uniform, keep it in RAM, and emit its canonical `Wire.encoding` bytes.

* `33,660` field cells (curve, rows, the `52 · 642` scale joins), each by constant-time bounded
  rejection over 254 coins with `attempts = 256` tries, aborting on exhaustion;
* `1,092` exception bytes, `808` fold-join blocks and the `1016`-block Lamport key, each from fair
  coins (the key is retained for stage 2, which selects one label per input bit);
* the serializer pushes the `8,825,632` wire bits in reverse, most significant bit of each cell
  first, so the response stack reads the encoding least significant bit first; each chunk word's
  four zero bits are two explicit zeros and the two top bits of its last cell, pushed as `256`
  bits;
* every register is zeroed at the end, so the retained state is a function of RAM and stacks.

Stage 1 contains no oracle instruction at all.
-/

import Construction.Simulator.Blocks

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
def bytes : Prog := Prog.rep exceptionByteCount fun index => wordCell 8 (exceptionBase + index)

/-- All fold-join blocks. -/
def blocks : Prog := Prog.rep hotBlockCount fun index => wordCell 128 (hotBase + index)

/-- The Lamport key: `1016` uniform blocks (P3's `Stage1Source.key`). -/
def key : Prog := Prog.rep keyBlockCount fun index => wordCell 128 (keyBase + index)

/-- The scale cells of one chunk word, counted from the top (`chunk = 0` is the last word): the
word's two top zero bits, its last slot as `256` bits (a field cell is below `2 ^ 254`, so its
two top bits are the word's other two zero bits), then its other `641` slots as `254` bits
each. -/
def serializeChunk (chunk : Nat) : Prog :=
  .seq (.op (.push 3 false)) (.seq (.op (.push 3 false))
    (.seq (emitWord (fieldBase + fieldCellCount - 1 - 642 * chunk) 256)
      (Prog.rep 641 fun index =>
        emitWord (fieldBase + fieldCellCount - 1 - 642 * chunk - 1 - index) 254)))

/-- The serializer, in reverse wire order: the `52` scale words, fold joins (128), exception
bytes (8), then rows and curve (256 bits each). -/
def serialize : Prog :=
  .seq (Prog.rep 52 serializeChunk)
    (.seq (Prog.rep hotBlockCount fun index => emitWord (hotBase + hotBlockCount - 1 - index) 128)
      (.seq (Prog.rep exceptionByteCount fun index =>
          emitWord (exceptionBase + exceptionByteCount - 1 - index) 8)
        (Prog.rep (curveCellCount + rowCellCount) fun index =>
          emitWord (fieldBase + curveCellCount + rowCellCount - 1 - index) 256)))

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

theorem size_bytes : bytes.size = exceptionByteCount * 62 :=
  Prog.size_rep _ _ _ fun _ _ => size_wordCell _ _

theorem cost_bytes : bytes.cost = exceptionByteCount * 46 :=
  Prog.cost_rep _ _ _ fun _ _ => cost_wordCell _ _

theorem size_blocks : blocks.size = hotBlockCount * 902 :=
  Prog.size_rep _ _ _ fun _ _ => size_wordCell _ _

theorem cost_blocks : blocks.cost = hotBlockCount * 646 :=
  Prog.cost_rep _ _ _ fun _ _ => cost_wordCell _ _

theorem size_key : key.size = keyBlockCount * 902 :=
  Prog.size_rep _ _ _ fun _ _ => size_wordCell _ _

theorem cost_key : key.cost = keyBlockCount * 646 :=
  Prog.cost_rep _ _ _ fun _ _ => cost_wordCell _ _

/-- The serializer's size equals its cost: it is straight-line code. -/
def serializeCount : Nat :=
  52 * (2 + (2 + 3 * 256) + 641 * (2 + 3 * 254)) + hotBlockCount * (2 + 3 * 128) +
    exceptionByteCount * (2 + 3 * 8) + (curveCellCount + rowCellCount) * (2 + 3 * 256)

theorem size_serializeChunk (chunk : Nat) :
    (serializeChunk chunk).size = 2 + (2 + 3 * 256) + 641 * (2 + 3 * 254) := by
  unfold serializeChunk
  rw [Prog.size_seq, Prog.size_seq, Prog.size_seq, size_emitWord,
    Prog.size_rep _ _ _ fun _ _ => size_emitWord _ _]
  rfl

theorem cost_serializeChunk (chunk : Nat) :
    (serializeChunk chunk).cost = 2 + (2 + 3 * 256) + 641 * (2 + 3 * 254) := by
  unfold serializeChunk
  rw [Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, cost_emitWord,
    Prog.cost_rep _ _ _ fun _ _ => cost_emitWord _ _]
  rfl

theorem size_serialize : serialize.size = serializeCount := by
  unfold serialize serializeCount
  rw [Prog.size_seq, Prog.size_seq, Prog.size_seq,
    Prog.size_rep _ _ _ fun _ _ => size_serializeChunk _,
    Prog.size_rep _ _ _ fun _ _ => size_emitWord _ _,
    Prog.size_rep _ _ _ fun _ _ => size_emitWord _ _,
    Prog.size_rep _ _ _ fun _ _ => size_emitWord _ _]
  omega

theorem cost_serialize : serialize.cost = serializeCount := by
  unfold serialize serializeCount
  rw [Prog.cost_seq, Prog.cost_seq, Prog.cost_seq,
    Prog.cost_rep _ _ _ fun _ _ => cost_serializeChunk _,
    Prog.cost_rep _ _ _ fun _ _ => cost_emitWord _ _,
    Prog.cost_rep _ _ _ fun _ _ => cost_emitWord _ _,
    Prog.cost_rep _ _ _ fun _ _ => cost_emitWord _ _]
  omega

theorem size_program : program.size =
    fieldCellCount * 457231 + exceptionByteCount * 62 + hotBlockCount * 902 +
      keyBlockCount * 902 + serializeCount + 16 := by
  unfold program
  rw [Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_seq, size_fields,
    size_bytes, size_blocks, size_key, size_serialize, size_zeroRegs, allRegisters,
    List.length_finRange]
  omega

theorem cost_program : program.cost =
    fieldCellCount * 327180 + exceptionByteCount * 46 + hotBlockCount * 646 +
      keyBlockCount * 646 + serializeCount + 16 := by
  unfold program
  rw [Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, cost_fields,
    cost_bytes, cost_blocks, cost_key, cost_serialize, cost_zeroRegs, allRegisters,
    List.length_finRange]
  omega

end Stage1

end Kriterion.ArgoMAC.PlanB.SimMachine
