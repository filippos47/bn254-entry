/-
Stage 2, the request and the response.

* `parse`: after the dispatcher has consumed the tag `[false, true]`, stack `0` holds
  `affine u` (`254 + 254` bits, least significant first) and `output (f_k u)`
  (`[false, false]` for `none`, `[false, true]` for `O`, `[true, false] ++ affine Q`). The two
  coordinates, both tag bits and `Q` (zero when absent) go to the request cells.
* `selectLabels`: label `i` is `key[i].(bit i of u)`, i.e.
  `Lamport.selectedLabels (key.encode (BitInput.ofAffine u))`, written to the label region.
* `emitLabels`: the `508` labels as `words 128 508` on the response stack.
-/

import Construction.Simulator.Blocks

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine Blocks

namespace Request

/-- Pop `254` little-endian bits into `RAM[address]`. -/
def parseWord (address : Nat) : Prog :=
  .seq (cst rAcc 0)
    (.seq (Prog.rep 254 fun position =>
        .seq (.popBit 0 rBit) (.seq (cst rAddr (2 ^ position))
          (.seq (ar .mul rBit rBit rAddr) (ar .add rAcc rAcc rBit))))
      (storeAt address rAcc))

/-- Parse the request. -/
def parse : Prog :=
  .seq (parseWord reqX)
    (.seq (parseWord reqY)
    (.seq (.popBit 0 rBit)
    (.seq (storeAt reqTag0 rBit)
    (.seq (.popBit 0 rBit)
    (.seq (storeAt reqTag1 rBit)
    (.seq (loadAt rFlag reqTag0)
    (.seq (.ite rFlag (.seq (parseWord reqQX) (parseWord reqQY))
        (.seq (cst rA 0) (.seq (storeAt reqQX rA) (storeAt reqQY rA))))
      (zeroRegs [rAcc, rBit, rAddr, rFlag, rA]))))))))

/-- The request cell of input bit `i` and the bit's position in it. -/
def bitCell (position : Nat) : Nat := if position < 254 then reqX else reqY

/-- Select label `i` from the key by bit `i` of `u`. -/
def selectOne (position : Nat) : Prog :=
  .seq (loadAt rA (bitCell position))
    (.seq (cst rB (position % 254))
    (.seq (ar .shiftRight rA rA rB)
    (.seq (cst rB 1)
    (.seq (ar .and rA rA rB)
    (.seq (cst rB (keyBase + 2 * position))
    (.seq (ar .add rA rA rB)
    (.seq (.op (.load rC rA)) (storeAt (labelBase + position) rC))))))))

/-- Select all `508` labels. -/
def selectLabels : Prog :=
  .seq (Prog.rep labelCount fun position => selectOne position) (zeroRegs [rAddr, rA, rB, rC])

/-- Emit the `508` labels, last first. -/
def emitLabels : Prog :=
  Prog.rep labelCount fun index => emitWord (labelBase + labelCount - 1 - index) 128

/-- The common prefix of stage 2; it leaves `rFlag = tag₀ + tag₁` (nonzero iff `f_k u` is
defined) for the dispatcher's branch. -/
def prefixProgram : Prog :=
  .seq parse (.seq selectLabels
    (.seq (loadAt rFlag reqTag0) (.seq (loadAt rBit reqTag1) (ar .add rFlag rFlag rBit))))

/-! ### Sizes and costs -/

theorem size_parseWord (address : Nat) : (parseWord address).size = 1 + 254 * 7 + 2 := by
  simp only [parseWord, Prog.size_seq, size_cst, size_storeAt]
  rw [Prog.size_rep _ _ 7 fun _ _ => by simp only [Prog.size_seq, size_cst, ar, Prog.size]]

theorem cost_parseWord (address : Nat) : (parseWord address).cost = 1 + 254 * 5 + 2 := by
  simp only [parseWord, Prog.cost_seq, cost_cst, cost_storeAt]
  rw [Prog.cost_rep _ _ 5 fun _ _ => by simp only [Prog.cost_seq, cost_cst, ar, Prog.cost]]

theorem size_parse : parse.size = 9692 := by
  simp only [parse, Prog.size_seq, size_parseWord, size_storeAt, size_loadAt, size_cst,
    size_zeroRegs, Prog.size, Prog.padSet, Prog.padClear, cost_parseWord,
    cost_storeAt, cost_cst, Prog.cost, List.length_cons, List.length_nil]
  norm_num

theorem cost_parse : parse.cost = 5109 := by
  simp only [parse, Prog.cost_seq, cost_parseWord, cost_storeAt, cost_loadAt, cost_cst,
    cost_zeroRegs, Prog.cost, List.length_cons, List.length_nil]
  norm_num

theorem size_selectOne (position : Nat) : (selectOne position).size = 11 := by
  simp only [selectOne, Prog.size_seq, size_cst, size_loadAt, size_storeAt, ar, Prog.size]

theorem cost_selectOne (position : Nat) : (selectOne position).cost = 11 := by
  simp only [selectOne, Prog.cost_seq, cost_cst, cost_loadAt, cost_storeAt, ar, Prog.cost]

theorem size_selectLabels : selectLabels.size = labelCount * 11 + 4 := by
  simp only [selectLabels, Prog.size_seq, size_zeroRegs, List.length_cons, List.length_nil]
  rw [Prog.size_rep _ _ _ fun _ _ => size_selectOne _]

theorem cost_selectLabels : selectLabels.cost = labelCount * 11 + 4 := by
  simp only [selectLabels, Prog.cost_seq, cost_zeroRegs, List.length_cons, List.length_nil]
  rw [Prog.cost_rep _ _ _ fun _ _ => cost_selectOne _]

theorem size_emitLabels : emitLabels.size = labelCount * (2 + 3 * 128) :=
  Prog.size_rep _ _ _ fun _ _ => size_emitWord _ _

theorem cost_emitLabels : emitLabels.cost = labelCount * (2 + 3 * 128) :=
  Prog.cost_rep _ _ _ fun _ _ => cost_emitWord _ _

theorem size_prefixProgram : prefixProgram.size = 9692 + (labelCount * 11 + 4) + 5 := by
  simp only [prefixProgram, Prog.size_seq, size_selectLabels, size_loadAt, ar, Prog.size,
    size_parse]
  omega

theorem cost_prefixProgram : prefixProgram.cost = 5109 + (labelCount * 11 + 4) + 5 := by
  simp only [prefixProgram, Prog.cost_seq, cost_selectLabels, cost_loadAt, ar, Prog.cost,
    cost_parse]
  omega

end Request

end Kriterion.ArgoMAC.PlanB.SimMachine
