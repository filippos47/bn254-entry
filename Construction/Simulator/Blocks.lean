/-
Reusable machine blocks: constants, constant-address RAM access, coin words, bounded rejection
sampling, and bit emission. Each block comes with its exact size and cost.
-/

import Construction.Simulator.Prog
import Construction.Simulator.Layout

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine

namespace Blocks

/-- Load a constant. -/
def cst (target : Register) (value : Nat) : Prog := .op (.constant target (word value))
/-- One arithmetic instruction. -/
def ar (operation : Arithmetic) (target left right : Register) : Prog :=
  .op (.arith operation target left right)
/-- Load `RAM[address]` into `target` (clobbers `rAddr`). -/
def loadAt (target : Register) (address : Nat) : Prog :=
  .seq (cst rAddr address) (.op (.load target rAddr))
/-- Store `source` at `RAM[address]` (clobbers `rAddr`). -/
def storeAt (address : Nat) (source : Register) : Prog :=
  .seq (cst rAddr address) (.op (.store rAddr source))
/-- Zero a list of registers. -/
def zeroRegs : List Register → Prog
  | [] => .skip 0
  | register :: rest => .seq (cst register 0) (zeroRegs rest)
/-- Every register. -/
def allRegisters : List Register := List.finRange 16

/-- One fair coin into `target`: push a coin on the private stack and pop it. -/
def coinBit (target : Register) : Prog := .seq (.op (.coin 1)) (.popBit 1 target)

/-- One big-endian coin step: `rAcc := 2 · rAcc + coin`. -/
def bitStep : Prog :=
  .seq (coinBit rBit) (.seq (ar .add rAcc rAcc rAcc) (ar .add rAcc rAcc rBit))

/-- `width` fair coins into `rAcc`, most significant first. -/
def sampleWord (width : Nat) : Prog := .seq (cst rAcc 0) (Prog.rep width fun _ => bitStep)

/-- The acceptance test `rAcc < bound` into `rBit` (clobbers `rAddr`). -/
def testBelow (bound : Nat) : Prog := .seq (cst rAddr bound) (ar .less rBit rAcc rAddr)

/-- The acceptance test `1 ≤ rAcc < bound` into `rBit` (clobbers `rAddr`). -/
def testPositiveBelow (bound : Nat) : Prog :=
  .seq (cst rAddr 1) (.seq (ar .sub rBit rAcc rAddr)
    (.seq (cst rAddr (bound - 1)) (ar .less rBit rBit rAddr)))

/-- One constant-time attempt: draw, test, and keep the draw iff nothing was kept yet. -/
def attempt (width : Nat) (test : Prog) : Prog :=
  .seq (sampleWord width) (.seq test
    (.seq (ar .less rSel rFlag rBit)
      (.seq (ar .sub rAddr rAcc rOut)
        (.seq (ar .mul rAddr rAddr rSel)
          (.seq (ar .add rOut rOut rAddr) (ar .add rFlag rFlag rSel))))))

/-- `count` constant-time attempts; `rOut` holds the first accepted draw, `rFlag` whether one
was accepted. -/
def rejection (width : Nat) (test : Prog) (count : Nat) : Prog :=
  .seq (cst rOut 0) (.seq (cst rFlag 0) (Prog.rep count fun _ => attempt width test))

/-- Bounded rejection sampling: on success run `use` (which reads `rOut`), on exhaustion
abort. -/
def bounded (width : Nat) (test : Prog) (count : Nat) (use : Prog) : Prog :=
  .seq (rejection width test count) (.ite rFlag use (.abort rSel))

/-- The sampler scratch registers. -/
def samplerScratch : List Register := [rAcc, rOut, rFlag, rBit, rAddr, rSel]

/-- Emit the low `width` bits of `rAcc` onto the response stack, most significant first (so
the least significant bit ends on top). Clobbers `rOut`, `rFlag`. -/
def emitBits (width : Nat) : Prog :=
  Prog.rep width fun index =>
    .seq (cst rOut (width - 1 - index)) (.seq (ar .shiftRight rFlag rAcc rOut)
      (.op (.pushBit 3 rFlag)))

/-- Emit the low `width` bits of `RAM[address]`. -/
def emitWord (address width : Nat) : Prog := .seq (loadAt rAcc address) (emitBits width)

/-! ### Sizes and costs -/

theorem size_cst (target : Register) (value : Nat) : (cst target value).size = 1 := rfl
theorem cost_cst (target : Register) (value : Nat) : (cst target value).cost = 1 := rfl
theorem size_loadAt (target : Register) (address : Nat) : (loadAt target address).size = 2 := rfl
theorem cost_loadAt (target : Register) (address : Nat) : (loadAt target address).cost = 2 := rfl
theorem size_storeAt (address : Nat) (source : Register) : (storeAt address source).size = 2 := rfl
theorem cost_storeAt (address : Nat) (source : Register) : (storeAt address source).cost = 2 := rfl

theorem size_zeroRegs (registers : List Register) : (zeroRegs registers).size = registers.length := by
  induction registers with
  | nil => rfl
  | cons register rest ih => simp only [zeroRegs, Prog.size, ih, cst, List.length_cons]; omega

theorem cost_zeroRegs (registers : List Register) : (zeroRegs registers).cost = registers.length := by
  induction registers with
  | nil => rfl
  | cons register rest ih => simp only [zeroRegs, Prog.cost, ih, cst, List.length_cons]; omega

theorem size_bitStep : bitStep.size = 7 := rfl
theorem cost_bitStep : bitStep.cost = 5 := rfl

theorem size_sampleWord (width : Nat) : (sampleWord width).size = 1 + 7 * width := by
  simp only [sampleWord, Prog.size, cst]
  rw [Prog.size_rep width _ 7 (fun _ _ => size_bitStep)]
  omega

theorem cost_sampleWord (width : Nat) : (sampleWord width).cost = 1 + 5 * width := by
  simp only [sampleWord, Prog.cost, cst]
  rw [Prog.cost_rep width _ 5 (fun _ _ => cost_bitStep)]
  omega

theorem size_attempt (width : Nat) (test : Prog) :
    (attempt width test).size = 1 + 7 * width + test.size + 5 := by
  simp only [attempt, Prog.size, ar, size_sampleWord]; omega

theorem cost_attempt (width : Nat) (test : Prog) :
    (attempt width test).cost = 1 + 5 * width + test.cost + 5 := by
  simp only [attempt, Prog.cost, ar, cost_sampleWord]; omega

theorem size_rejection (width : Nat) (test : Prog) (count : Nat) :
    (rejection width test count).size = 2 + count * (1 + 7 * width + test.size + 5) := by
  simp only [rejection, Prog.size, cst]
  rw [Prog.size_rep count _ _ (fun _ _ => size_attempt width test)]
  omega

theorem cost_rejection (width : Nat) (test : Prog) (count : Nat) :
    (rejection width test count).cost = 2 + count * (1 + 5 * width + test.cost + 5) := by
  simp only [rejection, Prog.cost, cst]
  rw [Prog.cost_rep count _ _ (fun _ _ => cost_attempt width test)]
  omega

/-- A sampler whose continuation costs at least one instruction. -/
theorem size_bounded (width : Nat) (test : Prog) (count : Nat) (use : Prog) (busy : 1 ≤ use.cost) :
    (bounded width test count use).size =
      2 + count * (1 + 7 * width + test.size + 5) + (3 + use.size + use.cost) := by
  simp only [bounded, Prog.size, size_rejection, Prog.padSet, Prog.padClear, Prog.cost]
  omega

theorem cost_bounded (width : Nat) (test : Prog) (count : Nat) (use : Prog) (busy : 1 ≤ use.cost) :
    (bounded width test count use).cost =
      2 + count * (1 + 5 * width + test.cost + 5) + (2 + use.cost) := by
  simp only [bounded, Prog.cost, cost_rejection]
  omega

theorem size_emitBits (width : Nat) : (emitBits width).size = 3 * width := by
  simp only [emitBits]
  rw [Prog.size_rep width _ 3 (fun _ _ => rfl)]
  omega

theorem cost_emitBits (width : Nat) : (emitBits width).cost = 3 * width := by
  simp only [emitBits]
  rw [Prog.cost_rep width _ 3 (fun _ _ => rfl)]
  omega

theorem size_emitWord (address width : Nat) : (emitWord address width).size = 2 + 3 * width := by
  simp only [emitWord, Prog.size, size_loadAt, size_emitBits]

theorem cost_emitWord (address width : Nat) : (emitWord address width).cost = 2 + 3 * width := by
  simp only [emitWord, Prog.cost, cost_loadAt, cost_emitBits]

end Blocks

end Kriterion.ArgoMAC.PlanB.SimMachine
