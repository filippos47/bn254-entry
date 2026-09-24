/-
A structured assembly language for the Plan B simulator machine.

The library's `BoundedMachine.Simulator` is a flat code table. Every Plan B machine here is
written as a `Prog` tree instead and compiled by `emit`, which lays each sub-program out at an
absolute base address. The tree is never materialised: `Vector.ofFn` receives `emit` as a
function of the program counter, so a machine of `10 ^ 10` instructions costs nothing to state.

Design rules, all enforced by construction:

* **Static cost.** Every non-aborting path through a `Prog` executes exactly `Prog.cost`
  instructions. `ite` pads its cheaper arm with no-op jumps. This is what makes the fuel of a
  stage a closed formula and every fuel bound exact.
* **No halts inside a block.** `Prog` has no `halt`; the only way out of a block is its last
  instruction's fall-through, or an abort (a point addition on an invalid tag).
* **Nat labels.** `emit` produces `NInstr`, whose labels are natural numbers; `toInstr` clamps
  them into `Fin (size + 1)`. Every emitted label lies in `[base, base + size]`, so the clamp is
  the identity (`Proof/Simulator/Semantics.lean`).
-/

import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine

/-- A straight-line operation with one fall-through successor. -/
inductive Op
  | constant (target : Register) (value : Word)
  | arith (operation : Arithmetic) (target left right : Register)
  | load (target address : Register)
  | store (address source : Register)
  | push (stack : Fin 4) (bit : Bool)
  | pushBit (stack : Fin 4) (source : Register)
  | coin (stack : Fin 4)
  | pointAdd (target left right : PointRegisters)
  | query (kind : Fin 5) (index input first second : Register)
  | lookup (kind : Fin 5) (index input first second present : Register)
  | program (kind : Fin 5) (index input first second : Register)

/-- A structured program. -/
inductive Prog
  /-- One straight-line operation. -/
  | op (operation : Op)
  /-- Pop one bit of `stack` into `target`: `0`, `1`, or `2` when the stack is empty. -/
  | popBit (stack : Fin 4) (target : Register)
  /-- `count` no-op jumps. -/
  | skip (count : Nat)
  /-- Abort the run: load the invalid point tag `2` into `scratch` and add that point. -/
  | abort (scratch : Register)
  /-- Run `first`, then `second`. -/
  | seq (first second : Prog)
  /-- If register `source` is nonzero run `whenSet`, else `whenClear`; the cheaper arm is
  padded with no-op jumps so both paths cost the same. -/
  | ite (source : Register) (whenSet whenClear : Prog)

namespace Prog

/-- The number of instructions every non-aborting path executes. -/
def cost : Prog → Nat
  | .op _ => 1
  | .popBit _ _ => 2
  | .skip count => count
  | .abort _ => 2
  | .seq first second => first.cost + second.cost
  | .ite _ whenSet whenClear => 1 + max (whenSet.cost + 1) whenClear.cost

/-- The padding of the nonzero arm of an `ite`. -/
def padSet (whenSet whenClear : Prog) : Nat :=
  max (whenSet.cost + 1) whenClear.cost - (whenSet.cost + 1)

/-- The padding of the zero arm of an `ite`. -/
def padClear (whenSet whenClear : Prog) : Nat :=
  max (whenSet.cost + 1) whenClear.cost - whenClear.cost

/-- The number of code slots. -/
def size : Prog → Nat
  | .op _ => 1
  | .popBit _ _ => 4
  | .skip count => count
  | .abort _ => 2
  | .seq first second => first.size + second.size
  | .ite _ whenSet whenClear =>
      2 + whenSet.size + padSet whenSet whenClear + whenClear.size + padClear whenSet whenClear

/-- `count` copies of a body, unrolled at compile time: `body 0; body 1; …`. -/
def rep : (count : Nat) → (Nat → Prog) → Prog
  | 0, _ => .skip 0
  | count + 1, body => .seq (rep count body) (body count)

/- `rep` is sealed: a `rep` of `10 ^ 5` bodies must never be unfolded by the elaborator's
defeq checks. Its equation lemmas (`Prog.rep.eq_1`, `Prog.rep.eq_2`) remain available. -/
attribute [irreducible] rep

/-- A list of programs in sequence. -/
def seqList : List Prog → Prog
  | [] => .skip 0
  | first :: rest => .seq first (seqList rest)

end Prog

/-- A machine instruction with natural-number labels. -/
inductive NInstr
  | op (operation : Op) (next : Nat)
  | pop (stack : Fin 4) (empty onZero onOne : Nat)
  | branch (source : Register) (onZero onNonzero : Nat)
  | halt

/-- An unconditional jump: a branch whose two targets agree. -/
def NInstr.jump (target : Nat) : NInstr := .branch 0 target target

/-- The code of a program laid out at `base`, at offset `offset`. -/
def emit : Prog → (base offset : Nat) → NInstr
  | .op operation, base, _ => .op operation (base + 1)
  | .popBit stack target, base, offset =>
      if offset = 0 then .pop stack (base + 3) (base + 1) (base + 2)
      else if offset = 1 then .op (.constant target 0) (base + 4)
      else if offset = 2 then .op (.constant target 1) (base + 4)
      else .op (.constant target 2) (base + 4)
  | .skip _, base, offset => .jump (base + offset + 1)
  | .abort scratch, base, offset =>
      if offset = 0 then .op (.constant scratch 2) (base + 1)
      else .op (.pointAdd ⟨scratch, scratch, scratch⟩ ⟨scratch, scratch, scratch⟩
        ⟨scratch, scratch, scratch⟩) (base + 2)
  | .seq first second, base, offset =>
      if offset < first.size then emit first base offset
      else emit second (base + first.size) (offset - first.size)
  | .ite source whenSet whenClear, base, offset =>
      let padA := Prog.padSet whenSet whenClear
      let padB := Prog.padClear whenSet whenClear
      let jumpAt := 1 + whenSet.size + padA
      let clearAt := jumpAt + 1
      let finish := base + clearAt + whenClear.size + padB
      if offset = 0 then .branch source (base + clearAt) (base + 1)
      else if offset < 1 + whenSet.size then emit whenSet (base + 1) (offset - 1)
      else if offset < jumpAt then .jump (base + offset + 1)
      else if offset = jumpAt then .jump finish
      else if offset < clearAt + whenClear.size then
        emit whenClear (base + clearAt) (offset - clearAt)
      else .jump (base + offset + 1)

/-- A label clamped into the code table. -/
def label (total target : Nat) : Fin (total + 1) :=
  ⟨min target total, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- A straight-line operation as a simulator instruction. -/
def Op.toInstr {labels : Nat} (next : Fin labels) : Op → SimulatorInstruction labels
  | .constant target value => .compute (.constant target value next)
  | .arith operation target left right => .compute (.arithmetic operation target left right next)
  | .load target address => .compute (.load target address next)
  | .store address source => .compute (.store address source next)
  | .push stack bit => .compute (.push stack bit next)
  | .pushBit stack source => .compute (.pushBit stack source next)
  | .coin stack => .compute (.coin stack next)
  | .pointAdd target left right => .compute (.pointAdd target left right next)
  | .query kind index input first second => .query kind index input first second next
  | .lookup kind index input first second present =>
      .lookup kind index input first second present next
  | .program kind index input first second => .program kind index input first second next

/-- A natural-number instruction as a simulator instruction of a `total + 1` code table. -/
def NInstr.toInstr (total : Nat) : NInstr → SimulatorInstruction (total + 1)
  | .op operation next => operation.toInstr (label total next)
  | .pop stack empty onZero onOne =>
      .compute (.pop stack (label total empty) (label total onZero) (label total onOne))
  | .branch source onZero onNonzero =>
      .compute (.branch source (label total onZero) (label total onNonzero))
  | .halt => .compute .halt

/-- Assemble a code function of `size + 1` slots into a simulator. -/
def assemble (size : Nat) (code : Nat → NInstr) (addressBound : size < 2 ^ 256)
    (firstFuel secondFuel : Nat) (within : size + 1 + firstFuel + secondFuel ≤ 2 ^ 60) :
    Simulator :=
  ⟨size, Vector.ofFn (fun pc => (code pc.val).toInstr size), addressBound, firstFuel, secondFuel,
    within⟩

/-! ### Sizes of the derived forms -/

namespace Prog

@[simp] theorem size_seq (first second : Prog) : (seq first second).size = first.size + second.size :=
  rfl

@[simp] theorem cost_seq (first second : Prog) : (seq first second).cost = first.cost + second.cost :=
  rfl

theorem size_rep (count : Nat) (body : Nat → Prog) (width : Nat)
    (uniform : ∀ index, index < count → (body index).size = width) :
    (rep count body).size = count * width := by
  induction count with
  | zero => simp [rep, size]
  | succ count ih =>
      simp only [rep, size]
      rw [ih (fun index bound => uniform index (by omega)), uniform count (by omega),
        Nat.succ_mul]

theorem cost_rep (count : Nat) (body : Nat → Prog) (charge : Nat)
    (uniform : ∀ index, index < count → (body index).cost = charge) :
    (rep count body).cost = count * charge := by
  induction count with
  | zero => simp [rep, cost]
  | succ count ih =>
      simp only [rep, cost]
      rw [ih (fun index bound => uniform index (by omega)), uniform count (by omega),
        Nat.succ_mul]

theorem size_ite_of_eq (source : Register) (whenSet whenClear : Prog)
    (balanced : whenClear.cost = whenSet.cost + 1) :
    (ite source whenSet whenClear).size = 2 + whenSet.size + whenClear.size := by
  simp only [size, padSet, padClear, balanced, Nat.max_self, Nat.sub_self]
  omega

theorem cost_ite_of_eq (source : Register) (whenSet whenClear : Prog)
    (balanced : whenClear.cost = whenSet.cost + 1) :
    (ite source whenSet whenClear).cost = 2 + whenSet.cost := by
  simp only [cost, balanced, Nat.max_self]
  omega

/-- An `ite` whose zero arm costs at most one more than its nonzero arm: only the zero arm is
padded. -/
theorem size_ite_of_le (source : Register) (whenSet whenClear : Prog)
    (cheaper : whenClear.cost ≤ whenSet.cost + 1) :
    (ite source whenSet whenClear).size =
      2 + whenSet.size + whenClear.size + (whenSet.cost + 1 - whenClear.cost) := by
  simp only [size, padSet, padClear, Nat.max_eq_left cheaper]
  omega

theorem cost_ite_of_le (source : Register) (whenSet whenClear : Prog)
    (cheaper : whenClear.cost ≤ whenSet.cost + 1) :
    (ite source whenSet whenClear).cost = 2 + whenSet.cost := by
  simp only [cost, Nat.max_eq_left cheaper]
  omega

theorem cost_ite (source : Register) (whenSet whenClear : Prog) :
    (ite source whenSet whenClear).cost = 1 + max (whenSet.cost + 1) whenClear.cost := rfl

theorem size_ite (source : Register) (whenSet whenClear : Prog) :
    (ite source whenSet whenClear).size = 2 + whenSet.size + whenClear.size +
      (max (whenSet.cost + 1) whenClear.cost - (whenSet.cost + 1)) +
      (max (whenSet.cost + 1) whenClear.cost - whenClear.cost) := by
  simp only [size, padSet, padClear]
  omega

end Prog

end Kriterion.ArgoMAC.PlanB.SimMachine
