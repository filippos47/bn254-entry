/-
The denotational semantics of `Prog` and the compiler-correctness theorem.

`Prog.sem` gives every structured program a law on (memory, lazy-oracle state), with abort as
`none`. `run_placed` shows that the library's `Simulator.run`, started at the base of a placed
block, *is* that law followed by the run from the block's exit, charged exactly `Prog.cost`
fuel. Every machine-level statement about the Plan B simulator reduces to `Prog.sem` through
this one theorem, by structural induction on the program — never by executing code.
-/

import Construction.Simulator.Prog

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine

section Semantics

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- The oracle state the simulator threads. -/
abbrev OState (FixedIndex EncIndex : Type) := LazyOracle.State FixedIndex EncIndex

/-- Replace one register. -/
def setReg (memory : Memory) (target : Register) (value : Word) : Memory :=
  { memory with registers := Function.update memory.registers target value }

/-- Push one bit onto a stack. -/
def pushOn (memory : Memory) (stack : Fin 4) (bit : Bool) : Memory :=
  { memory with bits := Function.update memory.bits stack (bit :: memory.bits stack) }

/-- The memory after popping one bit of `stack` into `target` (`2` on an empty stack). -/
def popInto (memory : Memory) (stack : Fin 4) (target : Register) : Memory :=
  match memory.bits stack with
  | [] => setReg memory target 2
  | bit :: rest =>
      setReg { memory with bits := Function.update memory.bits stack rest } target
        (if bit then 1 else 0)

/-- Write one RAM word. -/
def storeRam (memory : Memory) (address value : Word) : Memory :=
  { memory with ram := Function.update memory.ram address value }

/-- Write an oracle answer's two words. -/
def writePair (memory : Memory) (first second : Register) (values : Word × Word) : Memory :=
  { memory with registers :=
      Function.update (Function.update memory.registers first values.1) second values.2 }

/-- Write a point into its three registers. -/
def writePointMem (memory : Memory) (target : PointRegisters) (point : BN254.Point) : Memory :=
  { memory with registers := writePoint memory.registers target point }

/-- The law of one straight-line operation; it mirrors `Simulator.step` case by case. -/
noncomputable def Op.sem (operation : Op) (memory : Memory)
    (oracle : OState FixedIndex EncIndex) :
    PMF (Option (Memory × OState FixedIndex EncIndex)) :=
  match operation with
  | .constant target value => PMF.pure (some (setReg memory target value, oracle))
  | .arith operation target left right =>
      PMF.pure (some (setReg memory target
        (operation.eval (memory.registers left) (memory.registers right)), oracle))
  | .load target address =>
      PMF.pure (some (setReg memory target (memory.ram (memory.registers address)), oracle))
  | .store address source =>
      PMF.pure (some (storeRam memory (memory.registers address) (memory.registers source),
        oracle))
  | .push stack bit => PMF.pure (some (pushOn memory stack bit, oracle))
  | .pushBit stack source =>
      PMF.pure (some (pushOn memory stack ((memory.registers source).getLsbD 0), oracle))
  | .coin stack =>
      (PMF.uniformOfFintype Bool).bind fun bit => PMF.pure (some (pushOn memory stack bit, oracle))
  | .pointAdd target left right =>
      match readPoint memory.registers left, readPoint memory.registers right with
      | some a, some b => PMF.pure (some (writePointMem memory target (a + b), oracle))
      | _, _ => PMF.pure none
  | .query kind index input first second =>
      match queryFromRegisters (FixedIndex := FixedIndex) (EncIndex := EncIndex) kind
          (memory.registers index) (memory.registers input) with
      | none => PMF.pure none
      | some request => (LazyOracle.query request oracle).map fun answer =>
          some (writePair memory first second (answerWords request answer.1), answer.2)
  | .lookup kind index input first second present =>
      match queryFromRegisters (FixedIndex := FixedIndex) (EncIndex := EncIndex) kind
          (memory.registers index) (memory.registers input) with
      | none => PMF.pure none
      | some request => PMF.pure (match LazyOracle.lookup request oracle with
          | none => some (setReg memory present 0, oracle)
          | some answer =>
              some (setReg (writePair memory first second (answerWords request answer)) present 1,
                oracle))
  | .program kind index input first second =>
      match queryFromRegisters (FixedIndex := FixedIndex) (EncIndex := EncIndex) kind
          (memory.registers index) (memory.registers input) with
      | none => PMF.pure none
      | some request => PMF.pure ((LazyOracle.program request
          (answerFromWords request (memory.registers first) (memory.registers second))
            oracle).map fun updated => (memory, updated))

/-- Sequential composition of two laws with abort. -/
noncomputable def andThen
    (first : Memory → OState FixedIndex EncIndex → PMF (Option (Memory × OState FixedIndex EncIndex)))
    (second : Memory → OState FixedIndex EncIndex → PMF (Option (Memory × OState FixedIndex EncIndex)))
    (memory : Memory) (oracle : OState FixedIndex EncIndex) :
    PMF (Option (Memory × OState FixedIndex EncIndex)) :=
  (first memory oracle).bind fun result => match result with
    | none => PMF.pure none
    | some (next, updated) => second next updated

/-- The law of a structured program. -/
noncomputable def Prog.sem : Prog → Memory → OState FixedIndex EncIndex →
    PMF (Option (Memory × OState FixedIndex EncIndex))
  | .op operation, memory, oracle => operation.sem memory oracle
  | .popBit stack target, memory, oracle => PMF.pure (some (popInto memory stack target, oracle))
  | .skip _, memory, oracle => PMF.pure (some (memory, oracle))
  | .abort _, _, _ => PMF.pure none
  | .seq first second, memory, oracle => andThen first.sem second.sem memory oracle
  | .ite source whenSet whenClear, memory, oracle =>
      if memory.registers source = 0 then whenClear.sem memory oracle
      else whenSet.sem memory oracle

end Semantics

/-! ### Placement and runs -/

/-- The configuration at a (clamped) natural-number program counter. -/
def atPc (machine : Simulator) (pc : Nat) (memory : Memory) :
    Configuration (machine.size + 1) :=
  ⟨label machine.size pc, memory⟩

/-- The instruction at a natural-number address, `halt` outside the table. -/
def codeAt (machine : Simulator) (pc : Nat) : SimulatorInstruction (machine.size + 1) :=
  if inside : pc < machine.size + 1 then machine.code[pc] else .compute .halt

section Runs

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- `program` is laid out at `base` in `machine`. -/
def Placed (machine : Simulator) (program : Prog) (base : Nat) : Prop :=
  base + program.size ≤ machine.size ∧
    ∀ offset, offset < program.size →
      codeAt machine (base + offset) = (emit program base offset).toInstr machine.size

/-- What follows a block of cost `charge` exiting at `exit`, with `fuel` supplied at entry. -/
noncomputable def after (machine : Simulator) (charge exit fuel : Nat) :
    Option (Memory × OState FixedIndex EncIndex) →
      PMF (Option (Configuration (machine.size + 1) × OState FixedIndex EncIndex × Nat))
  | none => PMF.pure none
  | some (memory, oracle) =>
      if charge ≤ fuel then
        (machine.run (fuel - charge) (atPc machine exit memory) oracle).map
          (Option.map fun result => (result.1, result.2.1, result.2.2 + charge))
      else PMF.pure none

/-- Starting at `start`, the machine runs the law `law`, spends exactly `charge`, and resumes at
`exit`. -/
def RunsAs (machine : Simulator) (start : Nat)
    (law : Memory → OState FixedIndex EncIndex → PMF (Option (Memory × OState FixedIndex EncIndex)))
    (charge exit : Nat) : Prop :=
  ∀ fuel memory oracle, machine.run fuel (atPc machine start memory) oracle =
    (law memory oracle).bind (after machine charge exit fuel)

end Runs

theorem label_of_le {total target : Nat} (inside : target ≤ total) :
    label total target = ⟨target, Nat.lt_succ_of_le inside⟩ := by
  simp [label, Nat.min_eq_left inside]

theorem codeAt_of_lt (machine : Simulator) {pc : Nat} (inside : pc < machine.size + 1) :
    codeAt machine pc = machine.code[pc] := by
  simp [codeAt, inside]

/-- The run from a clamped counter reads the clamped instruction. -/
theorem code_atPc (machine : Simulator) {pc : Nat} (inside : pc ≤ machine.size) (memory : Memory) :
    machine.code[(atPc machine pc memory).pc.val] = codeAt machine pc := by
  simp only [atPc, label_of_le inside]
  rw [codeAt_of_lt machine (Nat.lt_succ_of_le inside)]

/-! ### One step -/

section Steps

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

theorem arithmetic_code_of (machine : Simulator) {index : Nat} (inside : index < machine.size + 1)
    {instruction : Instruction (machine.size + 1)}
    (code : machine.code[index] = .compute instruction) :
    machine.arithmetic.code[index] = instruction := by
  simp [Simulator.arithmetic, Vector.getElem_map, code]

/-- A straight-line operation steps by its law. -/
theorem step_op (machine : Simulator) {pc : Nat} (inside : pc ≤ machine.size) (operation : Op)
    (next : Nat) (code : codeAt machine pc = (NInstr.op operation next).toInstr machine.size)
    (memory : Memory) (oracle : OState FixedIndex EncIndex) :
    machine.step (atPc machine pc memory) oracle =
      (operation.sem memory oracle).map
        (Option.map fun result => (false, atPc machine next result.1, result.2)) := by
  have located := code_atPc machine inside memory
  rw [code] at located
  unfold Simulator.step
  cases operation with
  | query kind index input first second =>
      rw [located]
      dsimp only [NInstr.toInstr, Op.toInstr, atPc]
      simp only [Op.sem]
      cases decoded : queryFromRegisters (FixedIndex := FixedIndex) (EncIndex := EncIndex) kind
          (memory.registers index) (memory.registers input) with
      | none => simp [PMF.pure_map]
      | some request => simp [PMF.map_comp, Function.comp_def, writePair]
  | lookup kind index input first second present =>
      rw [located]
      dsimp only [NInstr.toInstr, Op.toInstr, atPc]
      simp only [Op.sem]
      cases decoded : queryFromRegisters (FixedIndex := FixedIndex) (EncIndex := EncIndex) kind
          (memory.registers index) (memory.registers input) with
      | none => simp [PMF.pure_map]
      | some request =>
          cases found : LazyOracle.lookup request oracle <;>
            simp [PMF.pure_map, writePair, setReg, found]
  | program kind index input first second =>
      rw [located]
      dsimp only [NInstr.toInstr, Op.toInstr, atPc]
      simp only [Op.sem]
      cases decoded : queryFromRegisters (FixedIndex := FixedIndex) (EncIndex := EncIndex) kind
          (memory.registers index) (memory.registers input) with
      | none => simp [PMF.pure_map]
      | some request =>
          simp only [PMF.pure_map]
          congr 1
          cases LazyOracle.program request _ oracle <;> rfl
  | coin stack =>
      have arith := arithmetic_code_of machine (atPc machine pc memory).pc.isLt located
      rw [located]
      dsimp only [NInstr.toInstr, Op.toInstr]
      unfold BoundedMachine.step
      rw [arith]
      dsimp only [atPc]
      simp only [Op.sem, PMF.map_bind, PMF.pure_map, Option.map_some, pushOn]
  | pointAdd target left right =>
      have arith := arithmetic_code_of machine (atPc machine pc memory).pc.isLt located
      rw [located]
      dsimp only [NInstr.toInstr, Op.toInstr]
      unfold BoundedMachine.step
      rw [arith]
      dsimp only [atPc]
      simp only [Op.sem]
      cases readPoint memory.registers left <;> cases readPoint memory.registers right <;>
        simp [PMF.pure_map, writePointMem]
  | _ =>
      have arith := arithmetic_code_of machine (atPc machine pc memory).pc.isLt located
      rw [located]
      dsimp only [NInstr.toInstr, Op.toInstr]
      unfold BoundedMachine.step
      rw [arith]
      dsimp only [atPc]
      simp [Op.sem, setReg, pushOn, storeRam, PMF.pure_map]

/-- A pop steps to the label of the popped bit. -/
theorem step_pop (machine : Simulator) {pc : Nat} (inside : pc ≤ machine.size) (stack : Fin 4)
    (empty onZero onOne : Nat)
    (code : codeAt machine pc = (NInstr.pop stack empty onZero onOne).toInstr machine.size)
    (memory : Memory) (oracle : OState FixedIndex EncIndex) :
    machine.step (atPc machine pc memory) oracle =
      PMF.pure (some (false, (match memory.bits stack with
        | [] => atPc machine empty memory
        | bit :: rest => atPc machine (if bit then onOne else onZero)
            { memory with bits := Function.update memory.bits stack rest }), oracle)) := by
  have located := code_atPc machine inside memory
  rw [code] at located
  have arith := arithmetic_code_of machine (atPc machine pc memory).pc.isLt located
  unfold Simulator.step
  rw [located]
  dsimp only [NInstr.toInstr]
  unfold BoundedMachine.step
  rw [arith]
  dsimp only [atPc]
  cases memory.bits stack with
  | nil => simp [PMF.pure_map]
  | cons bit rest => cases bit <;> simp [PMF.pure_map]

/-- A branch steps to the label its register selects. -/
theorem step_branch (machine : Simulator) {pc : Nat} (inside : pc ≤ machine.size)
    (source : Register) (onZero onNonzero : Nat)
    (code : codeAt machine pc = (NInstr.branch source onZero onNonzero).toInstr machine.size)
    (memory : Memory) (oracle : OState FixedIndex EncIndex) :
    machine.step (atPc machine pc memory) oracle =
      PMF.pure (some (false, atPc machine
        (if memory.registers source = 0 then onZero else onNonzero) memory, oracle)) := by
  have located := code_atPc machine inside memory
  rw [code] at located
  have arith := arithmetic_code_of machine (atPc machine pc memory).pc.isLt located
  unfold Simulator.step
  rw [located]
  dsimp only [NInstr.toInstr]
  unfold BoundedMachine.step
  rw [arith]
  dsimp only [atPc]
  by_cases zero : memory.registers source = 0
  · have literal : memory.registers source = 0#256 := zero
    simp [zero, literal, PMF.pure_map]
  · have literal : ¬ memory.registers source = 0#256 := zero
    simp [zero, literal, PMF.pure_map]

end Steps

/-! ### Runs of blocks -/

section Blocks

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- The law that changes nothing. -/
noncomputable def idLaw (memory : Memory) (oracle : OState FixedIndex EncIndex) :
    PMF (Option (Memory × OState FixedIndex EncIndex)) := PMF.pure (some (memory, oracle))

theorem run_zero (machine : Simulator) (state : Configuration (machine.size + 1))
    (oracle : OState FixedIndex EncIndex) : machine.run 0 state oracle = PMF.pure none := by
  rw [Simulator.run.eq_def]

theorem run_succ (machine : Simulator) (fuel : Nat) (state : Configuration (machine.size + 1))
    (oracle : OState FixedIndex EncIndex) :
    machine.run (fuel + 1) state oracle = (machine.step state oracle).bind fun outcome =>
      match outcome with
      | none => PMF.pure none
      | some (true, next, updated) => PMF.pure (some (next, updated, 1))
      | some (false, next, updated) => (machine.run fuel next updated).map
          (Option.map fun result => (result.1, result.2.1, result.2.2 + 1)) := by
  rw [Simulator.run.eq_def]
  rfl

/-- A continuation that never reaches its body is `none`. -/
theorem after_short (machine : Simulator) {charge exit fuel : Nat} (short : fuel < charge) :
    after (FixedIndex := FixedIndex) (EncIndex := EncIndex) machine charge exit fuel =
      fun _ => PMF.pure none := by
  funext result
  cases result with
  | none => rfl
  | some result => simp [after, show ¬ charge ≤ fuel by omega]

theorem bind_after_short (machine : Simulator) {charge exit fuel : Nat} (short : fuel < charge)
    (law : PMF (Option (Memory × OState FixedIndex EncIndex))) :
    law.bind (after machine charge exit fuel) = PMF.pure none := by
  rw [after_short machine short, PMF.bind_const]

omit [BN254.FieldCertificate] in
theorem map_charge_zero {α β : Type} :
    (Option.map fun result : α × β × Nat => (result.1, result.2.1, result.2.2 + 0)) = id := by
  funext result
  cases result <;> rfl

/-- The trivial block. -/
theorem runsAs_id (machine : Simulator) (start : Nat) :
    RunsAs machine start (idLaw (FixedIndex := FixedIndex) (EncIndex := EncIndex)) 0 start := by
  intro fuel memory oracle
  simp only [idLaw, PMF.pure_bind, after, Nat.zero_le, if_true, Nat.sub_zero]
  rw [map_charge_zero, PMF.map_id]

/-- Blocks compose: laws in sequence, charges added. -/
theorem runsAs_andThen (machine : Simulator) {start middle finish : Nat}
    {first second : Memory → OState FixedIndex EncIndex →
      PMF (Option (Memory × OState FixedIndex EncIndex))}
    {firstCharge secondCharge : Nat}
    (runFirst : RunsAs machine start first firstCharge middle)
    (runSecond : RunsAs machine middle second secondCharge finish) :
    RunsAs machine start (andThen first second) (firstCharge + secondCharge) finish := by
  intro fuel memory oracle
  rw [runFirst, andThen, PMF.bind_bind]
  congr 1
  funext result
  cases result with
  | none => simp [after]
  | some result =>
      rcases result with ⟨next, updated⟩
      by_cases enough : firstCharge ≤ fuel
      · simp only [after, if_pos enough]
        rw [runSecond, PMF.map_bind]
        congr 1
        funext final
        cases final with
        | none => simp [after, PMF.pure_map]
        | some final =>
            rcases final with ⟨last, lastOracle⟩
            by_cases rest : secondCharge ≤ fuel - firstCharge
            · simp only [after, if_pos rest, if_pos (show firstCharge + secondCharge ≤ fuel by omega),
                PMF.map_comp]
              rw [show fuel - firstCharge - secondCharge = fuel - (firstCharge + secondCharge) by omega]
              congr 1
              funext value
              cases value with
              | none => rfl
              | some value => simp only [Function.comp_apply, Option.map_some]; congr 3; omega
            · simp [after, if_neg rest, show ¬ firstCharge + secondCharge ≤ fuel by omega,
                PMF.pure_map]
      · simp only [after, if_neg enough]
        rw [bind_after_short machine (by omega)]

/-- One step whose law is `law`, continuing at `next`. -/
theorem runsAs_step (machine : Simulator) {pc next : Nat}
    {law : Memory → OState FixedIndex EncIndex → PMF (Option (Memory × OState FixedIndex EncIndex))}
    (stepping : ∀ memory oracle, machine.step (atPc machine pc memory) oracle =
      (law memory oracle).map (Option.map fun result => (false, atPc machine next result.1,
        result.2))) :
    RunsAs machine pc law 1 next := by
  intro fuel memory oracle
  cases fuel with
  | zero =>
      rw [run_zero, bind_after_short machine (by omega)]
  | succ fuel =>
      rw [run_succ, stepping, PMF.bind_map]
      congr 1
      funext result
      cases result with
      | none => rfl
      | some result =>
          rcases result with ⟨memory', oracle'⟩
          simp only [Function.comp_apply, Option.map_some, after,
            show 1 ≤ fuel + 1 by omega, if_true, Nat.add_sub_cancel]

theorem runsAs_op (machine : Simulator) {pc : Nat} (inside : pc ≤ machine.size) (operation : Op)
    (next : Nat) (code : codeAt machine pc = (NInstr.op operation next).toInstr machine.size) :
    RunsAs machine pc (Op.sem (FixedIndex := FixedIndex) (EncIndex := EncIndex) operation) 1 next :=
  runsAs_step machine fun memory oracle => step_op machine inside operation next code memory oracle

theorem runsAs_jump (machine : Simulator) {pc : Nat} (inside : pc ≤ machine.size) (target : Nat)
    (code : codeAt machine pc = (NInstr.jump target).toInstr machine.size) :
    RunsAs machine pc (idLaw (FixedIndex := FixedIndex) (EncIndex := EncIndex)) 1 target :=
  runsAs_step machine fun memory oracle => by
    rw [step_branch machine inside 0 target target code memory oracle]
    simp [idLaw, PMF.pure_map]

/-- A branch with a register-dependent continuation. -/
theorem run_branch (machine : Simulator) {pc : Nat} (inside : pc ≤ machine.size)
    (source : Register) (onZero onNonzero : Nat)
    (code : codeAt machine pc = (NInstr.branch source onZero onNonzero).toInstr machine.size)
    (fuel : Nat) (memory : Memory) (oracle : OState FixedIndex EncIndex) :
    machine.run (fuel + 1) (atPc machine pc memory) oracle =
      (machine.run fuel (atPc machine (if memory.registers source = 0 then onZero else onNonzero)
        memory) oracle).map (Option.map fun result => (result.1, result.2.1, result.2.2 + 1)) := by
  rw [run_succ, step_branch machine inside source onZero onNonzero code memory oracle,
    PMF.pure_bind]

theorem andThen_idLaw
    (law : Memory → OState FixedIndex EncIndex → PMF (Option (Memory × OState FixedIndex EncIndex))) :
    andThen law idLaw = law := by
  funext memory oracle
  simp only [andThen, idLaw]
  conv_rhs => rw [← PMF.bind_pure (law memory oracle)]
  congr 1
  funext result
  cases result <;> rfl

theorem idLaw_andThen
    (law : Memory → OState FixedIndex EncIndex → PMF (Option (Memory × OState FixedIndex EncIndex))) :
    andThen idLaw law = law := by
  funext memory oracle
  simp only [andThen, idLaw, PMF.pure_bind]

theorem runsAs_congr (machine : Simulator) {start charge exit : Nat}
    {law law' : Memory → OState FixedIndex EncIndex →
      PMF (Option (Memory × OState FixedIndex EncIndex))}
    (same : law = law') (runs : RunsAs machine start law charge exit) :
    RunsAs machine start law' charge exit := same ▸ runs

theorem runsAs_charge (machine : Simulator) {start charge charge' exit exit' : Nat}
    {law : Memory → OState FixedIndex EncIndex → PMF (Option (Memory × OState FixedIndex EncIndex))}
    (sameCharge : charge = charge') (sameExit : exit = exit')
    (runs : RunsAs machine start law charge exit) : RunsAs machine start law charge' exit' :=
  sameCharge ▸ sameExit ▸ runs

/-- A run of `count` fall-through jumps. -/
theorem runsAs_jumps (machine : Simulator) (count : Nat) :
    ∀ base, base + count ≤ machine.size →
      (∀ offset, offset < count →
        codeAt machine (base + offset) = (NInstr.jump (base + offset + 1)).toInstr machine.size) →
      RunsAs machine base (idLaw (FixedIndex := FixedIndex) (EncIndex := EncIndex)) count
        (base + count) := by
  induction count with
  | zero => intro base _ _; exact runsAs_id machine base
  | succ count ih =>
      intro base fits code
      have first := runsAs_jump (FixedIndex := FixedIndex) (EncIndex := EncIndex) machine
        (pc := base) (by omega) (base + 1) (by simpa using code 0 (by omega))
      have rest := ih (base + 1) (by omega) (fun offset bound => by
        have := code (offset + 1) (by omega)
        rw [show base + (offset + 1) = base + 1 + offset by omega] at this
        rw [this])
      have joined := runsAs_andThen machine first rest
      rw [idLaw_andThen] at joined
      exact runsAs_charge machine (by omega) (by omega) joined

/-- The trailing continuation of a block shifts by one step. -/
theorem after_map_succ (machine : Simulator) (charge exit fuel : Nat)
    (result : Option (Memory × OState FixedIndex EncIndex)) :
    (after machine charge exit fuel result).map
        (Option.map fun final => (final.1, final.2.1, final.2.2 + 1)) =
      after machine (charge + 1) exit (fuel + 1) result := by
  cases result with
  | none => simp [after, PMF.pure_map]
  | some result =>
      rcases result with ⟨memory, oracle⟩
      by_cases enough : charge ≤ fuel
      · simp only [after, if_pos enough, if_pos (show charge + 1 ≤ fuel + 1 by omega),
          PMF.map_comp, show fuel + 1 - (charge + 1) = fuel - charge by omega]
        congr 1
        funext value
        cases value with
        | none => rfl
        | some value => simp only [Function.comp_apply, Option.map_some]; congr 3
      · simp [after, if_neg enough, show ¬ charge + 1 ≤ fuel + 1 by omega, PMF.pure_map]

end Blocks

/-! ### Placement of structured programs -/

section Placement

theorem placed_code {machine : Simulator} {program : Prog} {base : Nat}
    (placed : Placed machine program base) {offset : Nat} (inside : offset < program.size) :
    codeAt machine (base + offset) = (emit program base offset).toInstr machine.size :=
  placed.2 offset inside

theorem placed_seq_first {machine : Simulator} {first second : Prog} {base : Nat}
    (placed : Placed machine (.seq first second) base) : Placed machine first base := by
  refine ⟨by have := placed.1; simp only [Prog.size] at this; omega, fun offset inside => ?_⟩
  have code := placed.2 offset (by simp only [Prog.size]; omega)
  simpa [emit, inside] using code

theorem placed_seq_second {machine : Simulator} {first second : Prog} {base : Nat}
    (placed : Placed machine (.seq first second) base) :
    Placed machine second (base + first.size) := by
  refine ⟨by have := placed.1; simp only [Prog.size] at this; omega, fun offset inside => ?_⟩
  have code := placed.2 (first.size + offset) (by simp only [Prog.size]; omega)
  rw [show base + (first.size + offset) = base + first.size + offset by omega] at code
  simpa [emit] using code

section EmitIte

variable (source : Register) (whenSet whenClear : Prog) (base : Nat)

theorem emit_ite_branch :
    emit (.ite source whenSet whenClear) base 0 =
      .branch source (base + (2 + whenSet.size + Prog.padSet whenSet whenClear)) (base + 1) := by
  simp only [emit, if_pos]
  congr 1
  omega

theorem emit_ite_set (offset : Nat) (inside : offset < whenSet.size) :
    emit (.ite source whenSet whenClear) base (1 + offset) = emit whenSet (base + 1) offset := by
  simp only [emit, show 1 + offset ≠ 0 by omega, if_false,
    show 1 + offset < 1 + whenSet.size by omega, if_true]
  congr 1
  omega

theorem emit_ite_padSet (offset : Nat) (inside : offset < Prog.padSet whenSet whenClear) :
    emit (.ite source whenSet whenClear) base (1 + whenSet.size + offset) =
      .jump (base + 1 + whenSet.size + offset + 1) := by
  simp only [emit, show 1 + whenSet.size + offset ≠ 0 by omega, if_false,
    show ¬ 1 + whenSet.size + offset < 1 + whenSet.size by omega,
    show 1 + whenSet.size + offset < 1 + whenSet.size + Prog.padSet whenSet whenClear by omega,
    if_true]
  congr 1
  omega

theorem emit_ite_close :
    emit (.ite source whenSet whenClear) base (1 + whenSet.size + Prog.padSet whenSet whenClear) =
      .jump (base + (Prog.ite source whenSet whenClear).size) := by
  simp only [emit, Prog.size, show 1 + whenSet.size + Prog.padSet whenSet whenClear ≠ 0 by omega,
    if_false, show ¬ 1 + whenSet.size + Prog.padSet whenSet whenClear < 1 + whenSet.size by omega,
    lt_self_iff_false, if_true]
  congr 1
  omega

theorem emit_ite_clear (offset : Nat) (inside : offset < whenClear.size) :
    emit (.ite source whenSet whenClear) base (2 + whenSet.size + Prog.padSet whenSet whenClear + offset) =
      emit whenClear (base + (2 + whenSet.size + Prog.padSet whenSet whenClear)) offset := by
  simp only [emit,
    show 2 + whenSet.size + Prog.padSet whenSet whenClear + offset ≠ 0 by omega, if_false,
    show ¬ 2 + whenSet.size + Prog.padSet whenSet whenClear + offset < 1 + whenSet.size by omega,
    show ¬ 2 + whenSet.size + Prog.padSet whenSet whenClear + offset <
      1 + whenSet.size + Prog.padSet whenSet whenClear by omega,
    show 2 + whenSet.size + Prog.padSet whenSet whenClear + offset ≠
      1 + whenSet.size + Prog.padSet whenSet whenClear by omega,
    show 2 + whenSet.size + Prog.padSet whenSet whenClear + offset <
      1 + whenSet.size + Prog.padSet whenSet whenClear + 1 + whenClear.size by omega, if_true]
  congr 2
  · omega
  · omega

theorem emit_ite_padClear (offset : Nat) (inside : offset < Prog.padClear whenSet whenClear) :
    emit (.ite source whenSet whenClear) base
        (2 + whenSet.size + Prog.padSet whenSet whenClear + whenClear.size + offset) =
      .jump (base + (2 + whenSet.size + Prog.padSet whenSet whenClear) + whenClear.size + offset
        + 1) := by
  simp only [emit,
    show 2 + whenSet.size + Prog.padSet whenSet whenClear + whenClear.size + offset ≠ 0 by omega,
    if_false,
    show ¬ 2 + whenSet.size + Prog.padSet whenSet whenClear + whenClear.size + offset <
      1 + whenSet.size by omega,
    show ¬ 2 + whenSet.size + Prog.padSet whenSet whenClear + whenClear.size + offset <
      1 + whenSet.size + Prog.padSet whenSet whenClear by omega,
    show 2 + whenSet.size + Prog.padSet whenSet whenClear + whenClear.size + offset ≠
      1 + whenSet.size + Prog.padSet whenSet whenClear by omega,
    show ¬ 2 + whenSet.size + Prog.padSet whenSet whenClear + whenClear.size + offset <
      1 + whenSet.size + Prog.padSet whenSet whenClear + 1 + whenClear.size by omega]
  congr 1
  omega

end EmitIte

theorem placed_ite_set {machine : Simulator} {source : Register} {whenSet whenClear : Prog}
    {base : Nat} (placed : Placed machine (.ite source whenSet whenClear) base) :
    Placed machine whenSet (base + 1) := by
  refine ⟨by have := placed.1; simp only [Prog.size] at this; omega, fun offset inside => ?_⟩
  have code := placed.2 (1 + offset) (by simp only [Prog.size]; omega)
  rw [emit_ite_set source whenSet whenClear base offset inside,
    show base + (1 + offset) = base + 1 + offset by omega] at code
  exact code

theorem placed_ite_clear {machine : Simulator} {source : Register} {whenSet whenClear : Prog}
    {base : Nat} (placed : Placed machine (.ite source whenSet whenClear) base) :
    Placed machine whenClear (base + (2 + whenSet.size + Prog.padSet whenSet whenClear)) := by
  refine ⟨by have := placed.1; simp only [Prog.size] at this; omega, fun offset inside => ?_⟩
  have code := placed.2 (2 + whenSet.size + Prog.padSet whenSet whenClear + offset)
    (by simp only [Prog.size]; omega)
  rw [emit_ite_clear source whenSet whenClear base offset inside,
    show base + (2 + whenSet.size + Prog.padSet whenSet whenClear + offset) =
      base + (2 + whenSet.size + Prog.padSet whenSet whenClear) + offset by omega] at code
  exact code

end Placement

section PlacedRuns

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

theorem runsAs_popBit (machine : Simulator) {stack : Fin 4} {target : Register} {base : Nat}
    (placed : Placed machine (.popBit stack target) base) :
    RunsAs machine base (fun memory (oracle : OState FixedIndex EncIndex) =>
      PMF.pure (some (popInto memory stack target, oracle))) 2 (base + 4) := by
  have fits := placed.1
  simp only [Prog.size] at fits
  have popCode := placed_code placed (offset := 0) (by simp [Prog.size])
  simp only [emit, if_pos, Nat.add_zero] at popCode
  have constCode (offset : Nat) (range : 1 ≤ offset ∧ offset ≤ 3) :
      codeAt machine (base + offset) =
        (NInstr.op (.constant target (if offset = 1 then 0 else if offset = 2 then 1 else 2))
          (base + 4)).toInstr machine.size := by
    have code := placed_code placed (offset := offset) (by simp only [Prog.size]; omega)
    rcases range with ⟨low, high⟩
    interval_cases offset <;> simpa [emit] using code
  intro fuel memory oracle
  cases fuel with
  | zero => rw [run_zero, PMF.pure_bind, after, if_neg (by omega)]
  | succ fuel =>
      rw [run_succ, step_pop machine (by omega) stack (base + 3) (base + 1) (base + 2) popCode,
        PMF.pure_bind, PMF.pure_bind]
      dsimp only
      have finish : ∀ (offset : Nat) (range : 1 ≤ offset ∧ offset ≤ 3) (next : Memory),
          (machine.run fuel (atPc machine (base + offset) next) oracle).map
              (Option.map fun result => (result.1, result.2.1, result.2.2 + 1)) =
            after machine 2 (base + 4) (fuel + 1) (some (setReg next target
              (if offset = 1 then 0 else if offset = 2 then 1 else 2), oracle)) := by
        intro offset range next
        rw [runsAs_op machine (by omega) _ _ (constCode offset range) fuel next oracle,
          Op.sem, PMF.pure_bind, after_map_succ]
      cases bits : memory.bits stack with
      | nil =>
          have := finish 3 (by omega) memory
          simp only [show (3 : Nat) ≠ 1 by omega, show (3 : Nat) ≠ 2 by omega, if_false] at this
          simp only [popInto, bits]
          exact this
      | cons bit rest =>
          cases bit
          · have := finish 1 (by omega) { memory with bits := Function.update memory.bits stack rest }
            simp only [if_pos rfl] at this
            simp only [popInto, bits, Bool.false_eq_true, if_false]
            exact this
          · have := finish 2 (by omega) { memory with bits := Function.update memory.bits stack rest }
            simp only [show (2 : Nat) ≠ 1 by omega, if_false, if_pos rfl] at this
            simp only [popInto, bits, if_true]
            exact this

theorem runsAs_abort (machine : Simulator) {scratch : Register} {base : Nat}
    (placed : Placed machine (.abort scratch) base) :
    RunsAs machine base (fun (_ : Memory) (_ : OState FixedIndex EncIndex) => PMF.pure none) 2
      (base + 2) := by
  have fits := placed.1
  simp only [Prog.size] at fits
  have first := placed_code placed (offset := 0) (by simp [Prog.size])
  have second := placed_code placed (offset := 1) (by simp [Prog.size])
  simp only [emit, if_pos, Nat.add_zero] at first
  simp only [emit, show (1 : Nat) ≠ 0 by omega, if_false] at second
  have joined := runsAs_andThen machine
    (runsAs_op (FixedIndex := FixedIndex) (EncIndex := EncIndex) machine (by omega) _ _ first)
    (runsAs_op (FixedIndex := FixedIndex) (EncIndex := EncIndex) machine (by omega) _ _ second)
  refine runsAs_congr machine ?_ joined
  funext memory oracle
  have tag : (setReg memory scratch 2).registers scratch = 2 := by simp [setReg]
  have invalid : readPoint (setReg memory scratch 2).registers ⟨scratch, scratch, scratch⟩ = none := by
    simp only [readPoint, tag]
    simp (config := { decide := true })
  simp only [andThen, Op.sem, PMF.pure_bind, invalid]

/-- The padded conditional runs the arm its register selects, at the balanced charge. -/
theorem runsAs_ite (machine : Simulator) {source : Register} {whenSet whenClear : Prog}
    {base : Nat} (placed : Placed machine (.ite source whenSet whenClear) base)
    (setRuns : RunsAs machine (base + 1) (Prog.sem (FixedIndex := FixedIndex)
      (EncIndex := EncIndex) whenSet) whenSet.cost (base + 1 + whenSet.size))
    (clearRuns : RunsAs machine (base + (2 + whenSet.size + Prog.padSet whenSet whenClear))
      (Prog.sem (FixedIndex := FixedIndex) (EncIndex := EncIndex) whenClear) whenClear.cost
      (base + (2 + whenSet.size + Prog.padSet whenSet whenClear) + whenClear.size)) :
    RunsAs machine base (Prog.sem (FixedIndex := FixedIndex) (EncIndex := EncIndex)
      (.ite source whenSet whenClear)) (Prog.ite source whenSet whenClear).cost
      (base + (Prog.ite source whenSet whenClear).size) := by
  have fits := placed.1
  have sizeEq : (Prog.ite source whenSet whenClear).size = 2 + whenSet.size +
      Prog.padSet whenSet whenClear + whenClear.size + Prog.padClear whenSet whenClear := rfl
  have costEq : (Prog.ite source whenSet whenClear).cost =
      1 + max (whenSet.cost + 1) whenClear.cost := rfl
  have balanceA : whenSet.cost + Prog.padSet whenSet whenClear + 1 =
      max (whenSet.cost + 1) whenClear.cost := by
    simp only [Prog.padSet]; omega
  have balanceB : whenClear.cost + Prog.padClear whenSet whenClear =
      max (whenSet.cost + 1) whenClear.cost := by
    simp only [Prog.padClear]; omega
  rw [sizeEq] at fits
  have branchCode := placed_code placed (offset := 0) (by rw [sizeEq]; omega)
  rw [emit_ite_branch] at branchCode
  simp only [Nat.add_zero] at branchCode
  have padSetRuns := runsAs_jumps (FixedIndex := FixedIndex) (EncIndex := EncIndex) machine
    (Prog.padSet whenSet whenClear) (base + 1 + whenSet.size) (by omega) (fun offset inside => by
      have code := placed_code placed (offset := 1 + whenSet.size + offset) (by rw [sizeEq]; omega)
      rw [emit_ite_padSet source whenSet whenClear base offset inside,
        show base + (1 + whenSet.size + offset) = base + 1 + whenSet.size + offset by omega] at code
      exact code)
  have closeCode := placed_code placed (offset := 1 + whenSet.size + Prog.padSet whenSet whenClear)
    (by rw [sizeEq]; omega)
  rw [emit_ite_close] at closeCode
  have closeRuns := runsAs_jump (FixedIndex := FixedIndex) (EncIndex := EncIndex) machine
    (by omega) _ closeCode
  have setArm := runsAs_andThen machine (runsAs_andThen machine setRuns padSetRuns)
    (runsAs_charge machine rfl rfl (by
      rw [show base + 1 + whenSet.size + Prog.padSet whenSet whenClear =
        base + (1 + whenSet.size + Prog.padSet whenSet whenClear) by omega]
      exact closeRuns))
  rw [andThen_idLaw, andThen_idLaw] at setArm
  have padClearRuns := runsAs_jumps (FixedIndex := FixedIndex) (EncIndex := EncIndex) machine
    (Prog.padClear whenSet whenClear)
    (base + (2 + whenSet.size + Prog.padSet whenSet whenClear) + whenClear.size) (by omega)
    (fun offset inside => by
      have code := placed_code placed
        (offset := 2 + whenSet.size + Prog.padSet whenSet whenClear + whenClear.size + offset)
        (by rw [sizeEq]; omega)
      rw [emit_ite_padClear source whenSet whenClear base offset inside,
        show base + (2 + whenSet.size + Prog.padSet whenSet whenClear + whenClear.size + offset) =
          base + (2 + whenSet.size + Prog.padSet whenSet whenClear) + whenClear.size + offset
          by omega] at code
      exact code)
  have clearArm := runsAs_andThen machine clearRuns padClearRuns
  rw [andThen_idLaw] at clearArm
  have clearCharge : whenClear.cost + Prog.padClear whenSet whenClear + 1 =
      (Prog.ite source whenSet whenClear).cost := by rw [costEq, ← balanceB]; omega
  have clearExit : base + (2 + whenSet.size + Prog.padSet whenSet whenClear) + whenClear.size +
      Prog.padClear whenSet whenClear = base + (Prog.ite source whenSet whenClear).size := by
    rw [sizeEq]; omega
  have setCharge : whenSet.cost + Prog.padSet whenSet whenClear + 1 + 1 =
      (Prog.ite source whenSet whenClear).cost := by rw [costEq, ← balanceA]; omega
  intro fuel memory oracle
  cases fuel with
  | zero =>
      rw [run_zero, bind_after_short machine (by rw [costEq]; omega)]
  | succ fuel =>
      rw [run_branch machine (by omega) source _ _ branchCode fuel memory oracle]
      by_cases zero : memory.registers source = 0
      · simp only [zero, if_true, Prog.sem]
        rw [clearArm fuel memory oracle, PMF.map_bind]
        congr 1
        funext result
        rw [after_map_succ, clearCharge, clearExit]
      · simp only [zero, if_false, Prog.sem]
        rw [setArm fuel memory oracle, PMF.map_bind]
        congr 1
        funext result
        rw [after_map_succ, setCharge]

/-- **Compiler correctness.** A placed program runs by its law, at exactly its static cost,
and resumes at its exit. -/
theorem run_placed (machine : Simulator) :
    ∀ (program : Prog) (base : Nat), Placed machine program base →
      RunsAs machine base (Prog.sem (FixedIndex := FixedIndex) (EncIndex := EncIndex) program)
        program.cost (base + program.size)
  | .op operation, base, placed => by
      have code := placed_code placed (offset := 0) (by simp [Prog.size])
      simp only [emit, Nat.add_zero] at code
      have fits := placed.1
      simp only [Prog.size] at fits
      exact runsAs_op machine (by omega) operation (base + 1) code
  | .popBit stack target, base, placed => runsAs_popBit machine placed
  | .skip count, base, placed =>
      runsAs_jumps machine count base placed.1 (fun offset inside => by
        have := placed_code placed (offset := offset) inside
        simpa [emit] using this)
  | .abort scratch, base, placed => runsAs_abort machine placed
  | .seq first second, base, placed => by
      have runFirst := run_placed machine first base (placed_seq_first placed)
      have runSecond := run_placed machine second (base + first.size) (placed_seq_second placed)
      have joined := runsAs_andThen machine runFirst runSecond
      exact runsAs_charge machine rfl (by simp only [Prog.size]; omega) joined
  | .ite source whenSet whenClear, base, placed =>
      runsAs_ite machine placed
        (run_placed machine whenSet (base + 1) (placed_ite_set placed))
        (run_placed machine whenClear _ (placed_ite_clear placed))

end PlacedRuns

end Kriterion.ArgoMAC.PlanB.SimMachine
