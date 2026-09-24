/-
**Query trees: the machine's replay and the abstract evaluator as the same free program.**

A coin-free, program-free machine block is deterministic given the oracle's answers, so its law
is the run of a free query tree on the lazy oracle (`Prog.tree`, `sem_eq_runT`). The abstract
side's `runIntercept` is the run of the intercepted tree (`interceptT`, `runIntercept_eq_runT`).

`Agree Post T S` says the machine tree `T` and the abstract tree `S` ask the same questions in the
same order and end in related leaves; `agree_run` turns it into an equality of the two runs
followed by any continuations that agree on related leaves. Composition is `Agree.bindOpt`.
-/

import Proof.Simulator.Stage2Invalid

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### Free query programs: monad laws and the lazy run -/

namespace TreeLaws

variable {spec : OracleSpec.{0, 0}} {α β γ : Type}

theorem bind_pure_left (value : α) (next : α → FreeQuery spec β) :
    FreeQuery.bind (.pure value) next = next value := rfl

theorem bind_query (request : spec.Query) (rest : spec.Answer request → FreeQuery spec α)
    (next : α → FreeQuery spec β) :
    FreeQuery.bind (.query request rest) next =
      .query request fun answer => FreeQuery.bind (rest answer) next := rfl

theorem bind_assoc : ∀ (program : FreeQuery spec α) (first : α → FreeQuery spec β)
    (second : β → FreeQuery spec γ),
    FreeQuery.bind (FreeQuery.bind program first) second =
      FreeQuery.bind program fun value => FreeQuery.bind (first value) second
  | .pure _, _, _ => rfl
  | .query request rest, first, second => by
      simp only [bind_query]
      congr 1
      funext answer
      exact bind_assoc (rest answer) first second

theorem bind_pure_right : ∀ (program : FreeQuery spec α),
    FreeQuery.bind program (fun value => .pure value) = program
  | .pure _ => rfl
  | .query request rest => by
      simp only [bind_query]
      congr 1
      funext answer
      exact bind_pure_right (rest answer)

theorem monad_bind (program : FreeQuery spec α) (next : α → FreeQuery spec β) :
    program >>= next = FreeQuery.bind program next := rfl

theorem monad_pure (value : α) : (pure value : FreeQuery spec α) = .pure value := rfl

end TreeLaws

section Run

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- A free query program run on the lazy oracle. -/
noncomputable def runT {α : Type} :
    FreeQuery (publicOracleSpec FixedIndex EncIndex) α → OState FixedIndex EncIndex →
      PMF (α × OState FixedIndex EncIndex)
  | .pure value, oracle => PMF.pure (value, oracle)
  | .query request next, oracle =>
      (LazyOracle.query request oracle).bind fun answer => runT (next answer.1) answer.2

theorem runT_bind {α β : Type} :
    ∀ (program : FreeQuery (publicOracleSpec FixedIndex EncIndex) α)
      (next : α → FreeQuery (publicOracleSpec FixedIndex EncIndex) β)
      (oracle : OState FixedIndex EncIndex),
      runT (FreeQuery.bind program next) oracle =
        (runT program oracle).bind fun result => runT (next result.1) result.2
  | .pure _, _, _ => by simp [FreeQuery.bind, runT]
  | .query request rest, next, oracle => by
      simp only [TreeLaws.bind_query, runT, PMF.bind_bind]
      congr 1
      funext answer
      exact runT_bind (rest answer.1) next answer.2

end Run

/-! ### The machine tree -/

section MachineTree

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- An operation the tree semantics covers: no coin, no lookup, no program. -/
def TreeOp : Op → Prop
  | .coin _ | .lookup .. | .program .. => False
  | _ => True

/-- One operation as a query tree. -/
noncomputable def Op.tree (operation : Op) (memory : Memory) :
    FreeQuery (publicOracleSpec FixedIndex EncIndex) (Option Memory) :=
  match operation with
  | .constant target value => .pure (some (setReg memory target value))
  | .arith operation target left right =>
      .pure (some (setReg memory target
        (operation.eval (memory.registers left) (memory.registers right))))
  | .load target address => .pure (some (setReg memory target (memory.ram (memory.registers address))))
  | .store address source =>
      .pure (some (storeRam memory (memory.registers address) (memory.registers source)))
  | .push stack bit => .pure (some (pushOn memory stack bit))
  | .pushBit stack source => .pure (some (pushOn memory stack ((memory.registers source).getLsbD 0)))
  | .coin _ => .pure none
  | .pointAdd target left right =>
      match readPoint memory.registers left, readPoint memory.registers right with
      | some a, some b => .pure (some (writePointMem memory target (a + b)))
      | _, _ => .pure none
  | .query kind index input first second =>
      match queryFromRegisters (FixedIndex := FixedIndex) (EncIndex := EncIndex) kind
          (memory.registers index) (memory.registers input) with
      | none => .pure none
      | some request => .query request fun answer =>
          .pure (some (writePair memory first second (answerWords request answer)))
  | .lookup .. => .pure none
  | .program .. => .pure none

/-- Continue a tree after a non-aborting result. -/
def bindOpt {spec : OracleSpec.{0, 0}} (tree : FreeQuery spec (Option Memory))
    (next : Memory → FreeQuery spec (Option Memory)) : FreeQuery spec (Option Memory) :=
  FreeQuery.bind tree fun result => match result with
    | none => .pure none
    | some memory => next memory

/-- A structured program as a query tree. -/
noncomputable def Prog.tree : Prog → Memory →
    FreeQuery (publicOracleSpec FixedIndex EncIndex) (Option Memory)
  | .op operation, memory => operation.tree memory
  | .popBit stack target, memory => .pure (some (popInto memory stack target))
  | .skip _, memory => .pure (some memory)
  | .abort _, _ => .pure none
  | .seq first second, memory => bindOpt (first.tree memory) second.tree
  | .ite source whenSet whenClear, memory =>
      if memory.registers source = 0 then whenClear.tree memory else whenSet.tree memory

/-- The lowering of a tree leaf and the oracle to a machine result. -/
def lower (result : Option Memory × OState FixedIndex EncIndex) :
    Option (Memory × OState FixedIndex EncIndex) :=
  result.1.map fun memory => (memory, result.2)

/-- **A tree block runs as its tree.** -/
theorem sem_eq_runT : ∀ (program : Prog), program.OpsSatisfy TreeOp →
    ∀ (memory : Memory) (oracle : OState FixedIndex EncIndex),
      program.sem memory oracle = (runT (program.tree memory) oracle).map lower
  | .op operation, allowed, memory, oracle => by
      cases operation with
      | coin => exact absurd allowed (by simp [Prog.OpsSatisfy, TreeOp])
      | lookup => exact absurd allowed (by simp [Prog.OpsSatisfy, TreeOp])
      | program => exact absurd allowed (by simp [Prog.OpsSatisfy, TreeOp])
      | query kind index input first second =>
          simp only [Prog.sem, Prog.tree, Op.sem, Op.tree]
          cases queryFromRegisters (FixedIndex := FixedIndex) (EncIndex := EncIndex) kind
              (memory.registers index) (memory.registers input) with
          | none => simp [runT, lower, PMF.pure_map]
          | some request =>
              simp only [runT, PMF.map_bind, PMF.pure_map, lower, Option.map_some]
              rw [PMF.map]
              rfl
      | pointAdd target left right =>
          simp only [Prog.sem, Prog.tree, Op.sem, Op.tree]
          cases readPoint memory.registers left <;> cases readPoint memory.registers right <;>
            simp [runT, lower, PMF.pure_map]
      | _ => simp [Prog.sem, Prog.tree, Op.sem, Op.tree, runT, lower, PMF.pure_map]
  | .popBit _ _, _, memory, oracle => by simp [Prog.sem, Prog.tree, runT, lower, PMF.pure_map]
  | .skip _, _, memory, oracle => by simp [Prog.sem, Prog.tree, runT, lower, PMF.pure_map]
  | .abort _, _, memory, oracle => by simp [Prog.sem, Prog.tree, runT, lower, PMF.pure_map]
  | .seq first second, allowed, memory, oracle => by
      simp only [Prog.sem, andThen, Prog.tree, bindOpt, runT_bind, PMF.map_bind]
      rw [sem_eq_runT first allowed.1 memory oracle, PMF.bind_map]
      congr 1
      funext result
      rcases result with ⟨_ | next, updated⟩
      · simp [runT, lower, PMF.pure_map]
      · simp only [Function.comp_apply, lower, Option.map_some]
        exact sem_eq_runT second allowed.2 next updated
  | .ite source whenSet whenClear, allowed, memory, oracle => by
      simp only [Prog.sem, Prog.tree]
      split
      · exact sem_eq_runT whenClear allowed.2 memory oracle
      · exact sem_eq_runT whenSet allowed.1 memory oracle

end MachineTree

/-! ### Agreement of a machine tree and an abstract tree -/

section Agree

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- The machine tree and the abstract tree ask the same questions in the same order and end in
leaves related by `Post` (the machine never aborts). -/
inductive Agree {β : Type} (Post : β → Memory → Prop) :
    FreeQuery (publicOracleSpec FixedIndex EncIndex) (Option Memory) →
      FreeQuery (publicOracleSpec FixedIndex EncIndex) β → Prop
  | leaf {memory : Memory} {value : β} (related : Post value memory) :
      Agree Post (.pure (some memory)) (.pure value)
  | node (request : PublicQuery FixedIndex EncIndex)
      {next : request.Answer → FreeQuery (publicOracleSpec FixedIndex EncIndex) (Option Memory)}
      {next' : request.Answer → FreeQuery (publicOracleSpec FixedIndex EncIndex) β}
      (each : ∀ answer, Agree Post (next answer) (next' answer)) :
      Agree Post (.query request next) (.query request next')

theorem Agree.mono {β : Type} {Post Post' : β → Memory → Prop}
    (weaker : ∀ value memory, Post value memory → Post' value memory) :
    ∀ {tree : FreeQuery (publicOracleSpec FixedIndex EncIndex) (Option Memory)}
      {tree' : FreeQuery (publicOracleSpec FixedIndex EncIndex) β},
      Agree Post tree tree' → Agree Post' tree tree'
  | _, _, .leaf related => .leaf (weaker _ _ related)
  | _, _, .node request each => .node request fun answer => (each answer).mono weaker

/-- **Composition.** -/
theorem Agree.bindOpt {β γ : Type} {Post : β → Memory → Prop} {Post' : γ → Memory → Prop}
    {next : Memory → FreeQuery (publicOracleSpec FixedIndex EncIndex) (Option Memory)}
    {next' : β → FreeQuery (publicOracleSpec FixedIndex EncIndex) γ}
    (continues : ∀ value memory, Post value memory → Agree Post' (next memory) (next' value)) :
    ∀ {tree : FreeQuery (publicOracleSpec FixedIndex EncIndex) (Option Memory)}
      {tree' : FreeQuery (publicOracleSpec FixedIndex EncIndex) β},
      Agree Post tree tree' →
        Agree Post' (SimMachine.bindOpt tree next) (FreeQuery.bind tree' next')
  | _, _, .leaf related => continues _ _ related
  | _, _, .node request each => .node request fun answer => (each answer).bindOpt continues

/-- **Agreeing trees run alike**: the machine run followed by `onMachine` is the abstract run
followed by `onAbstract`, when the two continuations agree on related leaves. -/
theorem agree_run {β δ : Type} {Post : β → Memory → Prop}
    (onMachine : Memory → OState FixedIndex EncIndex → PMF (Option δ))
    (onAbstract : β → OState FixedIndex EncIndex → PMF (Option δ))
    (agreeing : ∀ value memory oracle, Post value memory →
      onMachine memory oracle = onAbstract value oracle) :
    ∀ {tree : FreeQuery (publicOracleSpec FixedIndex EncIndex) (Option Memory)}
      {tree' : FreeQuery (publicOracleSpec FixedIndex EncIndex) β},
      Agree Post tree tree' → ∀ oracle,
        (runT tree oracle).bind (fun result => match result.1 with
          | none => PMF.pure none
          | some memory => onMachine memory result.2) =
        (runT tree' oracle).bind fun result => onAbstract result.1 result.2
  | _, _, .leaf related, oracle => by
      simp only [runT, PMF.pure_bind]
      exact agreeing _ _ _ related
  | _, _, .node request each, oracle => by
      simp only [runT, PMF.bind_bind]
      congr 1
      funext answer
      exact agree_run onMachine onAbstract agreeing (each answer.1) answer.2

end Agree

/-! ### The intercepted abstract tree -/

section Intercept

/-- The designated queries answered inline by `(0, 0)`, the record updated. -/
noncomputable def interceptT {α : Type} (bits : BitInput) :
    FreeQuery Programs.Spec α → DesignatedRecord →
      FreeQuery Programs.Spec (α × DesignatedRecord)
  | .pure value, record => .pure (value, record)
  | .query request next, record =>
      match interceptAnswer bits request with
      | some answer => interceptT bits (next answer) (recordAfter bits request record)
      | none => .query request fun answer => interceptT bits (next answer) record

/-- An intercepted question is answered inline and recorded. -/
theorem interceptT_query_some {α : Type} (bits : BitInput)
    (request : PublicQuery PlanB.FixedIndex EncPRF.PermutationIndex)
    (next : request.Answer → FreeQuery Programs.Spec α) (record : DesignatedRecord)
    (answer : request.Answer) (answered : interceptAnswer bits request = some answer) :
    interceptT bits (.query request next) record =
      interceptT bits (next answer) (recordAfter bits request record) := by
  simp only [interceptT, answered]

/-- **`runIntercept` is the run of the intercepted tree.** -/
theorem runIntercept_eq_runT [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    {α : Type} (bits : BitInput) :
    ∀ (program : FreeQuery Programs.Spec α) (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex)
      (record : DesignatedRecord),
      runIntercept bits program oracle record =
        (runT (interceptT bits program record) oracle).map fun result =>
          (result.1.1, result.2, result.1.2)
  | .pure value, oracle, record => by
      simp [runIntercept, interceptT, runT, PMF.pure_map]
  | .query request next, oracle, record => by
      simp only [runIntercept, interceptT]
      cases interceptAnswer bits request with
      | some answer =>
          dsimp only
          exact runIntercept_eq_runT bits (next answer) oracle _
      | none =>
          dsimp only
          simp only [runT, PMF.map_bind]
          congr 1
          funext answer
          exact runIntercept_eq_runT bits (next answer.1) answer.2 record

theorem interceptT_bind {α β : Type} (bits : BitInput) :
    ∀ (program : FreeQuery Programs.Spec α) (next : α → FreeQuery Programs.Spec β)
      (record : DesignatedRecord),
      interceptT bits (FreeQuery.bind program next) record =
        FreeQuery.bind (interceptT bits program record) fun result =>
          interceptT bits (next result.1) result.2
  | .pure _, _, _ => rfl
  | .query request rest, next, record => by
      simp only [TreeLaws.bind_query, interceptT]
      cases interceptAnswer bits request with
      | some answer => exact interceptT_bind bits (rest answer) next _
      | none =>
          simp only [TreeLaws.bind_query]
          congr 1
          funext answer
          exact interceptT_bind bits (rest answer) next record

/-- A tree none of whose questions is intercepted. -/
inductive Clean (bits : BitInput) {α : Type} : FreeQuery Programs.Spec α → Prop
  | pure (value : α) : Clean bits (.pure value)
  | query (request : PublicQuery PlanB.FixedIndex EncPRF.PermutationIndex)
      {next : request.Answer → FreeQuery Programs.Spec α}
      (asked : interceptAnswer bits request = none) (each : ∀ answer, Clean bits (next answer)) :
      Clean bits (.query request next)

/-- A clean tree is intercepted as itself, the record unchanged. -/
theorem interceptT_clean {α : Type} (bits : BitInput) (record : DesignatedRecord) :
    ∀ {program : FreeQuery Programs.Spec α}, Clean bits program →
      interceptT bits program record = FreeQuery.bind program fun value => .pure (value, record)
  | _, .pure _ => rfl
  | _, .query request asked each => by
      simp only [interceptT, asked, TreeLaws.bind_query]
      congr 1
      funext answer
      exact interceptT_clean bits record (each answer)

theorem Clean.bind {α β : Type} {bits : BitInput} {next : α → FreeQuery Programs.Spec β}
    (rest : ∀ value, Clean bits (next value)) :
    ∀ {program : FreeQuery Programs.Spec α}, Clean bits program →
      Clean bits (FreeQuery.bind program next)
  | _, .pure value => rest value
  | _, .query request asked each => .query request asked fun answer => (each answer).bind rest

theorem Clean.vector {α : Type} {bits : BitInput} :
    ∀ (count : Nat) {program : Fin count → FreeQuery Programs.Spec α},
      (∀ index, Clean bits (program index)) → Clean bits (FreeQuery.vector count program)
  | 0, _, _ => .pure _
  | count + 1, program, each => by
      simp only [FreeQuery.vector, TreeLaws.monad_bind]
      exact (Clean.vector count fun index => each index.castSucc).bind fun _ =>
        (each (Fin.last count)).bind fun _ => .pure _

theorem Clean.ask {bits : BitInput} (request : PublicQuery PlanB.FixedIndex EncPRF.PermutationIndex)
    (asked : interceptAnswer bits request = none) :
    Clean bits (FreeQuery.ask (spec := Programs.Spec) request) :=
  .query request asked fun answer => .pure answer

end Intercept

end

end Kriterion.ArgoMAC.PlanB.SimMachine
