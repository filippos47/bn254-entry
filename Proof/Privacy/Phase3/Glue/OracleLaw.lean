/-
Phase 3 glue: the generic lazy-oracle law (note C, T03).

Ported from the baseline `argomac-lean` (`Proof/Privacy/Simulator/{OperationalOracleLaw,
OperationalFamilyLaw, OperationalHashLaw, PublicOracleLaw}.lean`, commit c564e51), which targets the
same library revision `aaf2789`. The content is the baseline's, restricted to what
`public_run` and `lazy_real_uniform` need; the only edits are

* the namespace `Kriterion.ArgoMAC.Phase3.Glue` (so a second port elsewhere cannot clash), and
* the dot-notation calls of the ported `SparsePermutation.*` / `HashTable.*` extensions, which are
  written as ordinary applications because the extensions now live in this namespace.

The two headline results:

* `public_run`: the shared lazy oracle and its eager completion have the same joint law under
  every adaptive oracle program;
* `lazy_real_uniform`: the library's `lazyRealGame` with a query-program garbler is the game that
  samples coins, then one uniform eager oracle, and runs the garbler's `eval` and both adversary
  stages against it.
-/

import Proof.Privacy.Phase3.Glue.Uniform
import Security.AdaptivePrivacy
import Mathlib.Data.Fin.Tuple.Basic

namespace Kriterion.ArgoMAC.Phase3.Glue

open Cryptography GarbledCircuit
open Kriterion.ArgoMAC.Security.OperationalOracle

noncomputable section

/-! ### One sparse permutation (baseline `OperationalOracleLaw`) -/

section Sparse

open Kriterion.ArgoMAC.Security.OperationalOracle.SparsePermutation

/-- This function records the pair that an eager forward query reveals. -/
def SparsePermutation.afterForward {size : Nat} (state : SparsePermutation size)
    (x y : Fin size) : SparsePermutation size :=
  if known : state.knownInput x then state
  else state.extend (by have := (state.input.symm x).isLt; unfold knownInput at known; omega)
    (state.input.symm x) (state.output.symm y)

theorem SparsePermutation.afterForward_of_fresh {size : Nat} (state : SparsePermutation size)
    (x : Fin size) (fresh : ¬ state.knownInput x) (y : Fin size)
    (room : state.used < size) :
    (SparsePermutation.afterForward state) x y = state.extend room (state.input.symm x) (state.output.symm y) := by
  unfold afterForward
  split
  · contradiction
  · rfl

/-- A fresh output separates the eager completion into an answer and a fixed fiber. -/
def SparsePermutation.answerEquiv {size : Nat} (state : SparsePermutation size)
    (x : Fin size) (fresh : ¬ state.knownInput x)
    (reference : {y : Fin size // ¬ state.knownOutput y}) :
    state.Completion ≃ {y : Fin size // ¬ state.knownOutput y} ×
      {π : Equiv.Perm (Fin size) //
        (∀ a : {a : Fin size // state.knownInput a}, π a = state.assignment a) ∧
        π x = reference.val} :=
  (programCompatiblePermutationEquiv {a | state.knownInput a} {a | state.knownOutput a}
    state.assignment x fresh reference.val reference.property).trans (Equiv.prodComm _ _)

/-- The answer fiber is exactly the completed sparse update. -/
def SparsePermutation.answerFiberEquiv {size : Nat} (state : SparsePermutation size)
    (x : Fin size) (fresh : ¬ state.knownInput x)
    (reference answer : {y : Fin size // ¬ state.knownOutput y}) :
    ((SparsePermutation.afterForward state) x answer.val).Completion ≃
      {π : state.Completion // ((SparsePermutation.answerEquiv state) x fresh reference π).1 = answer} := by
  have room : state.used < size := by
    have := (state.input.symm x).isLt
    unfold knownInput at fresh
    omega
  have freshInput : state.used ≤ (state.input.symm x).val := Nat.le_of_not_gt fresh
  have freshOutput : state.used ≤ (state.output.symm answer.val).val :=
    Nat.le_of_not_gt answer.property
  have same (π : state.Completion) :
      π.val (state.input (state.input.symm x)) = state.output (state.output.symm answer.val) ↔
        ((SparsePermutation.answerEquiv state) x fresh reference π).1 = answer := by
    simp only [Equiv.apply_symm_apply]
    constructor
    · intro equal
      apply Subtype.ext
      exact equal
    · intro equal
      exact congrArg Subtype.val equal
  have transport (π : Equiv.Perm (Fin size)) :
      (∀ a : {a : Fin size // ((SparsePermutation.afterForward state) x answer.val).knownInput a},
        π a = ((SparsePermutation.afterForward state) x answer.val).assignment a) ↔
      (∀ a : {a : Fin size // state.knownInput a}, π a = state.assignment a) ∧
        π (state.input (state.input.symm x)) = state.output (state.output.symm answer.val) := by
    rw [(SparsePermutation.afterForward_of_fresh state) x fresh answer.val room]
    exact state.extend_completion_iff room (state.input.symm x)
      (state.output.symm answer.val) freshInput freshOutput π
  exact {
    toFun := fun π =>
      ⟨⟨π.val, ((transport π.val).mp π.property).1⟩,
        (same _).mp ((transport π.val).mp π.property).2⟩
    invFun := fun π =>
      ⟨π.val.val, (transport π.val.val).mpr ⟨π.val.property, (same π.val).mpr π.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }

/-- A sparse update retains the exact full conditional permutation law. -/
theorem SparsePermutation.forward_fresh_completion {size : Nat}
    (state : SparsePermutation size) (x : Fin size) (fresh : ¬ state.knownInput x)
    (reference : {y : Fin size // ¬ state.knownOutput y}) :
    letI : Nonempty {y : Fin size // ¬ state.knownOutput y} := ⟨reference⟩
    (PMF.uniformOfFintype state.Completion).map Subtype.val =
      (PMF.uniformOfFintype {y : Fin size // ¬ state.knownOutput y}).bind (fun answer =>
        (PMF.uniformOfFintype ((SparsePermutation.afterForward state) x answer.val).Completion).map Subtype.val) := by
  classical
  letI : Nonempty {y : Fin size // ¬ state.knownOutput y} := ⟨reference⟩
  let equiv := (SparsePermutation.answerEquiv state) x fresh reference
  letI : Nonempty {π : Equiv.Perm (Fin size) //
      (∀ a : {a : Fin size // state.knownInput a}, π a = state.assignment a) ∧
      π x = reference.val} :=
    ⟨(equiv (Classical.choice inferInstance)).2⟩
  have split := congrArg (fun distribution : PMF state.Completion => distribution.map Subtype.val)
    (uniform_fiber equiv)
  simp only [PMF.map_bind, PMF.map_comp] at split
  rw [split]
  congr 1
  funext answer
  letI : Nonempty {π : state.Completion // (equiv π).1 = answer} :=
    ⟨(SparsePermutation.answerFiberEquiv state) x fresh reference answer (Classical.choice inferInstance)⟩
  rw [← uniform_equiv ((SparsePermutation.answerFiberEquiv state) x fresh reference answer), PMF.map_comp]
  rfl

/-- A completed fresh update contains its newly revealed pair. -/
theorem SparsePermutation.afterForward_pair {size : Nat}
    (state : SparsePermutation size) (x : Fin size) (fresh : ¬ state.knownInput x)
    (answer : {y : Fin size // ¬ state.knownOutput y})
    (π : ((SparsePermutation.afterForward state) x answer.val).Completion) : π.val x = answer.val :=
  congrArg Subtype.val ((SparsePermutation.answerFiberEquiv state) x fresh answer answer π).property

/-- The forward law preserves the answer, sparse state, and complete eager permutation together. -/
theorem SparsePermutation.forward_joint {size : Nat}
    (state : SparsePermutation size) (x : Fin size) :
    (PMF.uniformOfFintype state.Completion).map
        (fun π => (π.val x, (SparsePermutation.afterForward state) x (π.val x), π.val)) =
      (state.forward x).distribution.bind (fun answer =>
        (PMF.uniformOfFintype answer.2.Completion).map
          (fun π => (answer.1, answer.2, π.val))) := by
  classical
  by_cases known : state.knownInput x
  · have same (π : state.Completion) : π.val x = state.output (state.input.symm x) :=
      π.property ⟨x, known⟩
    simp only [forward, knownInput] at known ⊢
    simp only [dif_pos known, Draw.distribution, PMF.pure_bind]
    simp_rw [same]
    simp [afterForward, knownInput, known]
  · have room : state.used < size := by
      have := (state.input.symm x).isLt
      unfold knownInput at known
      omega
    letI : Nonempty (Fin (size - state.used)) := ⟨⟨0, by omega⟩⟩
    let reference := state.unusedOutputEquiv ⟨0, by omega⟩
    letI : Nonempty {y : Fin size // ¬ state.knownOutput y} := ⟨reference⟩
    have joint := congrArg
      (fun distribution : PMF (Equiv.Perm (Fin size)) => distribution.map
        (fun π => (π x, (SparsePermutation.afterForward state) x (π x), π)))
      ((SparsePermutation.forward_fresh_completion state) x known reference)
    simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at joint
    simp_rw [(SparsePermutation.afterForward_pair state) x known] at joint
    apply joint.trans
    rw [← state.unusedOutput_uniform room, PMF.bind_map]
    simp only [forward, knownInput] at known ⊢
    simp only [dif_neg known, Draw.distribution, PMF.bind_map, Function.comp_def]
    congr 1
    funext rank
    change (PMF.uniformOfFintype
        ((SparsePermutation.afterForward state) x (state.output (state.suffix rank))).Completion).map
        (fun π => (state.output (state.suffix rank),
          (SparsePermutation.afterForward state) x (state.output (state.suffix rank)), π.val)) = _
    rw [(SparsePermutation.afterForward_of_fresh state) x known (state.output (state.suffix rank)) room]
    rw [Equiv.symm_apply_apply]

/-- An inverse query records the same pair in the reversed sparse state. -/
def SparsePermutation.afterInverse {size : Nat} (state : SparsePermutation size)
    (y x : Fin size) : SparsePermutation size := ((SparsePermutation.afterForward state.reverse) y x).reverse

/-- The inverse law preserves the answer, sparse state, and complete eager permutation together. -/
theorem SparsePermutation.inverse_joint {size : Nat}
    (state : SparsePermutation size) (y : Fin size) :
    (PMF.uniformOfFintype state.Completion).map
        (fun π => (π.val.symm y, (SparsePermutation.afterInverse state) y (π.val.symm y), π.val)) =
      (state.inverse y).distribution.bind (fun answer =>
        (PMF.uniformOfFintype answer.2.Completion).map
          (fun π => (answer.1, answer.2, π.val))) := by
  have reversed := congrArg
    (fun distribution : PMF (Fin size × SparsePermutation size × Equiv.Perm (Fin size)) =>
      distribution.map (fun output => (output.1, output.2.1.reverse, output.2.2.symm)))
    ((SparsePermutation.forward_joint state.reverse) y)
  simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at reversed
  have source := congrArg
    (fun distribution : PMF state.Completion => distribution.map
      (fun π => (π.val.symm y, (SparsePermutation.afterInverse state) y (π.val.symm y), π.val)))
    (uniform_equiv state.reverse_completionEquiv)
  simp only [PMF.map_comp, Function.comp_def] at source
  calc
    _ = (PMF.uniformOfFintype state.reverse.Completion).map
        (fun π => (π.val y, ((SparsePermutation.afterForward state.reverse) y (π.val y)).reverse, π.val.symm)) :=
      source.symm
    _ = _ := by
      apply reversed.trans
      rw [inverse_reverse_forward, Draw.map_distribution, PMF.bind_map]
      congr 1
      funext answer
      have target := congrArg
        (fun distribution : PMF answer.2.reverse.Completion => distribution.map
          (fun π => (answer.1, answer.2.reverse, π.val)))
        (uniform_equiv answer.2.reverse_completionEquiv.symm)
      simp only [PMF.map_comp, Function.comp_def] at target
      convert target using 1 <;> rfl

/-- A one-step joint law extends to every adaptive oracle program. -/
theorem adaptive_joint_law {oracle : OracleSpec} {Result Sparse Eager : Type}
    (eager : OracleHandler oracle Eager)
    (sparse : ∀ query, Sparse → PMF (oracle.Answer query × Sparse))
    (completion : Sparse → PMF Eager)
    (step : ∀ query state,
      (completion state).map (eager query) =
        (sparse query state).bind (fun answer =>
          (completion answer.2).map (fun eagerState => (answer.1, eagerState))))
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : Sparse) :
    (completion state).bind (fun eagerState => program.run eager eagerState) =
      (runSampled sparse program state).bind (fun output =>
        (completion output.2).map (fun eagerState => (output.1, eagerState))) := by
  induction program generalizing state with
  | pure distribution =>
      simp only [OracleProgram.run_pure, runSampled, PMF.bind_map, Function.comp_def]
      exact PMF.bind_comm _ _ _
  | query request next inductionHypothesis =>
      simp only [OracleProgram.run_query, runSampled, PMF.bind_bind]
      have transformed := congrArg
        (fun distribution : PMF (oracle.Answer request × Eager) =>
          distribution.bind (fun answer => (next answer.1).run eager answer.2)) (step request state)
      simp only [PMF.bind_map, Function.comp_def, PMF.bind_bind] at transformed
      rw [transformed]
      simp_rw [inductionHypothesis]
  | sample distribution next inductionHypothesis =>
      simp only [OracleProgram.run_sample, runSampled, PMF.bind_bind]
      rw [PMF.bind_comm]
      simp_rw [inductionHypothesis]


/-- The empty sparse state permits every eager permutation. -/
def emptyCompletionEquiv (size : Nat) :
    (SparsePermutation.empty size).Completion ≃ Equiv.Perm (Fin size) where
  toFun := Subtype.val
  invFun π := ⟨π, by intro a; exact (Nat.not_lt_zero _ a.property).elim⟩
  left_inv _ := rfl
  right_inv _ := rfl



end Sparse

/-! ### Independent families (baseline `OperationalFamilyLaw`) -/

/-- The family kernel samples independent conditional completions at all indices. -/
def finiteKernel {Sparse Eager : Type} (kernel : Sparse → PMF Eager) :
    {count : Nat} → (Fin count → Sparse) → PMF (Fin count → Eager)
  | 0, _ => PMF.pure Fin.elim0
  | _ + 1, state =>
      (kernel (state 0)).bind (fun head =>
        (finiteKernel kernel (Fin.tail state)).map (Fin.cons head))

/-- A family request selects one local oracle. -/
abbrev indexedSpec (Index : Type) (oracle : OracleSpec) : OracleSpec where
  Query := Index × oracle.Query
  Answer query := oracle.Answer query.2

/-- The eager family interpreter updates only the selected local state. -/
def indexedEager {Index State : Type} [DecidableEq Index] {oracle : OracleSpec}
    (handler : OracleHandler oracle State) : OracleHandler (indexedSpec Index oracle) (Index → State) :=
  fun query state =>
    let answer := handler query.2 (state query.1)
    (answer.1, Function.update state query.1 answer.2)

/-- The sampled family interpreter also updates only the selected local state. -/
def indexedSampled {Index State : Type} [DecidableEq Index] {oracle : OracleSpec}
    (handler : ∀ query, State → PMF (oracle.Answer query × State)) :
    ∀ query : (indexedSpec Index oracle).Query,
      (Index → State) → PMF ((indexedSpec Index oracle).Answer query × (Index → State)) :=
  fun query state => (handler query.2 (state query.1)).map
    (fun answer => (answer.1, Function.update state query.1 answer.2))

/-- Independent completion kernels preserve the local joint law at every family index. -/
theorem finiteKernel_step {oracle : OracleSpec} {Sparse Eager : Type}
    (eager : OracleHandler oracle Eager)
    (sampled : ∀ query, Sparse → PMF (oracle.Answer query × Sparse))
    (kernel : Sparse → PMF Eager)
    (step : ∀ query state,
      (kernel state).map (eager query) =
        (sampled query state).bind (fun answer =>
          (kernel answer.2).map (fun eagerState => (answer.1, eagerState))))
    {count : Nat} (query : (indexedSpec (Fin count) oracle).Query) (state : Fin count → Sparse) :
    (finiteKernel kernel state).map (indexedEager eager query) =
      (indexedSampled sampled query state).bind (fun answer =>
        (finiteKernel kernel answer.2).map (fun eagerState => (answer.1, eagerState))) := by
  induction count with
  | zero => exact Fin.elim0 query.1
  | succ count inductionHypothesis =>
      rcases query with ⟨index, request⟩
      refine Fin.cases ?_ (fun index => ?_) index
      · simp only [finiteKernel, indexedEager, indexedSampled, PMF.map_bind, PMF.map_comp,
          PMF.bind_map, Function.comp_def, Fin.cons_zero, Function.update_self, Fin.tail_update_zero]
        have law := congrArg
          (fun distribution : PMF (oracle.Answer request × Eager) =>
            distribution.bind (fun answer => (finiteKernel kernel (Fin.tail state)).map
              (fun tail => (answer.1, (Fin.cons answer.2 tail : Fin (count + 1) → Eager))))) (step request (state 0))
        simp only [PMF.bind_map, PMF.bind_bind, Function.comp_def] at law
        simpa only [Fin.update_cons_zero] using law
      · simp only [finiteKernel, indexedEager, indexedSampled, PMF.map_bind, PMF.map_comp,
          PMF.bind_map, Function.comp_def, Fin.cons_succ, Function.update_of_ne (Ne.symm (Fin.succ_ne_zero index)),
          Fin.tail_update_succ]
        have law := inductionHypothesis (query := (index, request)) (state := Fin.tail state)
        simp only [indexedSampled, PMF.bind_map, Function.comp_def] at law
        have mapped := congrArg
          (fun distribution : PMF (oracle.Answer request × (Fin count → Eager)) =>
            (kernel (state 0)).bind (fun head => distribution.map
              (fun answer => (answer.1, (Fin.cons head answer.2 : Fin (count + 1) → Eager))))) law
        simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at mapped
        simp_rw [← Fin.cons_update]
        apply mapped.trans
        exact PMF.bind_comm _ _ _

/-- This equality transports a local update through a finite index equivalence. -/
theorem update_reindex {Index Other Value : Type} [DecidableEq Index] [DecidableEq Other]
    (equiv : Other ≃ Index) (function : Index → Value) (index : Index) (value : Value) :
    (fun other => Function.update function index value (equiv other)) =
      Function.update (fun other => function (equiv other)) (equiv.symm index) value :=
  Function.update_comp_equiv function equiv index value

/-- The finite kernel uses the supplied index type without changing its queries. -/
def indexedKernel {Index Sparse Eager : Type} [Fintype Index]
    (kernel : Sparse → PMF Eager) (state : Index → Sparse) : PMF (Index → Eager) :=
  (finiteKernel kernel (fun index => state ((Fintype.equivFin Index).symm index))).map
    (fun complete index => complete (Fintype.equivFin Index index))

/-- The family coupling holds for every finite index type. -/
theorem indexedKernel_step {Index : Type} [Fintype Index] [DecidableEq Index]
    {oracle : OracleSpec} {Sparse Eager : Type}
    (eager : OracleHandler oracle Eager)
    (sampled : ∀ query, Sparse → PMF (oracle.Answer query × Sparse))
    (kernel : Sparse → PMF Eager)
    (step : ∀ query state,
      (kernel state).map (eager query) =
        (sampled query state).bind (fun answer =>
          (kernel answer.2).map (fun eagerState => (answer.1, eagerState))))
    (query : (indexedSpec Index oracle).Query) (state : Index → Sparse) :
    (indexedKernel kernel state).map (indexedEager eager query) =
      (indexedSampled sampled query state).bind (fun answer =>
        (indexedKernel kernel answer.2).map (fun eagerState => (answer.1, eagerState))) := by
  rcases query with ⟨index, request⟩
  let equiv := Fintype.equivFin Index
  have law := finiteKernel_step eager sampled kernel step (equiv index, request)
    (fun position => state (equiv.symm position))
  have mapped := congrArg
    (fun distribution : PMF (oracle.Answer request × (Fin (Fintype.card Index) → Eager)) =>
      distribution.map (fun result => (result.1, fun index => result.2 (equiv index)))) law
  simp only [indexedEager, indexedSampled, PMF.map_bind, PMF.map_comp, PMF.bind_map,
    Function.comp_def, Equiv.symm_apply_apply] at mapped
  simp_rw [update_reindex equiv, Equiv.symm_apply_apply] at mapped
  simp only [indexedKernel, indexedEager, indexedSampled, PMF.map_comp,
    PMF.bind_map, Function.comp_def]
  simp_rw [update_reindex (Fintype.equivFin Index).symm, Equiv.symm_symm]
  exact mapped

/-- Independent uniform local samples give the exact uniform finite function. -/
theorem finiteKernel_uniform (Value : Type) [Fintype Value] [Nonempty Value] (count : Nat) :
    finiteKernel (fun _ : Unit => PMF.uniformOfFintype Value) (fun _ : Fin count => ()) =
      PMF.uniformOfFintype (Fin count → Value) := by
  induction count with
  | zero =>
      have equal (function : Fin 0 → Value) : function = Fin.elim0 := by
        funext index
        exact Fin.elim0 index
      ext function
      simp [finiteKernel, PMF.pure_apply, equal function, PMF.uniformOfFintype_apply]
  | succ count inductionHypothesis =>
      change (PMF.uniformOfFintype Value).bind (fun head =>
        (finiteKernel (fun _ : Unit => PMF.uniformOfFintype Value) (fun _ : Fin count => ())).map
          (fun tail => (Fin.cons head tail : Fin (count + 1) → Value))) = _
      rw [inductionHypothesis]
      have law := congrArg
        (fun distribution : PMF (Value × (Fin count → Value)) => distribution.map
          (Fin.consEquiv (fun _ : Fin (count + 1) => Value)))
        (uniform_product (A := Value) (B := Fin count → Value))
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at law
      exact law.trans (uniform_equiv (Fin.consEquiv (fun _ : Fin (count + 1) => Value)))

/-- Equal local kernels give equal independent families. -/
theorem finiteKernel_congr {First Second Eager : Type}
    (first : First → PMF Eager) (second : Second → PMF Eager)
    {count : Nat} (left : Fin count → First) (right : Fin count → Second)
    (equal : ∀ index, first (left index) = second (right index)) :
    finiteKernel first left = finiteKernel second right := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [finiteKernel, equal 0]
      congr 1
      funext head
      congr 1
      exact inductionHypothesis (Fin.tail left) (Fin.tail right) (fun index => equal index.succ)

/-! ### The hash table (baseline `OperationalHashLaw`) -/

section Hash

open Kriterion.ArgoMAC.Security.OperationalOracle.HashTable

/-- The hash state records a new answer only when the input is fresh. -/
def HashTable.afterQuery {Key : Type} [DecidableEq Key]
    (table : HashTable Key size) (key : Key) (value : Fin size) : HashTable Key size :=
  match table.lookup key with
  | none => table.program key value
  | some _ => table

/-- A fresh hash query preserves the entire conditional eager function. -/
theorem HashTable.fresh_completion {Key : Type} [Fintype Key] [DecidableEq Key]
    (positive : 0 < size) (table : HashTable Key size) (key : Key)
    (fresh : table.lookup key = none) :
    letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
    (PMF.uniformOfFintype table.Completion).map Subtype.val =
      (PMF.uniformOfFintype (Fin size)).bind (fun answer =>
        (PMF.uniformOfFintype (table.program key answer).Completion).map Subtype.val) := by
  classical
  letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
  let zero : Fin size := ⟨0, positive⟩
  let equiv := table.freshCompletionEquiv key fresh zero
  letI : Nonempty {f : table.Completion // f.val key = zero} :=
    ⟨⟨table.updateCompletion key fresh (Classical.choice inferInstance) zero, by
      simp [updateCompletion]⟩⟩
  have split := congrArg
    (fun distribution : PMF table.Completion => distribution.map Subtype.val)
    (uniform_fiber equiv)
  simp only [PMF.map_bind, PMF.map_comp] at split
  rw [split]
  congr 1
  funext answer
  letI : Nonempty {f : table.Completion // (equiv f).1 = answer} :=
    ⟨table.extend_completionEquiv key fresh answer (Classical.choice inferInstance)⟩
  letI : Nonempty {f : table.Completion // f.val key = answer} :=
    ⟨table.extend_completionEquiv key fresh answer (Classical.choice inferInstance)⟩
  change (PMF.uniformOfFintype {f : table.Completion // f.val key = answer}).map
    (fun f => f.val.val) = _
  rw [← uniform_equiv (table.extend_completionEquiv key fresh answer), PMF.map_comp]
  rfl

/-- The one-query law preserves the answer, hash table, and eager function together. -/
theorem HashTable.query_joint {Key : Type} [Fintype Key] [DecidableEq Key]
    (positive : 0 < size) (table : HashTable Key size) (key : Key) :
    letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
    (PMF.uniformOfFintype table.Completion).map
        (fun f => (f.val key, HashTable.afterQuery table key (f.val key), f.val)) =
      (table.query positive key).distribution.bind (fun answer =>
        (PMF.uniformOfFintype answer.2.Completion).map
          (fun f => (answer.1, answer.2, f.val))) := by
  classical
  letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
  cases found : table.lookup key with
  | some value =>
      have same (f : table.Completion) : f.val key = value :=
        f.property key value found
      simp only [HashTable.query, found, Draw.distribution, PMF.pure_bind]
      simp_rw [same]
      simp only [afterQuery, found]
  | none =>
      have joint := congrArg
        (fun distribution : PMF (Key → Fin size) => distribution.map
          (fun f => (f key, HashTable.afterQuery table key (f key), f)))
        (HashTable.fresh_completion positive table key found)
      simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at joint
      have pair (answer : Fin size) (f : (table.program key answer).Completion) :
          f.val key = answer :=
        (table.extend_completionEquiv key found answer f).property
      simp_rw [pair] at joint
      apply joint.trans
      simp only [HashTable.query, found, Draw.distribution, PMF.bind_map,
        Function.comp_def, afterQuery, program]


/-- An empty hash table permits every eager function. -/
def hashEmptyCompletionEquiv {Key : Type} [DecidableEq Key] (size : Nat) :
    HashTable.Completion ([] : HashTable Key size) ≃ (Key → Fin size) where
  toFun := Subtype.val
  invFun f := ⟨f, by intro key value present; simp [List.lookup] at present⟩
  left_inv _ := rfl
  right_inv _ := rfl


end Hash

/-! ### The public oracle (baseline `PublicOracleLaw`) -/

abbrev blockSpec : OracleSpec := ⟨Bool × Block, fun _ => Block⟩

def blockPermutation (permutation : Equiv.Perm (Fin (2 ^ 128))) : Equiv.Perm Block :=
  BitVec.equivFin.toEquiv.trans (permutation.trans BitVec.equivFin.symm.toEquiv)

def blockCompletion (state : SparsePermutation (2 ^ 128)) : PMF (Equiv.Perm Block) :=
  (PMF.uniformOfFintype state.Completion).map (fun permutation => blockPermutation permutation.val)

def blockEager : OracleHandler blockSpec (Equiv.Perm Block)
  | (inverse, input), permutation =>
      ((if inverse then permutation.symm input else permutation input), permutation)

def blockSampled (request : Bool × Block) (state : SparsePermutation (2 ^ 128)) :
    PMF (Block × SparsePermutation (2 ^ 128)) :=
  ((if request.1 then state.inverse request.2.toFin else state.forward request.2.toFin).distribution).map
    (fun answer => (BitVec.ofFin answer.1, answer.2))

theorem block_step (request : blockSpec.Query) (state : SparsePermutation (2 ^ 128)) :
    (blockCompletion state).map (blockEager request) =
      (blockSampled request state).bind (fun answer =>
        (blockCompletion answer.2).map (fun complete => (answer.1, complete))) := by
  rcases request with ⟨inverse, input⟩
  cases inverse
  · have law := congrArg
      (fun distribution : PMF (Fin (2 ^ 128) × SparsePermutation (2 ^ 128) × Equiv.Perm (Fin (2 ^ 128))) =>
        distribution.map (fun result => (BitVec.ofFin result.1, blockPermutation result.2.2)))
      ((SparsePermutation.forward_joint state) input.toFin)
    simpa [blockCompletion, blockEager, blockSampled, blockPermutation,
      PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def, BitVec.equivFin] using law
  · have law := congrArg
      (fun distribution : PMF (Fin (2 ^ 128) × SparsePermutation (2 ^ 128) × Equiv.Perm (Fin (2 ^ 128))) =>
        distribution.map (fun result => (BitVec.ofFin result.1, blockPermutation result.2.2)))
      ((SparsePermutation.inverse_joint state) input.toFin)
    simpa [blockCompletion, blockEager, blockSampled, blockPermutation,
      PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def, BitVec.equivFin] using law

abbrev hashSize := Fintype.card (Block × Block)
def pairHashCompletion (state : HashTable BN254.BaseField hashSize) : PMF (BN254.BaseField → Block × Block) :=
  (PMF.uniformOfFintype state.Completion).map
    (fun complete key => (Fintype.equivFin (Block × Block)).symm (complete.val key))

def publicCompletion {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    (state : LazyOracle.State FixedIndex EncIndex) : PMF (PublicOracle FixedIndex EncIndex) :=
  (indexedKernel blockCompletion state.fixed).bind fun fixed =>
    (indexedKernel blockCompletion state.enc).bind fun enc =>
      (pairHashCompletion state.hash).map (fun hash => (⟨fixed⟩, ⟨enc⟩, hash))

theorem public_fixed_step {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (state : LazyOracle.State FixedIndex EncIndex) (index : FixedIndex) (input : Block) :
    (publicCompletion state).map (publicHandler id (.fixedForward index input)) =
      (LazyOracle.query (.fixedForward index input) state).bind (fun answer =>
        (publicCompletion answer.2).map (fun complete => (answer.1, complete))) := by
  change (publicCompletion state).map (fun complete => (complete.1.permutation index input, complete)) = _
  have law := indexedKernel_step blockEager blockSampled blockCompletion block_step
    (index, (false, input)) state.fixed
  have joined := congrArg
    (fun distribution : PMF (Block × (FixedIndex → Equiv.Perm Block)) =>
      distribution.bind fun answer =>
        (indexedKernel blockCompletion state.enc).bind fun enc =>
          (pairHashCompletion state.hash).map fun hash =>
            (answer.1, ((⟨answer.2⟩, ⟨enc⟩, hash) : PublicOracle FixedIndex EncIndex))) law
  simpa [PublicQuery.Answer, publicCompletion, indexedEager, indexedSampled,
    blockEager, blockSampled, LazyOracle.query, PMF.map_bind, PMF.map_comp, PMF.bind_map,
    PMF.bind_bind, Function.comp_def, Function.update_eq_self] using joined
theorem public_fixed_inverse_step {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (state : LazyOracle.State FixedIndex EncIndex) (index : FixedIndex) (input : Block) :
    (publicCompletion state).map (publicHandler id (.fixedInverse index input)) =
      (LazyOracle.query (.fixedInverse index input) state).bind (fun answer =>
        (publicCompletion answer.2).map (fun complete => (answer.1, complete))) := by
  change (publicCompletion state).map (fun complete => ((complete.1.permutation index).symm input, complete)) = _
  have law := indexedKernel_step blockEager blockSampled blockCompletion block_step
    (index, (true, input)) state.fixed
  have joined := congrArg
    (fun distribution : PMF (Block × (FixedIndex → Equiv.Perm Block)) =>
      distribution.bind fun answer =>
        (indexedKernel blockCompletion state.enc).bind fun enc =>
          (pairHashCompletion state.hash).map fun hash =>
            (answer.1, ((⟨answer.2⟩, ⟨enc⟩, hash) : PublicOracle FixedIndex EncIndex))) law
  simpa [PublicQuery.Answer, publicCompletion, indexedEager, indexedSampled,
    blockEager, blockSampled, LazyOracle.query, PMF.map_bind, PMF.map_comp, PMF.bind_map,
    PMF.bind_bind, Function.comp_def, Function.update_eq_self] using joined

theorem public_enc_step {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (state : LazyOracle.State FixedIndex EncIndex) (index : EncIndex) (input : Block) :
    (publicCompletion state).map (publicHandler id (.encForward index input)) =
      (LazyOracle.query (.encForward index input) state).bind (fun answer =>
        (publicCompletion answer.2).map (fun complete => (answer.1, complete))) := by
  change (publicCompletion state).map (fun complete => (complete.2.1.permutation index input, complete)) = _
  have law := indexedKernel_step blockEager blockSampled blockCompletion block_step
    (index, (false, input)) state.enc
  have joined := congrArg
    (fun distribution : PMF (Block × (EncIndex → Equiv.Perm Block)) =>
      (indexedKernel blockCompletion state.fixed).bind fun fixed =>
        distribution.bind fun answer =>
          (pairHashCompletion state.hash).map fun hash =>
            (answer.1, ((⟨fixed⟩, ⟨answer.2⟩, hash) : PublicOracle FixedIndex EncIndex))) law
  simp [PublicQuery.Answer, publicCompletion, indexedEager, indexedSampled,
    blockEager, blockSampled, LazyOracle.query, PMF.map_bind, PMF.map_comp, PMF.bind_map,
    PMF.bind_bind, Function.comp_def, Function.update_eq_self] at joined ⊢
  rw [joined]
  exact PMF.bind_comm _ _ _
theorem public_enc_inverse_step {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (state : LazyOracle.State FixedIndex EncIndex) (index : EncIndex) (input : Block) :
    (publicCompletion state).map (publicHandler id (.encInverse index input)) =
      (LazyOracle.query (.encInverse index input) state).bind (fun answer =>
        (publicCompletion answer.2).map (fun complete => (answer.1, complete))) := by
  change (publicCompletion state).map (fun complete => ((complete.2.1.permutation index).symm input, complete)) = _
  have law := indexedKernel_step blockEager blockSampled blockCompletion block_step
    (index, (true, input)) state.enc
  have joined := congrArg
    (fun distribution : PMF (Block × (EncIndex → Equiv.Perm Block)) =>
      (indexedKernel blockCompletion state.fixed).bind fun fixed =>
        distribution.bind fun answer =>
          (pairHashCompletion state.hash).map fun hash =>
            (answer.1, ((⟨fixed⟩, ⟨answer.2⟩, hash) : PublicOracle FixedIndex EncIndex))) law
  simp [PublicQuery.Answer, publicCompletion, indexedEager, indexedSampled,
    blockEager, blockSampled, LazyOracle.query, PMF.map_bind, PMF.map_comp, PMF.bind_map,
    PMF.bind_bind, Function.comp_def, Function.update_eq_self] at joined ⊢
  rw [joined]
  exact PMF.bind_comm _ _ _

theorem public_hash_step {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (state : LazyOracle.State FixedIndex EncIndex) (input : BN254.BaseField) :
    (publicCompletion state).map (publicHandler id (.hash input)) =
      (LazyOracle.query (.hash input) state).bind (fun answer =>
        (publicCompletion answer.2).map (fun complete => (answer.1, complete))) := by
  change (publicCompletion state).map (fun complete => (complete.2.2 input, complete)) = _
  have law := congrArg
    (fun distribution : PMF (Fin hashSize × HashTable BN254.BaseField hashSize × (BN254.BaseField → Fin hashSize)) =>
      distribution.map (fun result => ((Fintype.equivFin (Block × Block)).symm result.1,
        fun key => (Fintype.equivFin (Block × Block)).symm (result.2.2 key))))
    (HashTable.query_joint Fintype.card_pos state.hash input)
  have joined := congrArg
    (fun distribution : PMF ((Block × Block) × (BN254.BaseField → Block × Block)) =>
      (indexedKernel blockCompletion state.fixed).bind fun fixed =>
        (indexedKernel blockCompletion state.enc).bind fun enc =>
          distribution.map fun answer =>
            (answer.1, ((⟨fixed⟩, ⟨enc⟩, answer.2) : PublicOracle FixedIndex EncIndex))) law
  simp [PublicQuery.Answer, publicCompletion, pairHashCompletion, LazyOracle.query,
    PMF.map_bind, PMF.map_comp, PMF.bind_map, PMF.bind_bind, Function.comp_def] at joined ⊢
  rw [joined]
  conv_lhs => arg 2; ext fixed; rw [PMF.bind_comm]
  exact PMF.bind_comm _ _ _

/-- Every public query preserves the full conditional completion law. -/
theorem public_step {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (request : PublicQuery FixedIndex EncIndex) (state : LazyOracle.State FixedIndex EncIndex) :
    (publicCompletion state).map (publicHandler id request) =
      (LazyOracle.query request state).bind (fun answer =>
        (publicCompletion answer.2).map (fun complete => (answer.1, complete))) := by
  cases request with
  | fixedForward index input => exact public_fixed_step state index input
  | fixedInverse index output => exact public_fixed_inverse_step state index output
  | encForward index input => exact public_enc_step state index input
  | encInverse index output => exact public_enc_inverse_step state index output
  | hash input => exact public_hash_step state input

/-- The fixed lazy oracle has the same adaptive query law as its eager completion. -/
theorem public_run {FixedIndex EncIndex Result : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : LazyOracle.State FixedIndex EncIndex) :
    (publicCompletion state).bind (fun complete => program.run (publicHandler id) complete) =
      (LazyOracle.run program state).bind (fun result =>
        (publicCompletion result.2).map (fun complete => (result.1, complete))) :=
  adaptive_joint_law (publicHandler id) LazyOracle.query publicCompletion public_step program state

theorem block_initial : blockCompletion (.empty (2 ^ 128)) = PMF.uniformOfFintype (Equiv.Perm Block) := by
  convert uniform_equiv ((emptyCompletionEquiv (2 ^ 128)).trans
    (Equiv.permCongr BitVec.equivFin.symm.toEquiv)) using 1 <;> rfl

theorem block_family_initial (Index : Type) [Fintype Index] [DecidableEq Index] :
    indexedKernel blockCompletion (fun _ : Index => SparsePermutation.empty (2 ^ 128)) =
      PMF.uniformOfFintype (Index → Equiv.Perm Block) := by
  classical
  have finite := finiteKernel_congr blockCompletion
    (fun _ : Unit => PMF.uniformOfFintype (Equiv.Perm Block))
    (fun _ : Fin (Fintype.card Index) => SparsePermutation.empty (2 ^ 128))
    (fun _ : Fin (Fintype.card Index) => ()) (fun _ => block_initial)
  let equiv : (Fin (Fintype.card Index) → Equiv.Perm Block) ≃ (Index → Equiv.Perm Block) := {
    toFun := fun complete index => complete (Fintype.equivFin Index index)
    invFun := fun complete index => complete ((Fintype.equivFin Index).symm index)
    left_inv := by intro complete; funext index; simp
    right_inv := by intro complete; funext index; simp }
  have mapped := congrArg (fun distribution : PMF (Fin (Fintype.card Index) → Equiv.Perm Block) =>
    distribution.map equiv) (finite.trans (finiteKernel_uniform _ _))
  convert mapped.trans (uniform_equiv equiv) using 1 <;> rfl

theorem pair_hash_initial : pairHashCompletion [] =
    PMF.uniformOfFintype (BN254.BaseField → Block × Block) := by
  convert uniform_equiv ((hashEmptyCompletionEquiv (Key := BN254.BaseField) hashSize).trans
    (Equiv.arrowCongr (Equiv.refl BN254.BaseField) (Fintype.equivFin (Block × Block)).symm)) using 1 <;> rfl

/-- The empty fixed oracle has the exact uniform complete-oracle distribution. -/
theorem public_initial {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex] :
    publicCompletion (LazyOracle.empty : LazyOracle.State FixedIndex EncIndex) =
      PMF.uniformOfFintype (PublicOracle FixedIndex EncIndex) := by
  classical
  simp only [publicCompletion, LazyOracle.empty, block_family_initial, pair_hash_initial]
  let equiv : ((FixedIndex → Equiv.Perm Block) × (EncIndex → Equiv.Perm Block) ×
      (BN254.BaseField → Block × Block)) ≃ PublicOracle FixedIndex EncIndex := {
    toFun := fun value => (⟨value.1⟩, ⟨value.2.1⟩, value.2.2)
    invFun := fun value => (value.1.permutation, value.2.1.permutation, value.2.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have product := uniform_product (A := FixedIndex → Equiv.Perm Block)
    (B := (EncIndex → Equiv.Perm Block) × (BN254.BaseField → Block × Block))
  rw [← uniform_product (A := EncIndex → Equiv.Perm Block) (B := BN254.BaseField → Block × Block)] at product
  have mapped := congrArg (fun distribution => distribution.map equiv) product
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at mapped
  exact mapped.trans (uniform_equiv equiv)

theorem public_run_result {FixedIndex EncIndex Result : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : LazyOracle.State FixedIndex EncIndex) :
    (publicCompletion state).bind (fun complete => (program.run (publicHandler id) complete).map Prod.fst) =
      (LazyOracle.run program state).map Prod.fst := by
  have constant {A B : Type} (distribution : PMF A) (value : B) :
      distribution.map (fun _ => value) = PMF.pure value := PMF.map_const _ _
  have law := congrArg (PMF.map Prod.fst) (public_run program state)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, constant] at law
  exact law.trans (PMF.bind_pure_comp _ _)

theorem program_run {FixedIndex EncIndex Result : Type} {budget : Nat}
    (program : QueryProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (oracle : PublicOracle FixedIndex EncIndex) :
    program.toOracleProgram.run (publicHandler id) oracle =
      PMF.pure (program.eval (publicAnswer oracle), oracle) := by
  induction program with
  | pure result => simp [QueryProgram.toOracleProgram, OracleProgram.run_pure, PMF.pure_map, QueryProgram.eval]
  | query request next ih =>
      simp [QueryProgram.toOracleProgram, OracleProgram.run_query, publicHandler, ih, QueryProgram.eval]

theorem public_run_tape {FixedIndex EncIndex Result Tape : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (project : Tape → PublicOracle FixedIndex EncIndex) (tape : Tape) :
    program.run (publicHandler project) tape =
      (program.run (publicHandler id) (project tape)).map (fun result => (result.1, tape)) := by
  induction program with
  | pure result => simp [OracleProgram.run_pure, PMF.map_comp, Function.comp_def]
  | query request next ih => simp [OracleProgram.run_query, publicHandler, ih]
  | sample distribution next ih => simp [OracleProgram.run_sample, PMF.map_bind, ih]

theorem lazy_real_uniform {FixedIndex EncIndex Coins Circuit Input Public Key Labels Aux : Type}
    [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (coins : Nat → PMF Coins) {budget : Nat}
    (garble : Nat → Circuit → Coins → QueryProgram (publicOracleSpec FixedIndex EncIndex) (Public × Key) budget)
    (encode : Key → Input → Labels)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedIndex EncIndex) Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    lazyRealGame coins (fun p c r => (garble p c r).toOracleProgram) encode adversary parameter circuit auxiliary =
      (coins parameter).bind (fun randomness =>
        (PMF.uniformOfFintype (PublicOracle FixedIndex EncIndex)).bind (fun oracle =>
          let garbled := (garble parameter circuit randomness).eval (publicAnswer oracle)
          ((adversary.chooseInput parameter garbled.1 auxiliary).run (publicHandler id) oracle).bind (fun selected =>
            ((adversary.decide parameter garbled.1 (encode garbled.2 selected.1.1)
              auxiliary selected.1.2).run (publicHandler id) selected.2).map Prod.fst))) := by
  let eagerAfter (garbled : Public × Key) (oracle : PublicOracle FixedIndex EncIndex) : PMF Bool :=
    ((adversary.chooseInput parameter garbled.1 auxiliary).run (publicHandler id) oracle).bind fun selected =>
      ((adversary.decide parameter garbled.1 (encode garbled.2 selected.1.1)
        auxiliary selected.1.2).run (publicHandler id) selected.2).map Prod.fst
  let lazyAfter (garbled : Public × Key) (state : LazyOracle.State FixedIndex EncIndex) : PMF Bool :=
    (LazyOracle.run (adversary.chooseInput parameter garbled.1 auxiliary) state).bind fun selected =>
      (LazyOracle.run (adversary.decide parameter garbled.1 (encode garbled.2 selected.1.1)
        auxiliary selected.1.2) selected.2).map Prod.fst
  have after (garbled : Public × Key) (state : LazyOracle.State FixedIndex EncIndex) :
      (publicCompletion state).bind (eagerAfter garbled) = lazyAfter garbled state := by
    have law := congrArg
      (fun distribution : PMF ((Input × adversary.State) × PublicOracle FixedIndex EncIndex) =>
        distribution.bind fun selected =>
          ((adversary.decide parameter garbled.1 (encode garbled.2 selected.1.1)
            auxiliary selected.1.2).run (publicHandler id) selected.2).map Prod.fst)
      (public_run (adversary.chooseInput parameter garbled.1 auxiliary) state)
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at law
    change _ = (LazyOracle.run _ state).bind _
    rw [law]
    congr 1
    funext selected
    exact public_run_result _ _
  unfold lazyRealGame
  congr 1
  funext randomness
  have law := congrArg
    (fun distribution : PMF ((Public × Key) × PublicOracle FixedIndex EncIndex) =>
      distribution.bind fun result => eagerAfter result.1 result.2)
    (public_run (garble parameter circuit randomness).toOracleProgram LazyOracle.empty)
  simp only [public_initial, program_run, PMF.bind_bind, PMF.bind_map, PMF.pure_bind, Function.comp_def] at law
  simp_rw [after] at law
  exact law.symm



end

end Kriterion.ArgoMAC.Phase3.Glue
