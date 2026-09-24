/-
This file defines the free query monad the Plan B oracle programs are written in, and its
translation into the challenge's indexed `Cryptography.QueryProgram`.

The challenge's `QueryProgram oracle Result budget` carries its query bound in its type. Plan B's
programs are loops over lanes, chunks, switches and elements whose per-iteration budgets differ
(the first chunk is narrower, the four lanes carry different element counts, the evaluator skips
its active entries), so writing them directly at a fixed index would thread a budget equation
through every combinator. Instead they are written in `FreeQuery`, the same syntax without the
index, and their bound is a separate proposition `FreeQuery.Bounded program budget`: every path
through the program makes at most `budget` queries. `FreeQuery.toProgram` turns a bounded free
program into the indexed one, and `eval_toProgram` says the two interpret identically.

Nothing here is specific to Plan B.
-/

import Cryptography.Primitives

namespace Kriterion.ArgoMAC

open Cryptography

/-- A query program without a budget index: it returns a value, or asks one oracle question and
continues with the answer. -/
inductive FreeQuery (spec : OracleSpec.{0, 0}) (α : Type) : Type
  | pure (value : α) : FreeQuery spec α
  | query (request : spec.Query) (next : spec.Answer request → FreeQuery spec α) :
      FreeQuery spec α

namespace FreeQuery

variable {spec : OracleSpec.{0, 0}} {α β : Type}

/-- Sequencing: run the first program, then the continuation on its result. -/
def bind : FreeQuery spec α → (α → FreeQuery spec β) → FreeQuery spec β
  | .pure value, next => next value
  | .query request rest, next => .query request fun answer => bind (rest answer) next

instance : Monad (FreeQuery spec) where
  pure := FreeQuery.pure
  bind := FreeQuery.bind

/-- Ask one oracle question. -/
def ask (request : spec.Query) : FreeQuery spec (spec.Answer request) :=
  .query request .pure

/-- Run a program against one complete oracle. -/
def eval (answer : ∀ query, spec.Answer query) : FreeQuery spec α → α
  | .pure value => value
  | .query request next => eval answer (next (answer request))

@[simp] theorem eval_pure (answer : ∀ query, spec.Answer query) (value : α) :
    eval answer (Pure.pure value : FreeQuery spec α) = value := rfl

@[simp] theorem eval_bind (answer : ∀ query, spec.Answer query) (program : FreeQuery spec α)
    (next : α → FreeQuery spec β) :
    eval answer (program >>= next) = eval answer (next (eval answer program)) := by
  induction program with
  | pure value => rfl
  | query request rest ih => exact ih (answer request)

@[simp] theorem eval_ask (answer : ∀ query, spec.Answer query) (request : spec.Query) :
    eval answer (ask request) = answer request := rfl

/-! ### The query bound -/

/-- Every path through the program asks at most `budget` questions. -/
inductive Bounded : FreeQuery spec α → Nat → Prop
  | pure (value : α) (budget : Nat) : Bounded (.pure value) budget
  | query (request : spec.Query) (next : spec.Answer request → FreeQuery spec α)
      (budget : Nat) (bounded : ∀ answer, Bounded (next answer) budget) :
      Bounded (.query request next) (budget + 1)

namespace Bounded

theorem not_zero {request : spec.Query} {next : spec.Answer request → FreeQuery spec α} :
    ¬ Bounded (.query request next) 0 := by
  intro bounded
  cases bounded

theorem next {request : spec.Query} {next : spec.Answer request → FreeQuery spec α}
    {budget : Nat} (bounded : Bounded (.query request next) (budget + 1)) (answer) :
    Bounded (next answer) budget := by
  cases bounded with
  | query _ _ _ rest => exact rest answer

/-- A larger budget is still a bound. -/
theorem mono {program : FreeQuery spec α} {small large : Nat} (bounded : Bounded program small)
    (le : small ≤ large) : Bounded program large := by
  induction bounded generalizing large with
  | pure value budget => exact .pure value large
  | query request next budget _ ih =>
      obtain ⟨rest, rfl⟩ : ∃ rest, large = rest + 1 := ⟨large - 1, by omega⟩
      exact .query request next rest fun answer => ih answer (by omega)

/-- Restate a bound through an equation. -/
theorem of_eq {program : FreeQuery spec α} {first second : Nat} (bounded : Bounded program first)
    (equal : first = second) : Bounded program second :=
  equal ▸ bounded

theorem pure' (value : α) (budget : Nat) : Bounded (Pure.pure value : FreeQuery spec α) budget :=
  .pure value budget

theorem ask (request : spec.Query) : Bounded (FreeQuery.ask request) 1 :=
  .query request _ 0 fun answer => .pure answer 0

/-- The budgets of a sequence add. -/
theorem bind {program : FreeQuery spec α} {next : α → FreeQuery spec β} {first second : Nat}
    (bounded : Bounded program first) (rest : ∀ value, Bounded (next value) second) :
    Bounded (program >>= next) (first + second) := by
  induction bounded with
  | pure value budget => exact (rest value).mono (by omega)
  | query request step budget _ ih =>
      show Bounded (.query request fun answer => FreeQuery.bind (step answer) next)
        (budget + 1 + second)
      rw [Nat.add_right_comm]
      exact .query request _ (budget + second) fun answer => ih answer

/-- A branch is bounded by the larger of its two budgets. -/
theorem ite {condition : Prop} [Decidable condition] {first second : FreeQuery spec α}
    {budget : Nat} (yes : condition → Bounded first budget) (no : ¬ condition → Bounded second budget) :
    Bounded (if condition then first else second) budget := by
  by_cases holds : condition
  · rw [if_pos holds]
    exact yes holds
  · rw [if_neg holds]
    exact no holds

end Bounded

/-! ### Translation into the challenge's indexed programs -/

/-- A bounded free program, as the challenge's indexed query program. -/
def toProgram : (program : FreeQuery spec α) → (budget : Nat) → Bounded program budget →
    QueryProgram spec α budget
  | .pure value, _, _ => .pure value
  | .query _ _, 0, bounded => absurd bounded Bounded.not_zero
  | .query request next, budget + 1, bounded =>
      .query request fun answer => toProgram (next answer) budget (bounded.next answer)

/-- The translation does not change what the program computes. -/
theorem eval_toProgram (answer : ∀ query, spec.Answer query) (program : FreeQuery spec α)
    (budget : Nat) (bounded : Bounded program budget) :
    (toProgram program budget bounded).eval answer = eval answer program := by
  induction program generalizing budget with
  | pure value => rfl
  | query request next ih =>
      cases budget with
      | zero => exact absurd bounded Bounded.not_zero
      | succ budget => exact ih (answer request) budget (bounded.next (answer request))

/-! ### Loops -/

/-- Run one program per index, collecting the results in a vector. -/
def vector : (count : Nat) → (Fin count → FreeQuery spec α) → FreeQuery spec (Vector α count)
  | 0, _ => Pure.pure #v[]
  | count + 1, program =>
      vector count (fun index => program index.castSucc) >>= fun values =>
        program (Fin.last count) >>= fun value => Pure.pure (values.push value)

@[simp] theorem eval_vector (answer : ∀ query, spec.Answer query) (count : Nat)
    (program : Fin count → FreeQuery spec α) :
    eval answer (vector count program) = Vector.ofFn fun index => eval answer (program index) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [vector, eval_bind, eval_pure, ih]
      apply Vector.ext
      intro index bound
      rw [Vector.getElem_push, Vector.getElem_ofFn]
      split
      · rw [Vector.getElem_ofFn]
        rfl
      · have last : index = count := by omega
        subst last
        rfl

/-- A loop's budget is the sum of its iterations' budgets. -/
theorem Bounded.vector {count : Nat} {program : Fin count → FreeQuery spec α}
    {budget : Fin count → Nat} (bounded : ∀ index, Bounded (program index) (budget index)) :
    Bounded (FreeQuery.vector count program) (∑ index, budget index) := by
  induction count with
  | zero => exact .pure _ _
  | succ count ih =>
      rw [Fin.sum_univ_castSucc]
      refine (Bounded.bind (ih fun index => bounded index.castSucc) fun _ =>
        Bounded.bind (bounded (Fin.last count)) fun _ => Bounded.pure' _ 0).of_eq ?_
      omega

/-- A loop of equal iterations. -/
theorem Bounded.vector_const {count budget : Nat} {program : Fin count → FreeQuery spec α}
    (bounded : ∀ index, Bounded (program index) budget) :
    Bounded (FreeQuery.vector count program) (count * budget) :=
  (Bounded.vector (budget := fun _ => budget) bounded).of_eq (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul])

/-- A loop that skips one index: every other iteration costs `budget`. -/
theorem sum_ite_skip {count : Nat} (skip : Fin count) (budget : Nat) :
    (∑ index : Fin count, if index = skip then 0 else budget) = (count - 1) * budget := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ skip), if_pos rfl, Nat.add_zero,
    Finset.sum_congr rfl fun index member => if_neg (Finset.ne_of_mem_erase member),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ skip), Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- Run one program per index of a dependent family. -/
def pi : (count : Nat) → {β : Fin count → Type} → ((index : Fin count) → FreeQuery spec (β index)) →
    FreeQuery spec ((index : Fin count) → β index)
  | 0, _, _ => Pure.pure fun index => index.elim0
  | count + 1, _, program =>
      program 0 >>= fun head =>
        pi count (fun index => program index.succ) >>= fun tail =>
          Pure.pure (Fin.cons head tail)

@[simp] theorem eval_pi (answer : ∀ query, spec.Answer query) (count : Nat)
    {β : Fin count → Type} (program : (index : Fin count) → FreeQuery spec (β index)) :
    eval answer (pi count program) = fun index => eval answer (program index) := by
  induction count with
  | zero => funext index; exact index.elim0
  | succ count ih =>
      simp only [pi, eval_bind, eval_pure, ih]
      funext index
      refine Fin.cases ?_ (fun index => ?_) index
      · rfl
      · rfl

theorem Bounded.pi {count : Nat} {β : Fin count → Type}
    {program : (index : Fin count) → FreeQuery spec (β index)} {budget : Fin count → Nat}
    (bounded : ∀ index, Bounded (program index) (budget index)) :
    Bounded (FreeQuery.pi count program) (∑ index, budget index) := by
  induction count with
  | zero => exact .pure _ _
  | succ count ih =>
      rw [Fin.sum_univ_succ]
      refine (Bounded.bind (bounded 0) fun _ =>
        Bounded.bind (ih fun index => bounded index.succ) fun _ => Bounded.pure' _ 0).of_eq ?_
      omega

end FreeQuery

end Kriterion.ArgoMAC
