/-
**Phase 3, P1f — generic: two query runs related entry by entry.**

`Sim ans ans' rel R P P'`: the transcripts of `P` on `ans` and of `P'` on `ans'` are related
entrywise by `rel` (`List.Forall₂`), and the results by `R`. It is closed under `pure`, `bind`,
`ask`, `FreeQuery.vector` and `FreeQuery.pi`, so a relation between two runs of one program on two
tapes is proved gate by gate. With `rel e e' := e' = g e` it says the second transcript is the
first one mapped by `g` (`forall₂_map_eq`).
-/

import Proof.Privacy.Phase3.Hidden.Masks

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open Kriterion.Cryptography

noncomputable section

variable {FI EI : Type} [DecidableEq FI] [DecidableEq EI]

/-- Two runs, related entrywise and at their results. -/
def Sim {α β : Type} (ans ans' : ∀ query : PublicQuery FI EI, query.Answer)
    (rel : Asked FI EI → Asked FI EI → Prop) (R : α → β → Prop)
    (P : FreeQuery (publicOracleSpec FI EI) α) (P' : FreeQuery (publicOracleSpec FI EI) β) : Prop :=
  List.Forall₂ rel (transcriptOf ans P) (transcriptOf ans' P') ∧ R (P.eval ans) (P'.eval ans')

namespace Sim

variable {ans ans' : ∀ query : PublicQuery FI EI, query.Answer} {rel : Asked FI EI → Asked FI EI → Prop}

theorem pure' {α β : Type} {R : α → β → Prop} {a : α} {b : β} (related : R a b) :
    Sim ans ans' rel R (Pure.pure a : FreeQuery (publicOracleSpec FI EI) α) (Pure.pure b) :=
  ⟨List.Forall₂.nil, related⟩

theorem bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {P : FreeQuery (publicOracleSpec FI EI) α} {P' : FreeQuery (publicOracleSpec FI EI) β}
    {f : α → FreeQuery (publicOracleSpec FI EI) γ} {f' : β → FreeQuery (publicOracleSpec FI EI) δ}
    (first : Sim ans ans' rel R P P') (rest : ∀ a b, R a b → Sim ans ans' rel S (f a) (f' b)) :
    Sim ans ans' rel S (P >>= f) (P' >>= f') := by
  obtain ⟨entries, results⟩ := first
  obtain ⟨entries', results'⟩ := rest _ _ results
  refine ⟨?_, ?_⟩
  · rw [transcriptOf_bind, transcriptOf_bind]
    exact List.rel_append entries entries'
  · rw [FreeQuery.eval_bind, FreeQuery.eval_bind]
    exact results'

theorem mono {α β : Type} {R S : α → β → Prop} {P : FreeQuery (publicOracleSpec FI EI) α}
    {P' : FreeQuery (publicOracleSpec FI EI) β} (sim : Sim ans ans' rel R P P')
    (weaker : ∀ a b, R a b → S a b) : Sim ans ans' rel S P P' :=
  ⟨sim.1, weaker _ _ sim.2⟩

/-- One question each. -/
theorem ask (query query' : PublicQuery FI EI) (R : query.Answer → query'.Answer → Prop)
    (entry : rel ⟨query, ans query⟩ ⟨query', ans' query'⟩) (result : R (ans query) (ans' query')) :
    Sim ans ans' rel R (FreeQuery.ask (spec := publicOracleSpec FI EI) query)
      (FreeQuery.ask (spec := publicOracleSpec FI EI) query') :=
  ⟨List.Forall₂.cons entry List.Forall₂.nil, result⟩

/-- A loop, iteration by iteration. -/
theorem vector {α β : Type} :
    ∀ (count : Nat) {R : Fin count → α → β → Prop} (P : Fin count → FreeQuery (publicOracleSpec FI EI) α)
      (P' : Fin count → FreeQuery (publicOracleSpec FI EI) β),
      (∀ index, Sim ans ans' rel (R index) (P index) (P' index)) →
      Sim ans ans' rel (fun v v' => ∀ index, R index (v.get index) (v'.get index))
        (FreeQuery.vector count P) (FreeQuery.vector count P')
  | 0, _, _, _, _ => pure' fun index => index.elim0
  | count + 1, R, P, P', each => by
      show Sim ans ans' rel _ (FreeQuery.vector count (fun index => P index.castSucc) >>= fun values =>
          P (Fin.last count) >>= fun value => Pure.pure (values.push value))
        (FreeQuery.vector count (fun index => P' index.castSucc) >>= fun values =>
          P' (Fin.last count) >>= fun value => Pure.pure (values.push value))
      refine bind (vector count (R := fun index => R index.castSucc) _ _
        fun index => each index.castSucc) fun values values' early =>
        bind (each (Fin.last count)) fun value value' last => pure' ?_
      intro index
      rw [Vector.get_eq_getElem, Vector.get_eq_getElem, Vector.getElem_push, Vector.getElem_push]
      split
      · rename_i small
        have := early ⟨index.val, small⟩
        rwa [Vector.get_eq_getElem, Vector.get_eq_getElem] at this
      · have : index = Fin.last count := Fin.ext (by have := index.isLt; simp only [Fin.val_last]; omega)
        subst this
        simpa using last

/-- A dependent loop, iteration by iteration. -/
theorem pi : ∀ (count : Nat) {γ γ' : Fin count → Type} {R : ∀ index, γ index → γ' index → Prop}
    (P : (index : Fin count) → FreeQuery (publicOracleSpec FI EI) (γ index))
    (P' : (index : Fin count) → FreeQuery (publicOracleSpec FI EI) (γ' index)),
    (∀ index, Sim ans ans' rel (R index) (P index) (P' index)) →
    Sim ans ans' rel (fun v v' => ∀ index, R index (v index) (v' index))
      (FreeQuery.pi count P) (FreeQuery.pi count P')
  | 0, _, _, _, _, _, _ => pure' fun index => index.elim0
  | count + 1, _, _, R, P, P', each => by
      show Sim ans ans' rel _ (P 0 >>= fun head =>
          FreeQuery.pi count (fun index => P index.succ) >>= fun tail =>
            Pure.pure (Fin.cons head tail))
        (P' 0 >>= fun head =>
          FreeQuery.pi count (fun index => P' index.succ) >>= fun tail =>
            Pure.pure (Fin.cons head tail))
      refine bind (each 0) fun head head' first =>
        bind (pi count (R := fun index => R index.succ) _ _ fun index => each index.succ)
          fun tail tail' rest => pure' ?_
      intro index
      refine Fin.cases ?_ (fun index => ?_) index
      · exact first
      · exact rest index

end Sim

/-- `Forall₂` of an equation-with-side-condition is a map. -/
theorem forall₂_map_eq {g : Asked FI EI → Asked FI EI} {good : Asked FI EI → Prop} :
    ∀ {l l' : List (Asked FI EI)}, List.Forall₂ (fun e e' => e' = g e ∧ good e) l l' →
      l' = l.map g ∧ ∀ e ∈ l, good e
  | [], [], List.Forall₂.nil => ⟨rfl, fun _ member => by cases member⟩
  | _ :: _, _ :: _, List.Forall₂.cons head rest => by
      obtain ⟨tail, goods⟩ := forall₂_map_eq rest
      refine ⟨by rw [List.map_cons, head.1, tail], fun e member => ?_⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact head.2
      · exact goods e member

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
