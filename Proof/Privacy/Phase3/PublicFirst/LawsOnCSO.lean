/-
**Phase 3, P1q — `LawOn`, step (C), part 1: stored-or-fresh lazy runs.**

A lazy run of a computation that, along its path, asks only questions stored in the start state or
**fresh gadget questions** (at gadget indices empty in the state, each at most once) is an eager run
on the tape overridden at the fresh gadget indices by uniform translations (`ovrOracle`: the gadget
permutation at a fresh position `k` is `x ↦ x ⊕ v k`, `v` uniform):

* `SOn s O Y c` — along `O`'s answers every question is stored in `s` (with `O`'s answer), or a
  gadget question at a position of `Y`, whose continuations are again stored-or-fresh on `Y \ {k}`;
* **`sOn_eager`**: `E[F(lazy run of c from t)] = E_{v uniform} F(c's value and transcript on
  ovrOracle X v O, planted on t)`, for every state `t` growing `s` with the fresh indices empty;
* `sOn_path`: along the overridden oracle every question is stored or fresh; the closure lemmas
  `sOn_stored_bind`, `sOn_bind`, `sOn_vector`, `SOn.mono`.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnMergeLaw

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Request queriesAlong)
open scoped ENNReal

noncomputable section

/-! ### 1. Gadget positions and the overridden oracle -/

section Override

/-- A gadget position: digit, coordinate, label position. -/
abbrev GPos := Fin digitCount × Coord × Fin PlanB.coordinateBits

/-- The gadget index of a position. -/
def gIdx (k : GPos) : FixedIndex := .gadget k.1 k.2.1 k.2.2

theorem gIdx_injective : Function.Injective gIdx := by
  rintro ⟨o, κ, p⟩ ⟨o', κ', p'⟩ same
  simp only [gIdx, FixedIndex.gadget.injEq] at same
  obtain ⟨rfl, rfl, rfl⟩ := same
  rfl

/-- The fixed-key permutations overridden at the fresh gadget positions by translations. -/
def ovrPerm (X : GPos → Bool) (v : GPos → Block) (P : FixedIndex → Equiv.Perm Block) :
    FixedIndex → Equiv.Perm Block
  | .gadget o κ p => if X (o, κ, p) then xorPerm (v (o, κ, p)) else P (.gadget o κ p)
  | index => P index

/-- **The oracle overridden at the fresh gadget positions.** -/
def ovrOracle (X : GPos → Bool) (v : GPos → Block) (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    PublicOracle FixedIndex EncPRF.PermutationIndex :=
  (⟨ovrPerm X v O.1.permutation⟩, O.2)

/-- **Answers overridden at the fresh gadget positions**: a fresh gadget question at `x` is answered
`x ⊕ v k`. -/
def freshAnswer (X : GPos → Bool) (v : GPos → Block)
    (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) :
    ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer
  | .fixedForward (.gadget o κ p) x =>
      if X (o, κ, p) then x ^^^ v (o, κ, p) else ans (.fixedForward (.gadget o κ p) x)
  | q => ans q

theorem ovr_fresh (X : GPos → Bool) (v : GPos → Block) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (k : GPos) (fresh : X k = true) (x : Block) :
    publicAnswer (ovrOracle X v O) (.fixedForward (gIdx k) x) = x ^^^ v k := by
  obtain ⟨o, κ, p⟩ := k
  show (if X (o, κ, p) then xorPerm (v (o, κ, p)) else O.1.permutation (.gadget o κ p)) x = _
  rw [if_pos fresh]
  rfl

/-- Off the fresh gadget positions the overridden oracle is the oracle. -/
theorem ovr_other (X : GPos → Bool) (v : GPos → Block) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex) (forward : NoInverse q)
    (other : ∀ k x, q = .fixedForward (gIdx k) x → X k = false) :
    publicAnswer (ovrOracle X v O) q = publicAnswer O q := by
  cases q with
  | fixedForward index x =>
      cases index with
      | gadget o κ p =>
          have notFresh : X (o, κ, p) = false := other (o, κ, p) x rfl
          show (if X (o, κ, p) then xorPerm (v (o, κ, p)) else O.1.permutation (.gadget o κ p)) x =
            O.1.permutation (.gadget o κ p) x
          rw [if_neg (by rw [notFresh]; exact Bool.false_ne_true)]
      | hot _ _ _ _ _ => rfl
  | fixedInverse _ _ => exact forward.elim
  | encForward _ _ => rfl
  | encInverse _ _ => exact forward.elim
  | hash _ => rfl

theorem freshAnswer_fresh (X : GPos → Bool) (v : GPos → Block)
    (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) (k : GPos) (fresh : X k = true)
    (x : Block) : freshAnswer X v ans (.fixedForward (gIdx k) x) = x ^^^ v k := by
  obtain ⟨o, κ, p⟩ := k
  simp only [gIdx, freshAnswer]
  exact if_pos fresh

theorem freshAnswer_other (X : GPos → Bool) (v : GPos → Block)
    (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (other : ∀ k x, q = .fixedForward (gIdx k) x → X k = false) : freshAnswer X v ans q = ans q := by
  cases q with
  | fixedForward index x =>
      cases index with
      | gadget o κ p =>
          have notFresh : X (o, κ, p) = false := other (o, κ, p) x rfl
          simp only [freshAnswer]
          exact if_neg (by rw [notFresh]; exact Bool.false_ne_true)
      | hot _ _ _ _ _ => rfl
  | fixedInverse _ _ => rfl
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash _ => rfl

/-- An average of a translate of a uniform block. -/
theorem tsum_uniform_xor (x : Block) (f : Block → ℝ≥0∞) :
    ∑' b, PMF.uniformOfFintype Block b * f (x ^^^ b) = ∑' o, PMF.uniformOfFintype Block o * f o := by
  simp only [PMF.uniformOfFintype_apply]
  have same : ∀ b : Block, f (x ^^^ b) = f (xorPerm x b) := fun b => by
    show f (x ^^^ b) = f (b ^^^ x)
    rw [BitVec.xor_comm]
  simp_rw [same]
  exact Equiv.tsum_eq (xorPerm x) (fun o => (Fintype.card Block : ℝ≥0∞)⁻¹ * f o)

end Override

/-! ### 2. Stored-or-fresh computations -/

section Fresh

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **Stored or fresh along the oracle.** -/
inductive SOn (s : LState) (O : PublicOracle FixedIndex EncPRF.PermutationIndex) {α : Type} :
    Set GPos → FreeQuery Programs.Spec α → Prop
  | pure (Y : Set GPos) (value : α) : SOn s O Y (.pure value)
  | stored (Y : Set GPos) (q : PublicQuery FixedIndex EncPRF.PermutationIndex)
      (next : q.Answer → FreeQuery Programs.Spec α)
      (here : StoredAs s ⟨q, publicAnswer O q⟩) (forward : NoInverse q)
      (rest : SOn s O Y (next (publicAnswer O q))) : SOn s O Y (.query q next)
  | fresh (Y : Set GPos) (k : GPos) (x : Block)
      (next : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) (gIdx k) x).Answer →
        FreeQuery Programs.Spec α)
      (inside : k ∈ Y) (rest : ∀ a, SOn s O (Y \ {k}) (next a)) :
      SOn s O Y (.query (.fixedForward (gIdx k) x) next)

variable {s : LState} {O : PublicOracle FixedIndex EncPRF.PermutationIndex}

theorem SOn.mono {α : Type} {Y Z : Set GPos} {c : FreeQuery Programs.Spec α} (holds : SOn s O Y c)
    (sub : Y ⊆ Z) : SOn s O Z c := by
  induction holds generalizing Z with
  | pure Y value => exact .pure Z value
  | stored Y q next here forward rest ih => exact .stored Z q next here forward (ih sub)
  | fresh Y k x next inside rest ih =>
      exact .fresh Z k x next (sub inside) fun a => ih a (Set.sdiff_subset_sdiff_left sub)

/-- A stored prefix, then a stored-or-fresh continuation. -/
theorem sOn_stored_bind {α β : Type} (Y : Set GPos) (c : FreeQuery Programs.Spec α)
    (stored : ∀ e ∈ transcript (publicAnswer O) c, StoredAs s e ∧ NoInverse e.1)
    {f : α → FreeQuery Programs.Spec β} (rest : SOn s O Y (f (FreeQuery.eval (publicAnswer O) c))) :
    SOn s O Y (c >>= f) := by
  induction c with
  | pure value => exact rest
  | query request next ih =>
      have head := stored ⟨request, publicAnswer O request⟩ List.mem_cons_self
      exact .stored Y request (fun a => next a >>= f) head.1 head.2
        (ih _ (fun e member => stored e (List.mem_cons_of_mem _ member)) rest)

/-- Two stored-or-fresh computations in sequence, on disjoint fresh positions. -/
theorem sOn_bind {α β : Type} {Y Z : Set GPos} {c : FreeQuery Programs.Spec α}
    {f : α → FreeQuery Programs.Spec β} (first : SOn s O Y c) (second : ∀ a, SOn s O Z (f a))
    (disjoint : Disjoint Y Z) : SOn s O (Y ∪ Z) (c >>= f) := by
  revert disjoint
  induction first with
  | pure Y value => exact fun _ => (second value).mono Set.subset_union_right
  | stored Y q next here forward rest ih =>
      intro disjoint
      exact .stored (Y ∪ Z) q (fun a => next a >>= f) here forward (ih disjoint)
  | fresh Y k x next inside rest ih =>
      intro disjoint
      have notZ : k ∉ Z := fun hit => Set.disjoint_left.mp disjoint inside hit
      refine .fresh (Y ∪ Z) k x (fun a => next a >>= f) (Or.inl inside) fun a => ?_
      have sets : (Y ∪ Z) \ {k} = (Y \ {k}) ∪ Z := by
        ext i
        constructor
        · rintro ⟨hi | hi, ne⟩
          · exact Or.inl ⟨hi, ne⟩
          · exact Or.inr hi
        · rintro (⟨hi, ne⟩ | hi)
          · exact ⟨Or.inl hi, ne⟩
          · refine ⟨Or.inr hi, fun same => notZ ?_⟩
            rw [Set.mem_singleton_iff.mp same] at hi
            exact hi
      rw [sets]
      exact ih a (Set.disjoint_of_subset_left Set.sdiff_subset disjoint)

theorem sOn_pure' {α : Type} (Y : Set GPos) (value : α) :
    SOn s O Y (Pure.pure value : FreeQuery Programs.Spec α) := .pure Y value

/-- A loop of stored-or-fresh iterations on pairwise disjoint fresh positions. -/
theorem sOn_vector {α : Type} : ∀ (count : Nat) (Y : Fin count → Set GPos)
    (program : Fin count → FreeQuery Programs.Spec α), (∀ k, SOn s O (Y k) (program k)) →
    (∀ k k', k ≠ k' → Disjoint (Y k) (Y k')) → SOn s O (⋃ k, Y k) (FreeQuery.vector count program)
  | 0, _, _, _, _ => .pure _ _
  | count + 1, Y, program, each, disjoint => by
      have prefixOn := sOn_vector count (fun k => Y k.castSucc) (fun k => program k.castSucc)
        (fun k => each _) (fun k k' ne => disjoint _ _ fun same => ne (Fin.castSucc_injective _ same))
      have tail : ∀ values : Vector α count, SOn s O (Y (Fin.last count) ∪ ∅)
          (program (Fin.last count) >>= fun value => Pure.pure (values.push value)) :=
        fun values => sOn_bind (each _) (fun _ => sOn_pure' ∅ _) (Set.disjoint_empty _)
      have apart : Disjoint (⋃ k : Fin count, Y k.castSucc) (Y (Fin.last count) ∪ ∅) := by
        rw [Set.union_empty, Set.disjoint_iUnion_left]
        exact fun k => disjoint _ _ (Fin.castSucc_lt_last k).ne
      refine (sOn_bind prefixOn tail apart).mono ?_
      rintro i (⟨_, ⟨k, rfl⟩, hi⟩ | hi | hi)
      · exact Set.mem_iUnion.mpr ⟨k.castSucc, hi⟩
      · exact Set.mem_iUnion.mpr ⟨Fin.last count, hi⟩
      · exact hi.elim

/-- A stored question is not at an empty index. -/
theorem stored_notFresh (X : GPos → Bool) (empty : ∀ k, X k = true → s.fixed (gIdx k) = SparsePermutation.empty _)
    {q : PublicQuery FixedIndex EncPRF.PermutationIndex} {a : q.Answer} (here : StoredAs s ⟨q, a⟩) :
    ∀ k x, q = .fixedForward (gIdx k) x → X k = false := by
  intro k x same
  subst same
  by_contra fresh
  have emptyK := empty k (by simpa using fresh)
  have look : (LazyOracle.permutationLookup (s.fixed (gIdx k)) x.toFin).map BitVec.ofFin = some a := here
  rw [emptyK] at look
  simp [LazyOracle.permutationLookup, SparsePermutation.knownInput, SparsePermutation.empty] at look

/-- Planting a stored entry changes nothing. -/
theorem plantEntry_stored (t : LState) (e : Entry FixedIndex EncPRF.PermutationIndex)
    (stored : StoredAs t e) (forward : NoInverse e.1) : plantEntry t e = t := by
  obtain ⟨q, a⟩ := e
  unfold plantEntry
  cases q with
  | fixedForward index x =>
      have known : (t.fixed index).knownInput x.toFin := by
        by_contra unknown
        have look : (LazyOracle.permutationLookup (t.fixed index) x.toFin).map BitVec.ofFin = some a := stored
        simp [LazyOracle.permutationLookup, unknown] at look
      show ((LazyOracle.permutationProgram (t.fixed index) x.toFin _).map _).getD t = t
      rw [LazyOracle.permutationProgram_reject _ _ _ (Or.inl known)]
      rfl
  | fixedInverse _ _ => exact forward.elim
  | encForward index x =>
      have known : (t.enc index).knownInput x.toFin := by
        by_contra unknown
        have look : (LazyOracle.permutationLookup (t.enc index) x.toFin).map BitVec.ofFin = some a := stored
        simp [LazyOracle.permutationLookup, unknown] at look
      show ((LazyOracle.permutationProgram (t.enc index) x.toFin _).map _).getD t = t
      rw [LazyOracle.permutationProgram_reject _ _ _ (Or.inl known)]
      rfl
  | encInverse _ _ => exact forward.elim
  | hash key =>
      have found : t.hash.lookup key ≠ none := by
        intro none
        have look : (t.hash.lookup key).map _ = some a := stored
        rw [none] at look
        cases look
      show (if t.hash.lookup key = none then _ else none).getD t = t
      rw [if_neg found]
      rfl

/-- **Along the overridden oracle, the answers do not depend on the offsets outside `Y`.** -/
theorem sOn_indep (X : GPos → Bool) (empty : ∀ k, X k = true → s.fixed (gIdx k) = SparsePermutation.empty _)
    {α : Type} {Y : Set GPos} {c : FreeQuery Programs.Spec α} (holds : SOn s O Y c)
    (inX : ∀ k ∈ Y, X k = true) :
    ∀ v v' : GPos → Block, (∀ k ∈ Y, v k = v' k) →
      transcript (publicAnswer (ovrOracle X v O)) c = transcript (publicAnswer (ovrOracle X v' O)) c ∧
        FreeQuery.eval (publicAnswer (ovrOracle X v O)) c = FreeQuery.eval (publicAnswer (ovrOracle X v' O)) c := by
  induction holds with
  | pure Y value => exact fun _ _ _ => ⟨rfl, rfl⟩
  | stored Y q next here forward rest ih =>
      intro v v' agree
      have other := stored_notFresh X empty here
      have a1 := ovr_other X v O q forward other
      have a2 := ovr_other X v' O q forward other
      obtain ⟨tr, ev⟩ := ih inX v v' agree
      refine ⟨?_, ?_⟩
      · rw [transcript_query_eq _ q next _ a1, transcript_query_eq _ q next _ a2, tr]
      · rw [eval_query_eq _ q next _ a1, eval_query_eq _ q next _ a2, ev]
  | fresh Y k x next inside rest ih =>
      intro v v' agree
      have a1 := ovr_fresh X v O k (inX k inside) x
      have a2 := ovr_fresh X v' O k (inX k inside) x
      rw [agree k inside] at a1
      obtain ⟨tr, ev⟩ := ih (x ^^^ v' k) (fun j hj => inX j hj.1) v v'
        (fun j hj => agree j hj.1)
      refine ⟨?_, ?_⟩
      · rw [transcript_query_eq _ _ next _ a1, transcript_query_eq _ _ next _ a2, tr]
      · rw [eval_query_eq _ _ next _ a1, eval_query_eq _ _ next _ a2, ev]

/-- **Along the overridden oracle every question is stored or fresh.** -/
theorem sOn_path (X : GPos → Bool) (empty : ∀ k, X k = true → s.fixed (gIdx k) = SparsePermutation.empty _)
    {α : Type} {Y : Set GPos} {c : FreeQuery Programs.Spec α}
    (holds : SOn s O Y c) (v : GPos → Block) (inX : ∀ k ∈ Y, X k = true) :
    ∀ q ∈ queriesAlong (publicAnswer (ovrOracle X v O)) c,
      (StoredAs s ⟨q, publicAnswer O q⟩ ∧ NoInverse q) ∨ ∃ k ∈ Y, ∃ x, q = .fixedForward (gIdx k) x := by
  induction holds with
  | pure Y value => intro q member; nomatch member
  | stored Y q next here forward rest ih =>
      intro r member
      have same := ovr_other X v O q forward (stored_notFresh X empty here)
      rcases List.mem_cons.mp member with rfl | later
      · exact Or.inl ⟨here, forward⟩
      · rw [same] at later
        exact ih inX r later
  | fresh Y k x next inside rest ih =>
      intro r member
      rcases List.mem_cons.mp member with rfl | later
      · exact Or.inr ⟨k, inside, x, rfl⟩
      · rcases ih _ (fun j hj => inX j hj.1) r later with stored | ⟨j, hj, y, hy⟩
        · exact Or.inl stored
        · exact Or.inr ⟨j, hj.1, y, hy⟩

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]

/-- **A stored-or-fresh lazy run is an eager run on the overridden oracle.** -/
theorem sOn_eager (X : GPos → Bool) (empty : ∀ k, X k = true → s.fixed (gIdx k) = SparsePermutation.empty _)
    {α : Type} {Y : Set GPos} {c : FreeQuery Programs.Spec α} (holds : SOn s O Y c)
    (inX : ∀ k ∈ Y, X k = true) :
    ∀ t : LState, Grows s t → (∀ k ∈ Y, t.fixed (gIdx k) = SparsePermutation.empty _) →
      ∀ F : α → LState → ℝ≥0∞,
        ∑' r, runLazyQ c t r * F r.1 r.2 =
          ∑' v, PMF.uniformOfFintype (GPos → Block) v *
            F (FreeQuery.eval (publicAnswer (ovrOracle X v O)) c)
              (plantAll (transcript (publicAnswer (ovrOracle X v O)) c) t) := by
  induction holds with
  | pure Y value =>
      intro t _ _ F
      simp only [runLazyQ, tsum_pure_mul]
      show F value t = ∑' v, _ * F value (plantAll [] t)
      rw [plantAll_nil, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | stored Y q next here forward rest ih =>
      intro t grow emptyT F
      have hereT := storedAs_grows grow here
      have other := stored_notFresh X empty here
      simp only [runLazyQ]
      rw [query_of_stored hereT, PMF.pure_bind]
      dsimp only
      rw [ih inX t grow emptyT F]
      refine tsum_congr fun v => congrArg _ ?_
      have answer := ovr_other X v O q forward other
      rw [transcript_query_eq _ q next _ answer, eval_query_eq _ q next _ answer, plantAll_cons,
        plantEntry_stored t _ hereT forward]
  | fresh Y k x next inside rest ih =>
      intro t grow emptyT F
      have emptyHere := emptyT k inside
      simp only [runLazyQ]
      rw [tsum_bind_mul, tsum_query_empty t (gIdx k) x emptyHere]
      dsimp only
      have laterEmpty : ∀ o : Block, ∀ j ∈ Y \ {k},
          (storeOne t (gIdx k) x o).fixed (gIdx j) = SparsePermutation.empty _ := by
        intro o j hj
        show Function.update t.fixed (gIdx k) _ (gIdx j) = _
        rw [Function.update_of_ne (fun same => hj.2 (gIdx_injective same))]
        exact emptyT j hj.1
      have growOne : ∀ o : Block, Grows s (storeOne t (gIdx k) x o) := fun o =>
        grow.trans (program_state_grows (gIdx k) x o t _ (program_empty t (gIdx k) x o emptyHere))
      refine (tsum_congr fun o => congrArg _ (ih o (fun j hj => inX j hj.1) (storeOne t (gIdx k) x o)
        (growOne o) (laterEmpty o) F)).trans ?_
      -- the offset at `k` is the fresh answer
      let h : Block → (GPos → Block) → ℝ≥0∞ := fun b v =>
        F (FreeQuery.eval (publicAnswer (ovrOracle X v O)) (next (x ^^^ b)))
          (plantAll (transcript (publicAnswer (ovrOracle X v O)) (next (x ^^^ b)))
            (storeOne t (gIdx k) x (x ^^^ b)))
      have irrel : ∀ b v c', h b (Function.update v k c') = h b v := by
        intro b v c'
        obtain ⟨tr, ev⟩ := sOn_indep X empty (rest (x ^^^ b)) (fun j hj => inX j hj.1)
          (Function.update v k c') v (fun j hj => Function.update_of_ne hj.2 _ _)
        show F _ _ = F _ _
        rw [tr, ev]
      have answer : ∀ v : GPos → Block,
          publicAnswer (ovrOracle X v O) (.fixedForward (gIdx k) x) = x ^^^ v k :=
        fun v => ovr_fresh X v O k (inX k inside) x
      have rhs : ∀ v : GPos → Block,
          F (FreeQuery.eval (publicAnswer (ovrOracle X v O))
              (FreeQuery.query (spec := Programs.Spec) (PublicQuery.fixedForward (gIdx k) x) next))
            (plantAll (transcript (publicAnswer (ovrOracle X v O))
              (FreeQuery.query (spec := Programs.Spec) (PublicQuery.fixedForward (gIdx k) x) next)) t) =
          h (v k) v := by
        intro v
        rw [transcript_query_eq _ _ next _ (answer v), eval_query_eq _ _ next _ (answer v), plantAll_cons]
        show _ = F _ (plantAll _ (storeOne t (gIdx k) x (x ^^^ v k)))
        unfold plantEntry
        rw [program_empty t (gIdx k) x _ emptyHere]
        rfl
      simp only [rhs]
      have split := tsum_uniform_split k id h irrel
      rw [PMF.map_id] at split
      simp only [id] at split
      rw [split]
      refine (tsum_uniform_xor x (fun o => ∑' v, PMF.uniformOfFintype (GPos → Block) v *
        F (FreeQuery.eval (publicAnswer (ovrOracle X v O)) (next o))
          (plantAll (transcript (publicAnswer (ovrOracle X v O)) (next o)) (storeOne t (gIdx k) x o)))).symm.trans ?_
      exact tsum_congr fun b => rfl

end Fresh

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
