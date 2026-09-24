/-
**Phase 3, P1l — the two laws, part 1: generic tools.**

`LawOff` and `LawOn` compare two laws of `(published value, labels, lookups)`: the garbler's, on
`G1U`'s swapped tape, and the designed shadow's private run, on a uniform source. Both are reduced
to **answer tables** (`LawsTable.lean`, `LawsFill.lean`); this file holds the generic facts the
reductions use.

* **averages over independent draws** (`tsum_productPMF`, `tsum_uniform_prod`,
  `tsum_equiv_uniform`, `tsum_swap_mul`, `uniform_perm_eval`, `tsum_uniform_split`): a uniform
  permutation read at a point is uniform, and a uniform family's coordinate is independent of the
  others;
* **fixed-key questions asked once** (`FixedOnce`, `fixedOnce_uniform`): a computation that asks
  each fixed-key index at most once, forward, reads a uniform permutation family as one fresh
  uniform block per index, whatever the input — even when an input depends on earlier answers (a
  chunk's fold asks level `n` at labels built from level `n - 1`'s answers, at every chunk width);
* **the swap's hash answers at the points** (`swapLaw_evalAt`): under `MaskSwap.swapLaw` the limbs
  at the points are P4's mask tape (`Lazy.uniformMaskTape`: uniform switch-mask vectors, the limbs
  uniform on their `sampleLane` fibres), whatever the points, independent of the rest;
* **a transcript is read along itself** (`transcript_agree`): an answer function that agrees with
  a run's transcript runs the same way.
-/

import Proof.Privacy.Phase3.PublicFirst.LiftGuess

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell uniformMaskTape)
open scoped ENNReal

noncomputable section

/-! ### 1. One coordinate of a uniform family -/

section Eval

/-- **A uniform permutation read at a point is uniform.** -/
theorem uniform_perm_eval {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] (x : α) :
    (PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => π x) = PMF.uniformOfFintype α := by
  classical
  refine uniform_map_of_fibre_equiv _ fun first second => ?_
  exact {
    toFun := fun π => ⟨π.1.trans (Equiv.swap first second), by
      show Equiv.swap first second (π.1 x) = second
      rw [show π.1 x = first from π.2, Equiv.swap_apply_left]⟩
    invFun := fun π => ⟨π.1.trans (Equiv.swap second first), by
      show Equiv.swap second first (π.1 x) = first
      rw [show π.1 x = second from π.2, Equiv.swap_apply_left]⟩
    left_inv := fun π => by
      apply Subtype.ext
      apply Equiv.ext
      intro y
      show Equiv.swap second first (Equiv.swap first second (π.1 y)) = π.1 y
      rw [Equiv.swap_comm second first, Equiv.swap_apply_self]
    right_inv := fun π => by
      apply Subtype.ext
      apply Equiv.ext
      intro y
      show Equiv.swap first second (Equiv.swap second first (π.1 y)) = π.1 y
      rw [Equiv.swap_comm first second, Equiv.swap_apply_self] }

/-- An average over an independent pair. -/
theorem tsum_productPMF {α β : Type} (μ : PMF α) (ν : PMF β) (f : α × β → ℝ≥0∞) :
    ∑' p, productPMF μ ν p * f p = ∑' a, μ a * ∑' b, ν b * f (a, b) := by
  simp only [productPMF_apply]
  have split : ∑' p : α × β, μ p.1 * ν p.2 * f p = ∑' a, ∑' b, μ a * ν b * f (a, b) :=
    ENNReal.tsum_prod (f := fun a b => μ a * ν b * f (a, b))
  rw [split]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  rw [mul_assoc]

/-- An average over a uniform pair. -/
theorem tsum_uniform_prod {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α × β → ℝ≥0∞) :
    ∑' p, PMF.uniformOfFintype (α × β) p * f p =
      ∑' a, PMF.uniformOfFintype α a * ∑' b, PMF.uniformOfFintype β b * f (a, b) := by
  rw [uniformOfFintype_productPMF]
  exact tsum_productPMF _ _ f

/-- An average over a uniform law, moved along an equivalence. -/
theorem tsum_equiv_uniform {X Y : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] (e : X ≃ Y)
    (f : X → ℝ≥0∞) :
    ∑' x, PMF.uniformOfFintype X x * f x = ∑' y, PMF.uniformOfFintype Y y * f (e.symm y) := by
  rw [← Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv e, tsum_map_mul]
  exact tsum_congr fun x => by rw [Equiv.symm_apply_apply]

/-- A constant averaged over a uniform law. -/
theorem tsum_const_uniform {X : Type} [Fintype X] [Nonempty X] (c : ℝ≥0∞) :
    ∑' x, PMF.uniformOfFintype X x * c = c := by
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Two averages commute. -/
theorem tsum_swap_mul {α β : Type} (μ : α → ℝ≥0∞) (ν : β → ℝ≥0∞) (f : α → β → ℝ≥0∞) :
    ∑' a, μ a * ∑' b, ν b * f a b = ∑' b, ν b * ∑' a, μ a * f a b := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => by ring

/-- **A uniform family's coordinate, read through `f`, is independent of the others**: averaging a
function of `f (v i)` and of a family it ignores at `i`. -/
theorem tsum_uniform_split {ι β γ : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
    (i : ι) (f : β → γ) (h : γ → (ι → β) → ℝ≥0∞)
    (irrel : ∀ c v b, h c (Function.update v i b) = h c v) :
    ∑' v, PMF.uniformOfFintype (ι → β) v * h (f (v i)) v =
      ∑' c, ((PMF.uniformOfFintype β).map f) c *
        ∑' v, PMF.uniformOfFintype (ι → β) v * h c v := by
  classical
  let e := Equiv.piSplitAt i (fun _ : ι => β)
  obtain ⟨default⟩ := (inferInstance : Nonempty β)
  let h' : γ → ({j : ι // j ≠ i} → β) → ℝ≥0∞ := fun c w => h c (e.symm (default, w))
  have back : ∀ v : ι → β, e.symm (default, (e v).2) = Function.update v i default := by
    intro v
    funext j
    rw [Equiv.piSplitAt_symm_apply]
    by_cases same : j = i
    · subst same
      simp
    · rw [dif_neg same, Function.update_of_ne same]
      rfl
  have reduce : ∀ c v, h c v = h' c (e v).2 := by
    intro c v
    show h c v = h c (e.symm (default, (e v).2))
    rw [back, irrel]
  have average : ∀ g : β × ({j : ι // j ≠ i} → β) → ℝ≥0∞,
      ∑' v, PMF.uniformOfFintype (ι → β) v * g (e v) =
        ∑' b, PMF.uniformOfFintype β b *
          ∑' w, PMF.uniformOfFintype ({j : ι // j ≠ i} → β) w * g (b, w) := by
    intro g
    rw [← tsum_map_mul (PMF.uniformOfFintype (ι → β)) e g,
      Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv e, tsum_uniform_prod]
  have lhs : ∑' v, PMF.uniformOfFintype (ι → β) v * h (f (v i)) v =
      ∑' v, PMF.uniformOfFintype (ι → β) v *
        (fun p : β × ({j : ι // j ≠ i} → β) => h' (f p.1) p.2) (e v) :=
    tsum_congr fun v => by rw [reduce]; rfl
  rw [lhs, average fun p => h' (f p.1) p.2, tsum_map_mul]
  refine tsum_congr fun b => congrArg _ ?_
  have inner := average fun p => h' (f b) p.2
  have rhs : ∑' v, PMF.uniformOfFintype (ι → β) v * h (f b) v =
      ∑' v, PMF.uniformOfFintype (ι → β) v *
        (fun p : β × ({j : ι // j ≠ i} → β) => h' (f b) p.2) (e v) :=
    tsum_congr fun v => by rw [reduce]
  rw [rhs, inner]
  simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Eval

/-! ### 2. Fixed-key questions asked once -/

section Once

/-- A question that is not a fixed-key question. -/
def NotFixed : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward _ _ => False
  | .fixedInverse _ _ => False
  | .encForward _ _ => True
  | .encInverse _ _ => True
  | .hash _ => True

/-- **Every path asks each fixed-key index at most once**, forward and at an index of `X`; every
other question is free. -/
inductive FixedOnce {α : Type} : Set FixedIndex → FreeQuery Programs.Spec α → Prop
  | pure (X : Set FixedIndex) (value : α) : FixedOnce X (FreeQuery.pure value)
  | fixed (X : Set FixedIndex) (index : FixedIndex) (input : Block)
      (next : Programs.Spec.Answer (PublicQuery.fixedForward index input) →
        FreeQuery Programs.Spec α)
      (inside : index ∈ X) (rest : ∀ answer, FixedOnce (X \ {index}) (next answer)) :
      FixedOnce X (FreeQuery.query (PublicQuery.fixedForward index input) next)
  | other (X : Set FixedIndex) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
      (next : Programs.Spec.Answer request → FreeQuery Programs.Spec α) (notFixed : NotFixed request)
      (rest : ∀ answer, FixedOnce X (next answer)) : FixedOnce X (FreeQuery.query request next)

theorem FixedOnce.mono {α : Type} {X Y : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    (once : FixedOnce X c) (sub : X ⊆ Y) : FixedOnce Y c := by
  induction once generalizing Y with
  | pure X value => exact .pure Y value
  | fixed X index input next inside rest ih =>
      exact .fixed Y index input next (sub inside) fun answer =>
        ih answer (Set.sdiff_subset_sdiff_left sub)
  | other X request next notFixed rest ih =>
      exact .other Y request next notFixed fun answer => ih answer sub

theorem FixedOnce.bind {α β : Type} {X Y : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    {f : α → FreeQuery Programs.Spec β} (first : FixedOnce X c) (second : ∀ a, FixedOnce Y (f a))
    (disjoint : Disjoint X Y) : FixedOnce (X ∪ Y) (c >>= f) := by
  revert disjoint
  induction first with
  | pure X value => exact fun _ => (second value).mono Set.subset_union_right
  | fixed X index input next inside rest ih =>
      intro disjoint
      have notY : index ∉ Y := fun hit => Set.disjoint_left.mp disjoint inside hit
      show FixedOnce (X ∪ Y) (FreeQuery.query (PublicQuery.fixedForward index input)
        fun answer => next answer >>= f)
      refine .fixed (X ∪ Y) index input (fun answer => next answer >>= f) (Or.inl inside)
        fun answer => ?_
      have sets : (X ∪ Y) \ {index} = (X \ {index}) ∪ Y := by
        ext i
        constructor
        · rintro ⟨hi | hi, ne⟩
          · exact Or.inl ⟨hi, ne⟩
          · exact Or.inr hi
        · rintro (⟨hi, ne⟩ | hi)
          · exact ⟨Or.inl hi, ne⟩
          · refine ⟨Or.inr hi, fun same => notY ?_⟩
            rw [Set.mem_singleton_iff.mp same] at hi
            exact hi
      rw [sets]
      exact ih answer (Set.disjoint_of_subset_left Set.sdiff_subset disjoint)
  | other X request next notFixed rest ih =>
      intro disjoint
      exact .other (X ∪ Y) request (fun answer => next answer >>= f) notFixed fun answer =>
        ih answer disjoint

/-- A loop over pairwise disjoint index sets. -/
theorem FixedOnce.vector {α : Type} : ∀ (count : Nat) (X : Fin count → Set FixedIndex)
    (program : Fin count → FreeQuery Programs.Spec α), (∀ k, FixedOnce (X k) (program k)) →
    (∀ k k', k ≠ k' → Disjoint (X k) (X k')) →
      FixedOnce (⋃ k, X k) (FreeQuery.vector count program)
  | 0, _, _, _, _ => .pure _ _
  | count + 1, X, program, each, disjoint => by
      have prefixOnce := FixedOnce.vector count (fun k => X k.castSucc)
        (fun k => program k.castSucc) (fun k => each _)
        (fun k k' ne => disjoint _ _ fun same => ne (Fin.castSucc_injective _ same))
      have tail : ∀ values : Vector α count, FixedOnce (X (Fin.last count) ∪ ∅)
          (program (Fin.last count) >>= fun value => Pure.pure (values.push value)) :=
        fun values => (each _).bind (fun _ => .pure ∅ _) (Set.disjoint_empty _)
      have apart : Disjoint (⋃ k : Fin count, X k.castSucc) (X (Fin.last count) ∪ ∅) := by
        rw [Set.union_empty, Set.disjoint_iUnion_left]
        exact fun k => disjoint _ _ (Fin.castSucc_lt_last k).ne
      refine (prefixOnce.bind tail apart).mono ?_
      rintro i (⟨_, ⟨k, rfl⟩, hi⟩ | hi | hi)
      · exact Set.mem_iUnion.mpr ⟨k.castSucc, hi⟩
      · exact Set.mem_iUnion.mpr ⟨Fin.last count, hi⟩
      · exact hi.elim

/-- **A once-computation reads the fixed-key answers only at its own indices.** -/
theorem FixedOnce.agree {α : Type} {X : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    (once : FixedOnce X c) :
    ∀ (first second : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer),
      (∀ i ∈ X, ∀ x, first (.fixedForward i x) = second (.fixedForward i x)) →
      (∀ q, NotFixed q → first q = second q) →
      transcript first c = transcript second c ∧ c.eval first = c.eval second := by
  induction once with
  | pure X value => exact fun _ _ _ _ => ⟨rfl, rfl⟩
  | fixed X index input next inside rest ih =>
      intro first second same plain
      have head : first (.fixedForward index input) = second (.fixedForward index input) :=
        same index inside input
      have tail := ih (first (.fixedForward index input)) first second
        (fun i hi x => same i hi.1 x) plain
      refine ⟨?_, ?_⟩
      · show ⟨.fixedForward index input, first (.fixedForward index input)⟩ ::
            transcript first (next (first (.fixedForward index input))) =
          ⟨.fixedForward index input, second (.fixedForward index input)⟩ ::
            transcript second (next (second (.fixedForward index input)))
        rw [tail.1, ← head]
      · show (next (first (.fixedForward index input))).eval first =
          (next (second (.fixedForward index input))).eval second
        rw [tail.2, ← head]
  | other X request next notFixed rest ih =>
      intro first second same plain
      have head : first request = second request := plain request notFixed
      have tail := ih (first request) first second same plain
      refine ⟨?_, ?_⟩
      · show ⟨request, first request⟩ :: transcript first (next (first request)) =
          ⟨request, second request⟩ :: transcript second (next (second request))
        rw [tail.1, ← head]
      · show (next (first request)).eval first = (next (second request)).eval second
        rw [tail.2, ← head]

/-- An answer function with its fixed-key permutations replaced by `π`. -/
def withPerms (answer : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (π : FixedIndex → Equiv.Perm Block) :
    ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer
  | .fixedForward index input => π index input
  | .fixedInverse index output => (π index).symm output
  | .encForward index input => answer (.encForward index input)
  | .encInverse index output => answer (.encInverse index output)
  | .hash input => answer (.hash input)

/-- An answer function with one fixed-key answer per index, whatever the input. -/
def withFixed (answer : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (v : FixedIndex → Block) : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer
  | .fixedForward index _ => v index
  | .fixedInverse index _ => v index
  | .encForward index input => answer (.encForward index input)
  | .encInverse index output => answer (.encInverse index output)
  | .hash input => answer (.hash input)

theorem withPerms_plain (answer : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (π : FixedIndex → Equiv.Perm Block) (q : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (notFixed : NotFixed q) : withPerms answer π q = answer q := by
  cases q with
  | fixedForward _ _ => exact notFixed.elim
  | fixedInverse _ _ => exact notFixed.elim
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash _ => rfl

theorem withFixed_plain (answer : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (v : FixedIndex → Block) (q : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (notFixed : NotFixed q) : withFixed answer v q = answer q := by
  cases q with
  | fixedForward _ _ => exact notFixed.elim
  | fixedInverse _ _ => exact notFixed.elim
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash _ => rfl

/-- **A once-computation's fixed-key answers are realised by permutations**: whatever block each
index answers, some permutations answer the computation's one question per index by it. -/
theorem FixedOnce.realize {α : Type} {X : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    (once : FixedOnce X c) :
    ∀ (answer : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
      (v : FixedIndex → Block), ∃ π : FixedIndex → Equiv.Perm Block,
        transcript (withPerms answer π) c = transcript (withFixed answer v) c ∧
          c.eval (withPerms answer π) = c.eval (withFixed answer v) := by
  classical
  induction once with
  | pure X value => exact fun _ _ => ⟨fun _ => Equiv.refl Block, rfl, rfl⟩
  | fixed X index input next inside rest ih =>
      intro answer v
      obtain ⟨π, sameT, sameE⟩ := ih (v index) answer v
      refine ⟨Function.update π index (Equiv.swap input (v index)), ?_⟩
      have head : withPerms answer (Function.update π index (Equiv.swap input (v index)))
          (.fixedForward index input) = v index := by
        show Function.update π index (Equiv.swap input (v index)) index input = v index
        rw [Function.update_self, Equiv.swap_apply_left]
      have tail := (rest (v index)).agree
        (withPerms answer (Function.update π index (Equiv.swap input (v index))))
        (withPerms answer π) (fun i hi x => by
          show Function.update π index (Equiv.swap input (v index)) i x = π i x
          rw [Function.update_of_ne fun same => hi.2 (Set.mem_singleton_iff.mpr same)])
        (fun q plain => by rw [withPerms_plain _ _ q plain, withPerms_plain _ _ q plain])
      refine ⟨?_, ?_⟩
      · show ⟨.fixedForward index input, withPerms answer
              (Function.update π index (Equiv.swap input (v index))) (.fixedForward index input)⟩ ::
            transcript (withPerms answer (Function.update π index (Equiv.swap input (v index))))
              (next (withPerms answer (Function.update π index (Equiv.swap input (v index)))
                (.fixedForward index input))) =
          ⟨.fixedForward index input, v index⟩ :: transcript (withFixed answer v) (next (v index))
        rw [head, tail.1, sameT]
      · show (next (withPerms answer (Function.update π index (Equiv.swap input (v index)))
              (.fixedForward index input))).eval
            (withPerms answer (Function.update π index (Equiv.swap input (v index)))) =
          (next (v index)).eval (withFixed answer v)
        rw [head, tail.2, sameE]
  | other X request next notFixed rest ih =>
      intro answer v
      obtain ⟨π, sameT, sameE⟩ := ih (answer request) answer v
      have head : withPerms answer π request = withFixed answer v request := by
        rw [withPerms_plain _ _ request notFixed, withFixed_plain _ _ request notFixed]
      have plainAnswer : withFixed answer v request = answer request :=
        withFixed_plain _ _ request notFixed
      refine ⟨π, ?_, ?_⟩
      · show ⟨request, withPerms answer π request⟩ ::
            transcript (withPerms answer π) (next (withPerms answer π request)) =
          ⟨request, withFixed answer v request⟩ ::
            transcript (withFixed answer v) (next (withFixed answer v request))
        rw [head, plainAnswer]
        exact congrArg _ sameT
      · show (next (withPerms answer π request)).eval (withPerms answer π) =
          (next (withFixed answer v request)).eval (withFixed answer v)
        rw [head, plainAnswer]
        exact sameE

/-- **A once-computation reads a uniform permutation family as a uniform family of answers**,
jointly with its transcript and value; the other questions are answered by a fixed function. -/
theorem fixedOnce_uniform {α : Type} {X : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    (once : FixedOnce X c) :
    ∀ (answer : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
      (G : List (Entry FixedIndex EncPRF.PermutationIndex) → α → ℝ≥0∞),
      ∑' π, PMF.uniformOfFintype (FixedIndex → Equiv.Perm Block) π *
          G (transcript (withPerms answer π) c) (c.eval (withPerms answer π)) =
        ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
          G (transcript (withFixed answer v) c) (c.eval (withFixed answer v)) := by
  classical
  induction once with
  | pure X value =>
      intro answer G
      show ∑' π, _ * G [] value = ∑' v, _ * G [] value
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, PMF.tsum_coe, PMF.tsum_coe]
  | fixed X index input next inside rest ih =>
      intro answer G
      let hP : Block → (FixedIndex → Equiv.Perm Block) → ℝ≥0∞ := fun b π =>
        G (⟨.fixedForward index input, b⟩ :: transcript (withPerms answer π) (next b))
          (FreeQuery.eval (spec := Programs.Spec) (withPerms answer π) (next b))
      let hF : Block → (FixedIndex → Block) → ℝ≥0∞ := fun b v =>
        G (⟨.fixedForward index input, b⟩ :: transcript (withFixed answer v) (next b))
          (FreeQuery.eval (spec := Programs.Spec) (withFixed answer v) (next b))
      have irrelP : ∀ b π σ, hP b (Function.update π index σ) = hP b π := by
        intro b π σ
        have same := (rest b).agree (withPerms answer (Function.update π index σ))
          (withPerms answer π) (fun j hj x => by
            show Function.update π index σ j x = π j x
            rw [Function.update_of_ne hj.2]) (fun r plain => by
              rw [withPerms_plain _ _ _ plain, withPerms_plain _ _ _ plain])
        show G _ _ = G _ _
        rw [same.1, same.2]
      have irrelF : ∀ b v w, hF b (Function.update v index w) = hF b v := by
        intro b v w
        have same := (rest b).agree (withFixed answer (Function.update v index w))
          (withFixed answer v) (fun j hj x => by
            show Function.update v index w j = v j
            rw [Function.update_of_ne hj.2]) (fun r plain => by
              rw [withFixed_plain _ _ _ plain, withFixed_plain _ _ _ plain])
        show G _ _ = G _ _
        rw [same.1, same.2]
      have stepP := tsum_uniform_split index (fun σ : Equiv.Perm Block => σ input) hP irrelP
      have stepF := tsum_uniform_split index id hF irrelF
      rw [uniform_perm_eval] at stepP
      rw [PMF.map_id] at stepF
      refine stepP.trans (Eq.trans ?_ stepF.symm)
      refine tsum_congr fun b => congrArg _ ?_
      exact ih b answer fun entries value => G (⟨.fixedForward index input, b⟩ :: entries) value
  | other X request next notFixed rest ih =>
      intro answer G
      have lhs : ∀ π : FixedIndex → Equiv.Perm Block,
          G (transcript (withPerms answer π) (FreeQuery.query request next))
            (FreeQuery.eval (spec := Programs.Spec) (withPerms answer π)
              (FreeQuery.query request next)) =
          G (⟨request, answer request⟩ :: transcript (withPerms answer π) (next (answer request)))
            (FreeQuery.eval (spec := Programs.Spec) (withPerms answer π) (next (answer request))) := by
        intro π
        show G (⟨request, withPerms answer π request⟩ ::
            transcript (withPerms answer π) (next (withPerms answer π request)))
          (FreeQuery.eval (spec := Programs.Spec) (withPerms answer π)
            (next (withPerms answer π request))) = _
        rw [withPerms_plain _ _ _ notFixed]
      have rhs : ∀ v : FixedIndex → Block,
          G (transcript (withFixed answer v) (FreeQuery.query request next))
            (FreeQuery.eval (spec := Programs.Spec) (withFixed answer v)
              (FreeQuery.query request next)) =
          G (⟨request, answer request⟩ :: transcript (withFixed answer v) (next (answer request)))
            (FreeQuery.eval (spec := Programs.Spec) (withFixed answer v) (next (answer request))) := by
        intro v
        show G (⟨request, withFixed answer v request⟩ ::
            transcript (withFixed answer v) (next (withFixed answer v request)))
          (FreeQuery.eval (spec := Programs.Spec) (withFixed answer v)
            (next (withFixed answer v request))) = _
        rw [withFixed_plain _ _ _ notFixed]
      simp only [lhs, rhs]
      exact ih (answer request) answer fun entries value =>
        G (⟨request, answer request⟩ :: entries) value

end Once

/-! ### 3. The swap's hash answers at the points -/

section Swap

/-- **Under `swapLaw` the hash answers at the points are P4's mask tape, independent of the
rest**, whatever the points. -/
theorem swapLaw_evalAt {Rest D : Type} [Fintype D] [DecidableEq D] (restLaw : PMF Rest)
    (point : Rest → (Cell ↪ D)) :
    (swapLaw restLaw point).map (fun tape => (tape.1, evalAt (point tape.1) tape.2)) =
      productPMF restLaw uniformMaskTape := by
  rw [swapLaw, PMF.map_bind, productPMF]
  refine congrArg _ (funext fun rest => ?_)
  rw [PMF.map_comp]
  have factor : ((fun tape : Rest × (D → Block × Block) => (tape.1, evalAt (point tape.1) tape.2))
      ∘ Prod.mk rest) = Prod.mk rest ∘ evalAt (point rest) := rfl
  rw [factor, ← PMF.map_comp, swapKernel, PMF.map_bind]
  refine congrArg (PMF.map (Prod.mk rest)) ?_
  unfold uniformMaskTape
  exact congrArg _ (funext fun vectors => fibreKernel_evalAt (point rest) vectors)

end Swap

/-! ### 4. A transcript is read along itself -/

section Transcript

/-- **An answer function agreeing with a run's transcript runs the same way.** -/
theorem transcript_agree {α : Type} (computation : FreeQuery Programs.Spec α)
    (first second : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (agree : ∀ entry ∈ transcript first computation, second entry.1 = entry.2) :
    transcript second computation = transcript first computation ∧
      computation.eval second = computation.eval first := by
  induction computation with
  | pure value => exact ⟨rfl, rfl⟩
  | query request next ih =>
      have head : second request = first request :=
        agree ⟨request, first request⟩ List.mem_cons_self
      have rest := ih (first request)
        (fun entry member => agree entry (List.mem_cons_of_mem _ member))
      refine ⟨?_, ?_⟩
      · show ⟨request, second request⟩ :: transcript second (next (second request)) = _
        rw [head, rest.1]
        rfl
      · show (next (second request)).eval second = (next (first request)).eval first
        rw [head]
        exact rest.2

end Transcript

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
