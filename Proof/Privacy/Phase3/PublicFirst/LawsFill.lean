/-
**Phase 3, P1l — the two laws, part 3: the private run on an answer table.**

The designed shadow's private run off the curve (`LiftOff.offPrivate`) is a lazy run: the pads at
the coin `k₁` (EncPRF questions, two per index), then system A (fixed-key fold gates, each index at
most once, and the hash limbs of the switch masks, each limb at most once; the limbs programmed from
the mask tape). Two reductions turn it into an eager run:

* **lazy = eager, jointly with the final state** (`runLazyQ_eager`): the lazy run of any query
  computation from `s`, read through its result and (the lookups of) its final state, is the eager
  run on a completion of `s` with its transcript planted on `s` (the resampling argument of
  `Hidden.resample_joint`, one query at a time: `public_step`, `query_semEq_plant`);
* **a fresh run is a table run** (`runFill_once`; a lazy question at an empty fixed-key index is a
  uniform block stored, `query_empty`, and a program there succeeds, `program_empty`): a fill run of
  a computation that asks only
  forward fixed-key questions at pairwise distinct indices empty in the state, and hash questions at
  pairwise distinct limbs untouched and unstored in the state (`OnceIn`), is its run on a table
  whose fixed-key answers are uniform (one fresh uniform block per index, whatever the input) and
  whose limbs are the mask tape.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsTable

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion public_step)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape cellInput cellOf consumeCell touch refillAnswer)
open scoped ENNReal

noncomputable section

section Lazy

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

theorem sameLookups_of_semEq {s t : LState} (same : Hidden.SemEq s t) : SameLookups s t :=
  sameLookups_of_forward same.fixed same.enc same.hash

/-- **One query, split off a completion.** -/
theorem tsum_completion_split (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (s : LState)
    (h : request.Answer → PublicOracle FixedIndex EncPRF.PermutationIndex → ℝ≥0∞) :
    ∑' O, publicCompletion s O * h (publicAnswer O request) O =
      ∑' a, LazyOracle.query request s a * ∑' O, publicCompletion a.2 O * h a.1 O := by
  have step := public_step request s
  have lhs : ∑' p, ((publicCompletion s).map (publicHandler id request)) p * h p.1 p.2 =
      ∑' O, publicCompletion s O * h (publicAnswer O request) O := by
    rw [tsum_map_mul]
    rfl
  have rhs : ∑' p, ((LazyOracle.query request s).bind fun answer =>
        (publicCompletion answer.2).map fun complete => (answer.1, complete)) p * h p.1 p.2 =
      ∑' a, LazyOracle.query request s a * ∑' O, publicCompletion a.2 O * h a.1 O := by
    rw [tsum_bind_mul]
    refine tsum_congr fun a => congrArg _ ?_
    rw [tsum_map_mul]
  rw [← lhs, step, rhs]

/-- **Lazy = eager, jointly with the final state's lookups.** -/
theorem runLazyQ_eager {α : Type} (computation : FreeQuery Programs.Spec α) :
    ∀ (s : LState) (F : α → LState → ℝ≥0∞), (∀ a t t', SameLookups t t' → F a t = F a t') →
      ∑' r, runLazyQ computation s r * F r.1 r.2 =
        ∑' O, publicCompletion s O * F (computation.eval (publicAnswer O))
          (plantAll (transcript (publicAnswer O) computation) s) := by
  induction computation with
  | pure value =>
      intro s F _
      simp only [runLazyQ, tsum_pure_mul]
      show F value s = ∑' O, publicCompletion s O * F value (plantAll [] s)
      rw [plantAll_nil, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query request next ih =>
      intro s F invariant
      simp only [runLazyQ]
      rw [tsum_bind_mul]
      have right : ∑' O, publicCompletion s O *
          F ((FreeQuery.query request next).eval (publicAnswer O))
            (plantAll (transcript (publicAnswer O) (FreeQuery.query request next)) s) =
          ∑' O, publicCompletion s O * (fun b O' => F ((next b).eval (publicAnswer O'))
            (plantAll (transcript (publicAnswer O') (next b)) (plantEntry s ⟨request, b⟩)))
              (publicAnswer O request) O := rfl
      rw [right, tsum_completion_split request s (fun b O' => F ((next b).eval (publicAnswer O'))
        (plantAll (transcript (publicAnswer O') (next b)) (plantEntry s ⟨request, b⟩)))]
      refine tsum_congr fun a => ?_
      by_cases member : a ∈ (LazyOracle.query request s).support
      · congr 1
        rw [ih a.1 a.2 F invariant]
        have same := Hidden.query_semEq_plant request s a member
        rw [Hidden.publicCompletion_congr same]
        refine tsum_congr fun O => congrArg _ ?_
        exact invariant _ _ _ (plantAll_congr _ (sameLookups_of_semEq same))
      · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

end Lazy

/-! ### Computations that ask each fixed-key index and each limb at most once -/

section Once

/-- **Every path asks only forward fixed-key questions, at pairwise distinct indices of `X`, and
hash questions at the inputs of pairwise distinct limbs of `Y`** (each at one label). -/
inductive OnceIn {α : Type} : Set FixedIndex → Set Cell → FreeQuery Programs.Spec α → Prop
  | pure (X : Set FixedIndex) (Y : Set Cell) (value : α) : OnceIn X Y (FreeQuery.pure value)
  | fixed (X : Set FixedIndex) (Y : Set Cell) (index : FixedIndex) (input : Block)
      (next : Programs.Spec.Answer (PublicQuery.fixedForward index input) →
        FreeQuery Programs.Spec α)
      (inside : index ∈ X) (rest : ∀ answer, OnceIn (X \ {index}) Y (next answer)) :
      OnceIn X Y (FreeQuery.query (PublicQuery.fixedForward index input) next)
  | cell (X : Set FixedIndex) (Y : Set Cell) (cell : Cell) (label : Block)
      (next : Programs.Spec.Answer (PublicQuery.hash (cellInput cell label)) →
        FreeQuery Programs.Spec α)
      (inside : cell ∈ Y) (rest : ∀ answer, OnceIn X (Y \ {cell}) (next answer)) :
      OnceIn X Y (FreeQuery.query (PublicQuery.hash (cellInput cell label)) next)

theorem OnceIn.mono {α : Type} {X X' : Set FixedIndex} {Y Y' : Set Cell}
    {c : FreeQuery Programs.Spec α} (once : OnceIn X Y c) (subX : X ⊆ X') (subY : Y ⊆ Y') :
    OnceIn X' Y' c := by
  induction once generalizing X' Y' with
  | pure X Y value => exact .pure X' Y' value
  | fixed X Y index input next inside rest ih =>
      exact .fixed X' Y' index input next (subX inside) fun answer =>
        ih answer (Set.sdiff_subset_sdiff_left subX) subY
  | cell X Y cell label next inside rest ih =>
      exact .cell X' Y' cell label next (subY inside) fun answer =>
        ih answer subX (Set.sdiff_subset_sdiff_left subY)

/-- The index sets of two sequential stages, removed one element at a time. -/
theorem diff_union_of_not_mem {β : Type} {X Y : Set β} {x : β} (notY : x ∉ Y) :
    (X ∪ Y) \ {x} = (X \ {x}) ∪ Y := by
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

theorem OnceIn.bind {α β : Type} {X X' : Set FixedIndex} {Y Y' : Set Cell}
    {c : FreeQuery Programs.Spec α} {f : α → FreeQuery Programs.Spec β} (first : OnceIn X Y c)
    (second : ∀ a, OnceIn X' Y' (f a)) (disjointX : Disjoint X X') (disjointY : Disjoint Y Y') :
    OnceIn (X ∪ X') (Y ∪ Y') (c >>= f) := by
  revert disjointX disjointY
  induction first with
  | pure X Y value =>
      exact fun _ _ => (second value).mono Set.subset_union_right Set.subset_union_right
  | fixed X Y index input next inside rest ih =>
      intro disjointX disjointY
      have notX' : index ∉ X' := fun hit => Set.disjoint_left.mp disjointX inside hit
      show OnceIn (X ∪ X') (Y ∪ Y') (FreeQuery.query (PublicQuery.fixedForward index input)
        fun answer => next answer >>= f)
      refine .fixed (X ∪ X') (Y ∪ Y') index input (fun answer => next answer >>= f)
        (Or.inl inside) fun answer => ?_
      rw [diff_union_of_not_mem notX']
      exact ih answer (Set.disjoint_of_subset_left Set.sdiff_subset disjointX) disjointY
  | cell X Y cell label next inside rest ih =>
      intro disjointX disjointY
      have notY' : cell ∉ Y' := fun hit => Set.disjoint_left.mp disjointY inside hit
      show OnceIn (X ∪ X') (Y ∪ Y') (FreeQuery.query (PublicQuery.hash (cellInput cell label))
        fun answer => next answer >>= f)
      refine .cell (X ∪ X') (Y ∪ Y') cell label (fun answer => next answer >>= f)
        (Or.inl inside) fun answer => ?_
      rw [diff_union_of_not_mem notY']
      exact ih answer disjointX (Set.disjoint_of_subset_left Set.sdiff_subset disjointY)

theorem OnceIn.pure' {α : Type} (X : Set FixedIndex) (Y : Set Cell) (value : α) :
    OnceIn X Y (Pure.pure value : FreeQuery Programs.Spec α) := .pure X Y value

/-- One Davies–Meyer question. -/
theorem OnceIn.hashM (index : FixedIndex) (label : Block) :
    OnceIn {index} ∅ (Programs.hashM index label) :=
  .fixed {index} ∅ index label _ rfl fun _ => .pure _ _ _

/-- A loop over pairwise disjoint index and limb sets. -/
theorem OnceIn.vector {α : Type} : ∀ (count : Nat) (X : Fin count → Set FixedIndex)
    (Y : Fin count → Set Cell) (program : Fin count → FreeQuery Programs.Spec α),
    (∀ k, OnceIn (X k) (Y k) (program k)) → (∀ k k', k ≠ k' → Disjoint (X k) (X k')) →
    (∀ k k', k ≠ k' → Disjoint (Y k) (Y k')) →
      OnceIn (⋃ k, X k) (⋃ k, Y k) (FreeQuery.vector count program)
  | 0, _, _, _, _, _, _ => .pure _ _ _
  | count + 1, X, Y, program, each, disjointX, disjointY => by
      have prefixOnce := OnceIn.vector count (fun k => X k.castSucc) (fun k => Y k.castSucc)
        (fun k => program k.castSucc) (fun k => each _)
        (fun k k' ne => disjointX _ _ fun same => ne (Fin.castSucc_injective _ same))
        (fun k k' ne => disjointY _ _ fun same => ne (Fin.castSucc_injective _ same))
      have tail : ∀ values : Vector α count, OnceIn (X (Fin.last count) ∪ ∅) (Y (Fin.last count) ∪ ∅)
          (program (Fin.last count) >>= fun value => Pure.pure (values.push value)) :=
        fun values => (each _).bind (fun _ => .pure ∅ ∅ _) (Set.disjoint_empty _)
          (Set.disjoint_empty _)
      have apartX : Disjoint (⋃ k : Fin count, X k.castSucc) (X (Fin.last count) ∪ ∅) := by
        rw [Set.union_empty, Set.disjoint_iUnion_left]
        exact fun k => disjointX _ _ (Fin.castSucc_lt_last k).ne
      have apartY : Disjoint (⋃ k : Fin count, Y k.castSucc) (Y (Fin.last count) ∪ ∅) := by
        rw [Set.union_empty, Set.disjoint_iUnion_left]
        exact fun k => disjointY _ _ (Fin.castSucc_lt_last k).ne
      refine (prefixOnce.bind tail apartX apartY).mono ?_ ?_
      · rintro i (⟨_, ⟨k, rfl⟩, hi⟩ | hi | hi)
        · exact Set.mem_iUnion.mpr ⟨k.castSucc, hi⟩
        · exact Set.mem_iUnion.mpr ⟨Fin.last count, hi⟩
        · exact hi.elim
      · rintro i (⟨_, ⟨k, rfl⟩, hi⟩ | hi | hi)
        · exact Set.mem_iUnion.mpr ⟨k.castSucc, hi⟩
        · exact Set.mem_iUnion.mpr ⟨Fin.last count, hi⟩
        · exact hi.elim

/-- A switch's mask vector: each of its limbs once, at the switch's label. -/
theorem OnceIn.switchMaskM (lane : Lane) (chunk : Fin chunkCount)
    (switch : Fin (2 ^ chunkWidth chunk)) (label : Block) :
    OnceIn ∅ {cell | cell.1 = ⟨lane, chunk, switch⟩}
      (Programs.switchMaskM lane chunk switch.val label) := by
  have limbs := OnceIn.vector (limbCount lane) (fun _ => ∅)
    (fun k => {(⟨⟨lane, chunk, switch⟩, k⟩ : Cell)})
    (fun k => Programs.askHash (scaleInput lane chunk switch.val k.val label))
    (fun k => .cell ∅ _ ⟨⟨lane, chunk, switch⟩, k⟩ label _ rfl fun _ => .pure _ _ _)
    (fun _ _ _ => Set.disjoint_empty _)
    (fun k k' ne => Set.disjoint_singleton.mpr fun same =>
      ne (eq_of_heq (Sigma.mk.inj_iff.mp same).2))
  refine (limbs.bind (fun _ => .pure ∅ ∅ _) (Set.disjoint_empty _) (Set.disjoint_empty _)).mono
    ?_ ?_
  · rintro i (⟨_, ⟨_, rfl⟩, hi⟩ | hi) <;> exact hi.elim
  · rintro cell (⟨_, ⟨k, rfl⟩, hi⟩ | hi)
    · rw [Set.mem_singleton_iff.mp hi]
      rfl
    · exact hi.elim

/-- A branch: nothing, or a computation. -/
theorem OnceIn.ite {α : Type} (condition : Prop) [Decidable condition] (X : Set FixedIndex)
    (Y : Set Cell) (value : α) (c : FreeQuery Programs.Spec α) (once : OnceIn X Y c) :
    OnceIn X Y (if condition then Pure.pure value else c) := by
  by_cases hit : condition
  · rw [if_pos hit]
    exact .pure _ _ _
  · rw [if_neg hit]
    exact once

/-- **A once-computation reads its answers only at its own indices and limbs.** -/
theorem OnceIn.agree {α : Type} {X : Set FixedIndex} {Y : Set Cell} {c : FreeQuery Programs.Spec α}
    (once : OnceIn X Y c) :
    ∀ (first second : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer),
      (∀ i ∈ X, ∀ x, first (.fixedForward i x) = second (.fixedForward i x)) →
      (∀ cell ∈ Y, ∀ label, first (.hash (cellInput cell label)) =
        second (.hash (cellInput cell label))) →
      transcript first c = transcript second c ∧ c.eval first = c.eval second := by
  induction once with
  | pure X Y value => exact fun _ _ _ _ => ⟨rfl, rfl⟩
  | fixed X Y index input next inside rest ih =>
      intro first second sameX sameY
      have head : first (.fixedForward index input) = second (.fixedForward index input) :=
        sameX index inside input
      have tail := ih (first (.fixedForward index input)) first second
        (fun i hi x => sameX i hi.1 x) sameY
      refine ⟨?_, ?_⟩
      · show ⟨.fixedForward index input, first (.fixedForward index input)⟩ ::
            transcript first (next (first (.fixedForward index input))) =
          ⟨.fixedForward index input, second (.fixedForward index input)⟩ ::
            transcript second (next (second (.fixedForward index input)))
        rw [tail.1, ← head]
      · show (next (first (.fixedForward index input))).eval first =
          (next (second (.fixedForward index input))).eval second
        rw [tail.2, ← head]
  | cell X Y cell label next inside rest ih =>
      intro first second sameX sameY
      have head : first (.hash (cellInput cell label)) = second (.hash (cellInput cell label)) :=
        sameY cell inside label
      have tail := ih (first (.hash (cellInput cell label))) first second sameX
        (fun c hc l => sameY c hc.1 l)
      refine ⟨?_, ?_⟩
      · show ⟨.hash (cellInput cell label), first (.hash (cellInput cell label))⟩ ::
            transcript first (next (first (.hash (cellInput cell label)))) =
          ⟨.hash (cellInput cell label), second (.hash (cellInput cell label))⟩ ::
            transcript second (next (second (.hash (cellInput cell label))))
        rw [tail.1, ← head]
      · show (next (first (.hash (cellInput cell label)))).eval first =
          (next (second (.hash (cellInput cell label)))).eval second
        rw [tail.2, ← head]

end Once

/-! ### A fresh fill run is a table run -/

section Fill

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- The one-pair permutation `input ↦ output`, built on the empty one. -/
def storedPerm (input output : Block) : SparsePermutation (2 ^ 128) :=
  (SparsePermutation.empty (2 ^ 128)).extend (Nat.two_pow_pos 128)
    ((SparsePermutation.empty (2 ^ 128)).input.symm input.toFin)
    ((SparsePermutation.empty (2 ^ 128)).output.symm output.toFin)

/-- The state after storing one pair at an empty fixed-key index. -/
def storeOne (oracle : LState) (index : FixedIndex) (input output : Block) : LState :=
  { oracle with fixed := Function.update oracle.fixed index (storedPerm input output) }

/-- A program at an empty fixed-key index succeeds, storing the pair. -/
theorem program_empty (oracle : LState) (index : FixedIndex) (input output : Block)
    (empty : oracle.fixed index = SparsePermutation.empty _) :
    LazyOracle.program (.fixedForward index input) output oracle
      = some (storeOne oracle index input output) := by
  simp only [LazyOracle.program, LazyOracle.permutationProgram, empty]
  rw [dif_pos ⟨fun known => by
      unfold SparsePermutation.knownInput at known
      exact absurd known (by show ¬ (_ < 0); omega),
    fun known => by
      unfold SparsePermutation.knownOutput at known
      exact absurd known (by show ¬ (_ < 0); omega)⟩]
  rfl

/-- The unknown outputs of the empty permutation are all blocks. -/
def emptyUnknownEquiv :
    {y : Fin (2 ^ 128) // ¬ (SparsePermutation.empty (2 ^ 128)).knownOutput y} ≃ Block where
  toFun y := BitVec.ofFin y.val
  invFun b := ⟨b.toFin, by
    unfold SparsePermutation.knownOutput
    show ¬ (_ < 0)
    omega⟩
  left_inv y := rfl
  right_inv b := rfl

/-- **A lazy question at an empty fixed-key index is a uniform block, stored.** -/
theorem query_empty (oracle : LState) (index : FixedIndex) (input : Block)
    (empty : oracle.fixed index = SparsePermutation.empty _) :
    LazyOracle.query (.fixedForward index input) oracle =
      (PMF.uniformOfFintype Block).map fun output => (output, storeOne oracle index input output) := by
  have key : ∀ state : SparsePermutation (2 ^ 128), state = SparsePermutation.empty _ →
      (state.forward input.toFin).distribution.map (fun answer =>
        (BitVec.ofFin answer.1, ({ oracle with
          fixed := Function.update oracle.fixed index answer.2 } : LState))) =
      (PMF.uniformOfFintype Block).map fun output => (output, storeOne oracle index input output) := by
    intro state same
    subst same
    have fresh : ¬ (SparsePermutation.empty (2 ^ 128)).knownInput input.toFin := by
      show ¬ (_ < 0)
      omega
    obtain ⟨room, nonempty, law⟩ := forward_fresh_eq (SparsePermutation.empty (2 ^ 128))
      input.toFin fresh
    rw [law, PMF.map_comp, ← Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv
      emptyUnknownEquiv, PMF.map_comp]
    rfl
  exact key _ empty

/-- The answers of a once-computation from fixed-key answers `v` and a limb tape `T`. -/
def fixedAnswer (v : FixedIndex → Block) (T : Tape) :
    ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer :=
  tableAnswer (⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0), v, T)

/-- A lazy query at an empty index, averaged. -/
theorem tsum_query_empty (s : LState) (index : FixedIndex) (input : Block)
    (empty : s.fixed index = SparsePermutation.empty _)
    (g : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index input).Answer × LState →
      ℝ≥0∞) :
    ∑' a, LazyOracle.query (.fixedForward index input) s a * g a =
      ∑' o : Block, PMF.uniformOfFintype Block o * g (o, storeOne s index input o) := by
  rw [query_empty s index input empty]
  exact tsum_map_mul _ _ g

/-- A hash program at an unstored input, as a plant. -/
theorem program_hash_fresh (s : LState) (input : BaseField) (answer : Block × Block)
    (fresh : s.hash.lookup input = none) :
    LazyOracle.program (.hash input) answer s = some (plantEntry s ⟨.hash input, answer⟩) := by
  unfold plantEntry
  rw [Kriterion.ArgoMAC.Phase3.Lazy.program_hash_eq, if_pos fresh]
  rfl

/-- **A fresh fill run of a once-computation is its run on a uniform table.** -/
theorem runFill_once (T : Tape) {α : Type} {X : Set FixedIndex} {Y : Set Cell}
    {c : FreeQuery Programs.Spec α} (once : OnceIn X Y c) :
    ∀ (s : LState) (τ : Set Cell), (∀ i ∈ X, s.fixed i = SparsePermutation.empty _) →
      (∀ cell ∈ Y, ∀ label, s.hash.lookup (cellInput cell label) = none) →
      (∀ cell ∈ Y, cell ∉ τ) →
      ∀ (F : Option (α × LState) → ℝ≥0∞),
        (∀ a t t', SameLookups t t' → F (some (a, t)) = F (some (a, t'))) →
        ∑' r, runFillFlag LazyOracle.empty (fun cell => PMF.pure (T cell)) c s τ r * F r =
          ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
            F (some (c.eval (fixedAnswer v T), plantAll (transcript (fixedAnswer v T) c) s)) := by
  induction once with
  | pure X Y value =>
      intro s τ _ _ _ F _
      simp only [runFillFlag, tsum_pure_mul]
      have const : ∀ v : FixedIndex → Block,
          F (some ((FreeQuery.pure value : FreeQuery Programs.Spec α).eval (fixedAnswer v T),
            plantAll (transcript (fixedAnswer v T) (FreeQuery.pure value : FreeQuery Programs.Spec α)) s))
            = F (some (value, s)) := fun v => rfl
      simp_rw [const]
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | fixed X Y index input next inside rest ih =>
      intro s τ empty fresh untouched F invariant
      have emptyHere := empty index inside
      have later : ∀ output : Block, ∀ i ∈ X \ {index},
          (storeOne s index input output).fixed i = SparsePermutation.empty _ := by
        intro output i hi
        show Function.update s.fixed index _ i = _
        rw [Function.update_of_ne hi.2]
        exact empty i hi.1
      have laterTouched : touch (.fixedForward index input) τ = τ := by
        ext cell
        simp only [touch, Set.mem_ofPred_eq, Kriterion.ArgoMAC.Phase3.Lazy.touchedCell, reduceCtorEq,
          or_false]
      simp only [runFillFlag]
      show ∑' r, ((LazyOracle.query (.fixedForward index input) s).bind fun answer =>
        if FullTouch LazyOracle.empty (.fixedForward index input) answer.1 then PMF.pure none else
          runFillFlag LazyOracle.empty (fun cell => PMF.pure (T cell)) (next answer.1) answer.2
            (touch (.fixedForward index input) τ)) r * F r = _
      rw [tsum_bind_mul, tsum_query_empty s index input emptyHere]
      have step : ∀ o : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index input).Answer,
          ∑' r, (if FullTouch (LazyOracle.empty : LState)
              (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index input) o then
              PMF.pure none else
            runFillFlag LazyOracle.empty (fun cell => PMF.pure (T cell)) (next o)
              (storeOne s index input o) (touch (.fixedForward index input) τ)) r * F r =
          ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
            F (some ((next o).eval (fixedAnswer v T),
              plantAll (transcript (fixedAnswer v T) (next o)) (storeOne s index input o))) := by
        intro o
        rw [if_neg (not_fullTouch_empty _ _), laterTouched]
        exact ih o _ _ (later o) fresh untouched F invariant
      refine (tsum_congr fun o => congrArg (PMF.uniformOfFintype Block o * ·) (step o)).trans ?_
      have answer : ∀ v, fixedAnswer v T (.fixedForward index input) = v index := fun v => rfl
      have split := tsum_uniform_split (ι := FixedIndex) (β := Block) index id
        (fun b v => F (some ((next b).eval (fixedAnswer v T), plantAll
          (transcript (fixedAnswer v T) (next b)) (storeOne s index input b))))
        (fun b v c' => by
          have agree := (rest b).agree (fixedAnswer (Function.update v index c') T) (fixedAnswer v T)
            (fun i hi x => by
              show Function.update v index c' i = v i
              rw [Function.update_of_ne hi.2]) (fun _ _ _ => rfl)
          show F (some (_, _)) = F (some (_, _))
          rw [agree.1, agree.2])
      rw [PMF.map_id] at split
      have rhs : ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
          F (some ((FreeQuery.query (spec := Programs.Spec) (PublicQuery.fixedForward index input)
              next).eval (fixedAnswer v T),
            plantAll (transcript (fixedAnswer v T) (FreeQuery.query (spec := Programs.Spec)
              (PublicQuery.fixedForward index input) next)) s)) =
          ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
            F (some ((next (id (v index))).eval (fixedAnswer v T), plantAll
              (transcript (fixedAnswer v T) (next (id (v index))))
                (storeOne s index input (id (v index))))) := by
        refine tsum_congr fun v => congrArg _ ?_
        show F (some ((next (fixedAnswer v T (.fixedForward index input))).eval (fixedAnswer v T),
          plantAll (transcript (fixedAnswer v T) (next (fixedAnswer v T (.fixedForward index input))))
            (plantEntry s ⟨.fixedForward index input, fixedAnswer v T (.fixedForward index input)⟩)))
          = _
        rw [answer]
        unfold plantEntry
        rw [program_empty s _ input _ emptyHere]
        rfl
      rw [rhs]
      exact split.symm
  | cell X Y cell label next inside rest ih =>
      intro s τ empty fresh untouched F invariant
      have freshHere := fresh cell inside label
      have consumed : consumeCell τ s (.hash (cellInput cell label)) = some cell := by
        show Kriterion.ArgoMAC.Phase3.Lazy.consumeHash τ s (cellInput cell label) = some cell
        unfold Kriterion.ArgoMAC.Phase3.Lazy.consumeHash
        rw [Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput]
        dsimp only
        rw [if_neg]
        rintro (member | stored)
        · exact untouched cell inside member
        · exact stored freshHere
      have programmed := program_hash_fresh s (cellInput cell label) (T cell) freshHere
      have freshLater : ∀ c' ∈ Y \ {cell}, ∀ l,
          (plantEntry s ⟨.hash (cellInput cell label), T cell⟩).hash.lookup (cellInput c' l) =
            none := by
        intro c' hc' l
        have stored := programmed
        unfold plantEntry
        rw [Kriterion.ArgoMAC.Phase3.Lazy.program_hash_eq, if_pos freshHere]
        show (s.hash.program (cellInput cell label) _).lookup (cellInput c' l) = none
        rw [HashTable.program_lookup, Function.update_of_ne]
        · exact fresh c' hc'.1 l
        · intro same
          exact hc'.2 (congrArg Prod.fst (Kriterion.ArgoMAC.Phase3.Lazy.cellInput_injective
            (a₁ := (c', l)) (a₂ := (cell, label)) same))
      have emptyLater : ∀ i ∈ X,
          (plantEntry s ⟨.hash (cellInput cell label), T cell⟩).fixed i = SparsePermutation.empty _ := by
        intro i hi
        unfold plantEntry
        rw [Kriterion.ArgoMAC.Phase3.Lazy.program_hash_eq, if_pos freshHere]
        exact empty i hi
      have untouchedLater : ∀ c' ∈ Y \ {cell}, c' ∉ touch (.hash (cellInput cell label)) τ := by
        rintro c' hc' (member | same)
        · exact untouched c' hc'.1 member
        · change Kriterion.ArgoMAC.Phase3.Lazy.cellOf (cellInput cell label) = some c' at same
          rw [Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput] at same
          exact hc'.2 (Option.some.inj same).symm
      simp only [runFillFlag]
      rw [consumed]
      dsimp only
      rw [PMF.pure_bind, if_neg (not_fullTouch_empty _ _)]
      simp only [refillAnswer]
      rw [programmed]
      dsimp only
      rw [ih (T cell) _ _ emptyLater freshLater untouchedLater F invariant]
      refine tsum_congr fun v => congrArg _ ?_
      have answer : fixedAnswer v T (.hash (cellInput cell label)) = T cell :=
        tableAnswer_cell _ cell label
      show _ = F (some ((next (fixedAnswer v T (.hash (cellInput cell label)))).eval (fixedAnswer v T),
          plantAll (transcript (fixedAnswer v T) (next (fixedAnswer v T (.hash (cellInput cell label)))))
            (plantEntry s ⟨.hash (cellInput cell label), fixedAnswer v T (.hash (cellInput cell label))⟩)))
      rw [answer]

end Fill

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
