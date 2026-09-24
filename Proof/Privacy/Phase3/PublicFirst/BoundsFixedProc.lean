/-
**Phase 3, P1m — (B1) the fixed-key part: fold-label entropy on a refill run, at every chunk
width.**

* `cutAt P c` — the program `c` up to its first `P`-question, returning the rest of `c`
  (`cutAt_bind`: running it and then the rest is running `c`); its path is a prefix of `c`'s
  (`prefix_mem_cutAt`), it asks no `P`-question (`cutAt_avoids`), and it keeps `AllQ`-properties
  and freshness.
* `runRefill_potential_prog` — a potential not raised by any forward lazy question and kept by
  every hash program is a supermartingale along P4's refill run (the consumed questions are hash
  programs), e.g. any potential of the fixed-key or of the EncPRF part.
* **`runRefill_xor_le`** — the core: on a refill run from the empty oracle of a fresh forward-only
  program, a block `label = z ⊕ (xor of the answers at a nonempty set of fixed-key indices)`, where
  every index of the set is asked on every path at exactly one input and `z` is read off the path
  before the first question at one of them, hits any `L` with mass `≤ 1/2^128`. The run is split at
  that first question (`cutAt`); after it, `xorF` is a supermartingale starting at `1/2^128`.
* **`runRefill_level_le`** — **fold-label entropy**: for a program that runs a lane as one of its
  parts (`LaneSplit`: the lane's labels read off the questions before it, no question of the rest
  at the lane's fold indices), every label of level `2 ≤ t + 1 ≤ chunkWidth c` of the lane's chunk
  `c` hits any `L` with mass `≤ 1/2^128`, whatever the chunk's width: the fold inputs of the steps
  `2 … chunkWidth c − 1` and the one-hot labels (level `chunkWidth c`).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedStruct

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (interceptAnswer noRecord)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request AllQ FixedAt IndexAt
  runRefill runRefillT runRefill_eq_runRefillT runRefillT_bind continueT dropTouched
  consumeCell_spec queriesAlong query_frame evalLaneM_allQ)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### A program up to its first `P`-question -/

section Cut

variable (P : Request → Prop) {α : Type}

open Classical in
/-- **The program `c` up to its first `P`-question**, returning the rest of `c`. -/
def cutAt : FreeQuery Programs.Spec α → FreeQuery Programs.Spec (FreeQuery Programs.Spec α)
  | .pure value => .pure (.pure value)
  | .query request next =>
      if P request then .pure (.query request next)
      else .query request fun answer => cutAt (next answer)

theorem cutAt_bind (c : FreeQuery Programs.Spec α) : (cutAt P c >>= fun rest => rest) = c := by
  classical
  induction c with
  | pure value => rfl
  | query request next ih =>
    unfold cutAt
    split
    · rfl
    · show FreeQuery.query request (fun answer => cutAt P (next answer) >>= fun rest => rest) = _
      congr 1
      funext answer
      exact ih answer

/-- **The first part asks no `P`-question**, and keeps an `AllQ`-property of the program. -/
theorem cutAt_avoids {Q : Request → Prop} {c : FreeQuery Programs.Spec α} (holds : AllQ Q c) :
    AllQ (fun request => ¬ P request ∧ Q request) (cutAt P c) := by
  classical
  induction holds with
  | pure value => exact .pure _
  | query request next here _ ih =>
    unfold cutAt
    split
    · exact .pure _
    · rename_i notP
      exact .query _ _ ⟨notP, here⟩ ih

/-- **The rest of the program keeps an `AllQ`-property.** -/
theorem cutAt_rest_allQ {Q : Request → Prop} {c : FreeQuery Programs.Spec α} (holds : AllQ Q c)
    (ans : (request : Request) → request.Answer) : AllQ Q (FreeQuery.eval ans (cutAt P c)) := by
  classical
  induction holds with
  | pure value => exact .pure _
  | query request next here rest ih =>
    unfold cutAt
    split
    · exact .query _ _ here rest
    · exact ih _

theorem cutAt_fresh {bits : BitInput} {c : FreeQuery Programs.Spec α} {used : Set Cell}
    (fresh : Fresh bits used c) : Fresh bits used (cutAt P c) := by
  classical
  induction fresh with
  | pure used value => exact .pure _ _
  | query used request next avoid _ ih =>
    unfold cutAt
    split
    · exact .pure _ _
    · exact .query _ _ _ avoid ih

/-- **A `P`-free prefix of a path is a prefix of the first part's path.** -/
theorem prefix_mem_cutAt (ans : (request : Request) → request.Answer) :
    ∀ (c : FreeQuery Programs.Spec α) (front back : List Request),
      queriesAlong ans c = front ++ back → (∀ q ∈ front, ¬ P q) →
        ∀ q ∈ front, q ∈ queriesAlong ans (cutAt P c) := by
  classical
  intro c
  induction c with
  | pure value =>
    intro front back path _ q member
    have empty : front = [] := List.eq_nil_of_append_eq_nil path.symm |>.1
    subst empty
    cases member
  | query request next ih =>
    intro front back path free q member
    cases front with
    | nil => cases member
    | cons head tail =>
      have cons : request :: queriesAlong ans (next (ans request)) = head :: (tail ++ back) :=
        path
      injection cons with headEq tailEq
      subst headEq
      have notP : ¬ P request := free request List.mem_cons_self
      have first : cutAt P (.query request next) =
          .query request fun answer => cutAt P (next answer) := by
        rw [cutAt, if_neg notP]
      rw [first]
      rcases List.mem_cons.mp member with same | later
      · subst same
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (ans request) tail back tailEq
          (fun q' inside => free q' (List.mem_cons_of_mem _ inside)) q later)

end Cut

/-! ### Potentials of the fixed-key part along the refill run -/

section Potential

/-- The potential of a touched-set outcome (an abort weighs nothing). -/
def optWeightT {α : Type} (potential : LState → ℝ≥0∞) :
    Option (α × LState × Record × Set Cell) → ℝ≥0∞
  | none => 0
  | some result => potential result.2.1

/-- **A supermartingale along the refill run**, for a potential kept by every hash program (the
consumed questions are hash programs). -/
theorem runRefill_potential_prog (bits : BitInput) (draw : Cell → PMF (Block × Block))
    (Φ : LState → ℝ≥0∞)
    (hashSame : ∀ (state updated : LState) (input : BaseField) (value : Block × Block),
      LazyOracle.program (.hash input) value state = some updated → Φ updated = Φ state)
    (step : ∀ (request : Request) (state : LState), ForwardOnly request →
      ∑' answer, LazyOracle.query request state answer * Φ answer.2 ≤ Φ state)
    {α : Type} (computation : FreeQuery Programs.Spec α) (holds : AllQ ForwardOnly computation) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell),
      ∑' o, runRefill bits draw computation oracle record touched o * optWeight Φ o ≤ Φ oracle := by
  induction computation with
  | pure value =>
    intro oracle record touched
    simp only [runRefill]
    rw [tsum_pure_mul]
    rfl
  | query request next ih =>
    intro oracle record touched
    simp only [runRefill]
    cases intercept : interceptAnswer bits request with
    | some answer => exact ih answer (AllQ.tail holds _) _ _ _
    | none =>
      simp only
      cases consumed : Kriterion.ArgoMAC.Phase3.Lazy.consumeCell touched oracle request with
      | some cell =>
        obtain ⟨input, rfl, _, _, _⟩ := consumeCell_spec consumed
        rw [tsum_bind_mul]
        refine le_trans (ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (?_ :
          _ ≤ Φ oracle)) (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
        split
        · rw [tsum_pure_mul]
          exact zero_le
        · rename_i updated success
          rw [← hashSame oracle updated input _ success]
          exact ih _ (AllQ.tail holds _) _ _ _
      | none =>
        rw [tsum_bind_mul]
        exact le_trans (ENNReal.tsum_le_tsum fun answer =>
          mul_le_mul' le_rfl (ih answer.1 (AllQ.tail holds _) answer.2 _ _))
          (step request oracle (AllQ.head holds))

theorem runRefillT_potential_prog (bits : BitInput) (draw : Cell → PMF (Block × Block))
    (Φ : LState → ℝ≥0∞)
    (hashSame : ∀ (state updated : LState) (input : BaseField) (value : Block × Block),
      LazyOracle.program (.hash input) value state = some updated → Φ updated = Φ state)
    (step : ∀ (request : Request) (state : LState), ForwardOnly request →
      ∑' answer, LazyOracle.query request state answer * Φ answer.2 ≤ Φ state)
    {α : Type} (computation : FreeQuery Programs.Spec α) (holds : AllQ ForwardOnly computation)
    (oracle : LState) (record : Record) (touched : Set Cell) :
    ∑' o, runRefillT bits draw computation oracle record touched o * optWeightT Φ o ≤ Φ oracle := by
  have base := runRefill_potential_prog bits draw Φ hashSame step computation holds oracle record
    touched
  rw [runRefill_eq_runRefillT, tsum_map_mul] at base
  refine le_trans (le_of_eq (tsum_congr fun o => ?_)) base
  rcases o with _ | o <;> rfl

theorem runRefillT_mem_runRefill (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (c : FreeQuery Programs.Spec α) (oracle : LState) (record : Record) (touched : Set Cell)
    (result : α × LState × Record × Set Cell)
    (member : some result ∈ (runRefillT bits draw c oracle record touched).support) :
    some (dropTouched result) ∈ (runRefill bits draw c oracle record touched).support := by
  rw [runRefill_eq_runRefillT]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some result, member, rfl⟩

/-- A stored forward pair, as a lookup. -/
theorem stored_fixed_lk {state : LState} {i : FixedIndex} {x a : Block}
    (stored : StoredAs state ⟨.fixedForward i x, a⟩) :
    lk (state.fixed i) x.toFin = some a.toFin := by
  change (lk (state.fixed i) x.toFin).map BitVec.ofFin = some a at stored
  cases found : lk (state.fixed i) x.toFin with
  | none => rw [found] at stored; cases stored
  | some y =>
    rw [found] at stored
    simp only [Option.map_some, Option.some.injEq] at stored
    rw [← stored]

/-- A permutation whose stored inputs are all one input has at most one pair. -/
theorem used_le_one (S : SparsePermutation (2 ^ 128)) (x₀ : Fin (2 ^ 128))
    (all : ∀ x y, lk S x = some y → x = x₀) : S.used ≤ 1 := by
  classical
  rw [← card_known]
  refine le_trans (Fintype.card_le_of_injective (fun _ : {z // S.knownInput z} => (0 : Fin 1))
    ?_) (by simp)
  intro a b _
  apply Subtype.ext
  obtain ⟨ya, ha⟩ := Option.ne_none_iff_exists'.mp ((knownInput_iff _ _).mp a.2)
  obtain ⟨yb, hb⟩ := Option.ne_none_iff_exists'.mp ((knownInput_iff _ _).mp b.2)
  rw [all _ _ ha, all _ _ hb]

/-- A permutation with a pair, all at one input, has exactly one pair. -/
theorem used_eq_one (S : SparsePermutation (2 ^ 128)) (x₀ y₀ : Fin (2 ^ 128))
    (found : lk S x₀ = some y₀) (all : ∀ x y, lk S x = some y → x = x₀) : S.used = 1 := by
  have known : S.knownInput x₀ :=
    (knownInput_iff _ _).mpr (by rw [found]; exact Option.some_ne_none _)
  have positive : 0 < S.used := by
    unfold SparsePermutation.knownInput at known
    exact lt_of_le_of_lt (Nat.zero_le _) known
  exact le_antisymm (used_le_one S x₀ all) positive

end Potential

/-! ### The core: a xor of fresh answers, split off at its first question -/

section Core

variable (bits : BitInput) (tape : Tape)

/-- **The core of fold-label entropy**: a block that is a fixed part xor the answers at a nonempty
set of fixed-key indices, each asked on every path at exactly one input, the fixed part read off
the path before the first question at one of them, hits any point with mass `≤ 1/2^128` on a refill
run from the empty oracle. -/
theorem runRefill_xor_le {α : Type} (Q : FreeQuery Programs.Spec α)
    (forward : AllQ ForwardOnly Q) (fresh : Fresh bits ∅ Q) (P : Request → Prop)
    {ι : Type} [DecidableEq ι] (idx : ι → FixedIndex) (inj : Function.Injective idx)
    (J : Finset ι) (nonempty : J.Nonempty) (atP : ∀ p ∈ J, ∀ x, P (.fixedForward (idx p) x))
    (inputOf : ((request : Request) → request.Answer) → ι → Block)
    (z label : ((request : Request) → request.Answer) → Block)
    (algebra : ∀ ans, label ans = z ans ^^^ bigXor J fun p => fixedAns ans (idx p) (inputOf ans p))
    (asked : ∀ ans, ∀ p ∈ J, .fixedForward (idx p) (inputOf ans p) ∈ queriesAlong ans Q)
    (unique : ∀ ans, ∀ p ∈ J, ∀ x, .fixedForward (idx p) x ∈ queriesAlong ans Q →
      x = inputOf ans p)
    (early : ∀ ans, ∃ front back, queriesAlong ans Q = front ++ back ∧ (∀ q ∈ front, ¬ P q) ∧
      ∀ ans' : (request : Request) → request.Answer, (∀ q ∈ front, ans' q = ans q) →
        z ans' = z ans)
    (L : Block) :
    ∑' ran, runRefill bits (fun cell => PMF.pure (tape cell)) Q LazyOracle.empty noRecord ∅ ran *
      optWeight (fun state => ind (label (refillAns bits state) = L)) ran ≤ delta := by
  classical
  have whole : runRefill bits (fun cell => PMF.pure (tape cell)) Q LazyOracle.empty noRecord ∅ =
      ((runRefillT bits (fun cell => PMF.pure (tape cell)) (cutAt P Q) LazyOracle.empty noRecord
        ∅).bind (continueT bits (fun cell => PMF.pure (tape cell)) fun rest => rest)).map
          (Option.map dropTouched) := by
    conv_lhs => rw [← cutAt_bind P Q]
    rw [runRefill_eq_runRefillT, runRefillT_bind]
  rw [whole, tsum_map_mul, tsum_bind_mul]
  refine le_trans (tsum_mul_le_of_support _ _ (fun _ => delta) fun midT midMember => ?_)
    (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
  rcases midT with _ | mid
  · simp only [continueT, tsum_pure_mul, Option.map_none, optWeight]
    exact zero_le
  -- the first part: described, nothing asked at `J`
  have firstAvoid := cutAt_avoids P forward
  have firstRun := runRefillT_mem_runRefill bits _ _ _ _ _ _ midMember
  have d1 := runRefill_describe bits tape _ (firstAvoid.mono fun _ both => both.2) ∅
    (cutAt_fresh P fresh) LazyOracle.empty noRecord ∅ (fun _ _ => ⟨fun h => h, fun _ => rfl⟩) _
    firstRun
  have unused : ∀ p ∈ J, (mid.2.1.fixed (idx p)).used = 0 := by
    refine runRefill_invariant bits _ (fun request => ¬ P request ∧ ForwardOnly request)
      (fun state => ∀ p ∈ J, (state.fixed (idx p)).used = 0)
      (fun request state both holds answer member p inside => ?_)
      (fun request state touched cell value updated _ holds consumed success p inside => ?_)
      (cutAt P Q) firstAvoid LazyOracle.empty noRecord ∅ _ (fun _ _ => rfl) firstRun
    · rw [query_frame request state answer member (idx p) (by
        cases request with
        | fixedForward index input =>
          intro same
          cases same
          exact both.1 (atP p inside input)
        | fixedInverse _ _ => exact both.2.elim
        | encForward _ _ => exact fun same => by cases same
        | encInverse _ _ => exact fun same => by cases same
        | hash _ => exact fun same => by cases same)]
      exact holds p inside
    · obtain ⟨input, rfl, _, _, _⟩ := consumeCell_spec consumed
      rw [(program_hash_pairs input _ state updated success).1]
      exact holds p inside
  have restForward : AllQ ForwardOnly mid.1 := by
    have value : mid.1 = FreeQuery.eval (refillAns bits mid.2.1) (cutAt P Q) := d1.value
    rw [value]
    exact cutAt_rest_allQ P forward _
  -- after the split: the xor potential
  show ∑' ranT, runRefillT bits (fun cell => PMF.pure (tape cell)) mid.1 mid.2.1 mid.2.2.1
    mid.2.2.2 ranT * optWeight (fun state => ind (label (refillAns bits state) = L))
      (Option.map dropTouched ranT) ≤ delta
  refine le_trans (tsum_mul_le_of_support _ _
    (optWeightT fun state => xorF idx J (L ^^^ z (refillAns bits mid.2.1)) state.fixed)
    fun ranT ranMember => ?_)
    (le_trans (runRefillT_potential_prog bits _
      (fun state => xorF idx J (L ^^^ z (refillAns bits mid.2.1)) state.fixed)
      (fun state updated input value success => by
        rw [(program_hash_pairs input value state updated success).1])
      (fun request state fwd => fixedAll_lift_step _
        (fun fixed j x => xorF_step idx inj J _ fixed j x) request fwd state) mid.1 restForward
      mid.2.1 mid.2.2.1 mid.2.2.2)
      (le_of_eq (xorF_fresh idx J nonempty _ _ unused)))
  rcases ranT with _ | ranT
  · exact le_rfl
  simp only [Option.map_some, optWeight, optWeightT]
  -- the whole run, described
  have ranRun : some (dropTouched ranT) ∈
      (runRefill bits (fun cell => PMF.pure (tape cell)) Q LazyOracle.empty noRecord
        ∅).support := by
    rw [whole]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some ranT, (PMF.mem_support_bind_iff _ _ _).mpr
      ⟨some mid, midMember, ranMember⟩, rfl⟩
  have d := runRefill_describe bits tape Q forward ∅ fresh LazyOracle.empty noRecord ∅
    (fun _ _ => ⟨fun h => h, fun _ => rfl⟩) _ ranRun
  have grow : Grows mid.2.1 ranT.2.1 :=
    runRefill_grows bits _ mid.1 mid.2.1 mid.2.2.1 mid.2.2.2 _
      (runRefillT_mem_runRefill bits _ _ _ _ _ _ ranMember)
  -- the fixed part is the first part's
  have zSame : z (refillAns bits ranT.2.1) = z (refillAns bits mid.2.1) := by
    obtain ⟨front, back, path, free, determined⟩ := early (refillAns bits mid.2.1)
    refine determined _ fun q member => ?_
    have inFirst := prefix_mem_cutAt P (refillAns bits mid.2.1) Q front back path free q member
    cases intercept : interceptAnswer bits q with
    | some a => rw [refillAns_intercept intercept, refillAns_intercept intercept]
    | none =>
      rw [refillAns_plain intercept, refillAns_plain intercept]
      exact answerOf_of_stored (storedAs_grows grow (d1.stored q inFirst intercept))
  -- every index of `J` holds exactly its question's pair
  have pairs : ∀ p ∈ J, lk (ranT.2.1.fixed (idx p)) (inputOf (refillAns bits ranT.2.1) p).toFin =
      some (fixedAns (refillAns bits ranT.2.1) (idx p)
        (inputOf (refillAns bits ranT.2.1) p)).toFin := by
    intro p inside
    have stored := d.stored _ (asked _ p inside) rfl
    exact stored_fixed_lk (a := fixedAns (refillAns bits ranT.2.1) (idx p)
      (inputOf (refillAns bits ranT.2.1) p)) (by rw [fixedAns, refillAns_plain rfl]; exact stored)
  have one : ∀ p ∈ J, (ranT.2.1.fixed (idx p)).used = 1 := by
    intro p inside
    refine used_eq_one _ _ _ (pairs p inside) fun x y found => ?_
    rcases d.fixed (idx p) x y found with old | onPath
    · rw [show lk ((LazyOracle.empty : LState).fixed (idx p)) x = none from lk_empty x] at old
      cases old
    · have same : BitVec.ofFin x = inputOf (refillAns bits ranT.2.1) p :=
        unique (refillAns bits ranT.2.1) p inside _ onPath
      rw [← same, BitVec.toFin_ofFin]
  refine le_trans (le_of_eq (congrArg ind (propext ?_))) (xorF_bound idx J _ _ one
    (fun p => (inputOf (refillAns bits ranT.2.1) p).toFin)
    (fun p => (fixedAns (refillAns bits ranT.2.1) (idx p)
      (inputOf (refillAns bits ranT.2.1) p)).toFin) pairs)
  simp only [BitVec.ofFin_toFin]
  show label (refillAns bits ranT.2.1) = L ↔ _
  rw [algebra, zSame]
  constructor
  · intro same
    rw [← same, BitVec.xor_comm (z (refillAns bits mid.2.1)), BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]
  · intro same
    rw [same, BitVec.xor_comm L, xor_left_cancel']

end Core

/-! ### Fold-label entropy of a lane run inside a program -/

section Level

/-- A question away from a lane's fold: not a fold question of the lane. -/
def AwayFrom (lane : Lane) : Request → Prop
  | .fixedForward i _ => ∀ c, ¬ IndexAt lane c i
  | _ => True

theorem stepAt_indexAt {lane : Lane} {c : Fin chunkCount} {t : ℕ} {i : FixedIndex}
    (atStep : StepAt lane c t i) : IndexAt lane c i := by
  cases i with
  | hot l cc f e h => exact ⟨atStep.1, atStep.2.1⟩
  | gadget _ _ _ => exact atStep.elim

theorem awayFrom_not_stepAt {lane : Lane} {c : Fin chunkCount} {t : ℕ} {q : Request}
    (away : AwayFrom lane q) : ¬ FixedAt (StepAt lane c t) q := by
  cases q with
  | fixedForward i x => exact fun atStep => away c (stepAt_indexAt atStep)
  | _ => exact id

variable [FieldCertificate]

/-- **A program that runs a lane as one of its parts**: along every answer function its path is
the questions before the lane, the lane's own path at labels read off those questions, and the
questions after it; none of those is a fold question of the lane. -/
def LaneSplit {α : Type} (Q : FreeQuery Programs.Spec α) (lane : Lane)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (word : BitVec coordinateBitCount)
    (labelsOf : ((request : Request) → request.Answer) → Fin coordinateBitCount → Block) : Prop :=
  ∀ ans : (request : Request) → request.Answer, ∃ before after,
    queriesAlong ans Q = before ++
      queriesAlong ans (Programs.evalLaneM lane joins scale word (labelsOf ans)) ++ after ∧
    (∀ q ∈ before, AwayFrom lane q) ∧ (∀ q ∈ after, AwayFrom lane q) ∧
    ∀ ans' : (request : Request) → request.Answer, (∀ q ∈ before, ans' q = ans q) →
      labelsOf ans' = labelsOf ans

variable (bits : BitInput) (tape : Tape)

/-- **Fold-label entropy**: a label of level `t + 1 ≥ 2` of chunk `c` of a lane run inside a fresh
forward-only program hits any point with mass `≤ 1/2^128` on a refill run from the empty oracle,
at every chunk width. -/
theorem runRefill_level_le {α : Type} (Q : FreeQuery Programs.Spec α)
    (forward : AllQ ForwardOnly Q) (fresh : Fresh bits ∅ Q) (lane : Lane)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (word : BitVec coordinateBitCount)
    (labelsOf : ((request : Request) → request.Answer) → Fin coordinateBitCount → Block)
    (split : LaneSplit Q lane joins scale word labelsOf) (c : Fin chunkCount) (t : ℕ)
    (one : 1 ≤ t) (small : t < chunkWidth c) (n : Fin (2 ^ (t + 1))) (L : Block) :
    ∑' ran, runRefill bits (fun cell => PMF.pure (tape cell)) Q LazyOracle.empty noRecord ∅ ran *
      optWeight (fun state => ind (laneFoldLevel (refillAns bits state) lane joins word
        (labelsOf (refillAns bits state)) c (t + 1) n = L)) ran ≤ delta := by
  classical
  have stepSmall : t < chunkBits := step_lt_chunkBits small
  refine runRefill_xor_le bits tape Q forward fresh (FixedAt (StepAt lane c t))
    (fun p : Fin (2 ^ t) × Bool => hotIndexNat lane c t p.1.val p.2) ?_
    (nodeEntries (activeAt (chunkValue word c).toNat t) (nodeParent n) ×ˢ Finset.univ)
    ((nodeEntries_nonempty one _ _).product Finset.univ_nonempty)
    (fun p _ _ => stepAt_hot stepSmall p.1.val p.2)
    (fun ans p => laneFoldLevel ans lane joins word (labelsOf ans) c t p.1)
    (fun ans => (if n.val < 2 ^ t then laneFoldLevel ans lane joins word (labelsOf ans) c t
        (nodeParent n) else 0) ^^^
      (if nodeParent n = activeAt (chunkValue word c).toNat t then
        joinAt (hotSlice joins c) t ^^^ labelAt (chunkLabels (labelsOf ans) c) t else 0))
    (fun ans => laneFoldLevel ans lane joins word (labelsOf ans) c (t + 1) n)
    (fun ans => levelAt_node ans lane c _ _ _ t n) ?_ ?_ ?_ L
  · -- the fold indices of step `t` are distinct
    rintro ⟨e, h⟩ ⟨e', h'⟩ same
    obtain ⟨_, _, _, entryEq, halfEq⟩ := hotIndexNat_inj stepSmall stepSmall
      (entry_lt_chunkBits small e) (entry_lt_chunkBits small e') same
    exact Prod.ext (Fin.ext entryEq) halfEq
  · -- every entry of the node is asked
    intro ans p inside
    obtain ⟨before, after, path, _, _, _⟩ := split ans
    rw [path]
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    exact (lane_fold_question ans lane joins scale word (labelsOf ans) _ _).mpr ⟨c, t, small, p.1,
      nodeEntries_inactive (Finset.mem_product.mp inside).1, p.2, rfl, rfl⟩
  · -- at exactly one input
    intro ans p _ x member
    obtain ⟨before, after, path, away, awayAfter, _⟩ := split ans
    rw [path] at member
    have indexAt : IndexAt lane c (hotIndexNat lane c t p.1.val p.2) :=
      Kriterion.ArgoMAC.Phase3.Lazy.hotIndexNat_indexAt lane c _ _ _
    rcases List.mem_append.mp member with front | later
    · rcases List.mem_append.mp front with early | inLane
      · exact absurd indexAt (away _ early c)
      · obtain ⟨c', s, small', e', _, h', iEq, xEq⟩ :=
          (lane_fold_question ans lane joins scale word (labelsOf ans) _ _).mp inLane
        obtain ⟨_, chunkEq, stepEq, entryEq, _⟩ := hotIndexNat_inj stepSmall
          (step_lt_chunkBits small') (entry_lt_chunkBits small p.1)
          (entry_lt_chunkBits small' e') iEq
        subst chunkEq
        subst stepEq
        rw [xEq, show e' = p.1 from Fin.ext entryEq.symm]
    · exact absurd indexAt (awayAfter _ later c)
  · -- the fixed part is read off the questions before step `t`
    intro ans
    obtain ⟨before, after, path, away, _, labelsRead⟩ := split ans
    obtain ⟨front, back, lanePath, foldIn, free⟩ :=
      lane_prefix ans lane joins scale word (labelsOf ans) c t small.le
    refine ⟨before ++ front, back ++ after, ?_, ?_, ?_⟩
    · rw [path, lanePath]
      simp only [List.append_assoc]
    · intro q member
      rcases List.mem_append.mp member with early | inLane
      · exact awayFrom_not_stepAt (away q early)
      · exact free q inLane
    · intro ans' agree
      have labelsEq : labelsOf ans' = labelsOf ans :=
        labelsRead ans' fun q member => agree q (List.mem_append_left _ member)
      have levelEq : laneFoldLevel ans' lane joins word (labelsOf ans) c t =
          laneFoldLevel ans lane joins word (labelsOf ans) c t :=
        (queriesAlong_congr ans ans' _ fun q member =>
          agree q (List.mem_append_right _ (foldIn q member))).2
      simp only [labelsEq, levelEq]

end Level

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
