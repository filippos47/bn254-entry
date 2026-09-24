/-
**Phase 3, P4b — frames of the refill run, and expectations over it.**

* `runRefillT_intercepted`, `runRefillT_lazy`, `runRefillT_consumed`: one step of the runner.
* `expectO μ f`: the expectation of a nonnegative observable over the successful outcomes of `μ`
  (an abort contributes `0`); `expectO_runBind` is the bind law of `runRefillT` in this currency.
* `Plain bits Y Z`: a forward fixed-key query at an index in `Y`, an EncPRF forward query or a
  non-designated hash query at an input in `Z`. **`runRefillT_value_frame`**: a program of plain
  queries has the same law of values from any two states that agree on `Y`, on the EncPRF part and
  on the hash lookups at `Z`, and on which cells of the inputs in `Z` are touched -- whatever the
  records. **`runRefillT_support_frame`**: on every path it leaves every index outside `Y` and the
  record as it found them.
-/

import Proof.Privacy.Phase3.Lazy.Program

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### Expectations over outcomes with aborts -/

/-- The expectation of `f` over the successful outcomes of `μ`. -/
def expectO {β : Type} (μ : PMF (Option β)) (f : β → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' o, μ o * Option.elim o 0 f

section Expect

variable {β γ : Type}

theorem expectO_bind (μ : PMF γ) (g : γ → PMF (Option β)) (f : β → ℝ≥0∞) :
    expectO (μ.bind g) f = ∑' c, μ c * expectO (g c) f := by
  unfold expectO
  simp only [PMF.bind_apply]
  calc ∑' o, (∑' c, μ c * g c o) * Option.elim o 0 f
      = ∑' o, ∑' c, μ c * g c o * Option.elim o 0 f :=
        tsum_congr fun o => ENNReal.tsum_mul_right.symm
    _ = ∑' c, ∑' o, μ c * g c o * Option.elim o 0 f := ENNReal.tsum_comm
    _ = _ := tsum_congr fun c => by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun o => by ring

theorem expectO_pure_some (b : β) (f : β → ℝ≥0∞) : expectO (PMF.pure (some b)) f = f b := by
  unfold expectO
  rw [tsum_eq_single (some b)]
  · simp
  · intro o different
    simp [PMF.pure_apply, different]

theorem expectO_pure_none (f : β → ℝ≥0∞) : expectO (PMF.pure (none : Option β)) f = 0 := by
  unfold expectO
  refine ENNReal.tsum_eq_zero.mpr fun o => ?_
  cases o with
  | none => simp
  | some b => simp [PMF.pure_apply]

theorem expectO_mono (μ : PMF (Option β)) {f g : β → ℝ≥0∞} (le : ∀ b, f b ≤ g b) :
    expectO μ f ≤ expectO μ g := by
  unfold expectO
  refine ENNReal.tsum_le_tsum fun o => mul_le_mul_of_nonneg_left ?_ zero_le
  cases o with
  | none => exact le_rfl
  | some b => exact le b

theorem expectO_mono_support (μ : PMF (Option β)) {f g : β → ℝ≥0∞}
    (le : ∀ b, some b ∈ μ.support → f b ≤ g b) : expectO μ f ≤ expectO μ g := by
  unfold expectO
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases zero : μ o = 0
  · rw [zero, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left ?_ zero_le
    cases o with
    | none => exact le_rfl
    | some b => exact le b ((PMF.mem_support_iff _ _).mpr zero)

theorem expectO_le_one (μ : PMF (Option β)) {f : β → ℝ≥0∞} (le : ∀ b, f b ≤ 1) :
    expectO μ f ≤ 1 := by
  unfold expectO
  calc ∑' o, μ o * Option.elim o 0 f ≤ ∑' o, μ o * 1 := by
        refine ENNReal.tsum_le_tsum fun o => mul_le_mul_of_nonneg_left ?_ zero_le
        cases o with
        | none => exact zero_le
        | some b => exact le b
    _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem expectO_const_le (μ : PMF (Option β)) (c : ℝ≥0∞) : expectO μ (fun _ => c) ≤ c := by
  unfold expectO
  calc ∑' o, μ o * Option.elim o 0 (fun _ => c) ≤ ∑' o, μ o * c := by
        refine ENNReal.tsum_le_tsum fun o => mul_le_mul_of_nonneg_left ?_ zero_le
        cases o with
        | none => exact zero_le
        | some b => exact le_rfl
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem expectO_add (μ : PMF (Option β)) (f g : β → ℝ≥0∞) :
    expectO μ (fun b => f b + g b) = expectO μ f + expectO μ g := by
  unfold expectO
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun o => ?_
  cases o with
  | none => simp
  | some b => simp [mul_add]

theorem expectO_mul_left (μ : PMF (Option β)) (c : ℝ≥0∞) (f : β → ℝ≥0∞) :
    expectO μ (fun b => c * f b) = c * expectO μ f := by
  unfold expectO
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun o => ?_
  cases o with
  | none => simp
  | some b => simp only [Option.elim]; ring

theorem expectO_map (μ : PMF (Option γ)) (h : γ → β) (f : β → ℝ≥0∞) :
    expectO (μ.map (Option.map h)) f = expectO μ (f ∘ h) := by
  rw [← PMF.bind_pure_comp, expectO_bind]
  unfold expectO
  refine tsum_congr fun o => ?_
  congr 1
  cases o with
  | none => exact expectO_pure_none f
  | some b => exact expectO_pure_some (h b) f

end Expect

/-! ### One step of the runner -/

section Steps

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
  (bits : BitInput) (draw : Cell → PMF (Block × Block))

theorem runRefillT_intercepted {α : Type} (request : Request)
    (next : request.Answer → FreeQuery Programs.Spec α) (oracle : LState) (record : Record)
    (touched : Set Cell) (answer : request.Answer)
    (intercepted : interceptAnswer bits request = some answer) :
    runRefillT bits draw (.query request next) oracle record touched =
      runRefillT bits draw (next answer) oracle (recordAfter bits request record) touched := by
  simp only [runRefillT]
  split
  · rename_i answer' hit
    rw [intercepted] at hit
    cases hit
    rfl
  · rename_i hit
    rw [intercepted] at hit
    cases hit

theorem runRefillT_lazy {α : Type} (request : Request)
    (next : request.Answer → FreeQuery Programs.Spec α) (oracle : LState) (record : Record)
    (touched : Set Cell) (intercept : interceptAnswer bits request = none)
    (consume : consumeCell touched oracle request = none) :
    runRefillT bits draw (.query request next) oracle record touched =
      (LazyOracle.query request oracle).bind fun answer =>
        runRefillT bits draw (next answer.1) answer.2 record (touch request touched) := by
  simp only [runRefillT]
  split
  · rename_i answer hit
    rw [intercept] at hit
    cases hit
  · split
    · rename_i cell hit
      rw [consume] at hit
      cases hit
    · rfl

theorem runRefillT_consumed {α : Type} (request : Request)
    (next : request.Answer → FreeQuery Programs.Spec α) (oracle : LState) (record : Record)
    (touched : Set Cell) (cell : Cell) (intercept : interceptAnswer bits request = none)
    (consume : consumeCell touched oracle request = some cell) :
    runRefillT bits draw (.query request next) oracle record touched =
      (draw cell).bind fun value =>
        match LazyOracle.program request (refillAnswer request value) oracle with
        | none => PMF.pure none
        | some updated => runRefillT bits draw (next (refillAnswer request value)) updated record
            (touch request touched) := by
  simp only [runRefillT]
  split
  · rename_i answer hit
    rw [intercept] at hit
    cases hit
  · split
    · rename_i cell' hit
      rw [consume] at hit
      cases hit
      rfl
    · rename_i hit
      rw [consume] at hit
      cases hit

/-- **The bind law in the expectation currency.** -/
theorem expectO_runBind {α β : Type} (c : FreeQuery Programs.Spec α)
    (k : α → FreeQuery Programs.Spec β) (oracle : LState) (record : Record)
    (touched : Set Cell) (f : β × LState × Record × Set Cell → ℝ≥0∞) :
    expectO (runRefillT bits draw (c >>= k) oracle record touched) f =
      expectO (runRefillT bits draw c oracle record touched) fun r =>
        expectO (runRefillT bits draw (k r.1) r.2.1 r.2.2.1 r.2.2.2) f := by
  rw [runRefillT_bind, expectO_bind]
  unfold expectO
  refine tsum_congr fun o => ?_
  congr 1
  cases o with
  | none => exact expectO_pure_none f
  | some r => rfl

end Steps

/-! ### The frame lemmas -/

/-- **A plain request**: a forward fixed-key query at an index in `Y`, an EncPRF forward query or
a non-designated hash query at an input in `Z`. -/
def Plain (bits : BitInput) (Y : FixedIndex → Prop) (Z : BaseField → Prop) : Request → Prop
  | .fixedForward index _ => Y index
  | .fixedInverse _ _ => False
  | .encForward _ _ => True
  | .encInverse _ _ => False
  | .hash input => Z input ∧ ¬ IsDesignated bits input

/-- Two lazy states agree on the indices in `Y`, on the EncPRF part and on the hash lookups at
`Z`. -/
def AgreeOn (Y : FixedIndex → Prop) (Z : BaseField → Prop) (oracle oracle' : LState) : Prop :=
  (∀ index, Y index → oracle.fixed index = oracle'.fixed index) ∧ oracle.enc = oracle'.enc ∧
    ∀ input, Z input → oracle.hash.lookup input = oracle'.hash.lookup input

/-- Two touched sets agree on the cells of the inputs in `Z`. -/
def TouchAgree (Z : BaseField → Prop) (touched touched' : Set Cell) : Prop :=
  ∀ cell, (∃ label, Z (cellInput cell label)) → (cell ∈ touched ↔ cell ∈ touched')

section Frame

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
  (bits : BitInput) (draw : Cell → PMF (Block × Block))

theorem plain_intercept {Y : FixedIndex → Prop} {Z : BaseField → Prop} {request : Request}
    (plain : Plain bits Y Z request) : interceptAnswer bits request = none := by
  cases request with
  | fixedForward _ _ => rfl
  | fixedInverse _ _ => exact plain.elim
  | encForward _ _ => rfl
  | encInverse _ _ => exact plain.elim
  | hash input => exact interceptAnswer_plain bits plain.2

theorem touch_agree {Z : BaseField → Prop} {touched touched' : Set Cell}
    (agree : TouchAgree Z touched touched') (request : Request) :
    TouchAgree Z (touch request touched) (touch request touched') := by
  intro cell inside
  simp only [touch, Set.mem_ofPred_eq]
  rw [agree cell inside]

theorem consumeCell_agree {Y : FixedIndex → Prop} {Z : BaseField → Prop} {request : Request}
    (plain : Plain bits Y Z request) {oracle oracle' : LState} {touched touched' : Set Cell}
    (agree : AgreeOn Y Z oracle oracle') (touchAgree : TouchAgree Z touched touched') :
    consumeCell touched oracle request = consumeCell touched' oracle' request := by
  cases request with
  | fixedForward _ _ => rfl
  | fixedInverse _ _ => rfl
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash input =>
      change consumeHash touched oracle input = consumeHash touched' oracle' input
      unfold consumeHash
      cases found : cellOf input with
      | none => rfl
      | some cell =>
          obtain ⟨label, same⟩ := cellOf_spec found
          dsimp only
          rw [touchAgree cell ⟨label, same ▸ plain.1⟩, agree.2.2 input plain.1]

/-- One more hash entry, on two agreeing states, keeps them agreeing. -/
theorem agreeOn_cons {Y : FixedIndex → Prop} {Z : BaseField → Prop} {oracle oracle' : LState}
    (agree : AgreeOn Y Z oracle oracle') (input : BaseField)
    (value : Fin (Fintype.card (Block × Block))) :
    AgreeOn Y Z { oracle with hash := (input, value) :: oracle.hash }
      { oracle' with hash := (input, value) :: oracle'.hash } := by
  refine ⟨agree.1, agree.2.1, fun other inside => ?_⟩
  by_cases same : other = input
  · subst same
    simp [List.lookup]
  · rw [lookup_cons_ne _ input other value same, lookup_cons_ne _ input other value same]
    exact agree.2.2 other inside

/-- **The value law of a plain program depends only on the state it can see.** -/
theorem runRefillT_value_frame (Y : FixedIndex → Prop) (Z : BaseField → Prop) {α : Type}
    {c : FreeQuery Programs.Spec α} (plain : AllQ (Plain bits Y Z) c) :
    ∀ (oracle oracle' : LState) (record record' : Record) (touched touched' : Set Cell),
      AgreeOn Y Z oracle oracle' → TouchAgree Z touched touched' →
        (runRefillT bits draw c oracle record touched).map (Option.map Prod.fst) =
          (runRefillT bits draw c oracle' record' touched').map (Option.map Prod.fst) := by
  induction plain with
  | pure value =>
      intro oracle oracle' record record' touched touched' _ _
      simp only [runRefillT, PMF.pure_map, Option.map_some]
  | query request next here _ ih =>
      intro oracle oracle' record record' touched touched' agree touchAgree
      have intercept := plain_intercept bits here
      have consumeSame := consumeCell_agree bits here agree touchAgree
      cases consumed : consumeCell touched oracle request with
      | some cell =>
          obtain ⟨input, rfl, _, fresh, _⟩ := consumeCell_spec consumed
          obtain ⟨_, same, _, fresh', _⟩ := consumeCell_spec (consumeSame ▸ consumed)
          cases same
          rw [runRefillT_consumed bits draw _ next oracle record touched cell intercept
            consumed, runRefillT_consumed bits draw _ next oracle' record' touched' cell
            intercept (consumeSame ▸ consumed), PMF.map_bind, PMF.map_bind]
          refine congrArg _ (funext fun value => ?_)
          rw [program_hash_refill, program_hash_refill, if_pos fresh, if_pos fresh']
          exact ih _ _ _ _ _ _ _ (agreeOn_cons agree input _) (touch_agree touchAgree _)
      | none =>
          rw [runRefillT_lazy bits draw request next oracle record touched intercept consumed,
            runRefillT_lazy bits draw request next oracle' record' touched' intercept
              (consumeSame ▸ consumed), PMF.map_bind, PMF.map_bind]
          cases request with
          | fixedForward index input =>
              simp only [LazyOracle.query, PMF.bind_map]
              rw [agree.1 index here]
              refine congrArg _ (funext fun drawn => ?_)
              refine ih _ _ _ _ _ _ _ ⟨fun other inside => ?_, agree.2⟩ (touch_agree touchAgree _)
              by_cases same : other = index
              · subst same
                simp
              · simp [Function.update_of_ne same, agree.1 other inside]
          | fixedInverse _ _ => exact here.elim
          | encForward index input =>
              simp only [LazyOracle.query, PMF.bind_map]
              rw [agree.2.1]
              refine congrArg _ (funext fun drawn => ?_)
              exact ih _ _ _ _ _ _ _ ⟨agree.1, by simp, agree.2.2⟩ (touch_agree touchAgree _)
          | encInverse _ _ => exact here.elim
          | hash input =>
              have lookupSame := agree.2.2 input here.1
              cases found : oracle.hash.lookup input with
              | some value =>
                  rw [query_hash_bind_found input oracle value found,
                    query_hash_bind_found input oracle' value (lookupSame ▸ found)]
                  exact ih _ _ _ _ _ _ _ agree (touch_agree touchAgree _)
              | none =>
                  rw [query_hash_bind_fresh input oracle found,
                    query_hash_bind_fresh input oracle' (lookupSame ▸ found)]
                  refine congrArg _ (funext fun value => ?_)
                  exact ih _ _ _ _ _ _ _ (agreeOn_cons agree input value)
                    (touch_agree touchAgree _)

/-- **A plain program leaves every index outside `Y`, and the record, as it found them.** -/
theorem runRefillT_support_frame (Y : FixedIndex → Prop) (Z : BaseField → Prop) {α : Type}
    {c : FreeQuery Programs.Spec α} (plain : AllQ (Plain bits Y Z) c) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell)
      (result : α × LState × Record × Set Cell),
      some result ∈ (runRefillT bits draw c oracle record touched).support →
        (∀ index, ¬ Y index → result.2.1.fixed index = oracle.fixed index) ∧
          result.2.2.1 = record := by
  induction plain with
  | pure value =>
      intro oracle record touched result member
      simp only [runRefillT, PMF.support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
      subst member
      exact ⟨fun _ _ => rfl, rfl⟩
  | query request next here _ ih =>
      intro oracle record touched result member
      have intercept := plain_intercept bits here
      -- the touched index of a plain request is in `Y`
      have inY : ∀ index, ¬ Y index → touchedIndex request ≠ some index := by
        intro index outside hit
        cases request with
        | fixedForward index' input =>
            simp only [touchedIndex, Option.some.injEq] at hit
            subst hit
            exact outside here
        | fixedInverse _ _ => exact here.elim
        | encForward _ _ => simp [touchedIndex] at hit
        | encInverse _ _ => exact here.elim
        | hash _ => simp [touchedIndex] at hit
      cases consumed : consumeCell touched oracle request with
      | some cell =>
          rw [runRefillT_consumed bits draw request next oracle record touched cell intercept
            consumed] at member
          obtain ⟨value, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          obtain ⟨input, rfl, _, _, _⟩ := consumeCell_spec consumed
          split at member
          · simp at member
          · rename_i updated programmed
            obtain ⟨frame, recordSame⟩ := ih _ _ _ _ _ member
            refine ⟨fun index outside => ?_, recordSame⟩
            rw [frame index outside, (program_lookup_frame input _ oracle updated programmed).1]
      | none =>
          rw [runRefillT_lazy bits draw request next oracle record touched intercept consumed]
            at member
          obtain ⟨answer, answerMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          obtain ⟨frame, recordSame⟩ := ih _ _ _ _ _ member
          refine ⟨fun index outside => ?_, recordSame⟩
          exact (frame index outside).trans (query_frame request oracle answer answerMember index
            (inY index outside))

/-- A designated query carrying the label `label`. -/
def Labelled (bits : BitInput) (label : Block) (request : Request) : Prop :=
  ∀ input, request = .hash input → IsDesignated bits input → scaleLabel input = label

/-- **A program whose designated queries all carry `label` records at most `label`**: on every
path, each record entry is the old one or `label`. -/
theorem runRefillT_record_labelled (label : Block) {α : Type} {c : FreeQuery Programs.Spec α}
    (labelled : AllQ (Labelled bits label) c) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell)
      (result : α × LState × Record × Set Cell),
      some result ∈ (runRefillT bits draw c oracle record touched).support →
        ∀ limb, result.2.2.1 limb = record limb ∨ result.2.2.1 limb = some label := by
  induction labelled with
  | pure value =>
      intro oracle record touched result member limb
      simp only [runRefillT, PMF.support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
      subst member
      exact Or.inl rfl
  | query request next here _ ih =>
      intro oracle record touched result member limb
      cases intercept : interceptAnswer bits request with
      | some answer =>
          rw [runRefillT_intercepted bits draw request next oracle record touched answer intercept]
            at member
          rcases ih answer _ _ _ result member limb with same | same
          · cases request with
            | hash input =>
                have designated : IsDesignated bits input := by
                  by_contra notDesignated
                  rw [interceptAnswer_plain bits notDesignated] at intercept
                  cases intercept
                simp only [recordAfter] at same
                split at same
                · exact Or.inr (same.trans (congrArg some (here input rfl designated)))
                · exact Or.inl same
            | fixedForward _ _ => exact Or.inl same
            | fixedInverse _ _ => exact Or.inl same
            | encForward _ _ => exact Or.inl same
            | encInverse _ _ => exact Or.inl same
          · exact Or.inr same
      | none =>
          cases consume : consumeCell touched oracle request with
          | some cell =>
              rw [runRefillT_consumed bits draw request next oracle record touched cell intercept
                consume] at member
              obtain ⟨value, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
              split at member
              · simp at member
              · exact ih _ _ _ _ _ member limb
          | none =>
              rw [runRefillT_lazy bits draw request next oracle record touched intercept consume]
                at member
              obtain ⟨answer, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
              exact ih _ _ _ _ _ member limb

end Frame

end

end Kriterion.ArgoMAC.Phase3.Lazy
