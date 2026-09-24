/-
**Phase 3, P4 — evaluator unfolding (a): every designated limb is recorded.**

Event (a) of the abort analysis: a designated request with a missing input. In `I^U` it aborts; in
`H` it is skipped. It never happens: the honest evaluation `openingQueriesM` asks, **on every
path**, the hash query of each of the `452` limbs of switch `j* = α₀ xor 1` of chunk `0` of lane
`pointX` (at that switch's one-hot label), because `j*` is inactive, so `evalMasksM` evaluates its
`switchMaskM`. The refill runner intercepts each such query and records its label at its limb
(`runRefill_records`).

* `QueriesAt P c` — every path of `c` makes a query satisfying `P`. It is closed under `bind` on
  either side (`bind_left`, `bind_right`), under `FreeQuery.vector` at any iteration (`vector`) and
  under weakening (`mono`).
* `openingQueriesM_queriesAt` — the evaluation asks, for every limb, a designated input of that
  limb.
* `runRefill_records` — a program that asks a designated input of a limb leaves that limb recorded,
  whatever the tape law.
-/

import Proof.Privacy.Phase3.Lazy.AbortReduction

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-- Every path of the program makes a query satisfying `P`. -/
inductive QueriesAt (P : Request → Prop) {α : Type} : FreeQuery Programs.Spec α → Prop
  | here (request : Request) (next : request.Answer → FreeQuery Programs.Spec α) :
      P request → QueriesAt P (.query request next)
  | later (request : Request) (next : request.Answer → FreeQuery Programs.Spec α) :
      (∀ answer, QueriesAt P (next answer)) → QueriesAt P (.query request next)

namespace QueriesAt

variable {P Q : Request → Prop} {α β : Type}

/-- A path through `c` then `f` contains a path through `c`. -/
theorem bind_left {c : FreeQuery Programs.Spec α} (queries : QueriesAt P c)
    (f : α → FreeQuery Programs.Spec β) : QueriesAt P (c >>= f) := by
  induction queries with
  | here request next holds => exact .here request _ holds
  | later request next _ ih => exact .later request _ ih

/-- If every continuation queries, so does the sequence. -/
theorem bind_right (c : FreeQuery Programs.Spec α) {f : α → FreeQuery Programs.Spec β}
    (queries : ∀ value, QueriesAt P (f value)) : QueriesAt P (c >>= f) := by
  induction c with
  | pure value => exact queries value
  | query request next ih => exact .later request _ ih

/-- A loop queries if one iteration does. -/
theorem vector {count : Nat} (program : Fin count → FreeQuery Programs.Spec α) (iteration : Fin count)
    (queries : QueriesAt P (program iteration)) :
    QueriesAt P (FreeQuery.vector count program) := by
  induction count with
  | zero => exact iteration.elim0
  | succ count ih =>
      show QueriesAt P (FreeQuery.vector count (fun i => program i.castSucc) >>= fun values =>
        program (Fin.last count) >>= fun value => Pure.pure (values.push value))
      by_cases last : iteration = Fin.last count
      · subst last
        exact bind_right _ fun _ => bind_left queries _
      · obtain ⟨earlier, rfl⟩ := Fin.exists_castSucc_eq.mpr last
        exact bind_left (ih (fun i => program i.castSucc) earlier queries) _

/-- A weaker predicate is asked too. -/
theorem mono {c : FreeQuery Programs.Spec α} (queries : QueriesAt P c)
    (weaker : ∀ request, P request → Q request) : QueriesAt Q c := by
  induction queries with
  | here request next holds => exact .here request _ (weaker _ holds)
  | later request next _ ih => exact .later request _ ih

end QueriesAt

/-! ### The evaluation asks every designated limb -/

/-- `switchMaskM` asks every limb of its switch at its label. -/
theorem switchMaskM_queriesAt (lane : Lane) (chunk : Fin chunkCount) (switch : Nat)
    (label : Block) (limb : Fin (limbCount lane)) :
    QueriesAt (· = .hash (scaleInput lane chunk switch limb.val label))
      (Programs.switchMaskM lane chunk switch label) := by
  unfold Programs.switchMaskM
  have ask : QueriesAt (· = .hash (scaleInput lane chunk switch limb.val label))
      (Programs.askHash (scaleInput lane chunk switch limb.val label)) :=
    .here (.hash (scaleInput lane chunk switch limb.val label)) FreeQuery.pure rfl
  exact QueriesAt.bind_left (QueriesAt.vector _ limb ask) _

/-- `evalMasksM` asks every limb of every inactive switch at that switch's label. -/
theorem evalMasksM_queriesAt (lane : Lane) (chunk : Fin chunkCount) (width : Nat)
    (hot : HotLabels width) (alpha switch : Fin (2 ^ width)) (inactive : switch ≠ alpha)
    (limb : Fin (limbCount lane)) :
    QueriesAt (· = .hash (scaleInput lane chunk switch.val limb.val (hot switch)))
      (Programs.evalMasksM lane chunk width hot alpha) := by
  unfold Programs.evalMasksM
  refine QueriesAt.bind_left (QueriesAt.vector _ switch ?_) _
  simp only [if_neg inactive]
  exact switchMaskM_queriesAt lane chunk switch.val (hot switch) limb

/-- The designated switch is inactive. -/
theorem designatedSwitch_ne (bits : BitInput) : designatedSwitch bits ≠ activeSwitch bits := by
  intro same
  have values := congrArg Fin.val same
  simp only [designatedSwitch] at values
  have bit := congrArg (Nat.testBit · 0) values
  simp at bit
  omega

/-- **The honest evaluation asks a designated input of every limb, on every path.** -/
theorem openingQueriesM_queriesAt [FieldCertificate] (table : Public) (bits : BitInput)
    (mac : InputMac) (limb : Fin (limbCount .pointX)) :
    QueriesAt (fun request => ∃ label, request = .hash (designatedInput bits limb label))
      (openingQueriesM table bits mac) := by
  unfold openingQueriesM
  refine QueriesAt.bind_right _ fun _ => QueriesAt.bind_right _ fun _ =>
    QueriesAt.bind_right _ fun _ => QueriesAt.bind_right _ fun _ => QueriesAt.bind_left ?_ _
  unfold Programs.evalLaneM
  refine QueriesAt.bind_left (QueriesAt.vector _ chunkZero ?_) _
  unfold Programs.evalChunkM
  refine QueriesAt.bind_right _ fun hot => QueriesAt.bind_left ?_ _
  exact (evalMasksM_queriesAt .pointX chunkZero (chunkWidth chunkZero) hot
    (chunkOf (Pipeline.coordBits bits .x) chunkZero) (designatedSwitch bits)
    (designatedSwitch_ne bits) limb).mono fun _ same => ⟨_, same⟩

/-! ### The refill runner records every designated query -/

section Record

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A designated hash query is intercepted. -/
theorem interceptAnswer_designated (bits : BitInput) {input : BaseField}
    (designated : IsDesignated bits input) : interceptAnswer bits (.hash input) = some (0, 0) :=
  if_pos designated

/-- A non-designated hash query is not intercepted. -/
theorem interceptAnswer_plain (bits : BitInput) {input : BaseField}
    (notDesignated : ¬ IsDesignated bits input) : interceptAnswer bits (.hash input) = none :=
  if_neg notDesignated

/-- A recorded limb stays recorded. -/
theorem recordAfter_keeps (bits : BitInput) (request : Request) (record : Record)
    (limb : Fin (limbCount .pointX)) (kept : record limb ≠ none) :
    recordAfter bits request record limb ≠ none := by
  cases request with
  | fixedForward _ _ => exact kept
  | fixedInverse _ _ => exact kept
  | encForward _ _ => exact kept
  | encInverse _ _ => exact kept
  | hash input =>
      simp only [recordAfter]
      split
      · exact Option.some_ne_none _
      · exact kept

/-- Every path of the runner keeps a recorded limb recorded. -/
theorem runRefill_keeps (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (computation : FreeQuery Programs.Spec α) (limb : Fin (limbCount .pointX)) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell), record limb ≠ none →
      ∀ result ∈ (runRefill bits draw computation oracle record touched).support,
        ∀ value, result = some value → value.2.2 limb ≠ none := by
  induction computation with
  | pure value =>
      intro oracle record touched kept result member value same
      simp only [runRefill, PMF.support_pure, Set.mem_singleton_iff] at member
      subst member
      cases same
      exact kept
  | query request next ih =>
      intro oracle record touched kept result member value same
      simp only [runRefill] at member
      split at member
      · exact ih _ _ _ _ (recordAfter_keeps bits request record limb kept) result member value same
      · split at member
        · obtain ⟨answer, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          split at member
          · simp only [PMF.support_pure, Set.mem_singleton_iff] at member
            subst member
            cases same
          · exact ih _ _ _ _ kept result member value same
        · obtain ⟨answer, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          exact ih _ _ _ _ kept result member value same

/-- An intercepted query is answered by the interception and recorded. -/
theorem runRefill_intercept (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (request : Request) (next : request.Answer → FreeQuery Programs.Spec α) (oracle : LState)
    (record : Record) (touched : Set Cell) (answer : request.Answer)
    (intercept : interceptAnswer bits request = some answer) :
    runRefill bits draw (.query request next) oracle record touched =
      runRefill bits draw (next answer) oracle (recordAfter bits request record) touched := by
  simp only [runRefill]
  split
  · rename_i answer' hit
    rw [intercept] at hit
    cases hit
    rfl
  · rename_i hit
    rw [intercept] at hit
    cases hit

/-- **A program that asks a designated input of a limb leaves that limb recorded**, on every
path. -/
theorem runRefill_records (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (limb : Fin (limbCount .pointX)) {computation : FreeQuery Programs.Spec α}
    (queries : QueriesAt (fun request => ∃ label, request = .hash (designatedInput bits limb label))
      computation) :
    ∀ (oracle : LState) (record : Record) (touched : Set Cell),
      ∀ result ∈ (runRefill bits draw computation oracle record touched).support,
        ∀ value, result = some value → value.2.2 limb ≠ none := by
  induction queries with
  | here request next holds =>
      intro oracle record touched result member value same
      obtain ⟨label, rfl⟩ := holds
      rw [runRefill_intercept bits draw _ next oracle record touched (0, 0)
        (interceptAnswer_designated bits (isDesignated_designatedInput bits limb label))] at member
      refine runRefill_keeps bits draw _ limb oracle _ touched ?_ result member value same
      rw [recordAfter_designatedInput, Function.update_self]
      exact Option.some_ne_none _
  | later request next _ ih =>
      intro oracle record touched result member value same
      simp only [runRefill] at member
      split at member
      · exact ih _ _ _ _ result member value same
      · split at member
        · obtain ⟨answer, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          split at member
          · simp only [PMF.support_pure, Set.mem_singleton_iff] at member
            subst member
            cases same
          · exact ih _ _ _ _ result member value same
        · obtain ⟨answer, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          exact ih _ _ _ _ result member value same

end Record

end

end Kriterion.ArgoMAC.Phase3.Lazy
