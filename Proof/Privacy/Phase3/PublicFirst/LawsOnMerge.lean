/-
**Phase 3, P1q — `LawOn`, step (D5), part 1: merging the opening's and the shadow's oracles.**

The private run is the opening on a uniform oracle `O` (overlaid by the zeroed tape `T₀`), then the
shadow on a completion `O'` of the installed state (`shadow_installed_eager`, read through
`overlay T₁ O'`). Here the two oracles become one:

* **the overlay program** (`overlayProg T c`): every limb question answered by its tape limb
  without asking the oracle. Its transcript on `O` is the non-limb part of `c`'s transcript on
  `overlay T O`, and its value is `c`'s value there (`overlayProg_spec`);
* **limb entries are invisible through the overlay** (`completion_cells_map`): planting hash
  answers at unstored limb inputs does not change the law of `overlay T O'` for `O'` a completion
  (`public_program_hash`, `overlay_programHash`); hence a completion of the opening's whole
  transcript and of its non-limb part give the same law of `overlay T₁ O'`
  (`completion_overlay_transcript`);
* **resampling** (`merge_resample`, from `Hidden.resample_joint`): a completion of an adaptive
  transcript, averaged over the first oracle, is the first oracle itself — jointly with anything
  the transcript determines.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnShadow

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion openingQueriesM)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape AllQ Request queriesAlong cellOf cellInput)
open scoped ENNReal

noncomputable section

/-! ### 1. The overlay program -/

section Program

/-- A transcript entry at no limb input. -/
def nonCell (e : Entry FixedIndex EncPRF.PermutationIndex) : Bool :=
  match e.1 with
  | .hash key => (cellOf key).isNone
  | _ => true

theorem nonCell_cell (cell : Cell) (x : Block)
    (y : (PublicQuery.hash (FixedIndex := FixedIndex) (EncIndex := EncPRF.PermutationIndex)
      (cellInput cell x)).Answer) :
    nonCell ⟨.hash (cellInput cell x), y⟩ = false := by
  show (cellOf (cellInput cell x)).isNone = false
  rw [Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput]
  rfl

/-- **The overlay program**: a limb question is answered by its limb without asking. -/
def overlayProg (T : Tape) {α : Type} : FreeQuery Programs.Spec α → FreeQuery Programs.Spec α
  | .pure value => .pure value
  | .query (.fixedForward index input) next =>
      .query (.fixedForward index input) fun a => overlayProg T (next a)
  | .query (.fixedInverse index output) next =>
      .query (.fixedInverse index output) fun a => overlayProg T (next a)
  | .query (.encForward index input) next =>
      .query (.encForward index input) fun a => overlayProg T (next a)
  | .query (.encInverse index output) next =>
      .query (.encInverse index output) fun a => overlayProg T (next a)
  | .query (.hash key) next => (cellOf key).elim (.query (.hash key) fun a => overlayProg T (next a))
      fun cell => overlayProg T (next (T cell))

theorem overlayProg_hash (T : Tape) {α : Type} (key : BaseField)
    (next : (PublicQuery.hash (FixedIndex := FixedIndex) (EncIndex := EncPRF.PermutationIndex)
      key).Answer → FreeQuery Programs.Spec α) :
    overlayProg T (.query (.hash key) next) =
      (cellOf key).elim (.query (.hash key) fun a => overlayProg T (next a))
        fun cell => overlayProg T (next (T cell)) := by
  rw [overlayProg]

theorem overlayProg_cell (T : Tape) {α : Type} (cell : Cell) (x : Block)
    (next : (PublicQuery.hash (FixedIndex := FixedIndex) (EncIndex := EncPRF.PermutationIndex)
      (cellInput cell x)).Answer → FreeQuery Programs.Spec α) :
    overlayProg T (.query (.hash (cellInput cell x)) next) = overlayProg T (next (T cell)) := by
  rw [overlayProg_hash, Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput]
  rfl

theorem overlayProg_hash_other (T : Tape) {α : Type} (key : BaseField) (none : cellOf key = none)
    (next : (PublicQuery.hash (FixedIndex := FixedIndex) (EncIndex := EncPRF.PermutationIndex)
      key).Answer → FreeQuery Programs.Spec α) :
    overlayProg T (.query (.hash key) next) = .query (.hash key) fun a => overlayProg T (next a) := by
  rw [overlayProg_hash, none]
  rfl

theorem cellOnce_queryOnly {α : Type} {Y : Set Cell} {c : FreeQuery Programs.Spec α}
    (once : CellOnce Y c) : Hidden.QueryOnly NoInverse c := by
  induction once with
  | pure Y value => exact .pure value
  | cell Y cell label next inside rest ih => exact .query (.hash (cellInput cell label)) next trivial ih
  | other Y request next plain rest ih => exact .query request next plain.2 ih

/-- **The overlay program's run**: its transcript is the non-limb part of the transcript on the
overlaid oracle, and its value the value there. -/
theorem overlayProg_spec (T : Tape) {α : Type} {c : FreeQuery Programs.Spec α}
    (forward : Hidden.QueryOnly NoInverse c) (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    Hidden.transcriptOf (publicAnswer O) (overlayProg T c) =
        (transcript (publicAnswer (overlay T O)) c).filter nonCell ∧
      FreeQuery.eval (publicAnswer O) (overlayProg T c) = FreeQuery.eval (publicAnswer (overlay T O)) c := by
  induction forward with
  | pure value => exact ⟨rfl, rfl⟩
  | query request next holds rest ih =>
      cases request with
      | hash key =>
          cases found : cellOf key with
          | some cell =>
              obtain ⟨x, rfl⟩ := Kriterion.ArgoMAC.Phase3.Lazy.cellOf_spec found
              rw [overlayProg_cell]
              obtain ⟨tr, ev⟩ := ih (T cell)
              have answer : publicAnswer (overlay T O) (.hash (cellInput cell x)) = T cell :=
                overlay_cell T O cell x
              refine ⟨?_, ?_⟩
              · rw [tr, transcript_query_eq _ _ next _ answer]
                exact (List.filter_cons_of_neg (Bool.eq_false_iff.mp (nonCell_cell cell x _))).symm
              · rw [ev, eval_query_eq _ _ next _ answer]
          | none =>
              rw [overlayProg_hash_other T key found]
              have answer : publicAnswer (overlay T O) (.hash key) = publicAnswer O (.hash key) := by
                rw [overlay_hash, found]
                rfl
              obtain ⟨tr, ev⟩ := ih (publicAnswer O (.hash key))
              have keep : nonCell ⟨.hash key, publicAnswer O (.hash key)⟩ = true := by
                show (cellOf key).isNone = true
                rw [found]
                rfl
              refine ⟨?_, ?_⟩
              · show ⟨_, _⟩ :: Hidden.transcriptOf (publicAnswer O)
                    (overlayProg T (next (publicAnswer O (.hash key)))) = _
                rw [tr, transcript_query_eq _ _ next _ answer]
                exact (List.filter_cons_of_pos keep).symm
              · show FreeQuery.eval (publicAnswer O)
                    (overlayProg T (next (publicAnswer O (.hash key)))) = _
                rw [ev, eval_query_eq _ _ next _ answer]
      | fixedForward index input =>
          obtain ⟨tr, ev⟩ := ih (publicAnswer O (.fixedForward index input))
          exact ⟨by
            show ⟨_, _⟩ :: Hidden.transcriptOf (publicAnswer O)
                (overlayProg T (next (publicAnswer O (.fixedForward index input)))) = _
            rw [tr]
            rfl, ev⟩
      | fixedInverse index output => exact holds.elim
      | encForward index input =>
          obtain ⟨tr, ev⟩ := ih (publicAnswer O (.encForward index input))
          exact ⟨by
            show ⟨_, _⟩ :: Hidden.transcriptOf (publicAnswer O)
                (overlayProg T (next (publicAnswer O (.encForward index input)))) = _
            rw [tr]
            rfl, ev⟩
      | encInverse index output => exact holds.elim

end Program

/-! ### 2. Limb entries are invisible through the overlay -/

section Cells

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- A plant at another request leaves a hash lookup as it was. -/
theorem plantEntry_hash_notAt (key : BaseField) (s : LState)
    (e : Entry FixedIndex EncPRF.PermutationIndex) (other : e.1 ≠ .hash key) :
    (plantEntry s e).hash.lookup key = s.hash.lookup key := by
  obtain ⟨request, value⟩ := e
  unfold plantEntry
  cases found : LazyOracle.program request value s with
  | none => rfl
  | some updated =>
      show updated.hash.lookup key = s.hash.lookup key
      cases request with
      | hash asked =>
          refine (Kriterion.ArgoMAC.Phase3.Lazy.program_lookup_frame asked value s updated found).2.2
            key fun same => other (by rw [same])
      | fixedForward index input =>
          simp only [LazyOracle.program, Option.map_eq_some_iff] at found
          obtain ⟨_, _, rfl⟩ := found
          rfl
      | fixedInverse index output =>
          simp only [LazyOracle.program, Option.map_eq_some_iff] at found
          obtain ⟨_, _, rfl⟩ := found
          rfl
      | encForward index input =>
          simp only [LazyOracle.program, Option.map_eq_some_iff] at found
          obtain ⟨_, _, rfl⟩ := found
          rfl
      | encInverse index output =>
          simp only [LazyOracle.program, Option.map_eq_some_iff] at found
          obtain ⟨_, _, rfl⟩ := found
          rfl

/-- Planting entries at no request `hash key` leaves its lookup alone. -/
theorem plantAll_hash_notAt (key : BaseField) :
    ∀ (L : List (Entry FixedIndex EncPRF.PermutationIndex)) (s : LState),
      (∀ e ∈ L, e.1 ≠ .hash key) → (plantAll L s).hash.lookup key = s.hash.lookup key
  | [], _, _ => rfl
  | e :: L, s, absent => by
      rw [plantAll_cons, plantAll_hash_notAt key L _ fun f member =>
        absent f (List.mem_cons_of_mem _ member)]
      exact plantEntry_hash_notAt key s e (absent e List.mem_cons_self)

/-- **Limb entries at unstored inputs do not change the law of the overlaid completion.** -/
theorem completion_cells_map (T : Tape) :
    ∀ (L : List (Entry FixedIndex EncPRF.PermutationIndex)) (s : LState),
      (∀ e ∈ L, nonCell e = false) →
      L.Pairwise (fun e f => ∀ key, e.1 = .hash key → f.1 ≠ .hash key) →
      (∀ e ∈ L, ∀ key, e.1 = .hash key → s.hash.lookup key = none) →
      (publicCompletion (plantAll L s)).map (overlay T) = (publicCompletion s).map (overlay T)
  | [], _, _, _, _ => rfl
  | e :: L, s, cells, pairwise, fresh => by
      obtain ⟨request, y⟩ := e
      have isCell := cells _ List.mem_cons_self
      cases request with
      | hash key =>
          change Block × Block at y
          have freshHere := fresh _ List.mem_cons_self key rfl
          cases found : cellOf key with
          | none =>
              have keep : nonCell ⟨.hash key, y⟩ = true := by
                show (cellOf key).isNone = true
                rw [found]
                rfl
              rw [keep] at isCell
              cases isCell
          | some cell =>
              obtain ⟨x, rfl⟩ := Kriterion.ArgoMAC.Phase3.Lazy.cellOf_spec found
              have programmed := program_hash_fresh s (cellInput cell x) y freshHere
              rw [plantAll_cons]
              obtain ⟨headPair, tailPair⟩ := List.pairwise_cons.mp pairwise
              rw [completion_cells_map T L _ (fun f member => cells f (List.mem_cons_of_mem _ member))
                tailPair (fun f member key' same => ?_)]
              · rw [← public_program_hash s _ (cellInput cell x) y programmed, PMF.map_comp]
                exact congrArg (fun g => PMF.map g (publicCompletion s))
                  (funext fun O => overlay_programHash T O cell x y)
              · rw [← fresh f (List.mem_cons_of_mem _ member) key' same]
                refine (Kriterion.ArgoMAC.Phase3.Lazy.program_lookup_frame _ _ s _ programmed).2.2
                  key' fun keyEq => headPair f member (cellInput cell x) rfl ?_
                rw [same, keyEq]
      | fixedForward _ _ => cases isCell
      | fixedInverse _ _ => cases isCell
      | encForward _ _ => cases isCell
      | encInverse _ _ => cases isCell

/-- Two limb questions of a limb-once computation are at different inputs. -/
theorem cellOnce_pairwise {α : Type} {Y : Set Cell} {c : FreeQuery Programs.Spec α}
    (once : CellOnce Y c) : ∀ ans : (r : Request) → r.Answer,
      (queriesAlong ans c).Pairwise (fun q r => ∀ key, cellOf key ≠ none →
        q = .hash key → r ≠ .hash key) := by
  induction once with
  | pure Y value => intro _; exact List.Pairwise.nil
  | cell Y cell label next inside rest ih =>
      intro ans
      refine List.Pairwise.cons (fun r member key _ same other => ?_) (ih _ ans)
      injection same with keyEq
      subst keyEq
      subst other
      exact (cellOnce_inside (rest _) ans cell label member).2 rfl
  | other Y request next plain rest ih =>
      intro ans
      exact List.Pairwise.cons (fun r _ key isCell same _ => isCell (plain.1 key same)) (ih _ ans)

/-- **A completion of a limb-once transcript and of its non-limb part give the same overlaid
law.** -/
theorem completion_overlay_transcript (T₁ : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    {α : Type} {Y : Set Cell} (P : FreeQuery Programs.Spec α) (once : CellOnce Y P)
    (f : PublicOracle FixedIndex EncPRF.PermutationIndex → ℝ≥0∞) :
    ∑' O', publicCompletion (plantAll (transcript (publicAnswer (overlay T₁ O)) P) LazyOracle.empty) O' *
        f (overlay T₁ O') =
      ∑' O', publicCompletion (plantAll ((transcript (publicAnswer (overlay T₁ O)) P).filter nonCell)
        LazyOracle.empty) O' * f (overlay T₁ O') := by
  set L := transcript (publicAnswer (overlay T₁ O)) P with hL
  have consistent : Hidden.Consistent (overlay T₁ O) L :=
    fun e member => ((mem_transcript_iff _ _ e).mp member).2.symm
  have split : SameLookups (plantAll L LazyOracle.empty)
      (plantAll (L.filter nonCell ++ L.filter (fun e => !nonCell e)) LazyOracle.empty) := by
    refine sameLookups_of_mem_iff (overlay T₁ O) _ _ consistent (fun e member => ?_) fun e => ?_
    · rcases List.mem_append.mp member with h | h
      · exact consistent e (List.mem_filter.mp h).1
      · exact consistent e (List.mem_filter.mp h).1
    · constructor
      · intro member
        by_cases keep : nonCell e = true
        · exact List.mem_append_left _ (List.mem_filter.mpr ⟨member, keep⟩)
        · exact List.mem_append_right _ (List.mem_filter.mpr ⟨member, by simpa using keep⟩)
      · intro member
        rcases List.mem_append.mp member with h | h
        · exact (List.mem_filter.mp h).1
        · exact (List.mem_filter.mp h).1
  suffices key : (publicCompletion (plantAll L LazyOracle.empty)).map (overlay T₁) =
      (publicCompletion (plantAll (L.filter nonCell) LazyOracle.empty)).map (overlay T₁) by
    rw [← tsum_map_mul (publicCompletion (plantAll L LazyOracle.empty)) (overlay T₁) f,
      ← tsum_map_mul (publicCompletion (plantAll (L.filter nonCell) LazyOracle.empty)) (overlay T₁) f,
      key]
  rw [publicCompletion_congr split, ← plantAll_append_empty]
  have cellKey : ∀ e : Entry FixedIndex EncPRF.PermutationIndex, nonCell e = false → ∀ key,
      e.1 = .hash key → cellOf key ≠ none := by
    rintro ⟨request, value⟩ drop key rfl
    intro none
    have keep : nonCell ⟨.hash key, value⟩ = true := by
      show (cellOf key).isNone = true
      rw [none]
      rfl
    rw [keep] at drop
    cases drop
  refine completion_cells_map T₁ (L.filter (fun e => !nonCell e)) (plantAll (L.filter nonCell)
    LazyOracle.empty) (fun e member => by simpa using (List.mem_filter.mp member).2)
    ?_ fun e member key same => ?_
  · -- the limb questions are at pairwise different inputs
    have pairQ := cellOnce_pairwise once (publicAnswer (overlay T₁ O))
    rw [← map_fst_transcript, ← hL, List.pairwise_map] at pairQ
    refine (pairQ.filter _).imp_of_mem fun {e f} eMember _ rel key eSame => ?_
    exact rel key (cellKey e (by simpa using (List.mem_filter.mp eMember).2) key eSame) eSame
  · -- the non-limb part leaves the limb inputs unstored
    have isCell := cellKey e (by simpa using (List.mem_filter.mp member).2) key same
    rw [plantAll_hash_notAt key _ _ fun g gMember gSame => ?_]
    · rfl
    have keep := (List.mem_filter.mp gMember).2
    obtain ⟨request, value⟩ := g
    simp only at gSame
    subst gSame
    have drop : nonCell ⟨.hash key, value⟩ = false := by
      show (cellOf key).isNone = false
      cases found : cellOf key with
      | none => exact absurd found isCell
      | some _ => rfl
    rw [drop] at keep
    cases keep

end Cells

/-! ### 3. Resampling -/

section Resample

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **A completion of an adaptive transcript, averaged over the first oracle, is the first oracle**,
jointly with the computation's value. -/
theorem merge_resample {α : Type} (C : FreeQuery Programs.Spec α)
    (K : α → PublicOracle FixedIndex EncPRF.PermutationIndex → ℝ≥0∞) :
    ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
        ∑' O', publicCompletion (plantAll (Hidden.transcriptOf (publicAnswer O) C) LazyOracle.empty) O' *
          K (FreeQuery.eval (publicAnswer O) C) O' =
      ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
        K (FreeQuery.eval (publicAnswer O) C) O := by
  have onSupport : ∀ O O', O' ∈ (publicCompletion (plantAll (Hidden.transcriptOf (publicAnswer O) C)
      LazyOracle.empty)).support →
      FreeQuery.eval (publicAnswer O) C = FreeQuery.eval (publicAnswer O') C := fun O O' member =>
    ((Hidden.transcriptOf_of_agrees C O O' (Hidden.completion_agrees C O O' member)).2).symm
  have lhs : ∀ O, ∑' O', publicCompletion (plantAll (Hidden.transcriptOf (publicAnswer O) C)
        LazyOracle.empty) O' * K (FreeQuery.eval (publicAnswer O) C) O' =
      ∑' O', publicCompletion (plantAll (Hidden.transcriptOf (publicAnswer O) C) LazyOracle.empty) O' *
        K (FreeQuery.eval (publicAnswer O') C) O' := by
    intro O
    refine tsum_congr fun O' => ?_
    by_cases member : O' ∈ (publicCompletion (plantAll (Hidden.transcriptOf (publicAnswer O) C)
        LazyOracle.empty)).support
    · rw [onSupport O O' member]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]
  simp_rw [lhs]
  have joint := Hidden.resample_joint C (LazyOracle.empty : LState)
  have averaged := congrArg (fun μ : PMF (List (Entry FixedIndex EncPRF.PermutationIndex) ×
      PublicOracle FixedIndex EncPRF.PermutationIndex) =>
    ∑' p, μ p * K (FreeQuery.eval (publicAnswer p.2) C) p.2) joint
  rw [tsum_bind_mul, tsum_map_mul] at averaged
  simp_rw [tsum_map_mul] at averaged
  rw [Kriterion.ArgoMAC.Phase3.Glue.public_initial] at averaged
  exact averaged

end Resample

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
