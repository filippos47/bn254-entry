/-
**Phase 3, P1q — `LawOn`, step (D4): the shadow on the installed state.**

After the designated installation the private state has the lookups of the opening's transcript on
`overlay T₁ O` (`install_state`). The designed shadow then runs lazily on it. Here, along any
answer function:

* **the opening's questions are among the shadow's** (`opening_sub_shadow`): the prefix again, the
  bit-`false` pads among the evaluator's pads, system B at the same labels (both paddings whiten
  with the bit-`false` pads, `whiten_same`);
* **the shadow's limb questions are the opening's** (`shadow_cell_opening`): the other questions
  are EncPRF questions (the pads), the bridge hash, fold gates or gadget questions;
* hence (`shadow_view`), for every oracle `O'` agreeing with the opening's transcript on
  `overlay T₁ O`, the shadow's transcript on `O'` is its transcript on `overlay T₁ O'`, and planted
  over the installed state it has the lookups of `onView (overlay T₁ O')`;
* **`shadow_installed_eager`**: the lazy shadow run on the installed state, read through its final
  state's lookups, is `onView (overlay T₁ O')` for `O'` a completion of the installed state.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnInstall

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion openingQueriesM whitePadsM)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape AllQ Request queriesAlong queriesAlong_bind
  queriesAlong_pure EncAt LaneAt cellOf cellInput)
open scoped ENNReal

noncomputable section

/-! ### 1. Questions along an answer function -/

section Questions

variable {α : Type}

theorem queries_of_allQ {P : Request → Prop} (ans : (r : Request) → r.Answer)
    {c : FreeQuery Programs.Spec α} (holds : AllQ P c) : ∀ r ∈ queriesAlong ans c, P r := by
  induction holds with
  | pure value => exact fun _ member => by nomatch member
  | query request next here _ ih =>
      intro r member
      rcases List.mem_cons.mp member with rfl | later
      · exact here
      · exact ih _ r later

theorem queries_of_queryOnly {S : Request → Prop} (ans : (r : Request) → r.Answer)
    {c : FreeQuery Programs.Spec α} (holds : Hidden.QueryOnly S c) : ∀ r ∈ queriesAlong ans c, S r := by
  induction holds with
  | pure value => exact fun _ member => by nomatch member
  | query request next here _ ih =>
      intro r member
      rcases List.mem_cons.mp member with rfl | later
      · exact here
      · exact ih _ r later

theorem queries_of_asks (ans : (r : Request) → r.Answer) {c : FreeQuery Programs.Spec α} {q : Request}
    (asks : Asks ans c q) : q ∈ queriesAlong ans c := by
  unfold Asks at asks
  rw [← transcript_eq_transcriptOf, map_fst_transcript] at asks
  exact asks

end Questions

section Pads

theorem whitePads_first (keys : WhiteningKeys) (ans : (r : Request) → r.Answer)
    (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) :
    (FreeQuery.eval ans (whitePadsM keys) coordinate index).1 =
      FreeQuery.eval ans (Programs.padM keys coordinate index false) := by
  cases coordinate <;>
    simp only [whitePadsM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
      Vector.get_ofFn]

theorem evalPads_first (keys : WhiteningKeys) (bits : BitInput) (ans : (r : Request) → r.Answer)
    (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) :
    (FreeQuery.eval ans (Programs.evalPadsM keys bits) coordinate index).1 =
      FreeQuery.eval ans (Programs.padM keys coordinate index false) := by
  cases coordinate <;>
  · simp only [Programs.evalPadsM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
      Vector.get_ofFn]
    split <;> simp only [FreeQuery.eval_bind, FreeQuery.eval_pure]

/-- **Both paddings whiten alike.** -/
theorem whiten_same (keys : WhiteningKeys) (bits : BitInput) (ans : (r : Request) → r.Answer)
    (mac : InputMac) :
    Programs.whitenMacOf (FreeQuery.eval ans (Programs.evalPadsM keys bits)) mac =
      Programs.whitenMacOf (FreeQuery.eval ans (whitePadsM keys)) mac := by
  unfold Programs.whitenMacOf
  simp only [evalPads_first, whitePads_first]

theorem truePadsM_encAt' [FieldCertificate] (keys : WhiteningKeys) : AllQ EncAt (truePadsM keys) :=
  (AllQ.vector fun _ => Kriterion.ArgoMAC.Phase3.Lazy.padM_allQ _ _ _ _).bind fun _ =>
    (AllQ.vector fun _ => Kriterion.ArgoMAC.Phase3.Lazy.padM_allQ _ _ _ _).bind fun _ => .pure _

theorem evalPadsM_encAt' (bits : BitInput) (keys : WhiteningKeys) :
    AllQ EncAt (Programs.evalPadsM keys bits) := by
  unfold Programs.evalPadsM
  dsimp only
  exact (AllQ.vector fun _ => (Kriterion.ArgoMAC.Phase3.Lazy.padM_allQ keys _ _ _).bind fun _ =>
      AllQ.ite ((Kriterion.ArgoMAC.Phase3.Lazy.padM_allQ keys _ _ _).bind fun _ => .pure _)
        (.pure _)).bind fun _ =>
    (AllQ.vector fun _ => (Kriterion.ArgoMAC.Phase3.Lazy.padM_allQ keys _ _ _).bind fun _ =>
      AllQ.ite ((Kriterion.ArgoMAC.Phase3.Lazy.padM_allQ keys _ _ _).bind fun _ => .pure _)
        (.pure _)).bind fun _ => .pure _

/-- The whitening pads ask the bit-`false` pads at the first key. -/
theorem whitePadsM_form (keys : WhiteningKeys) :
    Hidden.QueryOnly (fun q => ∃ (c : EncPRF.Coordinate) (i : Fin coordinateBitCount),
      q = .encForward (c, i) (encodeBit false ^^^ keys.first)) (whitePadsM keys) := by
  have pad : ∀ c i, Hidden.QueryOnly (fun q => ∃ (c : EncPRF.Coordinate) (i : Fin coordinateBitCount),
      q = .encForward (c, i) (encodeBit false ^^^ keys.first)) (Programs.padM keys c i false) :=
    fun c i => Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ ⟨c, i, rfl⟩) fun _ => Hidden.QueryOnly.pure' _
  unfold whitePadsM
  exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _) fun _ =>
    Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _) fun _ => Hidden.QueryOnly.pure' _

/-- **The whitening pads are among the evaluator's pads.** -/
theorem white_sub_eval [FieldCertificate] [GroupCertificate] (keys : WhiteningKeys) (bits : BitInput) (ans : (r : Request) → r.Answer)
    (r : Request) (member : r ∈ queriesAlong ans (whitePadsM keys)) :
    r ∈ queriesAlong ans (Programs.evalPadsM keys bits) := by
  obtain ⟨c, i, rfl⟩ := queries_of_queryOnly ans (whitePadsM_form keys) r member
  exact queries_of_asks ans (asks_evalPadsM_false ans keys bits c i)

end Pads

/-! ### 2. The opening's and the shadow's questions -/

section Shadow

variable [FieldCertificate] [GroupCertificate] (table : Public) (bits : BitInput) (mac : InputMac)
  (ans : (r : Request) → r.Answer)

/-- The keys the prefix reads along `ans`. -/
abbrev keysAlong : Block × Block := FreeQuery.eval ans (curvePrefixM table bits mac)

/-- System B's `x` lane at some labels. -/
abbrev laneBX (labels : InputMac) : Programs.M (Fin pointElementCountX → BaseField) :=
  Programs.evalLaneM .pointX table.pointXHot
    (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .x) (Pipeline.macLabels labels .x)

/-- System B's `y` lane at some labels. -/
abbrev laneBY (labels : InputMac) : Programs.M (Fin pointElementCountY → BaseField) :=
  Programs.evalLaneM .pointY table.pointYHot
    (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .y) (Pipeline.macLabels labels .y)

theorem opening_questions (r : Request)
    (member : r ∈ queriesAlong ans (openingQueriesM table bits mac)) :
    r ∈ queriesAlong ans (curvePrefixM table bits mac) ∨
      r ∈ queriesAlong ans (whitePadsM ⟨(keysAlong table bits mac ans).1, (keysAlong table bits mac ans).2⟩) ∨
      r ∈ queriesAlong ans (laneBX table bits (Programs.whitenMacOf (FreeQuery.eval ans
        (whitePadsM ⟨(keysAlong table bits mac ans).1, (keysAlong table bits mac ans).2⟩)) mac)) ∨
      r ∈ queriesAlong ans (laneBY table bits (Programs.whitenMacOf (FreeQuery.eval ans
        (whitePadsM ⟨(keysAlong table bits mac ans).1, (keysAlong table bits mac ans).2⟩)) mac)) := by
  rw [openingQueriesM_eq_prefix] at member
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, List.mem_append] at member
  exact member

theorem shadow_questions (r : Request) (member : r ∈ queriesAlong ans (shadowOnM table bits mac)) :
    r ∈ queriesAlong ans (curvePrefixM table bits mac) ∨
      r ∈ queriesAlong ans (truePadsM ⟨(keysAlong table bits mac ans).1, (keysAlong table bits mac ans).2⟩) ∨
      r ∈ queriesAlong ans (Programs.evalPadsM ⟨(keysAlong table bits mac ans).1,
        (keysAlong table bits mac ans).2⟩ bits) ∨
      r ∈ queriesAlong ans (laneBX table bits (Programs.whitenMacOf (FreeQuery.eval ans
        (Programs.evalPadsM ⟨(keysAlong table bits mac ans).1, (keysAlong table bits mac ans).2⟩ bits)) mac)) ∨
      r ∈ queriesAlong ans (laneBY table bits (Programs.whitenMacOf (FreeQuery.eval ans
        (Programs.evalPadsM ⟨(keysAlong table bits mac ans).1, (keysAlong table bits mac ans).2⟩ bits)) mac)) ∨
      r ∈ queriesAlong ans (gadgetPart table bits mac (FreeQuery.eval ans (preM table bits mac))) := by
  unfold shadowOnM at member
  rw [onCurveM_split] at member
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, List.mem_append] at member
  rcases member with prefixQ | trueQ | preQ | gadgetQ
  · exact Or.inl prefixQ
  · exact Or.inr (Or.inl trueQ)
  · unfold preM at preQ
    simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, List.mem_append] at preQ
    rcases preQ with prefixQ | padsQ | xQ | yQ
    · exact Or.inl prefixQ
    · exact Or.inr (Or.inr (Or.inl padsQ))
    · exact Or.inr (Or.inr (Or.inr (Or.inl xQ)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl yQ))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr gadgetQ))))

theorem prefix_in_shadow (r : Request) (member : r ∈ queriesAlong ans (curvePrefixM table bits mac)) :
    r ∈ queriesAlong ans (shadowOnM table bits mac) := by
  unfold shadowOnM
  rw [queriesAlong_bind]
  exact List.mem_append_left _ member

theorem preM_in_shadow (r : Request) (member : r ∈ queriesAlong ans (preM table bits mac)) :
    r ∈ queriesAlong ans (shadowOnM table bits mac) := by
  unfold shadowOnM
  rw [onCurveM_split]
  simp only [queriesAlong_bind, List.mem_append]
  exact Or.inr (Or.inr (Or.inl (Or.inl member)))

/-- **The opening's questions are among the shadow's.** -/
theorem opening_sub_shadow (r : Request) (member : r ∈ queriesAlong ans (openingQueriesM table bits mac)) :
    r ∈ queriesAlong ans (shadowOnM table bits mac) := by
  rcases opening_questions table bits mac ans r member with prefixQ | padsQ | xQ | yQ
  · exact prefix_in_shadow table bits mac ans r prefixQ
  · refine preM_in_shadow table bits mac ans r ?_
    unfold preM
    simp only [queriesAlong_bind, List.mem_append]
    exact Or.inr (Or.inl (white_sub_eval _ bits ans r padsQ))
  · refine preM_in_shadow table bits mac ans r ?_
    unfold preM
    simp only [queriesAlong_bind, List.mem_append]
    refine Or.inr (Or.inr (Or.inl ?_))
    rw [whiten_same]
    exact xQ
  · refine preM_in_shadow table bits mac ans r ?_
    unfold preM
    simp only [queriesAlong_bind, List.mem_append]
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [whiten_same]
    exact yQ

theorem opening_of_prefix (r : Request) (member : r ∈ queriesAlong ans (curvePrefixM table bits mac)) :
    r ∈ queriesAlong ans (openingQueriesM table bits mac) := by
  rw [openingQueriesM_eq_prefix, queriesAlong_bind]
  exact List.mem_append_left _ member

/-- **The shadow's limb questions are the opening's.** -/
theorem shadow_cell_opening (cell : Cell) (x : Block)
    (member : (PublicQuery.hash (cellInput cell x) : Request) ∈
      queriesAlong ans (shadowOnM table bits mac)) :
    (PublicQuery.hash (cellInput cell x) : Request) ∈
      queriesAlong ans (openingQueriesM table bits mac) := by
  rcases shadow_questions table bits mac ans _ member with prefixQ | trueQ | padsQ | xQ | yQ | gadgetQ
  · exact opening_of_prefix table bits mac ans _ prefixQ
  · exact absurd (queries_of_allQ ans (truePadsM_encAt' _) _ trueQ) (fun h => h)
  · exact absurd (queries_of_allQ ans (evalPadsM_encAt' bits _) _ padsQ) (fun h => h)
  · rw [openingQueriesM_eq_prefix]
    simp only [queriesAlong_bind, List.mem_append]
    rw [whiten_same] at xQ
    exact Or.inr (Or.inr (Or.inl xQ))
  · rw [openingQueriesM_eq_prefix]
    simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, List.mem_append]
    rw [whiten_same] at yQ
    exact Or.inr (Or.inr (Or.inr yQ))
  · exfalso
    unfold gadgetPart at gadgetQ
    rw [queriesAlong_bind, queriesAlong_pure, List.append_nil] at gadgetQ
    obtain ⟨o, κ, p, same⟩ := queries_of_queryOnly ans (Guess.unlockM_asks _ _ _) _ gadgetQ
    cases same

end Shadow

/-! ### 3. The shadow on the installed state -/

section View

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex] (table : Public) (bits : BitInput) (mac : InputMac)

theorem noInverse_of_laneAt {lane : Lane} {r : Request} (inside : ∃ c, LaneAt lane c r) : NoInverse r := by
  obtain ⟨c, fixed | hash⟩ := inside <;> cases r <;> trivial

theorem noInverse_of_encAt {r : Request} (inside : EncAt r) : NoInverse r := by
  cases r <;> trivial

theorem prefix_forward : AllQ NoInverse (curvePrefixM table bits mac) := by
  unfold curvePrefixM
  exact ((evalLaneM_laneAt _ _ _ _ _).mono fun _ h => noInverse_of_laneAt h).bind
    fun _ => ((evalLaneM_laneAt _ _ _ _ _).mono fun _ h => noInverse_of_laneAt h).bind fun _ =>
      .query _ _ trivial fun _ => .pure _

/-- The shadow asks no inverse question. -/
theorem shadow_forward (ans : (r : Request) → r.Answer) (r : Request)
    (member : r ∈ queriesAlong ans (shadowOnM table bits mac)) : NoInverse r := by
  rcases shadow_questions table bits mac ans r member with prefixQ | trueQ | padsQ | xQ | yQ | gadgetQ
  · exact queries_of_allQ ans (prefix_forward table bits mac) r prefixQ
  · exact noInverse_of_encAt (queries_of_allQ ans (truePadsM_encAt' _) r trueQ)
  · exact noInverse_of_encAt (queries_of_allQ ans (evalPadsM_encAt' bits _) r padsQ)
  · exact noInverse_of_laneAt (queries_of_allQ ans (evalLaneM_laneAt _ _ _ _ _) r xQ)
  · exact noInverse_of_laneAt (queries_of_allQ ans (evalLaneM_laneAt _ _ _ _ _) r yQ)
  · unfold gadgetPart at gadgetQ
    rw [queriesAlong_bind, queriesAlong_pure, List.append_nil] at gadgetQ
    obtain ⟨o, κ, p, rfl⟩ := queries_of_queryOnly ans (Guess.unlockM_asks _ _ _) _ gadgetQ
    trivial

/-- **The shadow over the installed state is the view of the installed overlay.** For an oracle
agreeing with the opening's transcript on `overlay T₁ O`, the shadow's transcript planted over that
transcript has the lookups of `onView (overlay T₁ O')`. -/
theorem shadow_view (T₁ : Tape) (O O' : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (agrees : Hidden.AgreesWith O' (transcript (publicAnswer (overlay T₁ O)) (openingQueriesM table bits mac))) :
    SameLookups
      (plantAll (transcript (publicAnswer O') (shadowOnM table bits mac))
        (plantAll (transcript (publicAnswer (overlay T₁ O)) (openingQueriesM table bits mac)) LazyOracle.empty))
      (onView table bits mac (overlay T₁ O')) := by
  have forwardOpening := cellOnce_forward (cellOnce_opening table bits mac)
  -- the installed overlay of `O'` runs the opening as the installed overlay of `O`
  have agreesOverlay : Hidden.AgreesWith (overlay T₁ O')
      (Hidden.transcriptOf (publicAnswer (overlay T₁ O)) (openingQueriesM table bits mac)) := by
    intro e member
    rw [← transcript_eq_transcriptOf] at member
    have hyp := agrees e member
    obtain ⟨q, answer⟩ := (mem_transcript_iff _ _ e).mp member
    have forward := forwardOpening _ _ q
    obtain ⟨request, value⟩ := e
    simp only at q answer hyp forward ⊢
    cases request with
    | hash key =>
        rw [← answer, overlay_hash, overlay_hash]
        cases found : cellOf key with
        | some cell => rfl
        | none =>
            have stored := answer
            rw [overlay_hash, found] at stored
            exact hyp.trans stored.symm
    | fixedInverse _ _ => exact forward.elim
    | encInverse _ _ => exact forward.elim
    | fixedForward _ _ => exact hyp
    | encForward _ _ => exact hyp
  obtain ⟨openingSame, _⟩ := Hidden.transcriptOf_of_agrees _ _ _ agreesOverlay
  rw [← transcript_eq_transcriptOf, ← transcript_eq_transcriptOf] at openingSame
  -- `O'` and `overlay T₁ O'` agree along the shadow's path
  have agreesShadow : Hidden.AgreesWith O'
      (Hidden.transcriptOf (publicAnswer (overlay T₁ O')) (shadowOnM table bits mac)) := by
    intro e member
    rw [← transcript_eq_transcriptOf] at member
    obtain ⟨q, answer⟩ := (mem_transcript_iff _ _ e).mp member
    have forward := shadow_forward table bits mac _ _ q
    obtain ⟨request, value⟩ := e
    simp only at q answer forward ⊢
    subst answer
    cases request with
    | hash key =>
        cases found : cellOf key with
        | none =>
            rw [overlay_hash, found]
            rfl
        | some cell =>
            obtain ⟨x, rfl⟩ := Kriterion.ArgoMAC.Phase3.Lazy.cellOf_spec found
            have inOpening := shadow_cell_opening table bits mac _ cell x q
            rw [← map_fst_transcript, openingSame, map_fst_transcript] at inOpening
            have entry := (mem_transcript_iff _ _ ⟨.hash (cellInput cell x),
              publicAnswer (overlay T₁ O) (.hash (cellInput cell x))⟩).mpr ⟨inOpening, rfl⟩
            have agreeO := agrees _ entry
            simp only at agreeO
            rw [agreeO, overlay_cell, overlay_cell]
    | fixedInverse _ _ => exact forward.elim
    | encInverse _ _ => exact forward.elim
    | fixedForward _ _ => rfl
    | encForward _ _ => rfl
  obtain ⟨shadowSame, _⟩ := Hidden.transcriptOf_of_agrees _ _ _ agreesShadow
  rw [← transcript_eq_transcriptOf, ← transcript_eq_transcriptOf] at shadowSame
  unfold onView
  rw [shadowSame, ← openingSame]
  refine plantAll_sub (overlay T₁ O') _ _ (fun e member => ((mem_transcript_iff _ _ e).mp member).2.symm)
    (fun e member => ((mem_transcript_iff _ _ e).mp member).2.symm) fun e member => ?_
  obtain ⟨q, answer⟩ := (mem_transcript_iff _ _ e).mp member
  exact (mem_transcript_iff _ _ e).mpr ⟨opening_sub_shadow table bits mac _ _ q, answer⟩

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]

/-- **(D4) The shadow on the installed state, eager**: read through its final state's lookups, the
lazy shadow run on a state with the lookups of the opening's transcript on `overlay T₁ O` is the view
of `overlay T₁ O'`, `O'` a completion of that transcript. -/
theorem shadow_installed_eager (T₁ : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (state : LState)
    (same : SameLookups state (plantAll (transcript (publicAnswer (overlay T₁ O))
      (openingQueriesM table bits mac)) LazyOracle.empty))
    (W : LState → ℝ≥0∞) (invariant : ∀ s t, SameLookups s t → W s = W t) :
    ∑' x, runLazyQ (shadowOnM table bits mac) state x * W x.2 =
      ∑' O', publicCompletion (plantAll (transcript (publicAnswer (overlay T₁ O))
          (openingQueriesM table bits mac)) LazyOracle.empty) O' *
        W (onView table bits mac (overlay T₁ O')) := by
  rw [runLazyQ_eager (shadowOnM table bits mac) state (fun _ s => W s) (fun _ t t' h => invariant t t' h),
    publicCompletion_congr same]
  refine tsum_congr fun O' => ?_
  by_cases member : O' ∈ (publicCompletion (plantAll (transcript (publicAnswer (overlay T₁ O))
      (openingQueriesM table bits mac)) LazyOracle.empty)).support
  · have agrees : Hidden.AgreesWith O' (transcript (publicAnswer (overlay T₁ O))
        (openingQueriesM table bits mac)) := fun e inT =>
      completion_stored member (stored_of_mem (overlay T₁ O) _
        (fun f inF => ((mem_transcript_iff _ _ f).mp inF).2.symm)
        (fun f inF => cellOnce_forward (cellOnce_opening table bits mac) _ _
          ((mem_transcript_iff _ _ f).mp inF).1) e inT)
    refine congrArg _ ?_
    rw [invariant _ _ (plantAll_congr _ same)]
    exact invariant _ _ (shadow_view table bits mac T₁ O O' agrees)
  · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

end View

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
