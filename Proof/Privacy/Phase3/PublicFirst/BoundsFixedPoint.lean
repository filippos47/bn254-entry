/-
**Phase 3, P1m — (B1) `M'`'s on-curve private final state, described along the opening's answers.**

After the opening's refill run (final state `ran.2.1`, answers `ans = refillAns bits ran.2.1`), the
designated installation (hash programs) and the shadow's lazy run (final state `result.2`):

* `opening_agree`, `level_agree`, `tOf_agree`, `wPads_agree` — any later state reads the opening's
  non-intercepted questions as the opening did: the bridge value, the pads and every level label of
  every lane (`openLevel`) are the opening's;
* **`final_fixed`** — every stored fixed-key pair is a fold pair at its canonical input: at the
  index `hot lane c f e h`, `f < chunkWidth c`, `e < 2^f` is an inactive entry and the input is the
  level-`f` label `openLevel … lane c f e`; or a gadget pair at the transformed label;
  `final_used_le` — hence at most one pair per index;
* **`final_hash`** — every hash key of the private points is the bridge input
  `bridgeInput (tOf ans)` or a limb input of a lane's switch at its one-hot label
  `cellInput (maskCell lane c s limb) (openLevel … lane c (chunkWidth c) s)` (the designated
  requests' inputs included).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedCurve

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM whitePadsM noRecord IsDesignated
  interceptAnswer programRequests designatedInput)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request AllQ EncAt queriesAlong
  cellInput maskCell whitePadsM_allQ evalLaneM_allQ interceptAnswer_plain designated_cellAt
  bridgeInput_not_cellAt)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The installation keeps the fixed-key part and adds its requests' keys -/

section Install

theorem programAllSkip_fixed :
    ∀ (requests : List (Option BaseField × (Block × Block))) (state : LState),
      (programAllSkip requests state).fixed = state.fixed := by
  intro requests
  induction requests with
  | nil => exact fun state => rfl
  | cons request rest ih =>
    intro state
    obtain ⟨input, answer⟩ := request
    cases input with
    | none => exact ih state
    | some input =>
      show (programAllSkip rest
        ((LazyOracle.program (.hash input) answer state).getD state)).fixed = state.fixed
      rw [ih]
      cases success : LazyOracle.program (.hash input) answer state with
      | none => rfl
      | some updated => exact (program_hash_pairs input answer state updated success).1

theorem programAllSkip_keys :
    ∀ (requests : List (Option BaseField × (Block × Block))) (state : LState) (k : BaseField)
      (v : Fin (Fintype.card (Block × Block))),
      (programAllSkip requests state).hash.lookup k = some v →
        state.hash.lookup k = some v ∨ ∃ answer, (some k, answer) ∈ requests := by
  intro requests
  induction requests with
  | nil => exact fun _ _ _ found => Or.inl found
  | cons request rest ih =>
    intro state k v found
    obtain ⟨input, answer⟩ := request
    cases input with
    | none =>
      rcases ih state k v found with old | ⟨a, member⟩
      · exact Or.inl old
      · exact Or.inr ⟨a, List.mem_cons_of_mem _ member⟩
    | some input =>
      change (programAllSkip rest ((LazyOracle.program (.hash input) answer state).getD
        state)).hash.lookup k = some v at found
      rcases ih _ k v found with old | ⟨a, member⟩
      · cases success : LazyOracle.program (.hash input) answer state with
        | none =>
          rw [success] at old
          exact Or.inl old
        | some updated =>
          rw [success] at old
          rcases (program_hash_pairs input answer state updated success).2 k v old with
            older | ⟨rfl, _⟩
          · exact Or.inl older
          · exact Or.inr ⟨answer, List.mem_cons_self⟩
      · exact Or.inr ⟨a, List.mem_cons_of_mem _ member⟩

end Install

/-! ### The lanes of the opening and of the shadow -/

section Lanes

variable [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac)

/-- A lane's program, at the labels its pads give. -/
abbrev laneProg (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) (lane : Lane) :
    Programs.M (Fin (laneCount lane) → BaseField) :=
  Programs.evalLaneM lane (laneJoins table lane) (laneScale table lane) (laneWord bits lane)
    (laneLabels mac pads lane)

/-- **The opening's questions**: a lane's (system B at the opening's pads), the bridge hash, or
an EncPRF question. -/
theorem opening_cases (ans : (request : Request) → request.Answer) (q : Request)
    (member : q ∈ queriesAlong ans (openingQueriesM table bits mac)) :
    (∃ lane, q ∈ queriesAlong ans (laneProg table bits mac (wPadsOf table bits mac ans) lane)) ∨
      q = .hash (bridgeInput (tOf table bits mac ans)) ∨ EncAt q := by
  rcases mem_opening table bits mac ans q member with x | y | h | pads | x' | y'
  · exact Or.inl ⟨.curveX, x⟩
  · exact Or.inl ⟨.curveY, y⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (mem_queriesAlong_allQ ans (whitePadsM_allQ _) q pads))
  · exact Or.inl ⟨.pointX, x'⟩
  · exact Or.inl ⟨.pointY, y'⟩

/-- **A lane of the opening is a part of its path.** -/
theorem lane_mem_opening (ans : (request : Request) → request.Answer) (lane : Lane) (q : Request)
    (member : q ∈ queriesAlong ans (laneProg table bits mac (wPadsOf table bits mac ans) lane)) :
    q ∈ queriesAlong ans (openingQueriesM table bits mac) := by
  obtain ⟨before, after, path, _, _, _⟩ := opening_laneSplit table bits mac lane ans
  rw [path]
  exact List.mem_append_left _ (List.mem_append_right _ member)

variable [GroupCertificate]

/-- **The shadow's fixed-key questions**: a lane's (system B at the pads along the same answers)
or a gadget question at the transformed labels. -/
theorem shadow_fixed_cases (ans : (request : Request) → request.Answer) (i : FixedIndex) (x : Block)
    (member : .fixedForward i x ∈ queriesAlong ans (shadowOnM table bits mac)) :
    (∃ lane, .fixedForward i x ∈
      queriesAlong ans (laneProg table bits mac (wPadsOf table bits mac ans) lane)) ∨
      GadgetQ (Programs.transformMacOf (ePadsOf table bits mac ans) mac) (.fixedForward i x) := by
  rcases mem_shadow_fixed table bits mac ans i x member with x' | y' | px | py | g
  · exact Or.inl ⟨.curveX, x'⟩
  · exact Or.inl ⟨.curveY, y'⟩
  · exact Or.inl ⟨.pointX, px⟩
  · exact Or.inl ⟨.pointY, py⟩
  · exact Or.inr (mem_queriesAlong_allQ ans (masksM_gadgetQ _ _) _ g)

/-- **The shadow's hash questions**: the bridge input or a lane's. -/
theorem shadow_hash_cases (ans : (request : Request) → request.Answer) (k : BaseField)
    (member : .hash k ∈ queriesAlong ans (shadowOnM table bits mac)) :
    k = bridgeInput (tOf table bits mac ans) ∨
      ∃ lane, .hash k ∈
        queriesAlong ans (laneProg table bits mac (wPadsOf table bits mac ans) lane) := by
  rcases mem_shadow_hash table bits mac ans k member with h | x' | y' | px | py
  · exact Or.inl h
  · exact Or.inr ⟨.curveX, x'⟩
  · exact Or.inr ⟨.curveY, y'⟩
  · exact Or.inr ⟨.pointX, px⟩
  · exact Or.inr ⟨.pointY, py⟩

end Lanes

/-! ### Later states read the opening -/

section Agree

variable [FieldCertificate] [GroupCertificate] (source : Stage1Source) (input : AffineInput)
  (tape : Tape)
  (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
    LState × Record)
  (member : some ran ∈ (openingRun source input tape).support)
  (later : LState) (grow : Grows ran.2.1 later)

include member grow

/-- **A later state reads a non-intercepted question of the opening's path as the opening did.** -/
theorem opening_agree (q : Request)
    (onPath : q ∈ queriesAlong (refillAns (restoredBits source input) ran.2.1)
      (openingQueriesM source.publicValue (restoredBits source input) (restoredMac source input)))
    (notIntercepted : interceptAnswer (restoredBits source input) q = none) :
    answerOf later q = refillAns (restoredBits source input) ran.2.1 q := by
  rw [refillAns_plain notIntercepted]
  exact answerOf_of_stored (storedAs_grows grow
    ((opening_described source input tape ran (openingRun_mem member)).stored q onPath
      notIntercepted))

theorem curve_agree (lane : Lane) (curve : lane = .curveX ∨ lane = .curveY) :
    FreeQuery.eval (answerOf later) (laneProg source.publicValue (restoredBits source input)
        (restoredMac source input) (wPadsOf source.publicValue (restoredBits source input)
          (restoredMac source input) (refillAns (restoredBits source input) ran.2.1)) lane) =
      FreeQuery.eval (refillAns (restoredBits source input) ran.2.1)
        (laneProg source.publicValue (restoredBits source input) (restoredMac source input)
          (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1)) lane) := by
  refine (queriesAlong_congr _ _ _ fun q onPath => ?_).2
  have inside := mem_queriesAlong_allQ _ (evalLaneM_allQ _ _ _ _ _) q onPath
  exact opening_agree source input tape ran member later grow q
    (lane_mem_opening _ _ _ _ lane q onPath) (curve_notIntercepted _ lane curve q inside)

theorem tOf_agree :
    tOf source.publicValue (restoredBits source input) (restoredMac source input)
        (answerOf later) =
      tOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1) := by
  have x : FreeQuery.eval (answerOf later) (curveXM source.publicValue (restoredBits source input)
      (restoredMac source input)) = FreeQuery.eval (refillAns (restoredBits source input) ran.2.1)
        (curveXM source.publicValue (restoredBits source input) (restoredMac source input)) :=
    curve_agree source input tape ran member later grow .curveX (Or.inl rfl)
  have y : FreeQuery.eval (answerOf later) (curveYM source.publicValue (restoredBits source input)
      (restoredMac source input)) = FreeQuery.eval (refillAns (restoredBits source input) ran.2.1)
        (curveYM source.publicValue (restoredBits source input) (restoredMac source input)) :=
    curve_agree source input tape ran member later grow .curveY (Or.inr rfl)
  unfold tOf
  rw [x, y]

theorem wPads_agree :
    wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
        (answerOf later) =
      wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1) := by
  have tEq := tOf_agree source input tape ran member later grow
  have kEq : kOf source.publicValue (restoredBits source input) (restoredMac source input)
      (answerOf later) = kOf source.publicValue (restoredBits source input)
        (restoredMac source input) (refillAns (restoredBits source input) ran.2.1) := by
    show answerOf later (.hash (bridgeInput (tOf _ _ _ (answerOf later)))) = _
    rw [tEq]
    refine opening_agree source input tape ran member later grow _ ?_
      (interceptAnswer_plain _ fun designated =>
        bridgeInput_not_cellAt _ _ _ (designated_cellAt designated))
    rw [queriesAlong_opening]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ List.mem_cons_self))
  show FreeQuery.eval (answerOf later) (whitePadsM ⟨(kOf _ _ _ (answerOf later)).1,
      (kOf _ _ _ (answerOf later)).2⟩) = _
  rw [kEq]
  refine (queriesAlong_congr _ _ _ fun q onPath => ?_).2
  have enc := mem_queriesAlong_allQ _ (whitePadsM_allQ _) q onPath
  refine opening_agree source input tape ran member later grow q ?_ (by
    cases q with
    | encForward _ _ => rfl
    | _ => exact enc.elim)
  rw [queriesAlong_opening]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ onPath)))

/-- **A later state reads every level label of the opening as the opening did.** -/
theorem level_agree (lane : Lane) (c : Fin chunkCount) (s : ℕ) (le : s ≤ chunkWidth c) :
    openLevel source.publicValue (restoredBits source input) (restoredMac source input)
        (answerOf later) lane c s =
      openLevel source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1) lane c s := by
  show laneFoldLevel _ _ _ _ (laneLabels _ (wPadsOf source.publicValue (restoredBits source input)
    (restoredMac source input) (answerOf later)) lane) c s = _
  rw [wPads_agree source input tape ran member later grow]
  refine (queriesAlong_congr _ _ _ fun q onPath => ?_).2
  obtain ⟨s', small, e, inactive, h, rfl⟩ := (mem_evalFoldM _ _ _ _ _ _ _ _).mp onPath
  refine opening_agree source input tape ran member later grow _ ?_ rfl
  refine lane_mem_opening _ _ _ _ lane _ ?_
  exact (lane_fold_question _ lane _ _ _ _ _ _).mpr ⟨c, s', lt_of_lt_of_le small le, e, inactive, h,
    rfl, rfl⟩

end Agree

/-! ### The final state -/

section Final

variable [FieldCertificate] [GroupCertificate] (source : Stage1Source) (input : AffineInput)
  (tape : Tape)
  (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
    LState × Record)
  (member : some ran ∈ (openingRun source input tape).support)
  (answers : Kriterion.ArgoMAC.Phase3.Glue.DesignatedLimbs) (result : Unit × LState)
  (resultMember : result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
    (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
      ran.2.2 answers) ran.2.1)).support)

include member resultMember

theorem final_grows : Grows ran.2.1 result.2 :=
  (programAllSkip_grows _ _).trans (runLazyQ_grows _ _ result resultMember)

/-- A fixed-key question of a lane, along some answers, is a fold question at its level label. -/
theorem lane_fixed_canon (ans : (request : Request) → request.Answer) (lane : Lane) (i : FixedIndex)
    (x : Block) (inLane : .fixedForward i x ∈ queriesAlong ans
      (laneProg source.publicValue (restoredBits source input) (restoredMac source input)
        (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input) ans)
        lane))
    (agree : ∀ c s, s ≤ chunkWidth c → openLevel source.publicValue (restoredBits source input)
      (restoredMac source input) ans lane c s = openLevel source.publicValue
        (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1) lane c s) :
    ∃ (c : Fin chunkCount) (s : ℕ), s < chunkWidth c ∧ ∃ e : Fin (2 ^ s),
      e ≠ activeAt (chunkValue (laneWord (restoredBits source input) lane) c).toNat s ∧
        ∃ h : Bool, i = hotIndexNat lane c s e.val h ∧
          x = openLevel source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1) lane c s e := by
  obtain ⟨c, s, small, e, inactive, h, iEq, xEq⟩ :=
    (lane_fold_question _ lane _ _ _ _ _ _).mp inLane
  exact ⟨c, s, small, e, inactive, h, iEq, by rw [xEq, ← agree c s small.le]⟩

/-- **Every stored fixed-key pair of the final state is a fold pair at its level label, or a
gadget pair at the transformed label.** -/
theorem final_fixed (i : FixedIndex) (x y : Fin (2 ^ 128))
    (found : lk (result.2.fixed i) x = some y) :
    (∃ (lane : Lane) (c : Fin chunkCount) (s : ℕ), s < chunkWidth c ∧ ∃ e : Fin (2 ^ s),
      e ≠ activeAt (chunkValue (laneWord (restoredBits source input) lane) c).toNat s ∧
        ∃ h : Bool, i = hotIndexNat lane c s e.val h ∧
          BitVec.ofFin x = openLevel source.publicValue (restoredBits source input)
            (restoredMac source input) (refillAns (restoredBits source input) ran.2.1) lane c s e) ∨
      GadgetQ (Programs.transformMacOf (ePadsOf source.publicValue (restoredBits source input)
        (restoredMac source input) (answerOf result.2)) (restoredMac source input))
        (.fixedForward i (BitVec.ofFin x)) := by
  have grow := final_grows source input tape ran member answers result resultMember
  rcases (runLazyQ_provenance _ (shadowOnM_forwardOnly _ _ _) _ result resultMember).1 i x y found
    with old | onPath
  · rw [programAllSkip_fixed] at old
    rcases (opening_described source input tape ran (openingRun_mem member)).fixed i x y old with
      none' | onPath
    · rw [show lk ((LazyOracle.empty : LState).fixed i) x = none from lk_empty x] at none'
      cases none'
    · rcases opening_cases _ _ _ _ _ onPath with ⟨lane, inLane⟩ | h | enc
      · exact Or.inl ⟨lane, lane_fixed_canon source input tape ran member answers result
          resultMember _ lane i _ inLane fun _ _ _ => rfl⟩
      · cases h
      · exact enc.elim
  · rcases shadow_fixed_cases _ _ _ _ i _ onPath with ⟨lane, inLane⟩ | gadget
    · exact Or.inl ⟨lane, lane_fixed_canon source input tape ran member answers result
        resultMember _ lane i _ inLane fun c s le => level_agree source input tape ran member
          result.2 grow lane c s le⟩
    · exact Or.inr gadget

/-- **At most one pair per fixed-key index.** -/
theorem final_used_le (i : FixedIndex) : (result.2.fixed i).used ≤ 1 := by
  classical
  by_cases some : ∃ x y, lk (result.2.fixed i) x = some y
  · obtain ⟨x₀, y₀, found₀⟩ := some
    refine used_le_one _ x₀ fun x y found => ?_
    have canon : ∀ x y, lk (result.2.fixed i) x = some y → ∀ x' y',
        lk (result.2.fixed i) x' = some y' → BitVec.ofFin x = BitVec.ofFin x' := by
      intro x y found x' y' found'
      rcases final_fixed source input tape ran member answers result resultMember i x y found with
        ⟨lane, c, s, small, e, _, h, iEq, xEq⟩ | ⟨d, κ, pos, bit, same⟩
      · rcases final_fixed source input tape ran member answers result resultMember i x' y'
          found' with ⟨lane', c', s', small', e', _, h', iEq', xEq'⟩ | ⟨d', κ', pos', bit', same'⟩
        · obtain ⟨laneEq, chunkEq, stepEq, entryEq, _⟩ := hotIndexNat_inj
            (step_lt_chunkBits small) (step_lt_chunkBits small') (entry_lt_chunkBits small e)
            (entry_lt_chunkBits small' e') (iEq.symm.trans iEq')
          subst laneEq
          subst chunkEq
          subst stepEq
          rw [xEq, xEq', show e = e' from Fin.ext entryEq]
        · injection same' with iEq'' _
          rw [iEq] at iEq''
          unfold hotIndexNat at iEq''
          cases iEq''
      · rcases final_fixed source input tape ran member answers result resultMember i x' y'
          found' with ⟨lane', c', s', small', e', _, h', iEq', xEq'⟩ | ⟨d', κ', pos', bit', same'⟩
        · injection same with iEq'' _
          rw [iEq'] at iEq''
          unfold hotIndexNat at iEq''
          cases iEq''
        · injection same with iEq xEq
          injection same' with iEq' xEq'
          rw [xEq, xEq']
          rw [iEq] at iEq'
          injection iEq' with dEq κEq posEq bitEq
          have κSame : κ = κ' := by
            cases κ <;> cases κ' <;> first | rfl | cases κEq
          subst dEq
          subst κSame
          subst posEq
          rfl
    have := canon x y found x₀ y₀ found₀
    rw [← BitVec.toFin_ofFin x, this, BitVec.toFin_ofFin]
  · exact used_le_one _ 0 fun x y found => absurd ⟨x, y, found⟩ some

/-- **Every hash key of the private points is the bridge input or a lane's limb input at its one-hot
label.** -/
theorem final_hash (k : BaseField)
    (hit : ((pointsOf result.2).union (requestPoints (programRequests (restoredBits source input)
      ran.2.2 answers))).hashIn k) :
    k = bridgeInput (tOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1)) ∨
      ∃ (lane : Lane) (c : Fin chunkCount) (s : Fin (2 ^ chunkWidth c))
        (limb : Fin (limbCount lane)), k = cellInput (maskCell lane c s limb)
          (openLevel source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1) lane c (chunkWidth c) s) := by
  have grow := final_grows source input tape ran member answers result resultMember
  have d := opening_described source input tape ran member
  -- a hash question on the opening's path
  have onOpening : ∀ k, .hash k ∈ queriesAlong (refillAns (restoredBits source input) ran.2.1)
      (openingQueriesM source.publicValue (restoredBits source input) (restoredMac source input)) →
      k = bridgeInput (tOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1)) ∨
      ∃ (lane : Lane) (c : Fin chunkCount) (s : Fin (2 ^ chunkWidth c))
        (limb : Fin (limbCount lane)), k = cellInput (maskCell lane c s limb) (openLevel
          source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1) lane c (chunkWidth c) s) := by
    intro k onPath
    rcases opening_cases _ _ _ _ _ onPath with ⟨lane, inLane⟩ | h | enc
    · obtain ⟨c, s, limb, _, same⟩ := lane_hash_mem _ lane _ _ _ _ k inLane
      exact Or.inr ⟨lane, c, s, limb, same⟩
    · exact Or.inl (PublicQuery.hash.inj h)
    · exact enc.elim
  -- a designated request's input is a question of the opening
  have request : ∀ k answer, (some k, answer) ∈ programRequests (restoredBits source input) ran.2.2
      answers → .hash k ∈ queriesAlong (refillAns (restoredBits source input) ran.2.1)
        (openingQueriesM source.publicValue (restoredBits source input)
          (restoredMac source input)) := by
    intro k answer inside
    unfold programRequests at inside
    obtain ⟨limb, _, same⟩ := List.mem_map.mp inside
    injection same with inputEq _
    rcases d.records limb with none' | ⟨label, recorded, onPath⟩
    · rw [none'] at inputEq
      cases inputEq
    · rw [recorded] at inputEq
      injection inputEq with kEq
      rw [← kEq]
      exact onPath
  rcases hit with inside | ⟨answer, inRequests⟩
  · obtain ⟨v, found⟩ := Option.ne_none_iff_exists'.mp inside
    rcases (runLazyQ_provenance _ (shadowOnM_forwardOnly _ _ _) _ result resultMember).2 k v found
      with old | onPath
    · rcases programAllSkip_keys _ _ k v old with older | ⟨answer, inRequests⟩
      · rcases d.hash k v older with none' | onPath
        · cases none'
        · exact onOpening k onPath
      · exact onOpening k (request k answer inRequests)
    · rcases shadow_hash_cases _ _ _ _ k onPath with h | ⟨lane, inLane⟩
      · left
        rw [h, tOf_agree source input tape ran member result.2 grow]
      · obtain ⟨c, s, limb, _, same⟩ := lane_hash_mem _ lane _ _ _ _ k inLane
        refine Or.inr ⟨lane, c, s, limb, ?_⟩
        rw [same]
        exact congrArg _ (congrFun (level_agree source input tape ran member result.2 grow lane c
          (chunkWidth c) le_rfl) s)
  · exact onOpening k (request k answer inRequests)

end Final

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
