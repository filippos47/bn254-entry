/-
**Phase 3, P1q — `LawOn`, step (C): the garbler's side on an answer table.**

On the curve the upper side of `LawOn` runs the shadow lazily on `σ` (the garbler's EncPRF and
designed entries planted on the empty oracle). Along the tape the shadow asks only planted
questions or **fresh gadget questions** — at the positions `k = (o, κ, i)` where the garbler has no
designed entry (`freshPos`: the digit has no exceptional input, or its exceptional bit differs from
the input's), each at most once (`sOn_shadow`). Hence (`sOn_eager`) the lazy run is the eager run
on the tape overridden at the fresh positions by uniform translations `x ↦ x ⊕ v k`; the planted
entries are among its questions (`upper_covers`), and the planted questions are the garbler's, so
the tape reads as any table answering the garbler's questions as it does (`garbler_tape`). The
upper side at a tape reads the tape through its coins and its garbler's transcript only
(`shadowSide_congr`), so averaged over the swapped tape it is its average at the tapes realising
`tableLaw` tables (`LawsTable.swapped_tableTape`):

**`lawOn_garbler`**: the right side of `LawOn` equals

```
onGarbForm = E_{coins} E_{A ~ tableLaw} E_{v : GPos → Block uniform}
  Ψ(P_A, encode key u, plantAll (transcript (freshAnswer (freshPos scalar offsets u) v (tableAnswer A))
    (shadowOnM P_A u (key.encode u))) ∅),     P_A = (garbleM scalar coins).eval (tableAnswer A)).1.
```
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnCSO

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Request queriesAlong fq_bind_assoc)
open scoped ENNReal

noncomputable section

/-! ### 1. The fresh gadget positions -/

section Positions

variable [FieldCertificate] [GroupCertificate]

/-- **A fresh gadget position**: the garbler has no designed entry there (the digit has no
exceptional input, or its exceptional bit differs from the input's). -/
def freshPos (scalar : NonZeroScalar) (offsets : FieldMacToECMac.SuccessfulOffsets) (input : AffineInput)
    (k : GPos) : Bool :=
  !((digitEndomorphismBase (Hidden.digitKey scalar offsets k.1).digit).isSome &&
    decide ((inputBits input k.2.1).getLsb k.2.2 = Hidden.exceptionalBit scalar offsets k.1 k.2.1 k.2.2))

theorem freshPos_false (scalar : NonZeroScalar) (offsets : FieldMacToECMac.SuccessfulOffsets)
    (input : AffineInput) (k : GPos) :
    freshPos scalar offsets input k = false ↔
      (digitEndomorphismBase (Hidden.digitKey scalar offsets k.1).digit).isSome = true ∧
        (inputBits input k.2.1).getLsb k.2.2 = Hidden.exceptionalBit scalar offsets k.1 k.2.1 k.2.2 := by
  unfold freshPos
  simp

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
  (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)

/-- **A planted gadget entry is at a non-fresh position.** -/
theorem upper_gadget_planted (e : Entry FixedIndex EncPRF.PermutationIndex)
    (member : e ∈ upperEntries parameter scalar tape input) (o : Fin digitCount) (κ : Coord)
    (p : Fin PlanB.coordinateBits) (x : Block) (same : e.1 = .fixedForward (.gadget o κ p) x) :
    freshPos scalar tape.1.offsets input (o, κ, p) = false := by
  unfold upperEntries at member
  rcases List.mem_append.mp member with enc | designed
  · unfold encEntries at enc
    have isEnc := (List.mem_filter.mp enc).2
    obtain ⟨request, answer⟩ := e
    simp only at same
    subst same
    simp [Entry.IsEnc] at isEnc
  · unfold designedInstall at designed
    obtain ⟨inGarbler, rule⟩ := List.mem_filter.mp designed
    have shape := garblerTranscript_ask scalar tape e inGarbler
    obtain ⟨request, answer⟩ := e
    simp only at same
    subst same
    have some : (digitEndomorphismBase (Hidden.digitKey scalar tape.1.offsets o).digit).isSome = true :=
      shape
    have ruleTrue : designedIndex scalar tape input (.gadget o κ p) = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at rule
      exact rule.2
    have agree : (inputBits input κ).getLsb p = Hidden.exceptionalBit scalar tape.1.offsets o κ p := by
      have shown : designedIndex scalar tape input (.gadget o κ p) =
          (validate input && decide ((inputBits input κ).getLsb p =
            Hidden.exceptionalBit scalar tape.1.offsets o κ p)) := rfl
      rw [shown, Bool.and_eq_true, decide_eq_true_iff] at ruleTrue
      exact ruleTrue.2
    exact (freshPos_false scalar tape.1.offsets input (o, κ, p)).mpr ⟨some, agree⟩

/-- **At a non-fresh position the garbler's designed entry is planted.** -/
theorem planted_upper (valid : validate input = true) (o : Fin digitCount) (κ : Coord)
    (p : Fin PlanB.coordinateBits) (planted : freshPos scalar tape.1.offsets input (o, κ, p) = false) :
    ∃ e ∈ upperEntries parameter scalar tape input, ∃ x, e.1 = .fixedForward (.gadget o κ p) x := by
  obtain ⟨some, agree⟩ := (freshPos_false scalar tape.1.offsets input (o, κ, p)).mp planted
  obtain ⟨e, member, same⟩ := OnReach.upper_of_fixed parameter scalar tape input _ _
    (OnReach.asks_garbleM_gadget scalar tape o κ p some) (by
      show (validate input && decide ((inputBits input κ).getLsb p =
        Hidden.exceptionalBit scalar tape.1.offsets o κ p)) = true
      rw [valid, decide_eq_true agree]
      rfl)
  exact ⟨e, member, _, same⟩

/-- Planting entries at no index `i` leaves `i` alone. -/
theorem plantAll_fixed_notAt (i : FixedIndex) :
    ∀ (L : List (Entry FixedIndex EncPRF.PermutationIndex)) (s : LState),
      (∀ e ∈ L, ∀ x y, Hidden.fixedPair e ≠ some (i, x, y)) → (plantAll L s).fixed i = s.fixed i
  | [], _, _ => rfl
  | e :: L, s, absent => by
      rw [plantAll_cons, plantAll_fixed_notAt i L _ fun f member => absent f (List.mem_cons_of_mem _ member)]
      exact Hidden.plant_fixed_other s e i (absent e List.mem_cons_self)

/-- **No planted entry at a fresh index.** -/
theorem upper_fresh_empty (k : GPos) (fresh : freshPos scalar tape.1.offsets input k = true) :
    (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty).fixed (gIdx k) =
      SparsePermutation.empty _ := by
  rw [plantAll_fixed_notAt (gIdx k) _ _ fun e member x y pair => ?_]
  · rfl
  have forward := upperEntries_noInverse parameter scalar tape input e member
  obtain ⟨request, answer⟩ := e
  cases request with
  | fixedForward index z =>
      simp only [Hidden.fixedPair, Option.some.injEq, Prod.mk.injEq] at pair
      obtain ⟨same, -, -⟩ := pair
      obtain ⟨o, κ, p⟩ := k
      have notFresh := upper_gadget_planted parameter scalar tape input _ member o κ p z (by
        show PublicQuery.fixedForward index z = _
        rw [same]
        rfl)
      rw [notFresh] at fresh
      cases fresh
  | fixedInverse _ _ => exact forward.elim
  | encForward _ _ => cases pair
  | encInverse _ _ => cases pair
  | hash _ => cases pair

/-- A question stored in a planted consistent list is a question of the list. -/
theorem stored_upper (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (L : List (Entry FixedIndex EncPRF.PermutationIndex)) (consistent : Hidden.Consistent O L)
    (forwardL : ∀ e ∈ L, NoInverse e.1) (q : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (a : q.Answer) (stored : StoredAs (plantAll L LazyOracle.empty) ⟨q, a⟩) (forward : NoInverse q) :
    ∃ u ∈ L, u.1 = q := by
  cases q with
  | fixedForward index x =>
      have look : (LazyOracle.permutationLookup ((plantAll L LazyOracle.empty).fixed index) x.toFin).map
          BitVec.ofFin = some a := stored
      obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp look
      obtain ⟨e, member, pair⟩ := (look_plantAll_empty O L consistent index x.toFin y).mp hy
      have forwardE := forwardL e member
      obtain ⟨request, value⟩ := e
      cases request with
      | fixedForward j z =>
          simp only [Hidden.fixedPair, Option.some.injEq, Prod.mk.injEq] at pair
          obtain ⟨rfl, hz, -⟩ := pair
          exact ⟨_, member, by rw [show z = x from BitVec.toFin_inj.mp hz]⟩
      | fixedInverse _ _ => exact forwardE.elim
      | encForward _ _ => cases pair
      | encInverse _ _ => cases pair
      | hash _ => cases pair
  | fixedInverse _ _ => exact forward.elim
  | encForward index x =>
      have look : (LazyOracle.permutationLookup ((plantAll L LazyOracle.empty).enc index) x.toFin).map
          BitVec.ofFin = some a := stored
      obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp look
      obtain ⟨e, member, pair⟩ := (encLook_plantAll_empty O L consistent index x.toFin y).mp hy
      have forwardE := forwardL e member
      obtain ⟨request, value⟩ := e
      cases request with
      | encForward j z =>
          simp only [Hidden.encPair, Option.some.injEq, Prod.mk.injEq] at pair
          obtain ⟨rfl, hz, -⟩ := pair
          exact ⟨_, member, by rw [show z = x from BitVec.toFin_inj.mp hz]⟩
      | encInverse _ _ => exact forwardE.elim
      | fixedForward _ _ => cases pair
      | fixedInverse _ _ => cases pair
      | hash _ => cases pair
  | encInverse _ _ => exact forward.elim
  | hash key =>
      have look : ((plantAll L LazyOracle.empty).hash.lookup key).map _ = some a := stored
      rw [hashLookup_plantAll_empty O L consistent key] at look
      by_cases hit : ∃ e ∈ L, ∃ value, Hidden.hashPair e = some (key, value)
      · obtain ⟨e, member, value, pair⟩ := hit
        obtain ⟨request, answer⟩ := e
        cases request with
        | hash k =>
            simp only [Hidden.hashPair, Option.some.injEq] at pair
            obtain ⟨rfl, -⟩ := pair
            exact ⟨_, member, rfl⟩
        | fixedForward _ _ => cases pair
        | fixedInverse _ _ => cases pair
        | encForward _ _ => cases pair
        | encInverse _ _ => cases pair
      · rw [if_neg hit] at look
        cases look

/-- A question of a planted entry is stored with the tape's answer. -/
theorem stored_of_upper (q : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (hq : ∃ u ∈ upperEntries parameter scalar tape input, u.1 = q) :
    StoredAs (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) ⟨q, publicAnswer tape.2 q⟩ ∧
      NoInverse q := by
  obtain ⟨u, member, same⟩ := hq
  have stored := upper_stored parameter scalar tape input u member
  have consistent : u.2 = publicAnswer tape.2 u.1 := upper_consistent parameter scalar tape input u member
  have forward := upperEntries_noInverse parameter scalar tape input u member
  obtain ⟨uq, ua⟩ := u
  simp only at same consistent forward
  subst same
  subst consistent
  exact ⟨stored, forward⟩

end Positions

/-! ### 2. Along the tape, the shadow asks planted or fresh questions -/

section Shadow

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
  (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)

/-- A question of the evaluator on the tape, not at a fresh position, is planted. -/
theorem stored_of_onCurve (valid : validate input = true) (q : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (hq : Asks (publicAnswer tape.2) (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1
      (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))) q)
    (notFresh : ∀ (k : GPos) (x : Block), q = .fixedForward (gIdx k) x →
      freshPos scalar tape.1.offsets input k = false) :
    StoredAs (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) ⟨q, publicAnswer tape.2 q⟩ ∧
      NoInverse q := by
  have inOn : q ∈ (Hidden.transcriptOf (publicAnswer tape.2)
      (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
        (Guess.macOf tape input))).map Sigma.fst := hq
  rcases OnReach.onCurve_reach_classified parameter scalar tape input valid q inOn with
    ⟨u, uUpper, uEq⟩ | ⟨o, κ, p, qEq, noEntry⟩
  · exact stored_of_upper parameter scalar tape input q ⟨u, uUpper, uEq⟩
  · exfalso
    have planted := notFresh (o, κ, p) _ qEq
    obtain ⟨e, member, x, same⟩ := planted_upper parameter scalar tape input valid o κ p planted
    exact noEntry e member x same

/-- The shadow's pre-gadget evaluator on the tape is planted. -/
theorem preM_stored (valid : validate input = true) :
    ∀ e ∈ transcript (publicAnswer tape.2) (preM (Scheme.scheme.garble parameter scalar tape).1
      (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))),
      StoredAs (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) e ∧ NoInverse e.1 := by
  intro e member
  have answer : publicAnswer tape.2 e.1 = e.2 := transcript_mem _ _ e member
  rw [transcript_eq_transcriptOf] at member
  have inOn : Asks (publicAnswer tape.2) (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1
      (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))) e.1 := by
    rw [onCurveM_split]
    exact Asks.bind_left (asks_of_mem _ _ member)
  have stored := stored_of_onCurve parameter scalar tape input valid e.1 inOn fun k x same =>
    absurd same ((notGadget_preM _ _ _).mem _ e member k.1 k.2.1 k.2.2 x)
  obtain ⟨q, a⟩ := e
  simp only at answer stored ⊢
  subst answer
  exact stored

/-- The prefix on the tape is planted. -/
theorem prefix_stored (valid : validate input = true) :
    ∀ e ∈ transcript (publicAnswer tape.2) (curvePrefixM (Scheme.scheme.garble parameter scalar tape).1
      (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))),
      StoredAs (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) e ∧ NoInverse e.1 := by
  intro e member
  refine preM_stored parameter scalar tape input valid e ?_
  unfold preM
  rw [transcript_eq_transcriptOf, Hidden.transcriptOf_bind]
  rw [transcript_eq_transcriptOf] at member
  exact List.mem_append_left _ member

/-- The bit-`true` pads ask the pads at the first key. -/
theorem truePadsM_form (keys : WhiteningKeys) :
    Hidden.QueryOnly (fun q => ∃ (c : EncPRF.Coordinate) (i : Fin coordinateBitCount),
      q = .encForward (c, i) (encodeBit true ^^^ keys.first)) (truePadsM keys) := by
  have pad : ∀ c i, Hidden.QueryOnly (fun q => ∃ (c : EncPRF.Coordinate) (i : Fin coordinateBitCount),
      q = .encForward (c, i) (encodeBit true ^^^ keys.first)) (Programs.padM keys c i true) :=
    fun c i => Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ ⟨c, i, rfl⟩) fun _ => Hidden.QueryOnly.pure' _
  unfold truePadsM
  exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _) fun _ =>
    Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _) fun _ => Hidden.QueryOnly.pure' _

/-- The bit-`true` pads at the garbler's keys are planted. -/
theorem truePads_stored (key : Block × Block) (keyEq : key = tape.2.2.2 (bridgeInput tape.1.bridgeKey)) :
    ∀ e ∈ transcript (publicAnswer tape.2) (truePadsM ⟨key.1, key.2⟩),
      StoredAs (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) e ∧ NoInverse e.1 := by
  subst keyEq
  intro e member
  have answer : publicAnswer tape.2 e.1 = e.2 := transcript_mem _ _ e member
  rw [transcript_eq_transcriptOf] at member
  obtain ⟨c, i, qEq⟩ := (truePadsM_form _).mem _ e member
  obtain ⟨g, gMember, gEq⟩ := OnReach.entry_of_asks scalar tape (OnReach.asks_garbleM_enc scalar tape c i true)
  have stored := stored_of_upper parameter scalar tape input e.1 ⟨g,
    OnReach.upper_of_enc parameter scalar tape input g gMember (by
      obtain ⟨request, value⟩ := g
      simp only at gEq
      subst gEq
      rfl), gEq.trans qEq.symm⟩
  obtain ⟨q, a⟩ := e
  simp only at answer stored ⊢
  subst answer
  exact stored

/-- **The gadget at planted-or-fresh labels is planted or fresh.** -/
theorem sOn_unlock (valid : validate input = true) (m : InputMac)
    (asksAll : ∀ (o : Fin digitCount) (κ : Coord) (p : Fin PlanB.coordinateBits),
      Asks (publicAnswer tape.2) (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1
        (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input)))
        (.fixedForward (.gadget o κ p) (macAt m κ p))) :
    SOn (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) tape.2
      {k | freshPos scalar tape.1.offsets input k = true}
      (Programs.unlockM (Pipeline.pointTable (Scheme.scheme.garble parameter scalar tape).1)
        (BitInput.ofAffine input).toAffine m) := by
  let F : Set GPos := {k | freshPos scalar tape.1.offsets input k = true}
  -- one gadget question
  have one : ∀ (o : Fin digitCount) (κ : Coord) (p : Fin PlanB.coordinateBits),
      SOn (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) tape.2
        ({k | k = (o, κ, p)} ∩ F) (Programs.hashM (.gadget o κ p) (macAt m κ p)) := by
    intro o κ p
    by_cases fresh : freshPos scalar tape.1.offsets input (o, κ, p) = true
    · exact .fresh _ (o, κ, p) (macAt m κ p) _ ⟨rfl, fresh⟩ fun _ => .pure _ _
    · have notFresh : ∀ (k : GPos) (x : Block),
          (PublicQuery.fixedForward (.gadget o κ p) (macAt m κ p) :
            PublicQuery FixedIndex EncPRF.PermutationIndex) = .fixedForward (gIdx k) x →
          freshPos scalar tape.1.offsets input k = false := by
        intro k x same
        have kEq : k = (o, κ, p) := gIdx_injective (PublicQuery.fixedForward.inj same).1.symm
        rw [kEq]
        exact Bool.eq_false_iff.mpr fresh
      have stored := stored_of_onCurve parameter scalar tape input valid _ (asksAll o κ p) notFresh
      exact .stored _ _ _ stored.1 stored.2 (.pure _ _)
  -- one digest
  have digest : ∀ (o : Fin digitCount) (κ : EncPRF.Coordinate),
      SOn (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) tape.2
        {k | k.1 = o ∧ k.2.1 = Pipeline.gadgetCoord κ ∧ k ∈ F}
        (Programs.gadgetDigestM o κ (match κ with | .x => m.x | .y => m.y)) := by
    intro o κ
    unfold Programs.gadgetDigestM
    refine (sOn_bind (sOn_vector _ (fun i => {k | k = (o, Pipeline.gadgetCoord κ, i)} ∩ F) _
      (fun i => ?_) ?_) (fun _ => sOn_pure' ∅ _) (Set.disjoint_empty _)).mono ?_
    · cases κ
      · exact one o .x i
      · exact one o .y i
    · intro i i' ne
      rw [Set.disjoint_left]
      rintro k ⟨rfl, -⟩ ⟨same, -⟩
      exact ne (congrArg (fun k : GPos => k.2.2) same)
    · rintro k (hk | hk)
      · obtain ⟨i, ⟨rfl, hF⟩⟩ := Set.mem_iUnion.mp hk
        exact ⟨rfl, rfl, hF⟩
      · exact hk.elim
  unfold Programs.unlockM
  refine (sOn_vector _ (fun o => {k | k.1 = o ∧ k ∈ F}) _ (fun o => ?_) ?_).mono ?_
  · unfold Programs.gadgetMaskM
    refine (sOn_bind (sOn_bind (digest o .x) (fun _ => sOn_bind (digest o .y)
      (fun _ => sOn_pure' ∅ _) (Set.disjoint_empty _)) ?_) (fun _ => sOn_pure' ∅ _)
      (Set.disjoint_empty _)).mono ?_
    · rw [Set.disjoint_left]
      rintro k ⟨-, hx, -⟩ (⟨-, hy, -⟩ | hk)
      · rw [hx] at hy
        cases hy
      · exact hk.elim
    · rintro k ((⟨ho, -, hF⟩ | (⟨ho, -, hF⟩ | hk)) | hk)
      · exact ⟨ho, hF⟩
      · exact ⟨ho, hF⟩
      · exact hk.elim
      · exact hk.elim
  · intro o o' ne
    rw [Set.disjoint_left]
    rintro k ⟨ho, -⟩ ⟨ho', -⟩
    exact ne (ho.symm.trans ho')
  · intro k hk
    obtain ⟨o, -, hF⟩ := Set.mem_iUnion.mp hk
    exact hF

/-- **Along the tape the shadow asks planted questions or fresh gadget questions.** -/
theorem sOn_shadow (valid : validate input = true) :
    SOn (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) tape.2
      {k | freshPos scalar tape.1.offsets input k = true}
      (shadowOnM (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
        (tape.1.inputMacKey.encode (BitInput.ofAffine input))) := by
  unfold shadowOnM
  refine sOn_stored_bind _ _ (prefix_stored parameter scalar tape input valid) ?_
  refine sOn_stored_bind _ _ (truePads_stored parameter scalar tape input _
    (prefix_eval_tape parameter scalar tape input valid)) ?_
  rw [onCurveM_split, fq_bind_assoc]
  refine sOn_stored_bind _ _ (preM_stored parameter scalar tape input valid) ?_
  unfold gadgetPart
  rw [fq_bind_assoc]
  refine (sOn_bind (sOn_unlock parameter scalar tape input valid _ fun o κ p => ?_)
    (fun _ => sOn_pure' ∅ _) (Set.disjoint_empty _)).mono ?_
  · rw [onCurveM_split]
    refine Asks.bind_right ?_
    unfold gadgetPart
    exact Asks.bind_left (asks_unlock _ _ _ o κ p _ rfl)
  · rintro k (hk | hk)
    · exact hk
    · exact hk.elim

end Shadow

/-! ### 3. The upper side on a table -/

section Table

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
  [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- The overridden tape agrees with the planted entries. -/
theorem consistent_ovr (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (v : GPos → Block) :
    Hidden.Consistent (ovrOracle (freshPos scalar tape.1.offsets input) v tape.2)
      (upperEntries parameter scalar tape input) := by
  intro e member
  rw [ovr_other _ v tape.2 e.1 (upperEntries_noInverse parameter scalar tape input e member)
    fun k x same => upper_gadget_planted parameter scalar tape input e member k.1 k.2.1 k.2.2 x same]
  exact upper_consistent parameter scalar tape input e member

/-- **The upper side at one tape**: the lazy shadow run on the planted entries is the shadow's view
on any table answering the garbler's questions as the tape does, with uniform answers at the fresh
gadget positions. -/
theorem garbler_tape (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (valid : validate input = true) (A : Table)
    (agreeA : ∀ u ∈ garblerTranscript scalar tape, tableAnswer A u.1 = u.2)
    (Φ : LState → ℝ≥0∞) (invariant : ∀ s t, SameLookups s t → Φ s = Φ t) :
    ∑' s, runLazyQ (shadowOnM (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
          (tape.1.inputMacKey.encode (BitInput.ofAffine input)))
        (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) s * Φ s.2 =
      ∑' v, PMF.uniformOfFintype (GPos → Block) v *
        Φ (plantAll (transcript (freshAnswer (freshPos scalar tape.1.offsets input) v (tableAnswer A))
          (shadowOnM (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
            (tape.1.inputMacKey.encode (BitInput.ofAffine input)))) LazyOracle.empty) := by
  have empty : ∀ k, freshPos scalar tape.1.offsets input k = true →
      (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty).fixed (gIdx k) =
        SparsePermutation.empty _ := upper_fresh_empty parameter scalar tape input
  have holds := sOn_shadow parameter scalar tape input valid
  refine (sOn_eager _ empty holds (fun _ h => h) _ (Grows.refl _) (fun k h => empty k h)
    (fun _ s => Φ s)).trans (tsum_congr fun v => congrArg _ ?_)
  show Φ (plantAll _ _) = _
  -- the planted entries are among the shadow's questions
  have cover := plantAll_sub (ovrOracle (freshPos scalar tape.1.offsets input) v tape.2)
    (upperEntries parameter scalar tape input)
    (transcript (publicAnswer (ovrOracle (freshPos scalar tape.1.offsets input) v tape.2))
      (shadowOnM (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
        (tape.1.inputMacKey.encode (BitInput.ofAffine input))))
    (consistent_ovr parameter scalar tape input v) (fun e m => (transcript_mem _ _ e m).symm)
    (upper_covers parameter scalar tape input valid (consistent_ovr parameter scalar tape input v))
  rw [invariant _ _ cover]
  -- along the path, the overridden tape reads as the overridden table
  have agree := transcript_agree (shadowOnM (Scheme.scheme.garble parameter scalar tape).1
      (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input)))
    (publicAnswer (ovrOracle (freshPos scalar tape.1.offsets input) v tape.2))
    (freshAnswer (freshPos scalar tape.1.offsets input) v (tableAnswer A)) (by
      intro e member
      obtain ⟨q, answer⟩ := (mem_transcript_iff _ _ e).mp member
      rw [← answer]
      rcases sOn_path _ empty holds v (fun _ h => h) e.1 q with ⟨stored, forward⟩ | ⟨k, hk, x, same⟩
      · have notFresh := stored_notFresh _ empty stored
        rw [freshAnswer_other _ v _ e.1 notFresh, ovr_other _ v tape.2 e.1 forward notFresh]
        obtain ⟨u, uMember, uEq⟩ := stored_upper tape.2 _ (upper_consistent parameter scalar tape input)
          (upperEntries_noInverse parameter scalar tape input) e.1 _ stored forward
        have garbler := mem_garbler_of_upper parameter scalar tape input u uMember
        have tapeU := transcript_mem (publicAnswer tape.2) (Programs.garbleM scalar tape.1) u garbler
        rw [← uEq, agreeA u garbler, ← tapeU]
      · rw [same, freshAnswer_fresh _ v _ k hk x, ovr_fresh _ v tape.2 k hk x])
  rw [agree.1]

/-- The garbler's published value, on a table answering its questions as the tape does. -/
theorem garble_table (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (A : Table)
    (agreeA : ∀ u ∈ garblerTranscript scalar tape, tableAnswer A u.1 = u.2) :
    (Scheme.scheme.garble parameter scalar tape).1 =
      ((Programs.garbleM scalar tape.1).eval (tableAnswer A)).1 := by
  obtain ⟨coins, oracle⟩ := tape
  rw [← garble_eval parameter scalar coins oracle,
    (transcript_agree (Programs.garbleM scalar coins) (publicAnswer oracle) (tableAnswer A) agreeA).2]

/-- The garbler's side at a coins and a table. -/
def garbK (scalar : NonZeroScalar) (input : AffineInput) (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (coins : Coins) (A : Table) : ℝ≥0∞ :=
  ∑' v, PMF.uniformOfFintype (GPos → Block) v *
    Ψ ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 (Scheme.scheme.encode coins.inputMacKey input)
      (plantAll (transcript (freshAnswer (freshPos scalar coins.offsets input) v (tableAnswer A))
        (shadowOnM ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 (BitInput.ofAffine input)
          (coins.inputMacKey.encode (BitInput.ofAffine input)))) LazyOracle.empty)

/-- **The garbler's side's target form** (step C's result). -/
def onGarbForm (scalar : NonZeroScalar) (input : AffineInput)
    (Ψ : Public → LamportSignature → LState → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' coins, PMF.uniformOfFintype Coins coins * ∑' A, tableLaw A * garbK scalar input Ψ coins A

/-- The upper side of `LawOn` at one tape. -/
def shadowSide (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (tape : Coins × Oracle) : ℝ≥0∞ :=
  ∑' s, runLazyQ (shadowOnM (Scheme.scheme.garble parameter scalar tape).1
      (Lamport.restore input
        (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)).input
      (Lamport.restore input
        (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)).inputMac)
    (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) s *
    Ψ (Scheme.scheme.garble parameter scalar tape).1
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input) s.2

/-- **The upper side at a tape is the garbler's side at any table answering the garbler's questions
as the tape does.** -/
theorem shadowSide_table (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (valid : validate input = true) (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (invariant : ∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second)
    (tape : Coins × Oracle) (A : Table)
    (agreeA : ∀ u ∈ garblerTranscript scalar tape, tableAnswer A u.1 = u.2) :
    shadowSide parameter scalar input Ψ tape = garbK scalar input Ψ tape.1 A := by
  unfold shadowSide
  rw [restore_garble_input parameter scalar tape input, restore_garble_mac parameter scalar tape input,
    garbler_tape parameter scalar tape input valid A agreeA
      (fun st => Ψ (Scheme.scheme.garble parameter scalar tape).1
        (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input) st)
      (fun s t h => invariant _ _ s t h), garble_snd parameter scalar tape]
  unfold garbK
  rw [← garble_table parameter scalar tape A agreeA]

/-- The upper side at a tape reads the tape through its coins and its garbler's transcript only. -/
theorem shadowSide_congr (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (first second : Coins × Oracle)
    (coinsEq : first.1 = second.1)
    (transcriptEq : garblerTranscript scalar first = garblerTranscript scalar second) :
    shadowSide parameter scalar input Ψ first = shadowSide parameter scalar input Ψ second := by
  obtain ⟨coins, oracle⟩ := first
  obtain ⟨coins', oracle'⟩ := second
  change coins = coins' at coinsEq
  subst coinsEq
  have garbleEq : Scheme.scheme.garble parameter scalar (coins, oracle) =
      Scheme.scheme.garble parameter scalar (coins, oracle') := by
    rw [← garble_eval parameter scalar coins oracle, ← garble_eval parameter scalar coins oracle']
    refine (transcript_agree (Programs.garbleM scalar coins) (publicAnswer oracle) (publicAnswer oracle')
      fun e member => ?_).2.symm
    have member' : e ∈ garblerTranscript scalar (coins, oracle') := by
      rw [← transcriptEq]
      exact member
    exact transcript_mem _ _ e member'
  have ruleEq : designedRule scalar (coins, oracle) = designedRule scalar (coins, oracle') := by
    funext input entry
    obtain ⟨request, value⟩ := entry
    cases request with
    | fixedForward index _ => cases index <;> rfl
    | fixedInverse index _ => cases index <;> rfl
    | encForward _ _ => rfl
    | encInverse _ _ => rfl
    | hash _ => rfl
  have encEq : encEntries scalar (coins, oracle) = encEntries scalar (coins, oracle') := by
    unfold encEntries
    rw [transcriptEq]
  have installEq : ∀ table labels, designedInstall scalar (coins, oracle) table input labels =
      designedInstall scalar (coins, oracle') table input labels := by
    intro table labels
    unfold designedInstall
    rw [transcriptEq, ruleEq]
  have upperEq : upperEntries parameter scalar (coins, oracle) input =
      upperEntries parameter scalar (coins, oracle') input := by
    unfold upperEntries
    rw [encEq, installEq, garbleEq]
  unfold shadowSide
  rw [garbleEq, upperEq]

/-- **(C) The garbler's side of `LawOn` is `onGarbForm`.** -/
theorem lawOn_garbler (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (valid : validate input = true) (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (invariant : ∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second) :
    ∑' tape, swappedChallengeTape tape *
        ∑' s, runLazyQ (shadowOnM (Scheme.scheme.garble parameter scalar tape).1
            (Lamport.restore input
              (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)).input
            (Lamport.restore input
              (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)).inputMac)
          (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) s *
          Ψ (Scheme.scheme.garble parameter scalar tape).1
            (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input) s.2 =
      onGarbForm scalar input Ψ := by
  show ∑' tape, swappedChallengeTape tape * shadowSide parameter scalar input Ψ tape = _
  rw [swapped_tableTape scalar (shadowSide parameter scalar input Ψ)
    (shadowSide_congr parameter scalar input Ψ)]
  unfold onGarbForm
  refine tsum_congr fun coins => congrArg _ (tsum_congr fun A => congrArg _ ?_)
  refine shadowSide_table parameter scalar input valid Ψ invariant _ A fun u member => ?_
  rw [tableTape_garbler] at member
  exact transcript_mem _ _ u member

end Table

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
