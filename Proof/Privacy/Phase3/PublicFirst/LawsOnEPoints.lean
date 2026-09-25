/-
**Phase 3, P1r — `LawOn`, step (E), part 3: the shadow on a uniform overlaid oracle is the shadow
on a uniform table.**

`LawOn`'s private side runs the shadow on `overlay T₁ O`, `O` uniform. The shadow asks the curve
lanes twice — in the prefix and again in the evaluator — at the same questions, with the same
answers, so planting its transcript is planting the transcript of `shadowOnceM`, which asks them
once (`plantAll_shadow`: a replanted entry changes nothing, `replant`). `shadowOnceM` asks every
fixed-key index at most once (`fixedOnce_shadowOnce`: the fold gates of the four lanes at every
chunk width, `LawsOnce.once_evalLaneM`, and the gadget positions), although the inputs of a fold
level read the answers of the level below; so on uniform permutations its planted transcript has
the law it has on one uniform block per index (`Laws.fixedOnce_uniform`). On the shadow's questions
those answers are a table's (the EncPRF permutations, the hash off the scale range, the blocks, the
tape): **`overlay_uniform`**.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEView

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState cellOf cellInput)
open scoped ENNReal

noncomputable section

/-! ### 1. Planting again -/

section Replant

theorem plantAll_append (first second : List (Entry FixedIndex EncPRF.PermutationIndex)) (s : LState) :
    plantAll (first ++ second) s = plantAll second (plantAll first s) :=
  List.foldl_append ..

/-- **Planting a forward or hash entry keeps every stored pair.** -/
theorem plantEntry_grows (s : LState) (e : Entry FixedIndex EncPRF.PermutationIndex)
    (forward : NoInverse e.1) : Grows s (plantEntry s e) := by
  obtain ⟨request, answer⟩ := e
  unfold plantEntry
  cases programmed : LazyOracle.program request answer s with
  | none => exact Grows.refl s
  | some updated =>
      show Grows s updated
      cases request with
      | fixedForward index input => exact program_state_grows index input answer s updated programmed
      | fixedInverse _ _ => exact forward.elim
      | encForward index input =>
          simp only [LazyOracle.program, Option.map_eq_some_iff] at programmed
          obtain ⟨next, success, rfl⟩ := programmed
          refine ⟨fun _ _ _ found => found, fun i x y found => ?_, fun _ _ found => found⟩
          by_cases same : i = index
          · subst same
            simp only [Function.update_self]
            exact program_grows _ _ _ _ success x y found
          · simpa [Function.update_of_ne same] using found
      | encInverse _ _ => exact forward.elim
      | hash input => exact program_hash_grows input answer s updated programmed

theorem plantAll_grows_forward (entries : List (Entry FixedIndex EncPRF.PermutationIndex))
    (forward : ∀ e ∈ entries, NoInverse e.1) : ∀ s, Grows s (plantAll entries s) := by
  induction entries with
  | nil => exact Grows.refl
  | cons e rest ih =>
      intro s
      exact (plantEntry_grows s e (forward e List.mem_cons_self)).trans
        (ih (fun f member => forward f (List.mem_cons_of_mem _ member)) _)

/-- **Planting an entry again, after its planting, changes nothing**: whether its first planting
stored it or failed, the input (or output, or hash key) it needs is taken from then on. -/
theorem replant (s t : LState) (e : Entry FixedIndex EncPRF.PermutationIndex) (forward : NoInverse e.1)
    (grow : Grows (plantEntry s e) t) : plantEntry t e = t := by
  obtain ⟨request, answer⟩ := e
  unfold plantEntry at grow ⊢
  cases request with
  | fixedForward index x =>
      have used : (t.fixed index).knownInput x.toFin ∨ (t.fixed index).knownOutput answer.toFin := by
        cases programmed : LazyOracle.program (.fixedForward index x) answer s with
        | some updated =>
            rw [programmed] at grow
            simp only [LazyOracle.program, Option.map_eq_some_iff] at programmed
            obtain ⟨next, success, rfl⟩ := programmed
            have stored := LazyOracle.permutationProgram_lookup _ _ _ _ success
            refine Or.inl ((knownInput_iff _ _).mpr ?_)
            rw [grow.fixed index x.toFin answer.toFin (by
              show lk ((Function.update s.fixed index next) index) x.toFin = _
              rw [Function.update_self]
              exact stored)]
            simp
        | none =>
            rw [programmed] at grow
            have stale : ¬ (LazyOracle.permutationProgram (s.fixed index) x.toFin answer.toFin).isSome := by
              simp only [LazyOracle.program, Option.map_eq_none_iff] at programmed
              rw [programmed]
              simp
            rw [permutationProgram_isSome_iff] at stale
            by_cases known : (s.fixed index).knownInput x.toFin
            · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp ((knownInput_iff _ _).mp known)
              refine Or.inl ((knownInput_iff _ _).mpr ?_)
              rw [grow.fixed index _ y hy]
              simp
            · have output : (s.fixed index).knownOutput answer.toFin := by
                by_contra fresh
                exact stale ⟨known, fresh⟩
              obtain ⟨x', hx'⟩ := (knownOutput_iff _ _).mp output
              exact Or.inr ((knownOutput_iff _ _).mpr ⟨x', grow.fixed index x' _ hx'⟩)
      show ((LazyOracle.permutationProgram (t.fixed index) x.toFin answer.toFin).map _).getD t = t
      rw [LazyOracle.permutationProgram_reject _ _ _ used]
      rfl
  | fixedInverse _ _ => exact forward.elim
  | encForward index x =>
      have used : (t.enc index).knownInput x.toFin ∨ (t.enc index).knownOutput answer.toFin := by
        cases programmed : LazyOracle.program (.encForward index x) answer s with
        | some updated =>
            rw [programmed] at grow
            simp only [LazyOracle.program, Option.map_eq_some_iff] at programmed
            obtain ⟨next, success, rfl⟩ := programmed
            have stored := LazyOracle.permutationProgram_lookup _ _ _ _ success
            refine Or.inl ((knownInput_iff _ _).mpr ?_)
            rw [grow.enc index x.toFin answer.toFin (by
              show lk ((Function.update s.enc index next) index) x.toFin = _
              rw [Function.update_self]
              exact stored)]
            simp
        | none =>
            rw [programmed] at grow
            have stale : ¬ (LazyOracle.permutationProgram (s.enc index) x.toFin answer.toFin).isSome := by
              simp only [LazyOracle.program, Option.map_eq_none_iff] at programmed
              rw [programmed]
              simp
            rw [permutationProgram_isSome_iff] at stale
            by_cases known : (s.enc index).knownInput x.toFin
            · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp ((knownInput_iff _ _).mp known)
              refine Or.inl ((knownInput_iff _ _).mpr ?_)
              rw [grow.enc index _ y hy]
              simp
            · have output : (s.enc index).knownOutput answer.toFin := by
                by_contra fresh
                exact stale ⟨known, fresh⟩
              obtain ⟨x', hx'⟩ := (knownOutput_iff _ _).mp output
              exact Or.inr ((knownOutput_iff _ _).mpr ⟨x', grow.enc index x' _ hx'⟩)
      show ((LazyOracle.permutationProgram (t.enc index) x.toFin answer.toFin).map _).getD t = t
      rw [LazyOracle.permutationProgram_reject _ _ _ used]
      rfl
  | encInverse _ _ => exact forward.elim
  | hash key =>
      have stored : t.hash.lookup key ≠ none := by
        by_cases fresh : s.hash.lookup key = none
        · cases programmed : LazyOracle.program (.hash key) answer s with
          | none =>
              simp only [LazyOracle.program, if_pos fresh] at programmed
              cases programmed
          | some updated =>
              rw [programmed] at grow
              have found : updated.hash.lookup key ≠ none := by
                simp only [LazyOracle.program, if_pos fresh, Option.some.injEq] at programmed
                subst programmed
                show (s.hash.program key _).lookup key ≠ none
                rw [HashTable.program_lookup, Function.update_self]
                simp
              obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp found
              rw [grow.hash key v hv]
              simp
        · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp fresh
          have programmed : LazyOracle.program (.hash key) answer s = none := by
            simp only [LazyOracle.program, if_neg fresh]
          rw [programmed] at grow
          rw [grow.hash key v hv]
          simp
      show (if t.hash.lookup key = none then _ else none).getD t = t
      rw [if_neg stored]
      rfl

/-- **Planting a list again, after its planting, changes nothing.** -/
theorem plantAll_replant (entries : List (Entry FixedIndex EncPRF.PermutationIndex))
    (forward : ∀ e ∈ entries, NoInverse e.1) :
    ∀ s t, Grows (plantAll entries s) t → plantAll entries t = t := by
  induction entries with
  | nil => exact fun _ _ _ => rfl
  | cons e rest ih =>
      intro s t grow
      have forwardRest : ∀ f ∈ rest, NoInverse f.1 := fun f member =>
        forward f (List.mem_cons_of_mem _ member)
      have head : plantEntry t e = t := replant s t e (forward e List.mem_cons_self)
        ((plantAll_grows_forward rest forwardRest _).trans grow)
      rw [plantAll_cons, head]
      exact ih forwardRest _ t grow

/-- **A list planted again, after a second one, changes nothing.** -/
theorem plantAll_dup (first second rest : List (Entry FixedIndex EncPRF.PermutationIndex))
    (forwardFirst : ∀ e ∈ first, NoInverse e.1) (forwardSecond : ∀ e ∈ second, NoInverse e.1)
    (s : LState) :
    plantAll (first ++ (second ++ (first ++ rest))) s = plantAll (first ++ (second ++ rest)) s := by
  simp only [plantAll_append]
  rw [plantAll_replant first forwardFirst s _ (plantAll_grows_forward second forwardSecond _)]

end Replant

/-! ### 2. The shadow, asking the curve lanes once -/

section Once

variable [FieldCertificate] [GroupCertificate]

/-- The evaluator after the prefix: the pads at the prefix's answer, the point lanes. -/
def restM (table : Public) (bits : BitInput) (mac : InputMac) (hashed : Block × Block) :
    Programs.M ((EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) ×
      (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) :=
  Programs.evalPadsM ⟨hashed.1, hashed.2⟩ bits >>= fun pads =>
    Programs.evalLaneM .pointX table.pointXHot
        (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
        (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)
      >>= fun pointX =>
    Programs.evalLaneM .pointY table.pointYHot
        (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
        (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
      >>= fun pointY => pure (pads, pointX, pointY)

theorem preM_eq (table : Public) (bits : BitInput) (mac : InputMac) :
    OnLaw.preM table bits mac = curvePrefixM table bits mac >>= restM table bits mac := rfl

/-- **The shadow asking the curve lanes once**: the prefix, the bit-`true` pads, the evaluator
from the prefix's answer on. -/
def shadowOnceM (table : Public) (bits : BitInput) (mac : InputMac) : Programs.M Unit :=
  curvePrefixM table bits mac >>= fun hashed =>
    truePadsM ⟨hashed.1, hashed.2⟩ >>= fun _ =>
      (restM table bits mac hashed >>= OnLaw.gadgetPart table bits mac) >>= fun _ => pure ()

variable (input : AffineInput)

theorem onQ_forward (q : PublicQuery FixedIndex EncPRF.PermutationIndex) (view : OnQ input q) :
    NoInverse q := by
  cases q with
  | fixedInverse _ _ => exact view.elim
  | encInverse _ _ => exact view.elim
  | _ => trivial

theorem transcript_forward {α : Type} {c : FreeQuery Programs.Spec α}
    (only : Hidden.QueryOnly (OnQ input) c)
    (a : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) :
    ∀ e ∈ transcript a c, NoInverse e.1 := by
  intro e member
  rw [transcript_eq_transcriptOf] at member
  exact onQ_forward input e.1 (only.mem a e member)

/-- **Planting the shadow's transcript is planting `shadowOnceM`'s**, on any answers. -/
theorem plantAll_shadow (P : Public) (mac : InputMac)
    (a : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) (s : LState) :
    plantAll (transcript a (shadowOnM P (BitInput.ofAffine input) mac)) s =
      plantAll (transcript a (shadowOnceM P (BitInput.ofAffine input) mac)) s := by
  have prefixForward := transcript_forward input (curvePrefixM_onQ input P mac) a
  have padsForward : ∀ hashed : Block × Block,
      ∀ e ∈ transcript a (truePadsM ⟨hashed.1, hashed.2⟩), NoInverse e.1 := by
    intro hashed
    refine transcript_forward input ?_ a
    unfold truePadsM
    exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => padM_onQ input _ _ _ _) fun _ =>
      Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => padM_onQ input _ _ _ _) fun _ =>
        Hidden.QueryOnly.pure' _
  unfold shadowOnM shadowOnceM
  rw [OnLaw.onCurveM_split, preM_eq]
  simp only [transcript_bind, FreeQuery.eval_bind, List.append_assoc]
  exact plantAll_dup _ _ _ prefixForward (padsForward _) s

/-! ### 3. `shadowOnceM` asks each fixed-key index once -/

theorem fixedOnce_of_onceIn {α : Type} {X : Set FixedIndex} {Y : Set Cell}
    {c : FreeQuery Programs.Spec α} (once : OnceIn X Y c) : FixedOnce X c := by
  induction once with
  | pure X Y value => exact .pure X value
  | fixed X Y index input next inside rest ih => exact .fixed X index input next inside ih
  | cell X Y cell label next inside rest ih => exact .other X _ next trivial ih

theorem gadgetMaskM_once (output : Fin FieldMacToECMac.outputMacCount) (input : AffineInput)
    (mac : InputMac) : FixedOnce (digitSet output) (Programs.gadgetMaskM output input mac) := by
  have apart : Disjoint (coordSet output .x) (coordSet output .y ∪ ∅) := by
    rw [Set.union_empty, Set.disjoint_left]
    rintro i ⟨p, b, rfl⟩ ⟨p', b', same⟩
    injection same with sameOutput sameCoord
    cases sameCoord
  refine ((gadgetDigestM_once output .x _ _).bind (fun _ => (gadgetDigestM_once output .y _ _).bind
    (fun _ => .pure ∅ _) (Set.disjoint_empty _)) apart).mono ?_
  rintro i (⟨p, b, rfl⟩ | ⟨p, b, rfl⟩ | hi)
  · exact ⟨_, p, b, rfl⟩
  · exact ⟨_, p, b, rfl⟩
  · exact hi.elim

theorem masksM_once (point : AffineInput) (mac : InputMac) :
    FixedOnce {index | ∃ output, index ∈ digitSet output} (Programs.masksM point mac) := by
  refine (FixedOnce.vector FieldMacToECMac.outputMacCount digitSet _
    (fun output => ((gadgetMaskM_once output point mac).bind (fun _ => .pure ∅ _)
      (Set.disjoint_empty _)).mono (by rw [Set.union_empty])) (fun o o' ne => by
      rw [Set.disjoint_left]
      rintro i ⟨κ, p, b, rfl⟩ ⟨κ', p', b', same⟩
      injection same with sameOutput
      exact ne sameOutput)).mono ?_
  rintro i ⟨_, ⟨o, rfl⟩, hi⟩
  exact ⟨o, hi⟩

theorem laneSets_apart (first second : Lane) (ne : first ≠ second) :
    Disjoint (onceLaneSet first) (onceLaneSet second) := by
  rw [Set.disjoint_left]
  rintro i ⟨c, f, e, h, rfl⟩ ⟨c', f', e', h', same⟩
  injection same with sameLane
  exact ne sameLane

theorem laneSet_gadgets (lane : Lane) :
    Disjoint (onceLaneSet lane) {index | ∃ output, index ∈ digitSet output} := by
  rw [Set.disjoint_left]
  rintro i ⟨c, f, e, h, rfl⟩ ⟨o, κ, p, b, same⟩
  cases same

/-- **`shadowOnceM` asks every fixed-key index at most once.** -/
theorem fixedOnce_shadowOnce (P : Public) (bits : BitInput) (mac : InputMac) :
    FixedOnce Set.univ (shadowOnceM P bits mac) := by
  have lane : ∀ (ℓ : Lane) (joins : Vector Block foldStepCount)
      (scale : Fin chunkCount → Fin (laneCount ℓ) → BaseField) (bits : BitVec coordinateBitCount)
      (labels : Fin coordinateBitCount → Block),
      FixedOnce (onceLaneSet ℓ) (Programs.evalLaneM ℓ joins scale bits labels) :=
    fun ℓ joins scale bits labels => fixedOnce_of_onceIn (once_evalLaneM ℓ joins scale bits labels)
  have prefixOnce : FixedOnce (onceLaneSet .curveX ∪ (onceLaneSet .curveY ∪ ∅))
      (curvePrefixM P bits mac) :=
    (lane .curveX _ _ _ _).bind (fun _ => (lane .curveY _ _ _ _).bind
      (fun _ => askHash_once ∅ _) (Set.disjoint_empty _))
      (Set.disjoint_union_right.mpr ⟨laneSets_apart _ _ (by decide), Set.disjoint_empty _⟩)
  have padsOnce : ∀ keys : WhiteningKeys, FixedOnce ∅ (truePadsM keys) := by
    intro keys
    have pad : ∀ c i, Hidden.QueryOnly (fun q => ∃ (index : EncPRF.PermutationIndex) (x : Block),
        q = .encForward index x) (Programs.padM keys c i true) := fun c i =>
      Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ ⟨_, _, rfl⟩) fun _ => Hidden.QueryOnly.pure' _
    refine FixedOnce.of_queryOnly ?_ ∅ (Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _)
      fun _ => Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _) fun _ =>
        Hidden.QueryOnly.pure' _)
    rintro q ⟨_, _, rfl⟩
    trivial
  have restOnce : ∀ hashed : Block × Block,
      FixedOnce (∅ ∪ (onceLaneSet .pointX ∪ (onceLaneSet .pointY ∪ ∅))) (restM P bits mac hashed) := by
    intro hashed
    refine (FixedOnce.of_queryOnly ?_ ∅ (Guess.evalPadsM_encOnly _ bits)).bind (fun _ =>
      (lane .pointX _ _ _ _).bind (fun _ => (lane .pointY _ _ _ _).bind (fun _ => .pure ∅ _)
        (Set.disjoint_empty _))
        (Set.disjoint_union_right.mpr ⟨laneSets_apart _ _ (by decide), Set.disjoint_empty _⟩))
      (Set.empty_disjoint _)
    rintro q ⟨_, _, _, rfl⟩
    trivial
  have gadgetOnce : ∀ r, FixedOnce {index | ∃ output, index ∈ digitSet output}
      (OnLaw.gadgetPart P bits mac r) := by
    intro r
    unfold OnLaw.gadgetPart
    exact ((masksM_once _ _).bind (fun _ => .pure ∅ _) (Set.disjoint_empty _)).mono
      (by rw [Set.union_empty])
  refine (prefixOnce.bind (fun hashed => (padsOnce _).bind (fun _ =>
    (((restOnce hashed).bind gadgetOnce ?_).bind (fun _ => .pure ∅ _) (Set.disjoint_empty _)))
      (Set.empty_disjoint _)) ?_).mono (Set.subset_univ _)
  · simp only [Set.empty_union, Set.union_empty]
    exact Set.disjoint_union_left.mpr ⟨laneSet_gadgets _, laneSet_gadgets _⟩
  · simp only [Set.empty_union, Set.union_empty]
    exact Set.disjoint_union_left.mpr ⟨Set.disjoint_union_right.mpr ⟨Set.disjoint_union_right.mpr
      ⟨laneSets_apart _ _ (by decide), laneSets_apart _ _ (by decide)⟩, laneSet_gadgets _⟩,
      Set.disjoint_union_right.mpr ⟨Set.disjoint_union_right.mpr
      ⟨laneSets_apart _ _ (by decide), laneSets_apart _ _ (by decide)⟩, laneSet_gadgets _⟩⟩

end Once

/-! ### 4. The overlaid oracle is a table -/

theorem tsum_hash_other (F : OtherTable → ℝ≥0∞) :
    ∑' H, PMF.uniformOfFintype EncPRF.HashOracle H * F (otherTableOf H) =
      ∑' o, PMF.uniformOfFintype OtherTable o * F o := by
  rw [uniform_hash_eq, tsum_map_mul, tsum_productPMF]
  refine tsum_congr fun o => congrArg _ ?_
  simp only [otherTableOf_hashOf]
  exact tsum_const_uniform _

variable [FieldCertificate] [GroupCertificate] (input : AffineInput)

/-- The overlaid oracle's answers, the fixed-key permutations aside. -/
def overlayBase (T : Tape) (E : PermutationOracle EncPRF.PermutationIndex Block) (H : EncPRF.HashOracle) :
    ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer :=
  publicAnswer (OnLaw.overlay T (⟨fun _ => Equiv.refl Block⟩, E, H))

omit [FieldCertificate] [GroupCertificate] in
theorem overlay_withPerms (T : Tape) (O : Oracle) :
    publicAnswer (OnLaw.overlay T O) = withPerms (overlayBase T O.2.1 O.2.2) O.1.permutation := by
  funext q
  cases q <;> rfl

/-- **On the shadow's questions, the overlaid answers with one block per index are a table's.** -/
theorem withFixed_table (P : Public) (mac : InputMac) (T : Tape)
    (E : PermutationOracle EncPRF.PermutationIndex Block) (H : EncPRF.HashOracle) (v : FixedIndex → Block) :
    transcript (withFixed (overlayBase T E H) v) (shadowOnM P (BitInput.ofAffine input) mac) =
      transcript (tableAnswer (E, otherTableOf H, v, T)) (shadowOnM P (BitInput.ofAffine input) mac) := by
  refine transcript_agree_only (shadow_onQ input P mac) _ _ fun q view => ?_
  cases q with
  | fixedForward _ _ => rfl
  | fixedInverse _ _ => exact view.elim
  | encForward _ _ => rfl
  | encInverse _ _ => exact view.elim
  | hash key =>
      show publicAnswer (OnLaw.overlay T (⟨fun _ => Equiv.refl Block⟩, E, H)) (.hash key) = _
      rw [OnLaw.overlay_hash, tableAnswer_hash]
      cases found : cellOf key with
      | some cell => rfl
      | none =>
          have high : ¬ key.val < scaleRange := by
            have holds : HashView input key := view
            unfold HashView at holds
            rw [found] at holds
            exact holds
          exact (hashOf_other (otherTableOf H) blankScale ⟨key, high⟩).symm

/-- **The shadow on a uniform overlaid oracle is the shadow on a table with uniform EncPRF
permutations, hash off the scale range and fixed-key blocks**, read through a planted state. -/
theorem overlay_uniform (P : Public) (mac : InputMac) (T : Tape) (Φ : LState → ℝ≥0∞) :
    ∑' O, PMF.uniformOfFintype Oracle O *
        Φ (plantAll (transcript (publicAnswer (OnLaw.overlay T O))
          (shadowOnM P (BitInput.ofAffine input) mac)) LazyOracle.empty) =
      ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
        ∑' H, PMF.uniformOfFintype OtherTable H *
          ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
            Φ (plantAll (transcript (tableAnswer (E, H, v, T))
              (shadowOnM P (BitInput.ofAffine input) mac)) LazyOracle.empty) := by
  have perOracle : ∀ O : Oracle,
      Φ (plantAll (transcript (publicAnswer (OnLaw.overlay T O))
        (shadowOnM P (BitInput.ofAffine input) mac)) LazyOracle.empty) =
      Φ (plantAll (transcript (withPerms (overlayBase T O.2.1 O.2.2) O.1.permutation)
        (shadowOnceM P (BitInput.ofAffine input) mac)) LazyOracle.empty) := by
    intro O
    rw [plantAll_shadow input P mac, overlay_withPerms]
  have perBlocks : ∀ (E : PermutationOracle EncPRF.PermutationIndex Block) (H : EncPRF.HashOracle)
      (v : FixedIndex → Block),
      Φ (plantAll (transcript (withFixed (overlayBase T E H) v)
        (shadowOnceM P (BitInput.ofAffine input) mac)) LazyOracle.empty) =
      Φ (plantAll (transcript (tableAnswer (E, otherTableOf H, v, T))
        (shadowOnM P (BitInput.ofAffine input) mac)) LazyOracle.empty) := by
    intro E H v
    rw [← plantAll_shadow input P mac, withFixed_table input P mac T E H v]
  have inner : ∀ (E : PermutationOracle EncPRF.PermutationIndex Block) (H : EncPRF.HashOracle),
      ∑' p, PMF.uniformOfFintype (PermutationOracle FixedIndex Block) p *
        Φ (plantAll (transcript (withPerms (overlayBase T E H) p.permutation)
          (shadowOnceM P (BitInput.ofAffine input) mac)) LazyOracle.empty) =
      ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
        Φ (plantAll (transcript (tableAnswer (E, otherTableOf H, v, T))
          (shadowOnM P (BitInput.ofAffine input) mac)) LazyOracle.empty) := by
    intro E H
    rw [tsum_equiv_uniform (Equiv.mk PermutationOracle.permutation PermutationOracle.mk
      (fun _ => rfl) (fun _ => rfl))]
    exact (fixedOnce_uniform (fixedOnce_shadowOnce P (BitInput.ofAffine input) mac)
      (overlayBase T E H) (fun entries _ => Φ (plantAll entries LazyOracle.empty))).trans
      (tsum_congr fun v => congrArg _ (perBlocks E H v))
  rw [tsum_congr fun O => congrArg _ (perOracle O)]
  rw [tsum_uniform_prod (α := PermutationOracle FixedIndex Block)
    (β := PermutationOracle EncPRF.PermutationIndex Block × EncPRF.HashOracle), tsum_swap_mul,
    tsum_uniform_prod (α := PermutationOracle EncPRF.PermutationIndex Block) (β := EncPRF.HashOracle)]
  refine tsum_congr fun E => congrArg _ ?_
  exact (tsum_congr fun H => congrArg _ (inner E H)).trans (tsum_hash_other fun o =>
    ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
      Φ (plantAll (transcript (tableAnswer (E, o, v, T))
        (shadowOnM P (BitInput.ofAffine input) mac)) LazyOracle.empty))

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
