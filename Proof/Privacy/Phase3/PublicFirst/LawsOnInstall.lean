/-
**Phase 3, P1q — `LawOn`, step (D3): the designated installation.**

After `HW`'s refill opening from the empty oracle, eager (`opening_eager`: a uniform oracle `O`
overlaid by the tape `T₀ = zeroDesig bits T`), the opening's state is its non-designated transcript
planted on the empty oracle, and its record holds the label `E*` of each designated limb. The
designated installation (`programAllSkip (programRequests …)`) programs the hash at the `452`
designated inputs `scaleInput pointX 0 j* i E*` to the drawn limbs. Here:

* **path independence** (`PathSame`, `pathSame_opening`): the opening's questions do not depend on
  the answers at the designated questions (they are switch-mask limbs, read only by the lanes'
  values, never by a later question);
* the record holds, at each designated limb, the label of the opening's unique question there
  (`recordOf_unique`, from `CellOnce`: each limb is asked at most once);
* the installation is a plant (`programAllSkip_eq`);
* **`install_state`**: the installed state has the lookups of the opening's whole transcript on the
  oracle overlaid by the **installed tape** `T₁ = installTape bits T limbs` (the designated limbs
  are the drawn preimage's, the other limbs the tape's).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnOpening

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion openingQueriesM whitePadsM IsDesignated
  designatedInput interceptAnswer recordAfter programRequests DesignatedLimbs)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape Record AllQ Request queriesAlong
  queriesAlong_bind queriesAlong_pure queriesAlong_vector FixedAt IndexAt EncAt LaneAt
  cellOf cellInput)
open scoped ENNReal

noncomputable section

/-! ### 1. Transcripts and question paths -/

section Paths

variable {α β γ δ : Type}

theorem mem_transcript_iff (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (c : FreeQuery Programs.Spec α) (e : Entry FixedIndex EncPRF.PermutationIndex) :
    e ∈ transcript ans c ↔ e.1 ∈ queriesAlong ans c ∧ ans e.1 = e.2 := by
  induction c with
  | pure value =>
      show e ∈ ([] : List (Entry FixedIndex EncPRF.PermutationIndex)) ↔
        e.1 ∈ ([] : List Request) ∧ ans e.1 = e.2
      simp
  | query request next ih =>
      show e ∈ (⟨request, ans request⟩ :: transcript ans (next (ans request)) :
          List (Entry FixedIndex EncPRF.PermutationIndex)) ↔
        e.1 ∈ request :: queriesAlong ans (next (ans request)) ∧ ans e.1 = e.2
      rw [List.mem_cons, List.mem_cons, ih]
      constructor
      · rintro (same | ⟨member, answer⟩)
        · subst same
          exact ⟨Or.inl rfl, rfl⟩
        · exact ⟨Or.inr member, answer⟩
      · rintro ⟨same | member, answer⟩
        · left
          obtain ⟨q, a⟩ := e
          simp only at same answer
          subst same
          subst answer
          rfl
        · exact Or.inr ⟨member, answer⟩

theorem map_fst_transcript (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (c : FreeQuery Programs.Spec α) : (transcript ans c).map Sigma.fst = queriesAlong ans c := by
  induction c with
  | pure value => rfl
  | query request next ih =>
      show request :: (transcript ans (next (ans request))).map Sigma.fst =
        request :: queriesAlong ans (next (ans request))
      rw [ih]

/-- A forward question the refill run leaves to the oracle. -/
def Clear (bits : BitInput) (r : Request) : Prop := NotIntercepted bits r ∧ NoInverse r

/-- Two answer functions agreeing on every clear question. -/
def AgreeOff (bits : BitInput) (a b : (r : Request) → r.Answer) : Prop := ∀ r, Clear bits r → a r = b r

/-- **Two computations take the same question path** on any two answer functions agreeing off the
designated (and inverse) questions. -/
def PathSame (bits : BitInput) (c : FreeQuery Programs.Spec α) (c' : FreeQuery Programs.Spec β) : Prop :=
  ∀ a b, AgreeOff bits a b → queriesAlong a c = queriesAlong b c'

variable (bits : BitInput)

theorem clear_agree {c : FreeQuery Programs.Spec α} (clear : AllQ (Clear bits) c)
    (a b : (r : Request) → r.Answer) (agree : AgreeOff bits a b) :
    queriesAlong a c = queriesAlong b c ∧ FreeQuery.eval a c = FreeQuery.eval b c := by
  induction clear with
  | pure value => exact ⟨rfl, rfl⟩
  | query request next holds _ ih =>
      have head : a request = b request := agree request holds
      obtain ⟨sameQ, sameV⟩ := ih (a request)
      refine ⟨?_, ?_⟩
      · show request :: queriesAlong a (next (a request)) = request :: queriesAlong b (next (b request))
        rw [sameQ, head]
      · show FreeQuery.eval a (next (a request)) = FreeQuery.eval b (next (b request))
        rw [sameV, head]

namespace PathSame

variable {bits}

theorem pure' (x : α) (y : β) :
    PathSame bits (Pure.pure x : FreeQuery Programs.Spec α) (Pure.pure y : FreeQuery Programs.Spec β) :=
  fun _ _ _ => rfl

theorem bind {c : FreeQuery Programs.Spec α} {c' : FreeQuery Programs.Spec β}
    {f : α → FreeQuery Programs.Spec γ} {g : β → FreeQuery Programs.Spec δ}
    (first : PathSame bits c c') (rest : ∀ x y, PathSame bits (f x) (g y)) :
    PathSame bits (c >>= f) (c' >>= g) := by
  intro a b agree
  rw [queriesAlong_bind, queriesAlong_bind, first a b agree, rest _ _ a b agree]

theorem bind_clear {c : FreeQuery Programs.Spec α} (clear : AllQ (Clear bits) c)
    {f g : α → FreeQuery Programs.Spec β} (rest : ∀ x, PathSame bits (f x) (g x)) :
    PathSame bits (c >>= f) (c >>= g) := by
  intro a b agree
  obtain ⟨sameQ, sameV⟩ := clear_agree bits clear a b agree
  rw [queriesAlong_bind, queriesAlong_bind, sameQ, sameV, rest _ a b agree]

theorem ask (q : Request) :
    PathSame bits (FreeQuery.ask (spec := Programs.Spec) q) (FreeQuery.ask (spec := Programs.Spec) q) :=
  fun _ _ _ => rfl

theorem vector : ∀ (count : Nat) {p p' : Fin count → FreeQuery Programs.Spec α},
    (∀ k, PathSame bits (p k) (p' k)) →
      PathSame bits (FreeQuery.vector count p) (FreeQuery.vector count p')
  | 0, _, _, _ => fun _ _ _ => rfl
  | count + 1, p, p', each => by
      show PathSame bits (FreeQuery.vector count (fun k => p k.castSucc) >>= fun values =>
          p (Fin.last count) >>= fun value => Pure.pure (values.push value))
        (FreeQuery.vector count (fun k => p' k.castSucc) >>= fun values =>
          p' (Fin.last count) >>= fun value => Pure.pure (values.push value))
      exact bind (vector count fun k => each k.castSucc) fun _ _ =>
        bind (each _) fun _ _ => pure' _ _

end PathSame

end Paths

/-! ### 2. The opening's path does not depend on the designated answers -/

section Opening

variable (bits : BitInput)

theorem clear_fixed (index : FixedIndex) (x : Block) : Clear bits (.fixedForward index x) :=
  ⟨rfl, trivial⟩

theorem clear_of_encAt {r : Request} (inside : EncAt r) : Clear bits r := by
  cases r with
  | encForward _ _ => exact ⟨rfl, trivial⟩
  | fixedForward _ _ => exact inside.elim
  | fixedInverse _ _ => exact inside.elim
  | encInverse _ _ => exact inside.elim
  | hash _ => exact inside.elim

theorem clear_bridge (t : BaseField) : Clear bits (.hash (bridgeInput t)) :=
  ⟨Kriterion.ArgoMAC.Phase3.Lazy.interceptAnswer_plain bits fun designated =>
    cellOf_of_isDesignated bits designated (cellOf_of_not_lt _ (bridgeInput_not_lt t)), trivial⟩

theorem clear_hashM (index : FixedIndex) (label : Block) :
    AllQ (Clear bits) (Programs.hashM index label) :=
  AllQ.bind (.query _ _ (clear_fixed bits _ _) fun _ => .pure _) fun _ => .pure _

theorem clear_evalStepM (lane : Lane) (chunk : Fin chunkCount) (step : Nat) (bitLabel join : Block)
    (active : Fin (2 ^ step)) (parent : Fin (2 ^ step) → Block) :
    AllQ (Clear bits) (Programs.evalStepM lane chunk step bitLabel join active parent) :=
  (AllQ.vector fun _ => AllQ.ite (.pure _)
    ((clear_hashM bits _ _).bind fun _ =>
      (clear_hashM bits _ _).bind fun _ => .pure _)).bind fun _ => .pure _

theorem clear_evalFoldM (lane : Lane) (chunk : Fin chunkCount) (value : Nat) (bitLabel join : Nat → Block) :
    ∀ steps, AllQ (Clear bits) (Programs.evalFoldM lane chunk value bitLabel join steps)
  | 0 => .pure _
  | steps + 1 => (clear_evalFoldM lane chunk value bitLabel join steps).bind fun _ =>
      (clear_evalStepM bits lane chunk _ _ _ _ _).bind fun _ => .pure _

theorem pathSame_switchMaskM (lane : Lane) (chunk : Fin chunkCount) (switch : Nat) (label : Block) :
    PathSame bits (Programs.switchMaskM lane chunk switch label)
      (Programs.switchMaskM lane chunk switch label) := by
  unfold Programs.switchMaskM
  exact PathSame.bind (PathSame.vector _ fun _ => PathSame.ask _) fun _ _ => PathSame.pure' _ _

theorem pathSame_evalMasksM (lane : Lane) (chunk : Fin chunkCount) (width : Nat)
    (hot : Fin (2 ^ width) → Block) (alpha : Fin (2 ^ width)) :
    PathSame bits (Programs.evalMasksM lane chunk width hot alpha)
      (Programs.evalMasksM lane chunk width hot alpha) := by
  unfold Programs.evalMasksM
  refine PathSame.bind (PathSame.vector _ fun switch => ?_) fun _ _ => PathSame.pure' _ _
  by_cases active : switch = alpha
  · rw [if_pos active]
    exact PathSame.pure' _ _
  · rw [if_neg active]
    exact pathSame_switchMaskM bits _ _ _ _

/-- **A lane's path does not depend on its limb answers.** -/
theorem pathSame_evalLaneM (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    PathSame bits (Programs.evalLaneM lane joins scale word labels)
      (Programs.evalLaneM lane joins scale word labels) := by
  unfold Programs.evalLaneM
  refine PathSame.bind (PathSame.vector _ fun c => ?_) fun _ _ => PathSame.pure' _ _
  unfold Programs.evalChunkM
  exact PathSame.bind_clear (clear_evalFoldM bits _ _ _ _ _ _) fun _ =>
    PathSame.bind (pathSame_evalMasksM bits _ _ _ _ _) fun _ _ => PathSame.pure' _ _

variable [FieldCertificate]

/-- A lane other than `pointX` asks no designated question. -/
theorem clear_lane (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (other : lane ≠ .pointX) :
    AllQ (Clear bits) (Programs.evalLaneM lane joins scale word labels) := by
  refine (AllQ.vector fun c => (Kriterion.ArgoMAC.Phase3.Lazy.evalChunkM_allQ lane joins scale word
    labels c).mono fun r inside => ?_).bind fun _ => .pure _
  rcases inside with fixed | hash
  · cases r with
    | fixedForward index x => exact clear_fixed bits index x
    | _ => exact fixed.elim
  · cases r with
    | hash key =>
        refine ⟨Kriterion.ArgoMAC.Phase3.Lazy.interceptAnswer_plain bits fun designated => ?_,
          trivial⟩
        obtain ⟨cell, label, laneEq, -, rfl⟩ := hash
        have site := (isDesignated_cellInput bits cell label).mp designated
        apply other
        rw [← laneEq, site]
        rfl
    | _ => exact hash.elim

/-- **The opening's path does not depend on the designated answers.** -/
theorem pathSame_opening (table : Public) (mac : InputMac) :
    PathSame bits (openingQueriesM table bits mac) (openingQueriesM table bits mac) := by
  unfold openingQueriesM
  refine PathSame.bind_clear (clear_lane bits _ _ _ _ _ (by decide)) fun _ => ?_
  refine PathSame.bind_clear (clear_lane bits _ _ _ _ _ (by decide)) fun _ => ?_
  refine PathSame.bind_clear (.query _ _ (clear_bridge bits _) fun _ => .pure _) fun _ => ?_
  refine PathSame.bind_clear ((Kriterion.ArgoMAC.Phase3.Lazy.whitePadsM_allQ _).mono
    fun _ inside => clear_of_encAt bits inside) fun _ => ?_
  refine PathSame.bind (pathSame_evalLaneM bits _ _ _ _ _) fun _ _ => ?_
  exact PathSame.bind_clear (clear_lane bits _ _ _ _ _ (by decide)) fun _ => PathSame.pure' _ _

end Opening

/-! ### 3. Each limb at most once -/

section Once

variable {α : Type}

theorem cellOnce_inside {Y : Set Cell} {c : FreeQuery Programs.Spec α} (once : CellOnce Y c) :
    ∀ (ans : (r : Request) → r.Answer) (cell : Cell) (x : Block),
      (PublicQuery.hash (cellInput cell x) : Request) ∈ queriesAlong ans c → cell ∈ Y := by
  induction once with
  | pure Y value => intro _ _ _ member; nomatch member
  | cell Y cell' label next inside rest ih =>
      intro ans cell x member
      rcases List.mem_cons.mp member with same | later
      · injection same with inputs
        have pair := Kriterion.ArgoMAC.Phase3.Lazy.cellInput_injective (a₁ := (cell, x))
          (a₂ := (cell', label)) inputs
        rw [show cell = cell' from congrArg Prod.fst pair]
        exact inside
      · exact (ih _ ans cell x later).1
  | other Y request next plain rest ih =>
      intro ans cell x member
      rcases List.mem_cons.mp member with same | later
      · have none := plain.1 _ same.symm
        rw [Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput] at none
        cases none
      · exact ih _ ans cell x later

/-- **A limb is asked at one label only.** -/
theorem cellOnce_unique {Y : Set Cell} {c : FreeQuery Programs.Spec α} (once : CellOnce Y c) :
    ∀ (ans : (r : Request) → r.Answer) (cell : Cell) (x y : Block),
      (PublicQuery.hash (cellInput cell x) : Request) ∈ queriesAlong ans c →
      (PublicQuery.hash (cellInput cell y) : Request) ∈ queriesAlong ans c → x = y := by
  induction once with
  | pure Y value => intro _ _ _ _ member; nomatch member
  | cell Y cell' label next inside rest ih =>
      intro ans cell x y mx my
      have atHead : ∀ z, (PublicQuery.hash (cellInput cell z) : Request) =
          .hash (cellInput cell' label) → cell = cell' ∧ z = label := fun z same => by
        injection same with inputs
        exact Prod.mk.inj (Kriterion.ArgoMAC.Phase3.Lazy.cellInput_injective (a₁ := (cell, z))
          (a₂ := (cell', label)) inputs)
      rcases List.mem_cons.mp mx with hx | hx <;> rcases List.mem_cons.mp my with hy | hy
      · exact (atHead x hx).2.trans (atHead y hy).2.symm
      · obtain ⟨rfl, -⟩ := atHead x hx
        exact absurd rfl (cellOnce_inside (rest _) ans _ y hy).2
      · obtain ⟨rfl, -⟩ := atHead y hy
        exact absurd rfl (cellOnce_inside (rest _) ans _ x hx).2
      · exact ih _ ans cell x y hx hy
  | other Y request next plain rest ih =>
      intro ans cell x y mx my
      have notHead : ∀ z, (PublicQuery.hash (cellInput cell z) : Request) ≠ request := by
        intro z same
        have none := plain.1 _ same.symm
        rw [Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput] at none
        cases none
      rcases List.mem_cons.mp mx with hx | hx
      · exact absurd hx (notHead x)
      rcases List.mem_cons.mp my with hy | hy
      · exact absurd hy (notHead y)
      · exact ih _ ans cell x y hx hy

theorem cellOnce_forward {Y : Set Cell} {c : FreeQuery Programs.Spec α} (once : CellOnce Y c) :
    ∀ (ans : (r : Request) → r.Answer) (r : Request), r ∈ queriesAlong ans c → NoInverse r := by
  induction once with
  | pure Y value => intro _ _ member; nomatch member
  | cell Y cell label next inside rest ih =>
      intro ans r member
      rcases List.mem_cons.mp member with same | later
      · subst same
        trivial
      · exact ih _ ans r later
  | other Y request next plain rest ih =>
      intro ans r member
      rcases List.mem_cons.mp member with same | later
      · subst same
        exact plain.2
      · exact ih _ ans r later

end Once

/-! ### 4. The record -/

section Record

variable (bits : BitInput)

theorem recordOf_cons (e : Entry FixedIndex EncPRF.PermutationIndex)
    (es : List (Entry FixedIndex EncPRF.PermutationIndex)) (record : Record) :
    recordOf bits (e :: es) record = recordOf bits es (recordAfter bits e.1 record) := rfl

theorem recordAfter_other (limb : Fin (limbCount .pointX)) (request : Request)
    (other : ∀ x, request ≠ .hash (designatedInput bits limb x)) (record : Record) :
    recordAfter bits request record limb = record limb := by
  cases request with
  | hash input =>
      simp only [recordAfter]
      rw [if_neg]
      intro same
      exact other _ (by rw [same])
  | fixedForward _ _ => rfl
  | fixedInverse _ _ => rfl
  | encForward _ _ => rfl
  | encInverse _ _ => rfl

theorem recordAfter_self (limb : Fin (limbCount .pointX)) (x : Block) (record : Record) :
    recordAfter bits (.hash (designatedInput bits limb x)) record limb = some x := by
  rw [Kriterion.ArgoMAC.Phase3.Glue.recordAfter_designatedInput, Function.update_self]

theorem recordOf_absent (limb : Fin (limbCount .pointX)) :
    ∀ (es : List (Entry FixedIndex EncPRF.PermutationIndex)) (record : Record),
      (∀ x, (PublicQuery.hash (designatedInput bits limb x) : Request) ∉ es.map Sigma.fst) →
        recordOf bits es record limb = record limb
  | [], _, _ => rfl
  | e :: es, record, absent => by
      rw [recordOf_cons, recordOf_absent limb es _ fun x member =>
        absent x (List.mem_cons_of_mem _ member)]
      refine recordAfter_other bits limb e.1 (fun x same => absent x ?_) record
      rw [List.map_cons, ← same]
      exact List.mem_cons_self

/-- **The record holds the label of the unique designated question of a limb.** -/
theorem recordOf_unique (limb : Fin (limbCount .pointX)) (x : Block) :
    ∀ (es : List (Entry FixedIndex EncPRF.PermutationIndex)) (record : Record),
      (PublicQuery.hash (designatedInput bits limb x) : Request) ∈ es.map Sigma.fst →
      (∀ y, (PublicQuery.hash (designatedInput bits limb y) : Request) ∈ es.map Sigma.fst →
        y = x) →
        recordOf bits es record limb = some x
  | [], _, member, _ => nomatch member
  | e :: es, record, member, unique => by
      rw [recordOf_cons]
      have uniqueTail : ∀ y, (PublicQuery.hash (designatedInput bits limb y) : Request) ∈
          es.map Sigma.fst → y = x :=
        fun y later => unique y (List.mem_cons_of_mem _ later)
      by_cases head : ∃ y, e.1 = .hash (designatedInput bits limb y)
      · obtain ⟨y, hy⟩ := head
        have yx : y = x := unique y (by rw [List.map_cons, ← hy]; exact List.mem_cons_self)
        subst yx
        by_cases later : (PublicQuery.hash (designatedInput bits limb y) : Request) ∈
            es.map Sigma.fst
        · exact recordOf_unique limb y es _ later uniqueTail
        · have absent : ∀ z, (PublicQuery.hash (designatedInput bits limb z) : Request) ∉
              es.map Sigma.fst := by
            intro z inZ
            have zy := uniqueTail z inZ
            subst zy
            exact later inZ
          rw [recordOf_absent bits limb es _ absent, hy]
          exact recordAfter_self bits limb y record
      · have other : ∀ z, e.1 ≠ .hash (designatedInput bits limb z) :=
          fun z same => head ⟨z, same⟩
        rcases List.mem_cons.mp (show (PublicQuery.hash (designatedInput bits limb x) : Request) ∈
            e.1 :: es.map Sigma.fst from member) with same | later
        · exact absurd same.symm (other x)
        · exact recordOf_unique limb x es _ later uniqueTail

/-- A recorded label is a label the list asks (or the record's before). -/
theorem recordOf_some (limb : Fin (limbCount .pointX)) (x : Block) :
    ∀ (es : List (Entry FixedIndex EncPRF.PermutationIndex)) (record : Record),
      recordOf bits es record limb = some x →
        record limb = some x ∨
          (PublicQuery.hash (designatedInput bits limb x) : Request) ∈ es.map Sigma.fst
  | [], _, found => Or.inl found
  | e :: es, record, found => by
      rw [recordOf_cons] at found
      rcases recordOf_some limb x es _ found with before | later
      · by_cases head : ∃ y, e.1 = .hash (designatedInput bits limb y)
        · obtain ⟨y, hy⟩ := head
          rw [hy, recordAfter_self] at before
          cases before
          right
          rw [List.map_cons, hy]
          exact List.mem_cons_self
        · left
          rw [recordAfter_other bits limb e.1 (fun z same => head ⟨z, same⟩)] at before
          exact before
      · exact Or.inr (List.mem_cons_of_mem _ later)

end Record

/-! ### 5. The installation is a plant -/

section Plant

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- The entry of a program request (none if its input is missing). -/
def reqEntry (request : Option BaseField × (Block × Block)) :
    Option (Entry FixedIndex EncPRF.PermutationIndex) :=
  request.1.map fun input => ⟨.hash input, request.2⟩

theorem programAllSkip_eq (requests : List (Option BaseField × (Block × Block))) :
    ∀ state : LState, Kriterion.ArgoMAC.Security.Phase3.programAllSkip requests state =
      plantAll (requests.filterMap reqEntry) state := by
  induction requests with
  | nil => intro _; rfl
  | cons request rest ih =>
      intro state
      obtain ⟨input, answer⟩ := request
      cases input with
      | none => exact ih state
      | some x => exact ih _

theorem plantAll_append_empty (first second : List (Entry FixedIndex EncPRF.PermutationIndex)) :
    plantAll second (plantAll first LazyOracle.empty) = plantAll (first ++ second) (LazyOracle.empty : LState) := by
  unfold plantAll
  rw [List.foldl_append]

theorem mem_installEntries (bits : BitInput) (record : Record) (limbs : DesignatedLimbs)
    (e : Entry FixedIndex EncPRF.PermutationIndex) :
    e ∈ (programRequests bits record limbs).filterMap reqEntry ↔
      ∃ (limb : Fin (limbCount .pointX)) (x : Block), record limb = some x ∧
        e = ⟨.hash (designatedInput bits limb x), limbs limb⟩ := by
  unfold programRequests
  simp only [List.mem_filterMap, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨request, ⟨limb, rfl⟩, found⟩
    simp only [reqEntry, Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at found
    obtain ⟨x, hx, rfl⟩ := found
    exact ⟨limb, x, hx, rfl⟩
  · rintro ⟨limb, x, hx, rfl⟩
    refine ⟨_, ⟨limb, rfl⟩, ?_⟩
    simp only [reqEntry, hx, Option.map_some]

/-- **Two consistent lists with the same entries plant the same lookups.** -/
theorem sameLookups_of_mem_iff (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (first second : List (Entry FixedIndex EncPRF.PermutationIndex))
    (firstConsistent : Hidden.Consistent O first) (secondConsistent : Hidden.Consistent O second)
    (same : ∀ e, e ∈ first ↔ e ∈ second) :
    SameLookups (plantAll first LazyOracle.empty) (plantAll second LazyOracle.empty) := by
  refine sameLookups_of_forward (fun i z => ?_) (fun i z => ?_) (fun key => ?_)
  · apply Option.ext
    intro y
    change Hidden.look _ z = some y ↔ Hidden.look _ z = some y
    rw [look_plantAll_empty O first firstConsistent, look_plantAll_empty O second secondConsistent]
    simp only [same]
  · apply Option.ext
    intro y
    change Hidden.look _ z = some y ↔ Hidden.look _ z = some y
    rw [encLook_plantAll_empty O first firstConsistent, encLook_plantAll_empty O second secondConsistent]
    simp only [same]
  · rw [hashLookup_plantAll_empty O first firstConsistent,
      hashLookup_plantAll_empty O second secondConsistent]
    by_cases hit : ∃ e ∈ first, ∃ value, Hidden.hashPair e = some (key, value)
    · have hit' : ∃ e ∈ second, ∃ value, Hidden.hashPair e = some (key, value) := by
        obtain ⟨e, member, rest⟩ := hit
        exact ⟨e, (same e).mp member, rest⟩
      rw [if_pos hit, if_pos hit']
    · have hit' : ¬ ∃ e ∈ second, ∃ value, Hidden.hashPair e = some (key, value) := by
        rintro ⟨e, member, rest⟩
        exact hit ⟨e, (same e).mpr member, rest⟩
      rw [if_neg hit, if_neg hit']

end Plant

/-! ### 6. The installed tape -/

section Tape

/-- **The installed tape**: the drawn preimage's limbs at the designated vector site, the tape
elsewhere. -/
def installTape (bits : BitInput) (T : Tape) (limbs : DesignatedLimbs) : Tape := fun cell =>
  if designated : cell.1 = designatedSite bits then
    limbs ⟨cell.2.val, lt_of_lt_of_eq cell.2.isLt (congrArg (fun v => limbCount v.lane) designated)⟩
  else T cell

theorem installTape_designated (bits : BitInput) (T : Tape) (limbs : DesignatedLimbs)
    (limb : Fin (limbCount .pointX)) :
    installTape bits T limbs ⟨designatedSite bits, limb⟩ = limbs limb := by
  unfold installTape
  rw [dif_pos rfl]

theorem installTape_other (bits : BitInput) (T : Tape) (limbs : DesignatedLimbs) (cell : Cell)
    (other : cell.1 ≠ designatedSite bits) : installTape bits T limbs cell = T cell := by
  unfold installTape
  rw [dif_neg other]

theorem zeroDesig_other (bits : BitInput) (T : Tape) (cell : Cell)
    (other : cell.1 ≠ designatedSite bits) : zeroDesig bits T cell = T cell := by
  unfold zeroDesig
  exact if_neg other

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

theorem notDesignated_of_clear (bits : BitInput) {key : BaseField}
    (clear : Clear bits (.hash key)) : ¬ IsDesignated bits key := fun designated => by
  have none := clear.1
  unfold NotIntercepted at none
  rw [Kriterion.ArgoMAC.Phase3.Lazy.interceptAnswer_designated bits designated] at none
  cases none

/-- **The zeroed and the installed overlay agree off the designated questions.** -/
theorem agreeOff_install (bits : BitInput) (T : Tape) (limbs : DesignatedLimbs)
    (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    AgreeOff bits (publicAnswer (overlay (zeroDesig bits T) O))
      (publicAnswer (overlay (installTape bits T limbs) O)) := by
  intro r clear
  cases r with
  | hash key =>
      have notDesignated := notDesignated_of_clear bits clear
      rw [overlay_hash, overlay_hash]
      cases found : cellOf key with
      | none => rfl
      | some cell =>
          obtain ⟨label, rfl⟩ := Kriterion.ArgoMAC.Phase3.Lazy.cellOf_spec found
          have other : cell.1 ≠ designatedSite bits := fun site =>
            notDesignated ((isDesignated_cellInput bits cell label).mpr site)
          show zeroDesig bits T cell = installTape bits T limbs cell
          rw [installTape_other bits T limbs cell other, zeroDesig_other bits T cell other]
  | fixedInverse _ _ => exact clear.2.elim
  | fixedForward _ _ => rfl
  | encForward _ _ => rfl
  | encInverse _ _ => rfl

/-- The installed overlay at a designated question. -/
theorem install_designated_answer (bits : BitInput) (T : Tape) (limbs : DesignatedLimbs)
    (O : PublicOracle FixedIndex EncPRF.PermutationIndex) (limb : Fin (limbCount .pointX))
    (x : Block) :
    publicAnswer (overlay (installTape bits T limbs) O) (.hash (designatedInput bits limb x)) =
      limbs limb := by
  rw [designatedInput_eq, overlay_cell, installTape_designated]

end Tape

/-! ### 7. The installed state -/

section Install

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A designated hash question is the designated input of a limb at its own label. -/
theorem designated_form (bits : BitInput) {key : BaseField} (designated : IsDesignated bits key) :
    ∃ limb, key = designatedInput bits limb (Kriterion.ArgoMAC.Phase3.Glue.scaleLabel key) := by
  obtain ⟨limb, same⟩ := designated
  exact ⟨limb, same.symm⟩

/-- **The designated installation, generically**: for a computation asking each limb at most once,
forward, whose path does not depend on the designated answers, installing the drawn limbs on its
non-designated transcript gives the lookups of its transcript on the installed overlay. -/
theorem install_generic (bits : BitInput) (T : Tape) (limbs : DesignatedLimbs)
    (O : PublicOracle FixedIndex EncPRF.PermutationIndex) {α : Type} {Y : Set Cell}
    (P : FreeQuery Programs.Spec α) (once : CellOnce Y P) (path : PathSame bits P P) :
    SameLookups
      (Kriterion.ArgoMAC.Security.Phase3.programAllSkip (programRequests bits
          (recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O)) P)
            Kriterion.ArgoMAC.Phase3.Glue.noRecord) limbs)
        (plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O)) P).filter (notDesig bits))
          LazyOracle.empty))
      (plantAll (transcript (publicAnswer (overlay (installTape bits T limbs) O)) P) LazyOracle.empty) := by
  classical
  have agree := agreeOff_install bits T limbs O
  have sameQ : queriesAlong (publicAnswer (overlay (zeroDesig bits T) O)) P =
      queriesAlong (publicAnswer (overlay (installTape bits T limbs) O)) P := path _ _ agree
  have forward := cellOnce_forward once
  -- a question off the designated inputs is clear
  have clearOf : ∀ r ∈ queriesAlong (publicAnswer (overlay (zeroDesig bits T) O)) P,
      (∀ key, r = .hash key → ¬ IsDesignated bits key) → Clear bits r := by
    intro r member notD
    refine ⟨?_, forward _ r member⟩
    cases r with
    | hash key => exact Kriterion.ArgoMAC.Phase3.Lazy.interceptAnswer_plain bits (notD key rfl)
    | _ => rfl
  rw [programAllSkip_eq, plantAll_append_empty]
  refine sameLookups_of_mem_iff (overlay (installTape bits T limbs) O) _ _ ?_ ?_ ?_
  · -- consistency of the zeroed transcript and the installed entries
    intro e member
    rcases List.mem_append.mp member with zeroed | installed
    · obtain ⟨inT, keep⟩ := List.mem_filter.mp zeroed
      obtain ⟨q, answer⟩ := (mem_transcript_iff _ _ e).mp inT
      rw [← answer]
      refine agree _ (clearOf _ q fun key same designated => ?_)
      obtain ⟨request, value⟩ := e
      simp only at same
      subst same
      simp [notDesig, designated] at keep
    · obtain ⟨limb, x, _, rfl⟩ := (mem_installEntries bits _ limbs e).mp installed
      exact (install_designated_answer bits T limbs O limb x).symm
  · intro e member
    exact ((mem_transcript_iff _ _ e).mp member).2.symm
  · intro e
    constructor
    · intro member
      rcases List.mem_append.mp member with zeroed | installed
      · obtain ⟨inT, keep⟩ := List.mem_filter.mp zeroed
        obtain ⟨q, answer⟩ := (mem_transcript_iff _ _ e).mp inT
        refine (mem_transcript_iff _ _ e).mpr ⟨sameQ ▸ q, ?_⟩
        rw [← answer]
        refine (agree _ (clearOf _ q fun key same designated => ?_)).symm
        obtain ⟨request, value⟩ := e
        simp only at same
        subst same
        simp [notDesig, designated] at keep
      · obtain ⟨limb, x, hx, rfl⟩ := (mem_installEntries bits _ limbs e).mp installed
        refine (mem_transcript_iff _ _ _).mpr ⟨?_, install_designated_answer bits T limbs O limb x⟩
        rcases recordOf_some bits limb x _ _ hx with none | inList
        · cases none
        · rw [map_fst_transcript] at inList
          exact sameQ ▸ inList
    · intro member
      obtain ⟨q, answer⟩ := (mem_transcript_iff _ _ e).mp member
      rw [← sameQ] at q
      obtain ⟨request, value⟩ := e
      simp only at q answer
      subst answer
      by_cases designatedQ : ∃ key, request = .hash key ∧ IsDesignated bits key
      · obtain ⟨key, rfl, designated⟩ := designatedQ
        obtain ⟨limb, keyEq⟩ := designated_form bits designated
        rw [keyEq] at q ⊢
        refine List.mem_append_right _ ((mem_installEntries bits _ limbs _).mpr
          ⟨limb, Kriterion.ArgoMAC.Phase3.Glue.scaleLabel key, ?_, ?_⟩)
        · refine recordOf_unique bits limb _ _ _ ?_ fun y my => ?_
          · rw [map_fst_transcript]
            exact q
          · rw [map_fst_transcript] at my
            rw [designatedInput_eq] at q my
            exact cellOnce_unique once _ _ y _ my q
        · rw [install_designated_answer bits T limbs O limb]
      · have notD : ∀ key, request = .hash key → ¬ IsDesignated bits key :=
          fun key same designated => designatedQ ⟨key, same, designated⟩
        refine List.mem_append_left _ (List.mem_filter.mpr ⟨?_, ?_⟩)
        · refine (mem_transcript_iff _ _ _).mpr ⟨q, ?_⟩
          exact agree _ (clearOf _ q notD)
        · cases request with
          | hash key => simp [notDesig, notD key rfl]
          | _ => rfl

variable [FieldCertificate]

/-- **(D3) The designated installation on the opening's state**: it has the lookups of the
opening's transcript on the oracle overlaid by the installed tape. -/
theorem install_state (bits : BitInput) (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (table : Public) (mac : InputMac) (limbs : DesignatedLimbs) :
    SameLookups
      (Kriterion.ArgoMAC.Security.Phase3.programAllSkip (programRequests bits
          (recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O))
            (openingQueriesM table bits mac)) Kriterion.ArgoMAC.Phase3.Glue.noRecord) limbs)
        (plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O))
          (openingQueriesM table bits mac)).filter (notDesig bits)) LazyOracle.empty))
      (plantAll (transcript (publicAnswer (overlay (installTape bits T limbs) O))
        (openingQueriesM table bits mac)) LazyOracle.empty) :=
  install_generic bits T limbs O _ (cellOnce_opening table bits mac) (pathSame_opening bits table mac)

end Install

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
