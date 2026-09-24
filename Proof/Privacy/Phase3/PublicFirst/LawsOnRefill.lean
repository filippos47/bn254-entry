/-
**Phase 3, P1p — `LawOn`, step (D), part 1: `HW`'s refill opening, eager.**

The private side of `LawOn` starts with P4's refill run of `HW`'s opening from the empty oracle: a
designated hash question (a limb of the designated vector site `(pointX, 0, j*)`) is intercepted
(answered `(0, 0)`, recorded, not stored), the first question at an untouched limb's unstored input
is answered from the mask tape and programmed, every other question goes to the lazy oracle.
**`refill_eager`**: for a computation asking each limb at most once (`CellOnce`, from a state
untouched at those limbs and holding none of their inputs), the refill run, read through its value,
its final state's lookups and its record, is the eager run on a completion `O` of the start state
**overlaid** by the tape (`overlay`: a hash question at a limb's input, at any label, reads the
limb; the designated limbs zeroed, `zeroDesig`), with the non-designated part of its transcript
planted and the designated inputs recorded (`recordOf`).

The proof is `runLazyQ_eager`'s induction, with two new steps: an intercepted question plants
nothing, and a consumed limb question plants its limb — the completion of the programmed state is
the old completion reprogrammed at that input (`public_program_hash`), which the overlay does not
see (`overlay_programHash`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnCover

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion public_step pairHashCompletion hashSize
  IsDesignated interceptAnswer recordAfter designatedInput designatedSwitch chunkZero)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape Record cellOf cellInput consumeCell
  refillAnswer touch runRefill)
open scoped ENNReal

noncomputable section

/-! ### 1. A hash program on a completion -/

section Completion

/-- An oracle with its hash reprogrammed at one input. -/
def programHashOracle {FI EI : Type} (input : BaseField) (value : Block × Block)
    (oracle : PublicOracle FI EI) : PublicOracle FI EI :=
  (oracle.1, oracle.2.1, Function.update oracle.2.2 input value)

/-- A completion of a table programmed at an input, reprogrammed there, is a completion of the table
programmed at the new value. -/
theorem program_completion_update (table : HashTable BaseField hashSize) (input : BaseField)
    (first second : Fin hashSize) (f : (table.program input first).Completion) :
    ∀ key value, (table.program input second).lookup key = some value →
      Function.update f.val input second key = value := by
  intro key value present
  rw [HashTable.program_lookup] at present
  by_cases same : key = input
  · subst same
    simp only [Function.update_self, Option.some.injEq] at present ⊢
    exact present
  · rw [Function.update_of_ne same] at present ⊢
    refine f.property key value ?_
    rw [HashTable.program_lookup, Function.update_of_ne same]
    exact present

/-- Two completions of a table programmed at one input at different values correspond by
reprogramming that input. -/
def programCompletionEquiv (table : HashTable BaseField hashSize) (input : BaseField)
    (first second : Fin hashSize) :
    (table.program input first).Completion ≃ (table.program input second).Completion where
  toFun f := ⟨Function.update f.val input second, program_completion_update table input first second f⟩
  invFun f := ⟨Function.update f.val input first, program_completion_update table input second first f⟩
  left_inv f := by
    apply Subtype.ext
    funext key
    by_cases same : key = input
    · subst same
      simp only [Function.update_self]
      exact (f.property key first (by rw [HashTable.program_lookup, Function.update_self])).symm
    · simp only [Function.update_of_ne same]
  right_inv f := by
    apply Subtype.ext
    funext key
    by_cases same : key = input
    · subst same
      simp only [Function.update_self]
      exact (f.property key second (by rw [HashTable.program_lookup, Function.update_self])).symm
    · simp only [Function.update_of_ne same]

/-- Reprogramming a decoded completion at one input is decoding the reprogrammed completion. -/
theorem decode_update (g : BaseField → Fin hashSize) (input : BaseField) (value : Block × Block) :
    Function.update (fun key => (Fintype.equivFin (Block × Block)).symm (g key)) input value =
      fun key => (Fintype.equivFin (Block × Block)).symm
        (Function.update g input (Fintype.equivFin (Block × Block) value) key) := by
  funext key
  by_cases same : key = input
  · subst same
    simp
  · simp [Function.update_of_ne same]

/-- **A hash program at a fresh input has the exact conditional eager programming law.** -/
theorem pairHash_program (table : HashTable BaseField hashSize) (input : BaseField)
    (value : Block × Block) (fresh : table.lookup input = none) :
    (pairHashCompletion table).map (fun hash => Function.update hash input value) =
      pairHashCompletion (table.program input (Fintype.equivFin (Block × Block) value)) := by
  classical
  have positive : 0 < hashSize := Fintype.card_pos
  let : Nonempty (Fin hashSize) := ⟨⟨0, positive⟩⟩
  have split := Kriterion.ArgoMAC.Phase3.Glue.HashTable.fresh_completion positive table input fresh
  unfold pairHashCompletion
  rw [PMF.map_comp]
  have reshape : (PMF.uniformOfFintype table.Completion).map
      ((fun hash => Function.update hash input value) ∘
        fun complete key => (Fintype.equivFin (Block × Block)).symm (complete.val key)) =
      ((PMF.uniformOfFintype table.Completion).map Subtype.val).map
        (fun (g : BaseField → Fin hashSize) key => (Fintype.equivFin (Block × Block)).symm
          (Function.update g input (Fintype.equivFin (Block × Block) value) key)) := by
    rw [PMF.map_comp]
    congr 1
    funext complete
    exact decode_update complete.val input value
  rw [reshape, split, PMF.map_bind]
  have each : ∀ answer : Fin hashSize,
      ((PMF.uniformOfFintype (table.program input answer).Completion).map Subtype.val).map
          (fun (g : BaseField → Fin hashSize) key => (Fintype.equivFin (Block × Block)).symm
            (Function.update g input (Fintype.equivFin (Block × Block) value) key)) =
        (PMF.uniformOfFintype
            (table.program input (Fintype.equivFin (Block × Block) value)).Completion).map
          fun complete key => (Fintype.equivFin (Block × Block)).symm (complete.val key) := by
    intro answer
    rw [PMF.map_comp, ← Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv
      (programCompletionEquiv table input answer (Fintype.equivFin (Block × Block) value)),
      PMF.map_comp]
    congr 1
  simp_rw [each]
  exact PMF.bind_const _ _

variable {FI EI : Type} [Fintype FI] [Fintype EI] [DecidableEq FI] [DecidableEq EI]

/-- **A successful hash program has the exact conditional eager programming law.** -/
theorem public_program_hash (state updated : LazyOracle.State FI EI) (input : BaseField)
    (value : Block × Block)
    (success : LazyOracle.program (.hash input) value state = some updated) :
    (publicCompletion state).map (programHashOracle input value) = publicCompletion updated := by
  simp only [LazyOracle.program] at success
  split at success
  · rename_i fresh
    cases success
    unfold publicCompletion
    simp only [PMF.map_bind]
    refine congrArg _ (funext fun fixed => congrArg _ (funext fun enc => ?_))
    have key := congrArg (PMF.map fun hash => ((⟨fixed⟩, ⟨enc⟩, hash) : PublicOracle FI EI))
      (pairHash_program state.hash input value fresh)
    rw [PMF.map_comp] at key
    rw [PMF.map_comp]
    exact key
  · cases success

end Completion

/-! ### 2. The overlay and the designated site -/

section Overlay

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A hash oracle overlaid by a limb table: a limb's input, at any label, reads the limb.
(Irreducible: unfolding `cellOf` against an oracle's own hash sends definitional unification into
the field arithmetic of the scale inputs.) -/
@[irreducible] def overlayHash (T : Tape) (hash : EncPRF.HashOracle) : EncPRF.HashOracle :=
  fun key => (cellOf key).elim (hash key) T

/-- **An oracle overlaid by a limb table.** -/
def overlay (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    PublicOracle FixedIndex EncPRF.PermutationIndex :=
  (O.1, O.2.1, overlayHash T O.2.2)

theorem overlay_hash (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (key : BaseField) : publicAnswer (overlay T O) (.hash key) = (cellOf key).elim (O.2.2 key) T := by
  show overlayHash T O.2.2 key = _
  unfold overlayHash
  rfl

theorem overlay_cell (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex) (cell : Cell)
    (label : Block) : publicAnswer (overlay T O) (.hash (cellInput cell label)) = T cell := by
  rw [overlay_hash, Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput]
  rfl

/-- The overlay ignores the oracle's hash at every limb input. -/
theorem overlay_programHash (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (cell : Cell) (label : Block) (value : Block × Block) :
    overlay T (programHashOracle (cellInput cell label) value O) = overlay T O := by
  have hashes : overlayHash T (Function.update O.2.2 (cellInput cell label) value) =
      overlayHash T O.2.2 := by
    unfold overlayHash
    funext key
    cases found : cellOf key with
    | some c => rfl
    | none =>
        show Function.update O.2.2 (cellInput cell label) value key = O.2.2 key
        rw [Function.update_of_ne]
        rintro rfl
        rw [Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput] at found
        cases found
  unfold overlay programHashOracle
  rw [hashes]

/-- **The designated vector site** `(pointX, 0, j*)`. -/
def designatedSite (bits : BitInput) : Kriterion.ArgoMAC.Security.Phase3.VectorSite :=
  ⟨.pointX, chunkZero, designatedSwitch bits⟩

/-- A designated input is the input of a limb of the designated site. -/
theorem designatedInput_eq (bits : BitInput) (limb : Fin (limbCount .pointX)) (label : Block) :
    designatedInput bits limb label = cellInput ⟨designatedSite bits, limb⟩ label := rfl

/-- **A limb's input is designated exactly when its site is the designated one.** -/
theorem isDesignated_cellInput (bits : BitInput) (cell : Cell) (label : Block) :
    IsDesignated bits (cellInput cell label) ↔ cell.1 = designatedSite bits := by
  constructor
  · rintro ⟨limb, same⟩
    rw [show Kriterion.ArgoMAC.Phase3.Glue.scaleLabel (cellInput cell label) = label from
      Kriterion.ArgoMAC.Phase3.Glue.scaleLabel_scaleInput _ _ _ _ _, designatedInput_eq] at same
    exact (congrArg (fun pair : Cell × Block => pair.1.1)
      (Kriterion.ArgoMAC.Phase3.Lazy.cellInput_injective (a₁ := (⟨designatedSite bits, limb⟩, label))
        (a₂ := (cell, label)) same)).symm
  · intro site
    obtain ⟨vector, limb⟩ := cell
    simp only at site
    subst site
    exact Kriterion.ArgoMAC.Phase3.Glue.isDesignated_designatedInput bits limb label

/-- A designated input is a limb's input. -/
theorem cellOf_of_isDesignated (bits : BitInput) {key : BaseField} (designated : IsDesignated bits key) :
    cellOf key ≠ none := by
  obtain ⟨limb, same⟩ := designated
  rw [← same, designatedInput_eq, Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput]
  exact Option.some_ne_none _

open Classical in
/-- **The tape with the designated limbs zeroed**: an intercepted question reads `(0, 0)`. -/
def zeroDesig (bits : BitInput) (T : Tape) : Tape := fun cell =>
  if cell.1 = designatedSite bits then (0, 0) else T cell

open Classical in
/-- A transcript entry not at a designated input. -/
def notDesig (bits : BitInput) (entry : Entry FixedIndex EncPRF.PermutationIndex) : Bool :=
  match entry.1 with
  | .hash input => !decide (IsDesignated bits input)
  | _ => true

/-- The record after a list of questions. -/
def recordOf (bits : BitInput) (entries : List (Entry FixedIndex EncPRF.PermutationIndex))
    (record : Record) : Record :=
  entries.foldl (fun r e => recordAfter bits e.1 r) record

end Overlay

/-! ### 3. Computations asking each limb at most once -/

section Once

/-- A forward question at no limb's input. -/
def Plain (q : PublicQuery FixedIndex EncPRF.PermutationIndex) : Prop :=
  (∀ key, q = .hash key → cellOf key = none) ∧ NoInverse q

/-- **Every path asks each limb of `Y` at most once** (at one label), and asks no inverse question
and no other limb. -/
inductive CellOnce {α : Type} : Set Cell → FreeQuery Programs.Spec α → Prop
  | pure (Y : Set Cell) (value : α) : CellOnce Y (FreeQuery.pure value)
  | cell (Y : Set Cell) (cell : Cell) (label : Block)
      (next : Programs.Spec.Answer (PublicQuery.hash (cellInput cell label)) →
        FreeQuery Programs.Spec α)
      (inside : cell ∈ Y) (rest : ∀ answer, CellOnce (Y \ {cell}) (next answer)) :
      CellOnce Y (FreeQuery.query (PublicQuery.hash (cellInput cell label)) next)
  | other (Y : Set Cell) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
      (next : Programs.Spec.Answer request → FreeQuery Programs.Spec α) (plain : Plain request)
      (rest : ∀ answer, CellOnce Y (next answer)) : CellOnce Y (FreeQuery.query request next)

end Once

/-! ### 4. The refill run, eager -/

section Eager

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

theorem transcript_query_eq {α : Type}
    (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex) (next : q.Answer → FreeQuery Programs.Spec α)
    (a : q.Answer) (h : ans q = a) :
    transcript ans (FreeQuery.query q next) = ⟨q, a⟩ :: transcript ans (next a) := by
  subst h
  rfl

theorem eval_query_eq {α : Type} (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex) (next : q.Answer → FreeQuery Programs.Spec α)
    (a : q.Answer) (h : ans q = a) :
    (FreeQuery.query (spec := Programs.Spec) q next).eval ans = (next a).eval ans := by
  subst h
  rfl

theorem not_isDesignated_of_plain (bits : BitInput)
    (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (plain : Plain request) :
    ∀ key, request = .hash key → ¬ IsDesignated bits key := fun key same designated =>
  cellOf_of_isDesignated bits designated (plain.1 key same)

theorem notDesig_plain (bits : BitInput) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (plain : Plain request) (answer : request.Answer) : notDesig bits ⟨request, answer⟩ = true := by
  classical
  cases request with
  | hash key =>
      have notDesignated := not_isDesignated_of_plain bits _ plain key rfl
      simp [notDesig, notDesignated]
  | _ => rfl

theorem intercept_plain (bits : BitInput) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (plain : Plain request) : interceptAnswer bits request = none := by
  cases request with
  | hash key =>
      exact Kriterion.ArgoMAC.Phase3.Lazy.interceptAnswer_plain bits
        (not_isDesignated_of_plain bits _ plain key rfl)
  | _ => rfl

theorem consume_plain (τ : Set Cell) (s : LState)
    (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (plain : Plain request) :
    consumeCell τ s request = none := by
  cases request with
  | hash key =>
      show Kriterion.ArgoMAC.Phase3.Lazy.consumeHash τ s key = none
      unfold Kriterion.ArgoMAC.Phase3.Lazy.consumeHash
      rw [plain.1 key rfl]
  | _ => rfl

theorem touch_plain (τ : Set Cell) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (plain : Plain request) : touch request τ = τ := by
  ext cell
  constructor
  · rintro (member | touched)
    · exact member
    · cases request with
      | hash key =>
          change cellOf key = some cell at touched
          rw [plain.1 key rfl] at touched
          cases touched
      | _ => cases touched
  · exact Or.inl

theorem recordAfter_plain (bits : BitInput) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (plain : Plain request) (record : Record) : recordAfter bits request record = record := by
  cases request with
  | hash key =>
      exact Kriterion.ArgoMAC.Phase3.Glue.recordAfter_of_not_isDesignated bits key record
        (not_isDesignated_of_plain bits _ plain key rfl)
  | _ => rfl

theorem answer_overlay_plain (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (plain : Plain request) :
    publicAnswer (overlay T O) request = publicAnswer O request := by
  cases request with
  | hash key =>
      rw [overlay_hash, plain.1 key rfl]
      rfl
  | fixedInverse _ _ => exact plain.2.elim
  | encInverse _ _ => exact plain.2.elim
  | fixedForward _ _ => rfl
  | encForward _ _ => rfl

/-- **The refill run of a limb-once computation, eager.** -/
theorem refill_eager (bits : BitInput) (T : Tape) {α : Type} {Y : Set Cell}
    {c : FreeQuery Programs.Spec α} (once : CellOnce Y c) :
    ∀ (s : LState) (record : Record) (τ : Set Cell),
      (∀ cell ∈ Y, ∀ label, s.hash.lookup (cellInput cell label) = none) → (∀ cell ∈ Y, cell ∉ τ) →
      ∀ (F : Option (α × LState × Record) → ℝ≥0∞),
        (∀ a t t' r, SameLookups t t' → F (some (a, t, r)) = F (some (a, t', r))) →
        ∑' o, runRefill bits (fun cell => PMF.pure (T cell)) c s record τ o * F o =
          ∑' O, publicCompletion s O *
            F (some (c.eval (publicAnswer (overlay (zeroDesig bits T) O)),
              plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O)) c).filter
                (notDesig bits)) s,
              recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O)) c) record)) := by
  induction once with
  | pure Y value =>
      intro s record τ _ _ F _
      simp only [runRefill, tsum_pure_mul]
      show F (some (value, s, record)) = ∑' O, publicCompletion s O * F (some (value, plantAll [] s, record))
      rw [plantAll_nil, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | cell Y cell label next inside rest ih =>
      classical
      intro s record τ fresh untouched F invariant
      have freshHere := fresh cell inside label
      have freshRest : ∀ c' ∈ Y \ {cell}, ∀ l, s.hash.lookup (cellInput c' l) = none :=
        fun c' hc' l => fresh c' hc'.1 l
      have untouchedRest : ∀ c' ∈ Y \ {cell}, c' ∉ τ := fun c' hc' => untouched c' hc'.1
      by_cases designated : cell.1 = designatedSite bits
      · have isDesig : IsDesignated bits (cellInput cell label) :=
          (isDesignated_cellInput bits cell label).mpr designated
        have intercept : interceptAnswer bits (.hash (cellInput cell label)) = some (0, 0) :=
          Kriterion.ArgoMAC.Phase3.Lazy.interceptAnswer_designated bits isDesig
        have answer : ∀ O, publicAnswer (overlay (zeroDesig bits T) O)
            (.hash (cellInput cell label)) = (0, 0) := by
          intro O
          rw [overlay_cell]
          unfold zeroDesig
          exact if_pos designated
        rw [Kriterion.ArgoMAC.Phase3.Lazy.runRefill_intercept bits (fun cell => PMF.pure (T cell))
          (.hash (cellInput cell label)) next s record τ (0, 0) intercept]
        rw [ih (0, 0) s _ τ freshRest untouchedRest F invariant]
        refine tsum_congr fun O => congrArg _ ?_
        rw [transcript_query_eq _ (.hash (cellInput cell label)) next (0, 0) (answer O),
          eval_query_eq _ (.hash (cellInput cell label)) next (0, 0) (answer O),
          List.filter_cons_of_neg (by simp [notDesig, isDesig])]
        rfl
      · have notDesignated : ¬ IsDesignated bits (cellInput cell label) :=
          fun isDesig => designated ((isDesignated_cellInput bits cell label).mp isDesig)
        have intercept : interceptAnswer bits (.hash (cellInput cell label)) = none :=
          Kriterion.ArgoMAC.Phase3.Lazy.interceptAnswer_plain bits notDesignated
        have consumed : consumeCell τ s (.hash (cellInput cell label)) = some cell := by
          show Kriterion.ArgoMAC.Phase3.Lazy.consumeHash τ s (cellInput cell label) = some cell
          unfold Kriterion.ArgoMAC.Phase3.Lazy.consumeHash
          rw [Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput]
          dsimp only
          rw [if_neg]
          rintro (member | stored)
          · exact untouched cell inside member
          · exact stored freshHere
        have limbEq : zeroDesig bits T cell = T cell := by
          unfold zeroDesig
          exact if_neg designated
        have answer : ∀ O, publicAnswer (overlay (zeroDesig bits T) O)
            (.hash (cellInput cell label)) = T cell := by
          intro O
          rw [overlay_cell, limbEq]
        have programmed := program_hash_fresh s (cellInput cell label) (T cell) freshHere
        let s' := plantEntry s ⟨.hash (cellInput cell label), T cell⟩
        have freshLater : ∀ c' ∈ Y \ {cell}, ∀ l, s'.hash.lookup (cellInput c' l) = none := by
          intro c' hc' l
          rw [← freshRest c' hc' l]
          refine ((Kriterion.ArgoMAC.Phase3.Lazy.program_lookup_frame _ _ s s' programmed).2.2 _
            fun same => hc'.2 ?_)
          exact (congrArg Prod.fst (Kriterion.ArgoMAC.Phase3.Lazy.cellInput_injective
            (a₁ := (c', l)) (a₂ := (cell, label)) same))
        have untouchedLater : ∀ c' ∈ Y \ {cell}, c' ∉ touch (.hash (cellInput cell label)) τ := by
          rintro c' hc' (member | same)
          · exact untouched c' hc'.1 member
          · change cellOf (cellInput cell label) = some c' at same
            rw [Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput] at same
            exact hc'.2 (Option.some.inj same).symm
        simp only [runRefill]
        rw [intercept]
        dsimp only
        rw [consumed]
        dsimp only
        rw [PMF.pure_bind]
        simp only [refillAnswer]
        rw [programmed]
        dsimp only
        rw [ih (T cell) s' record _ freshLater untouchedLater F invariant]
        rw [← public_program_hash s s' (cellInput cell label) (T cell) programmed, tsum_map_mul]
        refine tsum_congr fun O => congrArg _ ?_
        rw [overlay_programHash]
        rw [transcript_query_eq _ (.hash (cellInput cell label)) next (T cell) (answer O),
          eval_query_eq _ (.hash (cellInput cell label)) next (T cell) (answer O),
          List.filter_cons_of_pos (by simp [notDesig, notDesignated])]
        have recordHead : recordOf bits (⟨.hash (cellInput cell label), T cell⟩ ::
            transcript (publicAnswer (overlay (zeroDesig bits T) O)) (next (T cell))) record =
            recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O))
              (next (T cell))) record := by
          unfold recordOf
          simp only [List.foldl_cons]
          rw [Kriterion.ArgoMAC.Phase3.Glue.recordAfter_of_not_isDesignated bits _ record
            notDesignated]
        rw [recordHead, plantAll_cons]
  | other Y request next plain rest ih =>
      intro s record τ fresh untouched F invariant
      simp only [runRefill]
      rw [intercept_plain bits request plain]
      dsimp only
      rw [consume_plain τ s request plain]
      dsimp only
      rw [tsum_bind_mul]
      have split := tsum_completion_split request s (fun b O =>
        F (some ((next b).eval (publicAnswer (overlay (zeroDesig bits T) O)),
          plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O)) (next b)).filter
            (notDesig bits)) (plantEntry s ⟨request, b⟩),
          recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O)) (next b))
            (recordAfter bits request record))))
      have lhsForm : ∀ O : PublicOracle FixedIndex EncPRF.PermutationIndex,
          F (some ((FreeQuery.query (spec := Programs.Spec) request next).eval
              (publicAnswer (overlay (zeroDesig bits T) O)),
            plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O))
              (FreeQuery.query request next)).filter (notDesig bits)) s,
            recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O))
              (FreeQuery.query request next)) record)) =
          F (some ((next (publicAnswer O request)).eval (publicAnswer (overlay (zeroDesig bits T) O)),
            plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O))
              (next (publicAnswer O request))).filter (notDesig bits))
                (plantEntry s ⟨request, publicAnswer O request⟩),
            recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O))
              (next (publicAnswer O request))) (recordAfter bits request record))) := by
        intro O
        have answer := answer_overlay_plain (zeroDesig bits T) O request plain
        show F (some ((next (publicAnswer (overlay (zeroDesig bits T) O) request)).eval _,
          plantAll ((⟨request, publicAnswer (overlay (zeroDesig bits T) O) request⟩ ::
            transcript _ (next (publicAnswer (overlay (zeroDesig bits T) O) request))).filter
              (notDesig bits)) s,
          recordOf bits (⟨request, publicAnswer (overlay (zeroDesig bits T) O) request⟩ ::
            transcript _ (next (publicAnswer (overlay (zeroDesig bits T) O) request))) record)) = _
        rw [answer, List.filter_cons_of_pos (notDesig_plain bits request plain _)]
        rfl
      rw [tsum_congr fun O => congrArg _ (lhsForm O), split]
      refine tsum_congr fun a => ?_
      by_cases member : a ∈ (LazyOracle.query request s).support
      · have freshAfter : ∀ cell ∈ Y, ∀ label, a.2.hash.lookup (cellInput cell label) = none := by
          intro cell hcell label
          rw [Kriterion.ArgoMAC.Phase3.Lazy.query_lookup_frame request s a member _ ?_]
          · exact fresh cell hcell label
          · cases request with
            | hash key =>
                intro same
                have keyEq : key = cellInput cell label := Option.some.inj same
                have none := plain.1 key rfl
                rw [keyEq, Kriterion.ArgoMAC.Phase3.Lazy.cellOf_cellInput] at none
                cases none
            | _ => exact fun same => by cases same
        refine congrArg _ ?_
        rw [ih a.1 a.2 record (touch request τ) freshAfter
          (by rw [touch_plain τ request plain]; exact untouched) F invariant,
          recordAfter_plain bits request plain]
        have same := Hidden.query_semEq_plant request s a member
        refine tsum_congr fun O => congrArg _ ?_
        exact invariant _ _ _ _ (plantAll_congr _ (sameLookups_of_semEq same))
      · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

end Eager

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
