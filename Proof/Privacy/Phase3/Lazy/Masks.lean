/-
**Phase 3, P4b — (b) the switch masks of a chunk on a tape.**

The masks of chunk `c` of a lane (`evalMasksM`) ask, for every inactive switch `s` and limb `i`,
one hash query at the cell input `scaleInput lane c s i (hot s)` (`queriesAlong_evalMasksM`). If
every non-designated one is a first touch of its cell at an unknown input, the tape runner answers
all of them (`masks_detRun_ne_none`), and, when none is designated, the value is

  `maskValues`: `sampleLane` of the tape's answers at the switch's cells (`0` at the active
  switch) -- **independent of the labels** (`masks_value`).

This is the output-independence step: once the masks are consumed, nothing the run computes
afterwards reads the labels of the chunk.
-/

import Proof.Privacy.Phase3.Lazy.ChunkZero

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open scoped ENNReal

noncomputable section

/-- The cell of limb `limb` of switch `switch` of a (lane, chunk). -/
abbrev maskCell (lane : Lane) (chunk : Fin chunkCount) (switch : Fin (2 ^ chunkWidth chunk))
    (limb : Fin (limbCount lane)) : Cell :=
  ⟨⟨lane, chunk, switch⟩, limb⟩

/-- The cells of one (lane, chunk) are distinct over (switch, limb). -/
theorem maskCell_injective (lane : Lane) (chunk : Fin chunkCount) :
    Function.Injective fun pair : Fin (2 ^ chunkWidth chunk) × Fin (limbCount lane) =>
      maskCell lane chunk pair.1 pair.2 := by
  rintro ⟨switch, limb⟩ ⟨switch', limb'⟩ same
  simp only [maskCell, Sigma.mk.injEq] at same
  obtain ⟨siteEq, limbEq⟩ := same
  simp only [Security.Phase3.VectorSite.mk.injEq, true_and] at siteEq
  subst siteEq
  exact Prod.ext rfl (eq_of_heq limbEq)

/-- The masks of a chunk ask each inactive switch's cells at that switch's label. -/
theorem evalMasksM_asks (lane : Lane) (chunk : Fin chunkCount) (hot : HotLabels (chunkWidth chunk))
    (alpha : Fin (2 ^ chunkWidth chunk)) :
    AllQ (fun request => ∃ switch limb,
        request = .hash (cellInput (maskCell lane chunk switch limb) (hot switch)))
      (Programs.evalMasksM lane chunk (chunkWidth chunk) hot alpha) :=
  (AllQ.vector fun switch => AllQ.ite (.pure _) ((switchMaskM_allQ lane chunk _ _).mono
    fun request inside => by
      cases request with
      | hash input =>
          obtain ⟨limb, rfl⟩ := inside
          exact ⟨switch, limb, rfl⟩
      | _ => exact inside.elim)).bind fun _ => .pure _

/-- A designated mask input of chunk 0 of `pointX` is at the designated switch. -/
theorem designated_maskCell {bits : BitInput} {switch : Fin (2 ^ chunkWidth chunkZero)}
    {limb : Fin (limbCount .pointX)} {label : Block}
    (designated : IsDesignated bits (cellInput (maskCell .pointX chunkZero switch limb) label)) :
    switch = designatedSwitch bits := by
  obtain ⟨limb', label', same⟩ := (isDesignated_iff bits _).mp designated
  have pair := cellInput_injective
    (a₁ := (maskCell .pointX chunkZero (designatedSwitch bits) limb', label'))
    (a₂ := (maskCell .pointX chunkZero switch limb, label)) same
  simp only [Prod.mk.injEq] at pair
  exact (congrArg Prod.fst (maskCell_injective .pointX chunkZero
    (a₁ := (designatedSwitch bits, limb')) (a₂ := (switch, limb)) pair.1)).symm

section Masks

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
  (bits : BitInput) (tape : Tape)

/-! ### The queries -/

theorem queriesAlong_switchMaskM (answer : (request : Request) → request.Answer) (lane : Lane)
    (chunk : Fin chunkCount) (switch : Nat) (label : Block) :
    queriesAlong answer (Programs.switchMaskM lane chunk switch label) =
      (List.finRange (limbCount lane)).map fun limb =>
        .hash (scaleInput lane chunk switch limb.val label) := by
  unfold Programs.switchMaskM
  rw [queriesAlong_bind, queriesAlong_vector, queriesAlong_pure, List.append_nil]
  generalize List.finRange (limbCount lane) = limbs
  induction limbs with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons, List.map_cons, ih]
      rfl

theorem queriesAlong_evalMasksM (answer : (request : Request) → request.Answer) (lane : Lane)
    (chunk : Fin chunkCount) (width : Nat) (hot : HotLabels width) (alpha : Fin (2 ^ width)) :
    queriesAlong answer (Programs.evalMasksM lane chunk width hot alpha) =
      (List.finRange (2 ^ width)).flatMap fun switch =>
        if switch = alpha then [] else
          queriesAlong answer (Programs.switchMaskM lane chunk switch.val (hot switch)) := by
  unfold Programs.evalMasksM
  rw [queriesAlong_bind, queriesAlong_vector, queriesAlong_pure, List.append_nil]
  congr 1
  funext switch
  split <;> rfl

/-- Membership in the query list of the masks. -/
theorem mem_queriesAlong_evalMasksM (answer : (request : Request) → request.Answer)
    (lane : Lane) (chunk : Fin chunkCount) (hot : HotLabels (chunkWidth chunk))
    (alpha : Fin (2 ^ chunkWidth chunk)) (request : Request)
    (member : request ∈ queriesAlong answer
      (Programs.evalMasksM lane chunk (chunkWidth chunk) hot alpha)) :
    ∃ switch : Fin (2 ^ chunkWidth chunk), switch ≠ alpha ∧ ∃ limb : Fin (limbCount lane),
      request = .hash (cellInput (maskCell lane chunk switch limb) (hot switch)) := by
  rw [queriesAlong_evalMasksM] at member
  obtain ⟨switch, _, inner⟩ := List.mem_flatMap.mp member
  split at inner
  · simp at inner
  · rename_i active
    rw [queriesAlong_switchMaskM] at inner
    obtain ⟨limb, _, rfl⟩ := List.mem_map.mp inner
    exact ⟨switch, active, limb, rfl⟩

/-! ### Distinct cells -/

/-- The cells a list of requests touches. -/
def touchedCells (requests : List Request) : List Cell := requests.filterMap touchedCell

theorem consumed_sublist (requests : List Request) :
    (requests.filterMap (consumedCell bits)).Sublist (touchedCells requests) := by
  induction requests with
  | nil => exact List.Sublist.slnil
  | cons request rest ih =>
      simp only [touchedCells, List.filterMap_cons] at ih ⊢
      cases request with
      | hash input =>
          by_cases designated : IsDesignated bits input
          · have none : consumedCell bits (.hash input) = none := by
              simp only [consumedCell]
              rw [if_pos designated]
            rw [none]
            cases touchedCell (.hash input) with
            | none => exact ih
            | some cell => exact ih.cons _
          · have same : consumedCell bits (.hash input) = touchedCell (.hash input) := by
              simp only [consumedCell, touchedCell]
              rw [if_neg designated]
            rw [same]
            cases touchedCell (.hash input) with
            | none => exact ih
            | some cell => exact ih.cons_cons _
      | fixedForward _ _ => exact ih
      | fixedInverse _ _ => exact ih
      | encForward _ _ => exact ih
      | encInverse _ _ => exact ih

theorem touchedCells_nodup (lane : Lane) (chunk : Fin chunkCount)
    (hot : HotLabels (chunkWidth chunk)) (alpha : Fin (2 ^ chunkWidth chunk))
    (answer : (request : Request) → request.Answer) :
    (touchedCells (queriesAlong answer
      (Programs.evalMasksM lane chunk (chunkWidth chunk) hot alpha))).Nodup := by
  have cellsOf : ∀ switch : Fin (2 ^ chunkWidth chunk),
      touchedCells (queriesAlong answer (Programs.switchMaskM lane chunk switch.val (hot switch)))
        = (List.finRange (limbCount lane)).map fun limb => maskCell lane chunk switch limb := by
    intro switch
    have cells : (touchedCell ∘ fun limb : Fin (limbCount lane) =>
        (PublicQuery.hash (scaleInput lane chunk switch.val limb.val (hot switch)) : Request)) =
        some ∘ fun limb => maskCell lane chunk switch limb := by
      funext limb
      rw [Function.comp_apply, Function.comp_apply]
      exact cellOf_cellInput (maskCell lane chunk switch limb) (hot switch)
    rw [queriesAlong_switchMaskM, touchedCells, List.filterMap_map, cells, List.filterMap_eq_map]
  rw [queriesAlong_evalMasksM, touchedCells, List.filterMap_flatMap]
  refine List.nodup_flatMap.mpr ⟨fun switch _ => ?_, ?_⟩
  · split
    · simp
    · rw [← touchedCells, cellsOf]
      exact (List.nodup_finRange _).map fun first second same =>
        congrArg Prod.snd (maskCell_injective lane chunk (a₁ := (switch, first))
          (a₂ := (switch, second)) same)
  · refine (List.nodup_finRange (2 ^ chunkWidth chunk)).pairwise_of_forall_ne
      fun first _ second _ different => ?_
    simp only [Function.onFun]
    split
    · simp
    · split
      · simp
      · rw [← touchedCells, ← touchedCells, cellsOf, cellsOf]
        simp only [List.disjoint_left, List.mem_map, List.mem_finRange, true_and]
        rintro _ ⟨limb, rfl⟩ ⟨limb', same⟩
        exact different (congrArg Prod.fst (maskCell_injective lane chunk (a₁ := (second, limb'))
          (a₂ := (first, limb)) same)).symm

/-! ### The tape runner succeeds -/

/-- **The masks run on the tape** when every non-designated mask query is a first touch of its
cell at an unknown input. -/
theorem masks_detRun_ne_none (lane : Lane) (chunk : Fin chunkCount)
    (hot : HotLabels (chunkWidth chunk)) (alpha : Fin (2 ^ chunkWidth chunk)) (oracle : LState)
    (record : Record) (touched : Set Cell)
    (untouched : ∀ switch, switch ≠ alpha → ∀ limb : Fin (limbCount lane),
      ¬ IsDesignated bits (cellInput (maskCell lane chunk switch limb) (hot switch)) →
        maskCell lane chunk switch limb ∉ touched)
    (fresh : ∀ switch, switch ≠ alpha → ∀ limb : Fin (limbCount lane),
      ¬ IsDesignated bits (cellInput (maskCell lane chunk switch limb) (hot switch)) →
        oracle.hash.lookup (cellInput (maskCell lane chunk switch limb) (hot switch)) = none) :
    detRun bits tape (Programs.evalMasksM lane chunk (chunkWidth chunk) hot alpha) oracle
      record touched ≠ none := by
  refine detRun_ne_none bits tape _ oracle record touched (fun request member => ?_)
    ((consumed_sublist bits _).nodup (touchedCells_nodup lane chunk hot alpha _))
  obtain ⟨switch, active, limb, rfl⟩ :=
    mem_queriesAlong_evalMasksM _ lane chunk hot alpha request member
  by_cases designated : IsDesignated bits (cellInput (maskCell lane chunk switch limb) (hot switch))
  · exact Or.inl designated
  · exact Or.inr ⟨maskCell lane chunk switch limb, cellOf_cellInput _ _,
      untouched switch active limb designated, fresh switch active limb designated⟩

/-! ### The value is the tape's -/

/-- **The mask values on the tape**: `sampleLane` of the tape's answers at each inactive switch's
cells, zeros at the active switch. They do not depend on the labels. -/
def maskValues (lane : Lane) (chunk : Fin chunkCount) (alpha : Fin (2 ^ chunkWidth chunk)) :
    Fin (2 ^ chunkWidth chunk) → Vector BaseField (laneCount lane) :=
  fun switch => if switch = alpha then Vector.ofFn fun _ => 0 else
    Vector.ofFn (sampleLane (laneCount lane) (limbCount lane) fun limb =>
      tape (maskCell lane chunk switch limb))

/-- **(b) The masks' value on the tape is `maskValues`, whatever the labels**, when none of their
queries is designated. -/
theorem masks_value (lane : Lane) (chunk : Fin chunkCount) (hot : HotLabels (chunkWidth chunk))
    (alpha : Fin (2 ^ chunkWidth chunk))
    (plain : ∀ switch limb, ¬ IsDesignated bits
      (cellInput (maskCell lane chunk switch limb) (hot switch))) :
    FreeQuery.eval (tapeAnswer bits tape)
        (Programs.evalMasksM lane chunk (chunkWidth chunk) hot alpha) =
      maskValues tape lane chunk alpha := by
  funext switch
  simp only [Programs.evalMasksM, FreeQuery.eval_bind, FreeQuery.eval_vector, FreeQuery.eval_pure,
    Vector.get_ofFn, maskValues]
  split
  · rfl
  · simp only [Programs.switchMaskM, FreeQuery.eval_bind, FreeQuery.eval_vector,
      FreeQuery.eval_pure]
    congr 1
    refine congrArg (sampleLane (laneCount lane) (limbCount lane)) (funext fun limb => ?_)
    rw [Vector.get_ofFn, eval_askHash_answer, tapeAnswer_hash,
      tapeHash_scale bits tape lane chunk switch limb (hot switch) (plain switch limb)]

end Masks

end

end Kriterion.ArgoMAC.Phase3.Lazy
