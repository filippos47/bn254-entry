/-
**Phase 3, P1p — `LawOn`, step (D), part 2: `HW`'s opening asks each limb at most once.**

`CellOnce` is closed under `bind` (disjoint limb sets) and monotone; a computation asking each
fixed-key index and each limb at most once (P1l's `OnceIn`) asks each limb at most once
(`cellOnce_of_onceIn`), and a computation asking only EncPRF questions and hash questions off the
scale range asks none (`cellOnce_of_plain`). Hence **`cellOnce_opening`**: `HW`'s opening
(`openingQueriesM`: the four lanes, the bridge hash at `bridgeInput`, the bit-`false` pads) asks each
limb at most once, so `refill_eager` applies to it from the empty oracle (`opening_eager`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnRefill

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion openingQueriesM whitePadsM)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape Record runRefill)
open scoped ENNReal

noncomputable section

/-! ### `CellOnce` is closed under binds -/

section Tools

theorem CellOnce.mono {α : Type} {Y Y' : Set Cell} {c : FreeQuery Programs.Spec α}
    (once : CellOnce Y c) (sub : Y ⊆ Y') : CellOnce Y' c := by
  induction once generalizing Y' with
  | pure Y value => exact .pure Y' value
  | cell Y cell label next inside rest ih =>
      exact .cell Y' cell label next (sub inside) fun a => ih a (Set.sdiff_subset_sdiff_left sub)
  | other Y request next plain rest ih =>
      exact .other Y' request next plain fun a => ih a sub

theorem CellOnce.bind {α β : Type} {Y Y' : Set Cell} {c : FreeQuery Programs.Spec α}
    {f : α → FreeQuery Programs.Spec β} (first : CellOnce Y c) (second : ∀ a, CellOnce Y' (f a))
    (disjoint : Disjoint Y Y') : CellOnce (Y ∪ Y') (c >>= f) := by
  revert disjoint
  induction first with
  | pure Y value => exact fun _ => (second value).mono Set.subset_union_right
  | cell Y cell label next inside rest ih =>
      intro disjoint
      have notY' : cell ∉ Y' := fun hit => Set.disjoint_left.mp disjoint inside hit
      show CellOnce (Y ∪ Y') (FreeQuery.query (PublicQuery.hash (Kriterion.ArgoMAC.Phase3.Lazy.cellInput
        cell label)) fun answer => next answer >>= f)
      refine .cell (Y ∪ Y') cell label (fun answer => next answer >>= f) (Or.inl inside)
        fun answer => ?_
      rw [diff_union_of_not_mem notY']
      exact ih answer (Set.disjoint_of_subset_left Set.sdiff_subset disjoint)
  | other Y request next plain rest ih =>
      intro disjoint
      show CellOnce (Y ∪ Y') (FreeQuery.query request fun answer => next answer >>= f)
      exact .other (Y ∪ Y') request (fun answer => next answer >>= f) plain
        fun answer => ih answer disjoint

/-- **A fixed-key-and-limb-once computation asks each limb at most once.** -/
theorem cellOnce_of_onceIn {α : Type} {X : Set FixedIndex} {Y : Set Cell}
    {c : FreeQuery Programs.Spec α} (once : OnceIn X Y c) : CellOnce Y c := by
  induction once with
  | pure X Y value => exact .pure _ value
  | fixed X Y index input next inside rest ih =>
      exact .other _ _ next ⟨fun key same => (by cases same), trivial⟩ ih
  | cell X Y cell label next inside rest ih => exact .cell _ cell label next inside ih

/-- **A computation of plain questions asks no limb.** -/
theorem cellOnce_of_plain {α : Type} (Y : Set Cell) {c : FreeQuery Programs.Spec α}
    (plain : Hidden.QueryOnly Plain c) : CellOnce Y c := by
  induction plain with
  | pure value => exact .pure Y value
  | query request next holds rest ih => exact .other Y request next holds ih

theorem plain_enc (index : EncPRF.PermutationIndex) (x : Block) : Plain (.encForward index x) :=
  ⟨fun _ same => (by cases same), trivial⟩

/-- The bridge hash is off the scale range. -/
theorem plain_bridge (t : BaseField) : Plain (.hash (bridgeInput t)) := by
  refine ⟨fun key same => ?_, trivial⟩
  cases same
  exact cellOf_of_not_lt _ (bridgeInput_not_lt t)

theorem whitePadsM_plain (keys : WhiteningKeys) : Hidden.QueryOnly Plain (whitePadsM keys) := by
  have pad : ∀ coordinate index, Hidden.QueryOnly Plain (Programs.padM keys coordinate index false) :=
    fun _ _ => Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ (plain_enc _ _)) fun _ =>
      Hidden.QueryOnly.pure' _
  unfold whitePadsM
  exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _) fun _ =>
    Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _) fun _ =>
      Hidden.QueryOnly.pure' _

theorem onceCellSet_disjoint {lane lane' : Lane} (different : lane ≠ lane') :
    Disjoint (onceCellSet lane) (onceCellSet lane') := by
  rw [Set.disjoint_left]
  intro cell left right
  exact different (left.symm.trans right)

end Tools

/-! ### The opening -/

section Opening

variable [FieldCertificate]

/-- **`HW`'s opening asks each limb at most once.** -/
theorem cellOnce_opening (table : Public) (bits : BitInput) (mac : InputMac) :
    CellOnce Set.univ (openingQueriesM table bits mac) := by
  have lane : ∀ (ℓ : Lane) joins scale word labels,
      CellOnce (onceCellSet ℓ) (Programs.evalLaneM ℓ joins scale word labels) :=
    fun ℓ joins scale word labels => cellOnce_of_onceIn (once_evalLaneM ℓ joins scale word labels)
  unfold openingQueriesM
  refine (CellOnce.bind (lane .curveX _ _ _ _) (fun _ =>
    CellOnce.bind (lane .curveY _ _ _ _) (fun _ =>
      CellOnce.bind (cellOnce_of_plain ∅ (Hidden.QueryOnly.ask _ (plain_bridge _))) (fun _ =>
        CellOnce.bind (cellOnce_of_plain ∅ (whitePadsM_plain _)) (fun _ =>
          CellOnce.bind (lane .pointX _ _ _ _) (fun _ =>
            CellOnce.bind (lane .pointY _ _ _ _) (fun _ => .pure ∅ _)
              (Set.disjoint_empty _)) ?_) (Set.disjoint_left.mpr fun _ h => h.elim))
        (Set.disjoint_left.mpr fun _ h => h.elim)) ?_) ?_).mono (Set.subset_univ _)
  · rw [Set.union_empty]
    exact onceCellSet_disjoint (by decide)
  · rw [Set.empty_union, Set.empty_union, Set.disjoint_union_right, Set.union_empty]
    exact ⟨onceCellSet_disjoint (by decide), onceCellSet_disjoint (by decide)⟩
  · rw [Set.disjoint_union_right, Set.disjoint_union_right, Set.disjoint_union_right,
      Set.disjoint_union_right, Set.union_empty]
    exact ⟨onceCellSet_disjoint (by decide), Set.disjoint_empty _, Set.disjoint_empty _,
      onceCellSet_disjoint (by decide), onceCellSet_disjoint (by decide)⟩

variable [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
  [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **`HW`'s refill opening from the empty oracle, eager**: a uniform oracle overlaid by the tape
(designated limbs zeroed), its non-designated transcript planted on the empty oracle, the
designated labels recorded. -/
theorem opening_eager (bits : BitInput) (T : Tape) (table : Public) (mac : InputMac)
    (F : Option (((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record) → ℝ≥0∞)
    (invariant : ∀ a t t' r, SameLookups t t' → F (some (a, t, r)) = F (some (a, t', r))) :
    ∑' o, runRefill bits (fun cell => PMF.pure (T cell)) (openingQueriesM table bits mac)
        LazyOracle.empty Kriterion.ArgoMAC.Phase3.Glue.noRecord ∅ o * F o =
      ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
        F (some ((openingQueriesM table bits mac).eval (publicAnswer (overlay (zeroDesig bits T) O)),
          plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O))
            (openingQueriesM table bits mac)).filter (notDesig bits)) LazyOracle.empty,
          recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O))
            (openingQueriesM table bits mac)) Kriterion.ArgoMAC.Phase3.Glue.noRecord)) := by
  rw [refill_eager bits T (cellOnce_opening table bits mac) LazyOracle.empty
    Kriterion.ArgoMAC.Phase3.Glue.noRecord ∅ (fun _ _ _ => rfl) (fun _ _ member => member.elim)
    F invariant, Kriterion.ArgoMAC.Phase3.Glue.public_initial]

end Opening

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
