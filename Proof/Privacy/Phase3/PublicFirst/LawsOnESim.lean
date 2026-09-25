/-
**Phase 3, P1r — `LawOn`, step (E), part 13: the private side's pieces.**

* `revealWeight_le`: the reveal flag contains `Exact0` (`exact0_reveal`), so the private weight is at
  most the `Exact0`-indicator weight;
* `solved_link`: D's designated vector (the free coordinates the tape's own, the collectors solved
  at the opening's value) is the designated vector of the tape's free coordinates and
  `simDesignated`;
* `installed_view`: the installed tape's view limbs are the tape's at the other view sites and the
  drawn limbs at the designated one (`joinV`);
* `inner_O`: the view of the installed overlay, averaged over the uniform oracle, is the view kernel
  averaged over uniform EncPRF permutations, hash off the scale range and view answers.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEGarb

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source collectorElement solvedVector designatedVector
  DesignatedLimbs)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (input : AffineInput)

/-! ### 1. The reveal flag contains `Exact0` -/

theorem exact0_reveal (source : Stage1Source) (coins : Coins) (Δ : EncPRF.Coordinate → Block) (state : LState)
    (h : Exact0 scalar input coins.offsets) : revealOnPred scalar source input coins Δ state := by
  obtain ⟨o, phi, found, kind, agree⟩ := h
  have restored : (Lamport.restore input (sourceLabels source input)).input = BitInput.ofAffine input := by
    rw [Kriterion.ArgoMAC.Phase3.Lazy.restore_selectedLabels]
  unfold revealOnPred
  refine ⟨o, phi, found, kind, fun c p => ?_⟩
  rw [restored]
  exact Or.inl ((agree c p).resolve_right id)

open Classical in
theorem revealWeight_le (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (source : Stage1Source)
    (coins : Coins) (Δ : EncPRF.Coordinate → Block) (state : LState) :
    OnLaw.revealWeight scalar source input coins Δ Ψ state ≤
      if Exact0 scalar input coins.offsets then 0 else Ψ source.publicValue (sourceLabels source input) state := by
  unfold OnLaw.revealWeight
  by_cases h : Exact0 scalar input coins.offsets
  · have r := exact0_reveal scalar input source coins Δ state h
    simp [r, h]
  · rw [if_neg h]
    split_ifs
    · exact zero_le
    · exact le_rfl

/-! ### 2. The designated vector -/

/-- **The private side's designated masks**: F4's collector solve at the coins' true rows. -/
def desT (coins : Coins) (cells : PublicCells) (vis : VisibleCells (offShape input)) : DSite → BaseField :=
  fun dc => simDesignated (offShape input) (rowTarget (rowsAt scalar coins dc.1) input) (cells.1 dc.1).1
    (cells.1 dc.1).2 (vis.1 dc.1) (.inl (collectorElement dc.2))

/-- **D's designated vector is F4's**: the tape's free coordinates, and the collectors solved at the
true rows from the cells and the tape's visible masks. -/
theorem solved_link (cells : PublicCells) (key : InputMacKey) (T : Tape) (O : Oracle) (coins : Coins)
    (xNe : input.x ≠ 0) :
    solvedVector (cellsSource cells key).publicValue (BitInput.ofAffine input)
        ((Kriterion.ArgoMAC.Phase3.Glue.openingQueriesM (cellsSource cells key).publicValue
          (BitInput.ofAffine input) ((cellsSource cells key).key.encode (BitInput.ofAffine input))).eval
          (publicAnswer (OnLaw.overlay (OnLaw.zeroDesig (BitInput.ofAffine input) T) O))).1
        ((Kriterion.ArgoMAC.Phase3.Glue.openingQueriesM (cellsSource cells key).publicValue
          (BitInput.ofAffine input) ((cellsSource cells key).key.encode (BitInput.ofAffine input))).eval
          (publicAnswer (OnLaw.overlay (OnLaw.zeroDesig (BitInput.ofAffine input) T) O))).2
        (freeOf input T) (fun digit => trueRows scalar coins input digit) =
      designatedVector (freeOf input T)
        (desT scalar input coins cells (visPart input (maskCoordEquiv (masksOf VectorSite.lane T)))) := by
  unfold solvedVector
  congr 1
  funext dc
  exact targets_eq input scalar cells key _ T O coins dc.1 dc.2 xNe

/-- The designated vector of the tape's free coordinates is the designated view site's vector. -/
theorem designatedVector_view (T : Tape) (des : DSite → BaseField) :
    designatedVector (freeOf input T) des =
      siteVector input (Sum.elim (visEquiv input (visPart input (maskCoordEquiv (masksOf VectorSite.lane T))))
        des) (dsiteV input) := by
  rw [siteVector_dsite]
  rfl

/-! ### 3. The installed tape at the view -/

/-- **The view's limbs from the other view sites' and the designated site's.** -/
def joinV (bdn : ∀ s : VSiteN input, Fin (limbCount s.1.1.lane) → Block × Block) (limbs : DesignatedLimbs) :
    VLimbs input :=
  (Equiv.piSplitAt (dsiteV input) fun s : VSite input => Fin (limbCount s.1.lane) → Block × Block).symm
    (limbs, bdn)

theorem installed_view (T : Tape) (limbs : DesignatedLimbs) :
    (fun (s : VSite input) limb => OnLaw.installTape (BitInput.ofAffine input) T limbs ⟨s.1, limb⟩) =
      joinV input (fun s limb => T ⟨s.1.1, limb⟩) limbs := by
  funext s limb
  unfold joinV
  rw [Equiv.piSplitAt_symm_apply]
  by_cases here : s = dsiteV input
  · subst here
    rw [dif_pos rfl]
    exact OnLaw.installTape_designated _ T limbs limb
  · rw [dif_neg here]
    exact OnLaw.installTape_other _ T limbs _ fun same => here (Subtype.ext same)

/-! ### 4. The oracle -/

/-- **The installed overlay's view, averaged over the uniform oracle.** -/
theorem inner_O (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (cells : PublicCells) (key : InputMacKey)
    (T : Tape) (limbs : DesignatedLimbs) :
    ∑' O, PMF.uniformOfFintype Oracle O *
        Ψ (cellsSource cells key).publicValue (sourceLabels (cellsSource cells key) input)
          (OnLaw.onView (cellsSource cells key).publicValue (BitInput.ofAffine input)
            ((cellsSource cells key).key.encode (BitInput.ofAffine input))
            (OnLaw.overlay (OnLaw.installTape (BitInput.ofAffine input) T limbs) O)) =
      ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
        ∑' H, PMF.uniformOfFintype OtherTable H * ∑' x, PMF.uniformOfFintype (VO input → Block) x *
          onKW input Ψ (cellsSource cells key).publicValue key E H x
            (joinV input (fun s limb => T ⟨s.1.1, limb⟩) limbs) := by
  unfold OnLaw.onView
  rw [overlay_uniform input _ _ _ (fun state => Ψ (cellsSource cells key).publicValue
    (sourceLabels (cellsSource cells key) input) state)]
  refine tsum_congr fun E => congrArg _ (tsum_congr fun H => congrArg _ ?_)
  have view : ∀ v : FixedIndex → Block,
      Ψ (cellsSource cells key).publicValue (sourceLabels (cellsSource cells key) input)
        (plantAll (transcript (tableAnswer (E, H, v, OnLaw.installTape (BitInput.ofAffine input) T limbs))
          (shadowOnM (cellsSource cells key).publicValue (BitInput.ofAffine input)
            ((cellsSource cells key).key.encode (BitInput.ofAffine input)))) LazyOracle.empty) =
      onKW input Ψ (cellsSource cells key).publicValue key E H (fun i => v i.1)
        (joinV input (fun s limb => T ⟨s.1.1, limb⟩) limbs) := by
    intro v
    show onK input Ψ _ key (E, H, v, _) = _
    rw [onK_view, onKV_tape, installed_view]
  simp only [view]
  exact tsum_restrict (fun i : VO input => i.1) Subtype.val_injective
    (fun x => onKW input Ψ (cellsSource cells key).publicValue key E H x
      (joinV input (fun s limb => T ⟨s.1.1, limb⟩) limbs))

/-! ### 5. The coins' offsets and `ρ` -/

omit [GroupCertificate] in
theorem rowsGet (keys : OutputKeys) (R : Randomness) (i : Fin digitCount) :
    (FieldMacToECMac.rowsForOutputKeys keys R).get i =
      Coordinates.rows (keys.get i).offset.coordinates (digitEndomorphismBase (keys.get i).digit)
        (R.get i).rho.value (R.get i).tau.value := by
  unfold FieldMacToECMac.rowsForOutputKeys
  exact Vector.get_ofFn _ i

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
