/-
**Phase 3, P1s — `LawOn`, step (E), part 15: the private side is at most the core; `OnJoint`.**

* `privSrc`, `privBound`, **`priv_le_bound`**: `onPrivForm` with the designated draws spelled out
  (`tsum_designatedLimbs`), the reveal weight bounded by the `Exact0` indicator (`revealWeight_le`)
  and `deltaLaw` summed out;
* **`privSrc_freeOf`**: the designated vector's free coordinates are the tape's own (`tsum_freeOf`:
  the private side reads the tape off the designated vector site only);
* **`oracle_step`**: at a source of cells, the designated vector is the tape's free coordinates and
  F4's collector solve (`solved_link`), and the uniform oracle is the view kernel's EncPRF
  permutations, hash off the scale range and view answers (`inner_O`);
* **`tape_step`**: the mask tape at the view is uniform visible cells and the limb laws of the other
  view sites (`sim_tape`, `visEquiv`);
* **`privSrc_cells`**: the private side at a source of cells, the coins read as offsets and `ρ`s
  (`coins_bd`);
* **`priv_le_core`**: `onPrivForm ≤ onCore` (`tsum_source_cells`, `reorder_core`, `tsum_views_join`);
* **`onJoint_global`**, **`onJoint`**: step (E), `OnLaw.OnJoint scalar input`, at every valid input
  (the garbler's side: `realCore_eq`, `realCore_le`, `onGarbForm_eq`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEPriv

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source collectorElement openingQueriesM solvedVector FreeSite
  DesignatedLimbs)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState uniformMaskTape)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (input : AffineInput)

/-! ### 1. The reveal weight bounded by the `Exact0` indicator -/

/-- The opening's value on the overlaid oracle with the designated vector zeroed. -/
def openVal (source : Stage1Source) (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField) :=
  FreeQuery.eval (publicAnswer (OnLaw.overlay (OnLaw.zeroDesig (BitInput.ofAffine input) T) O))
    (openingQueriesM source.publicValue (BitInput.ofAffine input)
      (source.key.encode (BitInput.ofAffine input)))

open Classical in
/-- The private side at a source, the designated draws spelled out, the reveal weight bounded by
the `Exact0` indicator. -/
def privSrc (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (source : Stage1Source) : ℝ≥0∞ :=
  ∑' T, uniformMaskTape T *
    ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
      ∑' coins, PMF.uniformOfFintype Coins coins *
        ∑' free, PMF.uniformOfFintype (FreeSite → BaseField) free *
          ∑' limbs, siteFibreLaw .pointX (solvedVector source.publicValue (BitInput.ofAffine input)
              (openVal input source T O).1 (openVal input source T O).2 free
              (fun digit => trueRows scalar coins input digit)) limbs *
            (if Exact0 scalar input coins.offsets then 0 else
              Ψ source.publicValue (sourceLabels source input)
                (OnLaw.onView source.publicValue (BitInput.ofAffine input)
                  (source.key.encode (BitInput.ofAffine input))
                  (OnLaw.overlay (OnLaw.installTape (BitInput.ofAffine input) T limbs) O)))

/-- The private side, the reveal weight bounded by the `Exact0` indicator. -/
def privBound (Ψ : Public → LamportSignature → LState → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' source, PMF.uniformOfFintype Stage1Source source * privSrc scalar input Ψ source

/-- **The private side is at most its `Exact0`-indicator bound.** -/
theorem priv_le_bound (Ψ : Public → LamportSignature → LState → ℝ≥0∞) :
    OnLaw.onPrivForm scalar input Ψ ≤ privBound scalar input Ψ := by
  unfold OnLaw.onPrivForm privBound privSrc OnLaw.mergeK OnLaw.limbsOf
  refine ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun T =>
    mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun O => mul_le_mul' le_rfl (ENNReal.tsum_le_tsum
      fun coins => mul_le_mul' le_rfl ?_)))
  rw [tsum_designatedLimbs]
  refine ENNReal.tsum_le_tsum fun free => mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun limbs =>
    mul_le_mul' le_rfl ?_)
  exact le_trans (ENNReal.tsum_le_tsum fun delta => mul_le_mul' le_rfl
    (revealWeight_le scalar input Ψ source coins delta _)) (le_of_eq (tsum_pmf_const deltaLaw _))

/-! ### 2. The free coordinates, the oracle, the tape, the coins -/

omit [FieldCertificate] [GroupCertificate] in
/-- The innermost of three averages moved outermost. -/
theorem swap3 {α β γ : Type} (μ : α → ℝ≥0∞) (ν : β → ℝ≥0∞) (ρ : γ → ℝ≥0∞) (K : α → β → γ → ℝ≥0∞) :
    ∑' a, μ a * ∑' b, ν b * ∑' c, ρ c * K a b c = ∑' c, ρ c * ∑' a, μ a * ∑' b, ν b * K a b c := by
  rw [tsum_congr fun a => congrArg (μ a * ·) (tsum_swap_mul ν ρ (K a)), tsum_swap_mul μ ρ]

theorem zeroDesig_offD (T T' : Tape)
    (agree : ∀ cell : Cell, cell.1 ≠ OnLaw.designatedSite (BitInput.ofAffine input) → T cell = T' cell) :
    OnLaw.zeroDesig (BitInput.ofAffine input) T = OnLaw.zeroDesig (BitInput.ofAffine input) T' := by
  funext cell
  unfold OnLaw.zeroDesig
  split_ifs with here
  · rfl
  · exact agree cell here

theorem installTape_offD (T T' : Tape) (limbs : DesignatedLimbs)
    (agree : ∀ cell : Cell, cell.1 ≠ OnLaw.designatedSite (BitInput.ofAffine input) → T cell = T' cell) :
    OnLaw.installTape (BitInput.ofAffine input) T limbs = OnLaw.installTape (BitInput.ofAffine input) T' limbs := by
  funext cell
  unfold OnLaw.installTape
  split_ifs with here
  · rfl
  · exact agree cell here

open Classical in
/-- **The designated vector's free coordinates are the tape's own.** -/
theorem privSrc_freeOf (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (source : Stage1Source) :
    privSrc scalar input Ψ source =
      ∑' T, uniformMaskTape T *
        ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
          ∑' coins, PMF.uniformOfFintype Coins coins *
            ∑' limbs, siteFibreLaw .pointX (solvedVector source.publicValue (BitInput.ofAffine input)
                (openVal input source T O).1 (openVal input source T O).2 (freeOf input T)
                (fun digit => trueRows scalar coins input digit)) limbs *
              (if Exact0 scalar input coins.offsets then 0 else
                Ψ source.publicValue (sourceLabels source input)
                  (OnLaw.onView source.publicValue (BitInput.ofAffine input)
                    (source.key.encode (BitInput.ofAffine input))
                    (OnLaw.overlay (OnLaw.installTape (BitInput.ofAffine input) T limbs) O))) := by
  let F : Tape → (FreeSite → BaseField) → ℝ≥0∞ := fun T free =>
    ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
      ∑' coins, PMF.uniformOfFintype Coins coins *
        ∑' limbs, siteFibreLaw .pointX (solvedVector source.publicValue (BitInput.ofAffine input)
            (openVal input source T O).1 (openVal input source T O).2 free
            (fun digit => trueRows scalar coins input digit)) limbs *
          (if Exact0 scalar input coins.offsets then 0 else
            Ψ source.publicValue (sourceLabels source input)
              (OnLaw.onView source.publicValue (BitInput.ofAffine input)
                (source.key.encode (BitInput.ofAffine input))
                (OnLaw.overlay (OnLaw.installTape (BitInput.ofAffine input) T limbs) O)))
  have offD : ∀ T T' free, (∀ cell : Cell, cell.1 ≠ OnLaw.designatedSite (BitInput.ofAffine input) →
      T cell = T' cell) → F T free = F T' free := by
    intro T T' free agree
    have value : ∀ O, openVal input source T O = openVal input source T' O := fun O => by
      unfold openVal
      rw [zeroDesig_offD input T T' agree]
    have installed : ∀ limbs, OnLaw.installTape (BitInput.ofAffine input) T limbs =
        OnLaw.installTape (BitInput.ofAffine input) T' limbs := fun limbs =>
      installTape_offD input T T' limbs agree
    simp only [F, value, installed]
  have swapped : privSrc scalar input Ψ source =
      ∑' T, uniformMaskTape T * ∑' free, PMF.uniformOfFintype (FreeSite → BaseField) free * F T free := by
    unfold privSrc
    refine tsum_congr fun T => congrArg _ ?_
    exact swap3 _ _ _ _
  rw [swapped, tsum_freeOf input F offD]

open Classical in
/-- **The oracle at a source of cells**: the designated vector is the tape's free coordinates and
F4's collector solve, the uniform oracle is the view kernel's. -/
theorem oracle_step (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (cells : PublicCells)
    (key : InputMacKey) (T : Tape) (xNe : input.x ≠ 0) :
    ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
      ∑' coins, PMF.uniformOfFintype Coins coins *
        ∑' limbs, siteFibreLaw .pointX (solvedVector (cellsSource cells key).publicValue
            (BitInput.ofAffine input) (openVal input (cellsSource cells key) T O).1
            (openVal input (cellsSource cells key) T O).2 (freeOf input T)
            (fun digit => trueRows scalar coins input digit)) limbs *
          (if Exact0 scalar input coins.offsets then 0 else
            Ψ (cellsSource cells key).publicValue (sourceLabels (cellsSource cells key) input)
              (OnLaw.onView (cellsSource cells key).publicValue (BitInput.ofAffine input)
                ((cellsSource cells key).key.encode (BitInput.ofAffine input))
                (OnLaw.overlay (OnLaw.installTape (BitInput.ofAffine input) T limbs) O))) =
    ∑' coins, PMF.uniformOfFintype Coins coins *
      ∑' limbs, siteFibreLaw .pointX (siteVector input (Sum.elim
          (visEquiv input (visPart input (maskCoordEquiv (masksOf VectorSite.lane T))))
          (desT scalar input coins cells (visPart input (maskCoordEquiv (masksOf VectorSite.lane T)))))
          (dsiteV input)) limbs *
        (if Exact0 scalar input coins.offsets then 0 else
          ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
            ∑' H, PMF.uniformOfFintype OtherTable H * ∑' x, PMF.uniformOfFintype (VO input → Block) x *
              onKW input Ψ (cellsSource cells key).publicValue key E H x
                (joinV input (fun s limb => T ⟨s.1.1, limb⟩) limbs)) := by
  have designated : ∀ (O : PublicOracle FixedIndex EncPRF.PermutationIndex) (coins : Coins),
      solvedVector (cellsSource cells key).publicValue (BitInput.ofAffine input)
          (openVal input (cellsSource cells key) T O).1 (openVal input (cellsSource cells key) T O).2
          (freeOf input T) (fun digit => trueRows scalar coins input digit) =
        siteVector input (Sum.elim (visEquiv input (visPart input (maskCoordEquiv (masksOf VectorSite.lane T))))
          (desT scalar input coins cells (visPart input (maskCoordEquiv (masksOf VectorSite.lane T)))))
          (dsiteV input) := fun O coins => by
    rw [← designatedVector_view]
    exact solved_link scalar input cells key T O coins xNe
  simp only [designated]
  rw [tsum_swap_mul]
  refine tsum_congr fun coins => congrArg _ ?_
  rw [tsum_swap_mul]
  refine tsum_congr fun limbs => congrArg _ ?_
  rw [tsum_mul_ite_zero, inner_O]

open Classical in
/-- **The mask tape at the view**: uniform visible cells, and the limb laws of the other view sites. -/
theorem tape_step (cells : PublicCells)
    (Z : (∀ s : VSiteN input, Fin (limbCount s.1.1.lane) → Block × Block) → DesignatedLimbs → ℝ≥0∞) :
    ∑' T, uniformMaskTape T * ∑' coins, PMF.uniformOfFintype Coins coins *
        ∑' limbs, siteFibreLaw .pointX (siteVector input (Sum.elim
            (visEquiv input (visPart input (maskCoordEquiv (masksOf VectorSite.lane T))))
            (desT scalar input coins cells (visPart input (maskCoordEquiv (masksOf VectorSite.lane T)))))
            (dsiteV input)) limbs *
          (if Exact0 scalar input coins.offsets then 0 else Z (fun s limb => T ⟨s.1.1, limb⟩) limbs) =
      ∑' vis, PMF.uniformOfFintype (VisibleCells (offShape input)) vis *
        ∑' bdn, piPMF (fun s : VSiteN input =>
            siteFibreLaw s.1.1.lane (siteVector input (Sum.elim (visEquiv input vis) 0) s.1)) bdn *
          ∑' coins, PMF.uniformOfFintype Coins coins *
            ∑' limbs, siteFibreLaw .pointX (siteVector input (Sum.elim (visEquiv input vis)
                (desT scalar input coins cells vis)) (dsiteV input)) limbs *
              (if Exact0 scalar input coins.offsets then 0 else Z bdn limbs) := by
  have visEq : ∀ T : Tape, visPart input (maskCoordEquiv (masksOf VectorSite.lane T)) =
      (visEquiv input).symm (maskCoordEquiv (masksOf VectorSite.lane T) ∘ visSite input) := by
    intro T
    rw [masks_visSite, Equiv.symm_apply_apply]
  simp only [visEq]
  rw [sim_tape input (fun μ bdn => ∑' coins, PMF.uniformOfFintype Coins coins *
    ∑' limbs, siteFibreLaw .pointX (siteVector input (Sum.elim (visEquiv input ((visEquiv input).symm μ))
        (desT scalar input coins cells ((visEquiv input).symm μ))) (dsiteV input)) limbs *
      (if Exact0 scalar input coins.offsets then 0 else Z bdn limbs))]
  rw [tsum_equiv_uniform (visEquiv input).symm]
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply]

open Classical in
/-- **The private side at a source of cells.** -/
theorem privSrc_cells (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (cells : PublicCells)
    (key : InputMacKey) (xNe : input.x ≠ 0) :
    privSrc scalar input Ψ (cellsSource cells key) =
      ∑' vis, PMF.uniformOfFintype (VisibleCells (offShape input)) vis *
        ∑' bdn, piPMF (fun s : VSiteN input =>
            siteFibreLaw s.1.1.lane (siteVector input (Sum.elim (visEquiv input vis) 0) s.1)) bdn *
          ∑' K, PMF.uniformOfFintype ClampedOffsets K *
            ∑' ρ, PMF.uniformOfFintype (Fin digitCount → NonZeroBase × NonZeroBase) ρ *
              ∑' limbs, siteFibreLaw .pointX (siteVector input (Sum.elim (visEquiv input vis)
                  (desK scalar input K ρ cells vis)) (dsiteV input)) limbs *
                (if Exact0 scalar input K.1 then 0 else
                  ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
                    ∑' H, PMF.uniformOfFintype OtherTable H *
                      ∑' x, PMF.uniformOfFintype (VO input → Block) x *
                        onKW input Ψ (cellsSource cells key).publicValue key E H x (joinV input bdn limbs)) := by
  rw [privSrc_freeOf]
  rw [tsum_congr fun T => congrArg _ (oracle_step scalar input Ψ cells key T xNe)]
  rw [tape_step scalar input cells (fun bdn limbs =>
    ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
      ∑' H, PMF.uniformOfFintype OtherTable H * ∑' x, PMF.uniformOfFintype (VO input → Block) x *
        onKW input Ψ (cellsSource cells key).publicValue key E H x (joinV input bdn limbs))]
  refine tsum_congr fun vis => congrArg _ (tsum_congr fun bdn => congrArg _ ?_)
  exact coins_bd scalar input cells vis _

/-! ### 3. The private side is at most the core; step (E) -/

/-- **The view's limbs are the other view sites' and the designated site's**, with the product of
their laws. -/
theorem tsum_views_join (vis : VisibleCells (offShape input)) (des : DSite → BaseField)
    (f : VLimbs input → ℝ≥0∞) :
    ∑' bdn, piPMF (fun s : VSiteN input =>
        siteFibreLaw s.1.1.lane (siteVector input (Sum.elim (visEquiv input vis) 0) s.1)) bdn *
      ∑' limbs, siteFibreLaw .pointX (siteVector input (Sum.elim (visEquiv input vis) des)
          (dsiteV input)) limbs * f (joinV input bdn limbs) =
      ∑' bd, viewWeight input (Sum.elim (visEquiv input vis) des) bd * f bd := by
  unfold viewWeight
  rw [tsum_piPMF_split _ (dsiteV input), tsum_swap_mul]
  refine tsum_congr fun limbs => congrArg _ (tsum_congr fun bdn => ?_)
  congr 1
  exact congrArg (fun law : PMF _ => law bdn) (congrArg piPMF (funext fun s =>
    congrArg _ (siteVector_other input _ 0 des s.1 s.2)))

/-- **The private side is at most the core.** -/
theorem priv_le_core (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (xNe : input.x ≠ 0) :
    OnLaw.onPrivForm scalar input Ψ ≤ onCore scalar input Ψ := by
  refine le_trans (priv_le_bound scalar input Ψ) (le_of_eq ?_)
  unfold privBound
  rw [tsum_source_cells]
  simp only [privSrc_cells scalar input Ψ _ _ xNe]
  unfold onCore coreKEH
  exact reorder_core (fun K : ClampedOffsets => Exact0 scalar input K.1)
    (PMF.uniformOfFintype PublicCells) (PMF.uniformOfFintype InputMacKey)
    (PMF.uniformOfFintype (VisibleCells (offShape input)))
    (fun vis bdn => piPMF (fun s : VSiteN input =>
      siteFibreLaw s.1.1.lane (siteVector input (Sum.elim (visEquiv input vis) 0) s.1)) bdn)
    (PMF.uniformOfFintype ClampedOffsets) (PMF.uniformOfFintype (Fin digitCount → NonZeroBase × NonZeroBase))
    (fun K ρ cells vis limbs => siteFibreLaw .pointX (siteVector input (Sum.elim (visEquiv input vis)
      (desK scalar input K ρ cells vis)) (dsiteV input)) limbs)
    (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block))
    (PMF.uniformOfFintype OtherTable) (PMF.uniformOfFintype (VO input → Block))
    (fun cells key E H x bdn limbs =>
      onKW input Ψ (cellsSource cells key).publicValue key E H x (joinV input bdn limbs))
    (fun K E H cells vis ρ key x =>
      ∑' bd, viewWeight input (Sum.elim (visEquiv input vis) (desK scalar input K ρ cells vis)) bd *
        onKW input Ψ (cellsSource cells key).publicValue key E H x bd)
    (fun K E H cells vis ρ key x => tsum_views_join input vis (desK scalar input K ρ cells vis)
      (fun bd => onKW input Ψ (cellsSource cells key).publicValue key E H x bd))

/-- **Step (E), the joint law on the curve**, at the global instances, at every valid input. -/
theorem onJoint_global (valid : validate input = true) : OnLaw.OnJoint scalar input := by
  intro Ψ _
  have xNe : input.x ≠ 0 := onCurve_x_ne_zero input ((validate_eq_true_iff input).mp valid)
  calc OnLaw.onPrivForm scalar input Ψ ≤ onCore scalar input Ψ := priv_le_core scalar input Ψ xNe
    _ = realCore scalar input Ψ := (realCore_eq scalar input valid Ψ).symm
    _ ≤ realTarget scalar input Ψ := realCore_le scalar input Ψ
    _ = OnLaw.onGarbForm scalar input Ψ := (onGarbForm_eq scalar input Ψ).symm

/-- **Step (E), the joint law on the curve**, at any instances (they are subsingletons), at every
valid input. -/
theorem onJoint (valid : validate input = true) [first : Fintype FixedIndex]
    [second : Fintype EncPRF.PermutationIndex] [third : DecidableEq FixedIndex]
    [fourth : DecidableEq EncPRF.PermutationIndex] : OnLaw.OnJoint scalar input := by
  have global := onJoint_global scalar input valid
  convert global using 1

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
