/-
**Phase 3, P1r — `LawOn`, step (E), part 5: the limb laws, vector site by vector site.**

Both sides of `LawOn` draw the view's limbs vector site by vector site, each uniform on the
`sampleLane` fibre of its vector (`MaskSwap.siteFibreLaw`): the garbler's mask tape
(`MaskSwap.fibreLaw_masksOf_eq`) and the private side's designated draws (`Glue.designatedLimbs`:
the free coordinates, the collector solve, the `452` hash answers of the solved vector, whose law
`Glue.idealPreimage` is `siteFibreLaw .pointX` by definition). Here:

* `tsum_piPMF_restrict`, `tsum_piPMF_split`: a product law read at some of its coordinates, or split
  at one coordinate;
* `fibre_restrict`: a mask tape's limbs at some vector sites, given the vectors, are the product of
  their per-site laws;
* `tsum_designatedLimbs`: the designated draws, as an average over the free coordinates and the
  solved vector's per-site law;
* `tsum_freeOf`: under the mask tape, a function of the tape off the designated site and of free
  coordinates drawn apart is the same function at the tape's own free coordinates (`freeOf`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEPartial

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Phase3.Glue (idealPreimage idealSamplers designatedLimbs solvedVector
  DesignatedLimbs FreeSite freeElement)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape uniformMaskTape)
open scoped ENNReal

noncomputable section

/-! ### 1. Product laws -/

section Product

variable {I : Type} [Fintype I] [DecidableEq I] {β : I → Type} [∀ i, Fintype (β i)]

/-- **A product law read at some coordinates is the product of their laws.** -/
theorem tsum_piPMF_restrict (law : ∀ i, PMF (β i)) (p : I → Prop) [DecidablePred p]
    (g : (∀ i : {i // p i}, β i.1) → ℝ≥0∞) :
    ∑' f, piPMF law f * g (fun i => f i.1) =
      ∑' f, piPMF (fun i : {i // p i} => law i.1) f * g f := by
  rw [← (Equiv.piEquivPiSubtypeProd p β).symm.tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  have split : ∀ b, piPMF law ((Equiv.piEquivPiSubtypeProd p β).symm (a, b)) =
      piPMF (fun i : {i // p i} => law i.1) a * piPMF (fun i : {i // ¬ p i} => law i.1) b := by
    intro b
    simp only [piPMF_apply]
    rw [← Fintype.prod_subtype_mul_prod_subtype p]
    congr 1
    · refine Fintype.prod_congr _ _ fun i => ?_
      rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos i.2]
    · refine Fintype.prod_congr _ _ fun i => ?_
      rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2]
  have restrict : ∀ b, (fun i : {i // p i} => (Equiv.piEquivPiSubtypeProd p β).symm (a, b) i.1) = a :=
    fun b => funext fun i => by rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos i.2]
  simp only [split, restrict]
  have total := (piPMF fun i : {i // ¬ p i} => law i.1).tsum_coe
  calc ∑' b, piPMF (fun i : {i // p i} => law i.1) a * piPMF (fun i : {i // ¬ p i} => law i.1) b * g a
      = piPMF (fun i : {i // p i} => law i.1) a * g a *
          ∑' b, piPMF (fun i : {i // ¬ p i} => law i.1) b := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun b => by ring
    _ = _ := by rw [total, mul_one]

/-- **A product law split at one coordinate.** -/
theorem tsum_piPMF_split (law : ∀ i, PMF (β i)) (index : I) (g : (∀ i, β i) → ℝ≥0∞) :
    ∑' f, piPMF law f * g f =
      ∑' head, law index head * ∑' tail, piPMF (fun other : {j // j ≠ index} => law other) tail *
        g ((Equiv.piSplitAt index β).symm (head, tail)) := by
  have mapped := tsum_map_mul (piPMF law) (Equiv.piSplitAt index β)
    (fun pair => g ((Equiv.piSplitAt index β).symm pair))
  rw [piPMF_split, tsum_productPMF] at mapped
  rw [mapped]
  exact tsum_congr fun f => by rw [Equiv.symm_apply_apply]

end Product

/-- A constant averaged over a law. -/
theorem tsum_pmf_const {α : Type} (μ : PMF α) (c : ℝ≥0∞) : ∑' a, μ a * c = c := by
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ### 2. The mask tape's limbs -/

/-- **A mask tape's limbs at some vector sites, given the vectors**: the product of the per-site
laws. -/
theorem fibre_restrict (p : VectorSite → Prop) [DecidablePred p] (M : MaskVectors)
    (G : (∀ s : {v // p v}, Fin (limbCount s.1.lane) → Block × Block) → ℝ≥0∞) :
    ∑' T, fibreLaw (masksOf VectorSite.lane) (masksOf_surjective VectorSite.lane) M T *
        G (fun s limb => T ⟨s.1, limb⟩) =
      ∑' bd, piPMF (fun s : {v // p v} => siteFibreLaw s.1.lane (M s.1)) bd * G bd := by
  rw [fibreLaw_masksOf_eq, tsum_map_mul]
  exact tsum_piPMF_restrict (fun v => siteFibreLaw v.lane (M v)) p G

/-- **The mask tape, site by site**: each vector site's limbs from its swapped law, independently. -/
theorem uniformMaskTape_eq :
    uniformMaskTape = (piPMF fun v : VectorSite => siteSwapLaw v.lane).map
      (slotCurry VectorSite.lane).symm := by
  unfold uniformMaskTape
  rw [show fibreLaw (masksOf VectorSite.lane) (masksOf_surjective VectorSite.lane) =
      fun M => (piPMF fun v => siteFibreLaw v.lane (M v)).map (slotCurry VectorSite.lane).symm from
    funext (fibreLaw_masksOf_eq VectorSite.lane), uniform_pi_eq_piPMF, ← PMF.map_bind, piPMF_bind]
  rfl

/-- **A site's swapped limbs make a uniform vector.** -/
theorem siteSwapLaw_map (lane : Lane) :
    (siteSwapLaw lane).map (sampleLane (laneCount lane) (limbCount lane)) =
      PMF.uniformOfFintype (Fin (laneCount lane) → BaseField) := by
  unfold siteSwapLaw
  rw [PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure (PMF.uniformOfFintype (Fin (laneCount lane) → BaseField))]
  refine congrArg _ (funext fun vector => ?_)
  unfold siteFibreLaw
  rw [fibreLaw_map_congr _ _ vector (second := fun _ => vector) fun _ hit => hit]
  exact PMF.map_const _ vector

/-! ### 3. The designated draws -/

variable [FieldCertificate] [GroupCertificate]

/-- **The designated draws**: the free coordinates uniform, then the solved vector's limbs on its
fibre. -/
theorem tsum_designatedLimbs (P : Public) (bits : BitInput) (pointX : Fin pointElementCountX → BaseField)
    (pointY : Fin pointElementCountY → BaseField)
    (targets : Fin digitCount → FieldMacToECMac.HomogeneousValue) (H : DesignatedLimbs → ℝ≥0∞) :
    ∑' r, designatedLimbs idealSamplers P bits pointX pointY targets r * r.elim 0 H =
      ∑' free, PMF.uniformOfFintype (FreeSite → BaseField) free *
        ∑' limbs, siteFibreLaw .pointX (solvedVector P bits pointX pointY free targets) limbs * H limbs := by
  unfold designatedLimbs idealSamplers
  rw [tsum_bind_mul, tsum_map_mul]
  refine tsum_congr fun free => congrArg _ ?_
  show ∑' r, ((idealPreimage (solvedVector P bits pointX pointY free targets)).map some) r * r.elim 0 H = _
  rw [tsum_map_mul]
  rfl

variable (input : AffineInput)

/-- A tape with the designated site's limbs split off. -/
def joinD (head : Fin (limbCount .pointX) → Block × Block)
    (tail : ∀ v : {v : VectorSite // v ≠ OnLaw.designatedSite (BitInput.ofAffine input)},
      Fin (limbCount v.1.lane) → Block × Block) : Tape :=
  (slotCurry VectorSite.lane).symm
    ((Equiv.piSplitAt (OnLaw.designatedSite (BitInput.ofAffine input))
      fun v => Fin (limbCount v.lane) → Block × Block).symm (head, tail))

theorem joinD_other (head head' : Fin (limbCount .pointX) → Block × Block)
    (tail : ∀ v : {v : VectorSite // v ≠ OnLaw.designatedSite (BitInput.ofAffine input)},
      Fin (limbCount v.1.lane) → Block × Block) (cell : Cell)
    (other : cell.1 ≠ OnLaw.designatedSite (BitInput.ofAffine input)) :
    joinD input head tail cell = joinD input head' tail cell := by
  obtain ⟨v, limb⟩ := cell
  show (Equiv.piSplitAt (OnLaw.designatedSite (BitInput.ofAffine input))
      (fun v => Fin (limbCount v.lane) → Block × Block)).symm (head, tail) v limb =
    (Equiv.piSplitAt (OnLaw.designatedSite (BitInput.ofAffine input))
      (fun v => Fin (limbCount v.lane) → Block × Block)).symm (head', tail) v limb
  rw [Equiv.piSplitAt_symm_apply, Equiv.piSplitAt_symm_apply, dif_neg other, dif_neg other]

theorem freeOf_joinD (head : Fin (limbCount .pointX) → Block × Block)
    (tail : ∀ v : {v : VectorSite // v ≠ OnLaw.designatedSite (BitInput.ofAffine input)},
      Fin (limbCount v.1.lane) → Block × Block) :
    freeOf input (joinD input head tail) = fun p =>
      sampleLane pointElementCountX (limbCount .pointX) head (xElementIndex p.1 (freeElement p.2)) := by
  funext p
  show sampleLane pointElementCountX (limbCount .pointX)
    (fun limb => (Equiv.piSplitAt (OnLaw.designatedSite (BitInput.ofAffine input))
      (fun v => Fin (limbCount v.lane) → Block × Block)).symm (head, tail)
        (OnLaw.designatedSite (BitInput.ofAffine input)) limb) (xElementIndex p.1 (freeElement p.2)) = _
  rw [Equiv.piSplitAt_symm_apply, dif_pos rfl]

/-- The free coordinates of a designated vector. -/
def freeCoords (vector : Fin pointElementCountX → BaseField) : FreeSite → BaseField := fun p =>
  vector (xElementIndex p.1 (freeElement p.2))

omit [FieldCertificate] [GroupCertificate] in
theorem freeSlot_injective :
    Function.Injective fun p : FreeSite => xElementIndex p.1 (freeElement p.2) := by
  rintro ⟨d, k⟩ ⟨d', k'⟩ same
  have pair := xElementIndex_injective (a₁ := (d, freeElement k)) (a₂ := (d', freeElement k')) same
  simp only [Prod.mk.injEq] at pair
  obtain ⟨rfl, same'⟩ := pair
  rw [Kriterion.ArgoMAC.Phase3.Glue.freeElement_injective same']

/-- **Free coordinates drawn apart are the tape's own**: under the mask tape, a function of the tape
off the designated site and of uniform free coordinates is the same function at `freeOf`. -/
theorem tsum_freeOf (F : Tape → (FreeSite → BaseField) → ℝ≥0∞)
    (offD : ∀ T T' free, (∀ cell : Cell, cell.1 ≠ OnLaw.designatedSite (BitInput.ofAffine input) →
      T cell = T' cell) → F T free = F T' free) :
    ∑' T, uniformMaskTape T * ∑' free, PMF.uniformOfFintype (FreeSite → BaseField) free * F T free =
      ∑' T, uniformMaskTape T * F T (freeOf input T) := by
  classical
  let head₀ : Fin (limbCount .pointX) → Block × Block := fun _ => (0, 0)
  have indep : ∀ head tail free, F (joinD input head tail) free = F (joinD input head₀ tail) free :=
    fun head tail free => offD _ _ free fun cell other => joinD_other input head head₀ tail cell other
  rw [uniformMaskTape_eq, tsum_map_mul, tsum_map_mul,
    tsum_piPMF_split _ (OnLaw.designatedSite (BitInput.ofAffine input)),
    tsum_piPMF_split _ (OnLaw.designatedSite (BitInput.ofAffine input))]
  change ∑' head, siteSwapLaw .pointX head * ∑' tail, _ * ∑' free, _ * F (joinD input head tail) free =
    ∑' head, siteSwapLaw .pointX head * ∑' tail, _ *
      F (joinD input head tail) (freeOf input (joinD input head tail))
  simp only [indep, freeOf_joinD]
  rw [tsum_pmf_const, tsum_swap_mul (siteSwapLaw Lane.pointX)]
  refine tsum_congr fun tail => congrArg _ ?_
  have pushed := tsum_map_mul (siteSwapLaw .pointX) (sampleLane (laneCount .pointX) (limbCount .pointX))
    (fun vector => F (joinD input head₀ tail) (freeCoords vector))
  rw [siteSwapLaw_map] at pushed
  refine Eq.trans ?_ pushed
  exact (tsum_restrict _ freeSlot_injective (fun free => F (joinD input head₀ tail) free)).symm

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
