/-
**Phase 3, P1r — `LawOn`, step (E), part 6: the view's sites and the two tapes.**

The view's inactive mask coordinates are F4's **visible** ones (`VisIdx`: digit elements off the
active switch, except the designated switch's collectors; curve elements off the active switch;
`visSite`) and the
**designated** ones (`DSite`: the three collectors of each digit at the designated switch); together
`WIdx`, `wSite` (injective, `wSite_injective`, and covering every inactive coordinate,
`inact_cover`). The view reads a tape through the limbs of its vector sites (`VSite`: the inactive
ones; `onKW`, `onKV_tape`), whose vectors are the view's coordinates (`siteVector`). F4's visible
cells are the functions on `VisIdx` (`visEquiv`), and a mask family's values at the view's
coordinates are its F4 visible and designated masks (`masks_wSite`).

The two tapes at the view: the garbler's mask tape is uniform masks and the product of the per-site
limb laws at the view's vector sites (`real_tape`); the private side's mask tape, away from the
designated vector site, is uniform visible masks and the product of the per-site limb laws at the
other view sites (`sim_tape`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEFibre

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (designatedSwitch chunkZero collectorElement freeElement FreeSite
  designatedVector)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState uniformMaskTape)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate] (input : AffineInput)

/-! ### 1. The view's mask coordinates -/

/-- **F4's visible coordinates**: digit elements off the active switch, except the designated
switch's collectors; curve elements off the active switch. -/
abbrev VisIdx :=
  (Fin digitCount × Σ e : Biquadratic.Element, {cs : ChunkSwitch // (offShape input).DigitVisibleAt e cs}) ⊕
    CurveW input

/-- The (digit, collector) slots. -/
abbrev DSite := Fin digitCount × Fin 3

/-- A mask coordinate is a (digit or curve) element and a (chunk, switch) pair. -/
def siteEquiv : MaskCoord ≃ ((Fin digitCount × Biquadratic.Element) ⊕ CurveMembership.Element) × ChunkSwitch :=
  maskSiteSplit.trans (Equiv.prodCongr laneSlots (Equiv.refl _))

/-- The key of a visible coordinate. -/
def visKey : VisIdx input → ((Fin digitCount × Biquadratic.Element) ⊕ CurveMembership.Element) × ChunkSwitch
  | .inl (d, ⟨e, cs⟩) => (.inl (d, e), cs.1)
  | .inr ⟨e, cs⟩ => (.inr e, cs.1)

/-- A visible coordinate as a mask coordinate. -/
def visSite (i : VisIdx input) : MaskCoord := siteEquiv.symm (visKey input i)

noncomputable instance visIdxDecEq : DecidableEq (VisIdx input) := Classical.decEq _

/-- **The view's coordinates**: the visible and the designated ones. -/
abbrev WIdx := VisIdx input ⊕ DSite

noncomputable instance wIdxDecEq : DecidableEq (WIdx input) := Classical.decEq _

/-- The key of a view coordinate. -/
def wKey : WIdx input → ((Fin digitCount × Biquadratic.Element) ⊕ CurveMembership.Element) × ChunkSwitch
  | .inl i => visKey input i
  | .inr (d, c) => (.inl (d, .inl (collectorElement c)), (offShape input).designated)

/-- A view coordinate as a mask coordinate. -/
def wSite (w : WIdx input) : MaskCoord := siteEquiv.symm (wKey input w)

theorem wKey_injective : Function.Injective (wKey input) := by
  rintro ((⟨d, e, cs, h⟩ | ⟨e, cs, h⟩) | ⟨d, c⟩) ((⟨d', e', cs', h'⟩ | ⟨e', cs', h'⟩) | ⟨d', c'⟩) same <;>
    simp only [wKey, visKey, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at same
  · obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
    rfl
  · obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
    exact absurd ⟨(isCollector_inl _).mpr ⟨c', rfl⟩, rfl⟩ h.2
  · obtain ⟨rfl, rfl⟩ := same
    rfl
  · obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
    exact absurd ⟨(isCollector_inl _).mpr ⟨c, rfl⟩, rfl⟩ h'.2
  · obtain ⟨⟨rfl, same⟩, -⟩ := same
    have : c = c' := Kriterion.ArgoMAC.Phase3.Glue.collectorElement_injective same
    subst this
    rfl

theorem wSite_injective : Function.Injective (wSite input) := fun _ _ same =>
  wKey_injective input (siteEquiv.symm.injective same)

theorem visSite_injective : Function.Injective (visSite input) := fun i j same =>
  Sum.inl_injective (wSite_injective input (a₁ := .inl i) (a₂ := .inl j) same)

/-- **Every inactive coordinate is a view coordinate.** -/
theorem inact_cover (c : MaskCoord) (inact : Inact input c.1) : ∃ w, wSite input w = c := by
  have back : siteEquiv.symm (siteEquiv c) = c := siteEquiv.symm_apply_apply c
  rcases hkey : siteEquiv c with ⟨(⟨d, e⟩ | e), cs⟩
  · rw [hkey] at back
    subst back
    by_cases visible : (offShape input).DigitVisibleAt e cs
    · exact ⟨.inl (.inl (d, ⟨e, ⟨cs, visible⟩⟩)), rfl⟩
    · have active : ¬ Active ((offShape input).digitAlpha e) cs := by
        rcases e with xe | ye <;> exact inact
      have des : IsCollector e ∧ cs = (offShape input).designated := by
        by_contra other
        exact visible ⟨active, other⟩
      obtain ⟨collector, rfl⟩ := des
      rcases e with xe | ye
      · obtain ⟨c, rfl⟩ := (isCollector_inl xe).mp collector
        exact ⟨.inr (d, c), rfl⟩
      · rcases collector with h | h | h <;> cases h
  · rw [hkey] at back
    subst back
    have active : ¬ Active ((offShape input).curveAlpha e) cs := by
      rcases e with xe | ye <;> exact inact
    exact ⟨.inl (.inr ⟨e, ⟨cs, active⟩⟩), rfl⟩

/-! ### 2. The view's vector sites and their limbs -/

/-- **The view's vector sites**: the inactive ones. -/
abbrev VSite := {s : VectorSite // Inact input s}

/-- The view's limbs, vector site by vector site. -/
abbrev VLimbs := ∀ s : VSite input, Fin (limbCount s.1.lane) → Block × Block

/-- The view's limbs, as a function on the inactive limbs. -/
def viewTape (bd : VLimbs input) : ICell input → Block × Block := fun c => bd ⟨c.1.1, c.2⟩ c.1.2

/-- The view coordinate of an inactive mask coordinate. -/
def coordW (c : MaskCoord) (inact : Inact input c.1) : WIdx input :=
  Classical.choose (inact_cover input c inact)

theorem wSite_coordW (c : MaskCoord) (inact : Inact input c.1) :
    wSite input (coordW input c inact) = c :=
  Classical.choose_spec (inact_cover input c inact)

theorem coordW_wSite (w : WIdx input) (inact : Inact input (wSite input w).1) :
    coordW input (wSite input w) inact = w :=
  wSite_injective input (wSite_coordW input _ inact)

/-- **A view site's vector**, from the view's coordinate values. -/
def siteVector (μ : WIdx input → BaseField) (s : VSite input) : Fin (laneCount s.1.lane) → BaseField :=
  fun e => μ (coordW input ⟨s.1, e⟩ s.2)

theorem siteVector_masks (m : MaskCoord → BaseField) (s : VSite input) :
    siteVector input (m ∘ wSite input) s = fun e => m ⟨s.1, e⟩ :=
  funext fun e => congrArg m (wSite_coordW input ⟨s.1, e⟩ s.2)

/-- **The view's limb weight**: the product of the per-site laws of the view sites' vectors. -/
def viewWeight (μ : WIdx input → BaseField) (bd : VLimbs input) : ℝ≥0∞ :=
  piPMF (fun s : VSite input => siteFibreLaw s.1.lane (siteVector input μ s)) bd

/-- **The kernel on the view sites' limbs.** -/
def onKW (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (P : Public) (key : InputMacKey)
    (E : PermutationOracle EncPRF.PermutationIndex Block) (H : OtherTable) (x : VO input → Block)
    (bd : VLimbs input) : ℝ≥0∞ :=
  onKV input Ψ P key E H x (viewTape input bd)

/-- **The kernel reads a tape only through its limbs at the view sites.** -/
theorem onKV_tape (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (P : Public) (key : InputMacKey)
    (E : PermutationOracle EncPRF.PermutationIndex Block) (H : OtherTable) (x : VO input → Block)
    (T : Tape) :
    onKV input Ψ P key E H x (fun c => T c.1) = onKW input Ψ P key E H x (fun s limb => T ⟨s.1, limb⟩) :=
  rfl

/-! ### 3. F4's visible and designated masks -/

/-- **F4's visible cells are the functions on the visible coordinates.** -/
def visEquiv : VisibleCells (offShape input) ≃ (VisIdx input → BaseField) where
  toFun vis i := match i with
    | .inl (d, ⟨e, cs⟩) => vis.1 d e cs
    | .inr ⟨e, cs⟩ => vis.2 e cs
  invFun f := (fun d e cs => f (.inl (d, ⟨e, cs⟩)), fun e cs => f (.inr ⟨e, cs⟩))
  left_inv _ := rfl
  right_inv f := funext fun i => by rcases i with ⟨d, e, cs⟩ | ⟨e, cs⟩ <;> rfl

/-- The visible masks of a mask family. -/
def visPart (m : MaskCoord → BaseField) : VisibleCells (offShape input) :=
  (fun d => digitVisible (offShape input) ((maskSiteEquiv m).1 d),
    curveVisible (offShape input) (maskSiteEquiv m).2)

/-- The designated masks of a mask family. -/
def desPart (m : MaskCoord → BaseField) : DSite → BaseField := fun dc =>
  (maskSiteEquiv m).1 dc.1 (.inl (collectorElement dc.2)) (offShape input).designated

/-- **A mask family at the view's coordinates is its visible and designated masks.** -/
theorem masks_wSite (m : MaskCoord → BaseField) :
    m ∘ wSite input = Sum.elim (visEquiv input (visPart input m)) (desPart input m) := by
  funext w
  rcases w with (⟨d, e, cs⟩ | ⟨e, cs⟩) | ⟨d, c⟩ <;> rfl

theorem masks_visSite (m : MaskCoord → BaseField) :
    m ∘ visSite input = visEquiv input (visPart input m) := by
  funext i
  rcases i with ⟨d, e, cs⟩ | ⟨e, cs⟩ <;> rfl

/-! ### 4. The designated vector site among the view's -/

theorem designatedSite_inact : Inact input (OnLaw.designatedSite (BitInput.ofAffine input)) :=
  (offShape input).designated_inactive'

/-- **The designated vector site**, as a view site. -/
def dsiteV : VSite input := ⟨OnLaw.designatedSite (BitInput.ofAffine input), designatedSite_inact input⟩

/-- The view's vector sites but the designated one. -/
abbrev VSiteN := {s : VSite input // s ≠ dsiteV input}

theorem wSite_inr (dc : DSite) :
    (wSite input (.inr dc)).1 = OnLaw.designatedSite (BitInput.ofAffine input) := rfl

/-- **Away from the designated site a vector reads visible coordinates only.** -/
theorem siteVector_other (a : VisIdx input → BaseField) (b b' : DSite → BaseField) (s : VSite input)
    (other : s ≠ dsiteV input) :
    siteVector input (Sum.elim a b) s = siteVector input (Sum.elim a b') s := by
  funext e
  unfold siteVector
  rcases hw : coordW input ⟨s.1, e⟩ s.2 with i | dc
  · rfl
  · exfalso
    have site := congrArg Sigma.fst (wSite_coordW input ⟨s.1, e⟩ s.2)
    rw [hw, wSite_inr] at site
    exact other (Subtype.ext site.symm)

/-- **The designated site's vector** is the designated vector of its free coordinates and its
collectors. -/
theorem siteVector_dsite (m : MaskCoord → BaseField) (des : DSite → BaseField) :
    siteVector input (Sum.elim (visEquiv input (visPart input m)) des) (dsiteV input) =
      designatedVector
        (fun p => m ⟨OnLaw.designatedSite (BitInput.ofAffine input), xElementIndex p.1 (freeElement p.2)⟩)
        des := by
  funext e
  obtain ⟨⟨d, xe⟩, rfl⟩ := pointXSlots.surjective e
  show siteVector input _ (dsiteV input) (xElementIndex d xe) = designatedVector _ des (xElementIndex d xe)
  cases xe with
  | rowX_x7 =>
      have visible : (offShape input).DigitVisibleAt (.inl .rowX_x7) (offShape input).designated :=
        ⟨(offShape input).designated_inactive', fun both => by
          rcases both.1 with h | h | h <;> cases h⟩
      have w : coordW input ⟨(dsiteV input).1, xElementIndex d .rowX_x7⟩
          (dsiteV input).2 = .inl (.inl (d, ⟨.inl .rowX_x7, ⟨_, visible⟩⟩)) :=
        coordW_wSite input (.inl (.inl (d, ⟨.inl .rowX_x7, ⟨_, visible⟩⟩))) (designatedSite_inact input)
      unfold siteVector
      simp only [w, Sum.elim_inl]
      refine Eq.trans ?_ (Kriterion.ArgoMAC.Phase3.Glue.designatedVector_free _ des d 0).symm
      show (maskSiteEquiv m).1 d (.inl .rowX_x7) (offShape input).designated = _
      rw [maskSiteEquiv_pointX]
      rfl
  | rowX_x9 =>
      have w : coordW input ⟨(dsiteV input).1, xElementIndex d .rowX_x9⟩
          (dsiteV input).2 = .inr (d, 0) :=
        coordW_wSite input (.inr (d, 0)) (designatedSite_inact input)
      unfold siteVector
      simp only [w, Sum.elim_inr]
      exact (Kriterion.ArgoMAC.Phase3.Glue.designatedVector_collector _ _ d 0).symm
  | rowY_cubic =>
      have w : coordW input ⟨(dsiteV input).1, xElementIndex d .rowY_cubic⟩
          (dsiteV input).2 = .inr (d, 1) :=
        coordW_wSite input (.inr (d, 1)) (designatedSite_inact input)
      unfold siteVector
      simp only [w, Sum.elim_inr]
      exact (Kriterion.ArgoMAC.Phase3.Glue.designatedVector_collector _ _ d 1).symm
  | rowZ_x9 =>
      have w : coordW input ⟨(dsiteV input).1, xElementIndex d .rowZ_x9⟩
          (dsiteV input).2 = .inr (d, 2) :=
        coordW_wSite input (.inr (d, 2)) (designatedSite_inact input)
      unfold siteVector
      simp only [w, Sum.elim_inr]
      exact (Kriterion.ArgoMAC.Phase3.Glue.designatedVector_collector _ _ d 2).symm

/-! ### 5. The two tapes at the view -/

theorem fibre_masks (M : MaskVectors) (T : Tape) {γ : Type} (G : MaskVectors → γ → ℝ≥0∞) (x : γ) :
    fibreLaw (masksOf VectorSite.lane) (masksOf_surjective VectorSite.lane) M T *
        G (masksOf VectorSite.lane T) x =
      fibreLaw (masksOf VectorSite.lane) (masksOf_surjective VectorSite.lane) M T * G M x := by
  rw [fibreLaw_apply]
  split_ifs with hit
  · rw [hit]
  · rw [zero_mul, zero_mul]

/-- **The garbler's tape at the view**: uniform masks, and the per-site limb laws at the view's
vector sites. -/
theorem real_tape (G : (MaskCoord → BaseField) → VLimbs input → ℝ≥0∞) :
    ∑' T, uniformMaskTape T *
        G (maskCoordEquiv (masksOf VectorSite.lane T)) (fun s limb => T ⟨s.1, limb⟩) =
      ∑' m, PMF.uniformOfFintype (MaskCoord → BaseField) m *
        ∑' bd, viewWeight input (m ∘ wSite input) bd * G m bd := by
  unfold uniformMaskTape
  rw [tsum_bind_mul]
  have perMask : ∀ M : MaskVectors,
      ∑' T, fibreLaw (masksOf VectorSite.lane) (masksOf_surjective VectorSite.lane) M T *
          G (maskCoordEquiv (masksOf VectorSite.lane T)) (fun s limb => T ⟨s.1, limb⟩) =
        ∑' bd, viewWeight input (maskCoordEquiv M ∘ wSite input) bd * G (maskCoordEquiv M) bd := by
    intro M
    rw [tsum_congr fun T => fibre_masks M T (fun M' bd => G (maskCoordEquiv M') bd) _,
      fibre_restrict (Inact input) M (G (maskCoordEquiv M))]
    refine tsum_congr fun bd => ?_
    unfold viewWeight
    simp only [siteVector_masks]
    rfl
  rw [tsum_congr fun M => congrArg _ (perMask M)]
  exact (tsum_equiv_uniform maskCoordEquiv (fun M : MaskVectors =>
    ∑' bd, viewWeight input (maskCoordEquiv M ∘ wSite input) bd * G (maskCoordEquiv M) bd)).trans
      (by simp only [Equiv.apply_symm_apply])

/-- **The private side's mask tape away from the designated site**: uniform visible masks, and the
per-site limb laws at the other view sites. -/
theorem sim_tape (G : (VisIdx input → BaseField) →
      (∀ s : VSiteN input, Fin (limbCount s.1.1.lane) → Block × Block) → ℝ≥0∞) :
    ∑' T, uniformMaskTape T *
        G (maskCoordEquiv (masksOf VectorSite.lane T) ∘ visSite input) (fun s limb => T ⟨s.1.1, limb⟩) =
      ∑' μ, PMF.uniformOfFintype (VisIdx input → BaseField) μ *
        ∑' bdn, piPMF (fun s : VSiteN input => siteFibreLaw s.1.1.lane (siteVector input (Sum.elim μ 0) s.1))
          bdn * G μ bdn := by
  unfold uniformMaskTape
  rw [tsum_bind_mul]
  have perMask : ∀ M : MaskVectors,
      ∑' T, fibreLaw (masksOf VectorSite.lane) (masksOf_surjective VectorSite.lane) M T *
          G (maskCoordEquiv (masksOf VectorSite.lane T) ∘ visSite input) (fun s limb => T ⟨s.1.1, limb⟩) =
        ∑' bdn, piPMF (fun s : VSiteN input =>
            siteFibreLaw s.1.1.lane (siteVector input (Sum.elim (maskCoordEquiv M ∘ visSite input) 0) s.1)) bdn *
          G (maskCoordEquiv M ∘ visSite input) bdn := by
    intro M
    rw [tsum_congr fun T => fibre_masks M T (fun M' bdn => G (maskCoordEquiv M' ∘ visSite input) bdn) _,
      fibre_restrict (Inact input) M (fun bd => G (maskCoordEquiv M ∘ visSite input) fun s => bd s.1),
      tsum_piPMF_restrict (fun s : VSite input => siteFibreLaw s.1.lane (M s.1)) (· ≠ dsiteV input)
        (G (maskCoordEquiv M ∘ visSite input))]
    refine tsum_congr fun bdn => congrArg (· * _) (congrArg (fun law => law bdn)
      (congrArg piPMF (funext fun s => congrArg _ ?_)))
    rw [← siteVector_other input _ (desPart input (maskCoordEquiv M)) 0 s.1 s.2, masks_visSite,
      ← masks_wSite, siteVector_masks]
    rfl
  rw [tsum_congr fun M => congrArg _ (perMask M)]
  rw [tsum_equiv_uniform maskCoordEquiv (fun M : MaskVectors => ∑' bdn, piPMF (fun s : VSiteN input =>
      siteFibreLaw s.1.1.lane (siteVector input (Sum.elim (maskCoordEquiv M ∘ visSite input) 0) s.1)) bdn *
        G (maskCoordEquiv M ∘ visSite input) bdn)]
  simp only [Equiv.apply_symm_apply]
  exact tsum_restrict (visSite input) (visSite_injective input) (fun μ => ∑' bdn, piPMF (fun s : VSiteN input =>
      siteFibreLaw s.1.1.lane (siteVector input (Sum.elim μ 0) s.1)) bdn * G μ bdn)

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
