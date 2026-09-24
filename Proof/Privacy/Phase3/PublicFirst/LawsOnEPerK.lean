/-
**Phase 3, P1r — `LawOn`, step (E), part 11: the garbler's side at fixed offsets is the core.**

`real_perK`: at fixed offsets `K` off `Exact0`, and fixed EncPRF permutations `E` and hash off the
scale range `H`, the garbler's side (coins' rest, table's fixed-key answers and tape, fresh answers)
is the average `coreKEH` of the view kernel over uniform cells, visible masks, `ρ`, key, view answers
`x`, and the per-site limb laws of the view's vector sites at the visible masks and the simulator's
designated solve (`desK`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEJoint

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (collectorElement)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState uniformMaskTape)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (input : AffineInput)

/-! ### 1. The core -/

/-- The rows at offsets and `ρ`. -/
def rowsK (K : ClampedOffsets) (ρ : Fin digitCount → NonZeroBase) (d : Fin digitCount) : Coordinates.Rows :=
  Coordinates.rows ((FieldMacToECMac.outputKeys construction scalar.value K.1).get d).offset.coordinates
    (digitEndomorphismBase ((FieldMacToECMac.outputKeys construction scalar.value K.1).get d).digit) (ρ d).value

/-- **The designated masks of the core**: F4's collector solve at the true rows. -/
def desK (K : ClampedOffsets) (ρ : Fin digitCount → NonZeroBase) (cells : PublicCells)
    (vis : VisibleCells (offShape input)) : DSite → BaseField := fun dc =>
  simDesignated (offShape input) (rowTarget (rowsK scalar K ρ dc.1) input) (cells.1 dc.1).1 (cells.1 dc.1).2
    (vis.1 dc.1) (.inl (collectorElement dc.2))

/-- **The core at offsets, EncPRF permutations and hash off the scale range.** -/
def coreKEH (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (K : ClampedOffsets)
    (E : PermutationOracle EncPRF.PermutationIndex Block) (H : OtherTable) : ℝ≥0∞ :=
  ∑' cells, PMF.uniformOfFintype PublicCells cells *
    ∑' vis, PMF.uniformOfFintype (VisibleCells (offShape input)) vis *
      ∑' ρ, PMF.uniformOfFintype (Fin digitCount → NonZeroBase) ρ *
        ∑' key, PMF.uniformOfFintype InputMacKey key *
          ∑' x, PMF.uniformOfFintype (VO input → Block) x *
            ∑' bd, viewWeight input (Sum.elim (visEquiv input vis) (desK scalar input K ρ cells vis)) bd *
              onKW input Ψ (cellsSource cells key).publicValue key E H x bd

/-! ### 2. The view answers from the rest and the fresh answers -/

variable (K : ClampedOffsets) (off : ¬ Exact0 scalar input K.1)

include off in
/-- **A view index the garbler does not refresh is not hidden.** -/
theorem notHidden_of_notFresh (i : VO input) (notFresh : ¬ FreshQ scalar input K.1 i.1) :
    i.1 ∉ Set.range (hidW input (posK scalar input K.1)) := by
  obtain ⟨index, view⟩ := i
  cases index with
  | hot lane c fold entry half =>
      exact viewHot_not_hidden scalar input K.1 _ view fun _ _ _ same => by cases same
  | gadget d κ p =>
      exact planted_not_hidden scalar input K.1 off d κ p (Classical.not_not.mp notFresh)

open Classical in
/-- Where the view reads a fixed-key answer: the rest (fold gates, planted gadget positions) or the
fresh answers. -/
def viewSource (i : VO input) : RestW input (posK scalar input K.1) ⊕ FixedIndex :=
  if h : FreshQ scalar input K.1 i.1 then .inr i.1
  else .inl ⟨i.1, notHidden_of_notFresh scalar input K off i h⟩

theorem viewSource_injective : Function.Injective (viewSource scalar input K off) := by
  intro i j same
  apply Subtype.ext
  unfold viewSource at same
  by_cases hi : FreshQ scalar input K.1 i.1 <;> by_cases hj : FreshQ scalar input K.1 j.1
  · rw [dif_pos hi, dif_pos hj] at same
    exact Sum.inr_injective same
  · rw [dif_pos hi, dif_neg hj] at same
    exact absurd same (by simp)
  · rw [dif_neg hi, dif_pos hj] at same
    exact absurd same (by simp)
  · rw [dif_neg hi, dif_neg hj] at same
    have rest := Sum.inl_injective same
    exact Subtype.mk.inj rest

/-- The view's answers from the rest and the fresh answers. -/
def xvO (rest : RestW input (posK scalar input K.1) → Block) (w : FixedIndex → Block) : VO input → Block :=
  Sum.elim rest w ∘ viewSource scalar input K off

open Classical in
theorem xvW_eq (v w : FixedIndex → Block) :
    xvW scalar input K.1 v w = xvO scalar input K off
      (splitAlong (hidW input (posK scalar input K.1)) (hidW_injective input _) v).2 w := by
  funext i
  unfold xvW xvO viewSource
  by_cases fresh : FreshQ scalar input K.1 i.1
  · rw [if_pos fresh, Function.comp_apply, dif_pos fresh]
    rfl
  · rw [if_neg fresh, Function.comp_apply, dif_neg fresh]
    rfl

/-- **The rest and the fresh answers read at the view are uniform view answers.** -/
theorem tsum_view_answers (G : (VO input → Block) → ℝ≥0∞) :
    ∑' rest, PMF.uniformOfFintype (RestW input (posK scalar input K.1) → Block) rest *
        ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w * G (xvO scalar input K off rest w) =
      ∑' x, PMF.uniformOfFintype (VO input → Block) x * G x := by
  classical
  rw [← tsum_uniform_prod (α := RestW input (posK scalar input K.1) → Block) (β := FixedIndex → Block)
    (fun p => G (xvO scalar input K off p.1 p.2))]
  rw [tsum_equiv_uniform (Equiv.sumArrowEquivProdArrow (RestW input (posK scalar input K.1)) FixedIndex Block).symm
    (fun p => G (xvO scalar input K off p.1 p.2))]
  have back : ∀ g : RestW input (posK scalar input K.1) ⊕ FixedIndex → Block,
      xvO scalar input K off ((Equiv.sumArrowEquivProdArrow _ _ Block).symm.symm g).1
        ((Equiv.sumArrowEquivProdArrow _ _ Block).symm.symm g).2 = g ∘ viewSource scalar input K off := by
    intro g
    funext o
    show Sum.elim (g ∘ Sum.inl) (g ∘ Sum.inr) (viewSource scalar input K off o) = g (viewSource scalar input K off o)
    rcases viewSource scalar input K off o with r | i <;> rfl
  simp only [back]
  exact tsum_restrict (viewSource scalar input K off) (viewSource_injective scalar input K off) G

/-! ### 3. The integrand, read at the rest and F4's coins -/

/-- The integrand as a function of the rest and F4's published, visible and designated cells. -/
def outerF (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (E : PermutationOracle EncPRF.PermutationIndex Block)
    (H : OtherTable) (o : OuterW input (posK scalar input K.1)) (cells : PublicCells)
    (vis : VisibleCells (offShape input)) (des : Fin digitCount → Biquadratic.Element → BaseField) : ℝ≥0∞ :=
  ∑' bd, viewWeight input (Sum.elim (visEquiv input vis) (fun dc => des dc.1 (.inl (collectorElement dc.2)))) bd *
    ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
      onKW input Ψ (cellsSource cells defaultKey).publicValue (labelKey o.2.1 o.2.2.1) E H
        (xvO scalar input K off o.2.2.2 w) bd

theorem integrand_eq (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (E : PermutationOracle EncPRF.PermutationIndex Block) (H : OtherTable)
    (o : OuterW input (posK scalar input K.1)) (jc : JointCoins) :
    (∑' bd, viewWeight input (((regroupW input (posK scalar input K.1)).symm (o, jc)).2.2 ∘ wSite input) bd *
      ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
        onKW input Ψ (pubM scalar input (posK scalar input K.1)
            (padsOf E (bridgeOf H (coinsSplit.symm (K, ((regroupW input (posK scalar input K.1)).symm (o, jc)).1)).bridgeKey))
            (coinsSplit.symm (K, ((regroupW input (posK scalar input K.1)).symm (o, jc)).1))
            ((regroupW input (posK scalar input K.1)).symm (o, jc)).2.1
            ((regroupW input (posK scalar input K.1)).symm (o, jc)).2.2)
          (coinsSplit.symm (K, ((regroupW input (posK scalar input K.1)).symm (o, jc)).1)).inputMacKey E H
          (xvW scalar input K.1 ((regroupW input (posK scalar input K.1)).symm (o, jc)).2.1 w) bd) =
      outerF scalar input K off Ψ E H o
        (publicOf (ctxOn input (posK scalar input K.1) E H
          (FieldMacToECMac.outputKeys construction scalar.value K.1) o) jc)
        (visibleOf (offShape input) jc) (designatedOf (offShape input) jc) := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := regroup_facts input (posK scalar input K.1) K o jc
  have masks : ((regroupW input (posK scalar input K.1)).symm (o, jc)).2.2 ∘ wSite input =
      Sum.elim (visEquiv input (visibleOf (offShape input) jc))
        (fun dc => designatedOf (offShape input) jc dc.1 (.inl (collectorElement dc.2))) := by
    rw [masks_wSite]
    congr 1
    · unfold visPart
      rw [f4]
      rfl
    · funext dc
      unfold desPart designatedOf
      rw [f4, if_pos ((isCollector_inl _).mpr ⟨dc.2, rfl⟩)]
  have pub : pubM scalar input (posK scalar input K.1)
      (padsOf E (bridgeOf H (coinsSplit.symm (K, ((regroupW input (posK scalar input K.1)).symm (o, jc)).1)).bridgeKey))
      (coinsSplit.symm (K, ((regroupW input (posK scalar input K.1)).symm (o, jc)).1))
      ((regroupW input (posK scalar input K.1)).symm (o, jc)).2.1
      ((regroupW input (posK scalar input K.1)).symm (o, jc)).2.2 =
      (cellsSource (publicOf (ctxOn input (posK scalar input K.1) E H
        (FieldMacToECMac.outputKeys construction scalar.value K.1) o) jc) defaultKey).publicValue := by
    unfold pubM
    rw [f1, f6, f2, publicOf_ctxOn]
    rfl
  unfold outerF
  rw [masks, pub, f3]
  simp only [xvW_eq scalar input K off, f5]

/-! ### 4. The garbler's side at fixed offsets -/

/-- The view kernel at a MAC. -/
def onKWm (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (P : Public) (mac : InputMac)
    (E : PermutationOracle EncPRF.PermutationIndex Block) (H : OtherTable) (x : VO input → Block)
    (bd : VLimbs input) : ℝ≥0∞ :=
  Ψ P (Lamport.selectedLabels mac)
    (plantAll (transcript (tableAnswer (viewTable input E H x (viewTape input bd)))
      (shadowOnM P (BitInput.ofAffine input) mac)) LazyOracle.empty)

include off in
/-- **The garbler's side at fixed offsets off `Exact0` is the core.** -/
theorem real_perK (valid : validate input = true) (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (E : PermutationOracle EncPRF.PermutationIndex Block) (H : OtherTable) :
    ∑' rest, PMF.uniformOfFintype CoinsRest rest * ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
      ∑' T, uniformMaskTape T * ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
        onKW input Ψ (tablePub scalar (coinsSplit.symm (K, rest))
            (padsOf E (bridgeOf H (coinsSplit.symm (K, rest)).bridgeKey)) v T)
          (coinsSplit.symm (K, rest)).inputMacKey E H (xvW scalar input K.1 v w)
          (fun s limb => T ⟨s.1, limb⟩) =
      coreKEH scalar input Ψ K E H := by
  have step1 : ∀ (rest : CoinsRest) (v : FixedIndex → Block),
      ∑' T, uniformMaskTape T * ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
        onKW input Ψ (tablePub scalar (coinsSplit.symm (K, rest))
            (padsOf E (bridgeOf H (coinsSplit.symm (K, rest)).bridgeKey)) v T)
          (coinsSplit.symm (K, rest)).inputMacKey E H (xvW scalar input K.1 v w)
          (fun s limb => T ⟨s.1, limb⟩) =
      ∑' m, PMF.uniformOfFintype (MaskCoord → BaseField) m *
        ∑' bd, viewWeight input (m ∘ wSite input) bd * ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
          onKW input Ψ (pubM scalar input (posK scalar input K.1)
              (padsOf E (bridgeOf H (coinsSplit.symm (K, rest)).bridgeKey)) (coinsSplit.symm (K, rest)) v m)
            (coinsSplit.symm (K, rest)).inputMacKey E H (xvW scalar input K.1 v w) bd :=
    fun rest v => real_tapeK scalar input (posK scalar input K.1) Ψ _ _ v E H
      (fun w => xvW scalar input K.1 v w)
  rw [tsum_congr fun rest => congrArg _ (tsum_congr fun v => congrArg _ (step1 rest v))]
  rw [regroup_sum input (posK scalar input K.1) (fun rest v m =>
    ∑' bd, viewWeight input (m ∘ wSite input) bd * ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
      onKW input Ψ (pubM scalar input (posK scalar input K.1)
          (padsOf E (bridgeOf H (coinsSplit.symm (K, rest)).bridgeKey)) (coinsSplit.symm (K, rest)) v m)
        (coinsSplit.symm (K, rest)).inputMacKey E H (xvW scalar input K.1 v w) bd)]
  rw [tsum_congr fun o => congrArg _ (tsum_congr fun jc => congrArg _
    (integrand_eq scalar input K off Ψ E H o jc))]
  rw [tsum_congr fun o => congrArg _ (jointLaw_sum input (ctxOn input (posK scalar input K.1) E H
    (FieldMacToECMac.outputKeys construction scalar.value K.1) o) valid (outerF scalar input K off Ψ E H o))]
  have desEq : ∀ (o : OuterW input (posK scalar input K.1)) (cells : PublicCells)
      (vis : VisibleCells (offShape input)),
      (fun dc : DSite => simulatorDesignated (offShape input) (ctxOn input (posK scalar input K.1) E H
        (FieldMacToECMac.outputKeys construction scalar.value K.1) o) (cells, vis) dc.1
          (.inl (collectorElement dc.2))) = desK scalar input K o.1 cells vis := fun o cells vis =>
    funext fun dc => if_pos ((isCollector_inl _).mpr ⟨dc.2, rfl⟩)
  have outerEq : ∀ (o : OuterW input (posK scalar input K.1)) (cells : PublicCells)
      (vis : VisibleCells (offShape input)),
      outerF scalar input K off Ψ E H o cells vis (simulatorDesignated (offShape input)
        (ctxOn input (posK scalar input K.1) E H (FieldMacToECMac.outputKeys construction scalar.value K.1) o)
          (cells, vis)) =
      ∑' bd, viewWeight input (Sum.elim (visEquiv input vis) (desK scalar input K o.1 cells vis)) bd *
        ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
          onKWm input Ψ (cellsSource cells defaultKey).publicValue
            ((labelKey o.2.1 o.2.2.1).encode (BitInput.ofAffine input)) E H
            (xvO scalar input K off o.2.2.2 w) bd := by
    intro o cells vis
    unfold outerF
    rw [desEq]
    rfl
  simp only [outerEq]
  rw [tsum_swap_mul]
  refine tsum_congr fun cells => congrArg _ ?_
  rw [tsum_swap_mul]
  refine tsum_congr fun vis => congrArg _ ?_
  rw [tsum_uniform_prod (α := Fin digitCount → NonZeroBase)]
  refine tsum_congr fun ρ => congrArg _ ?_
  rw [tsum_uniform_prod (α := Coord → Fin coordinateBitCount → Block)]
  have labels := tsum_labels (BitInput.ofAffine input) fun mac =>
    ∑' rest, PMF.uniformOfFintype (RestW input (posK scalar input K.1) → Block) rest *
      ∑' bd, viewWeight input (Sum.elim (visEquiv input vis) (desK scalar input K ρ cells vis)) bd *
        ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
          onKWm input Ψ (cellsSource cells defaultKey).publicValue mac E H (xvO scalar input K off rest w) bd
  have inner : ∀ Z : Coord → Fin coordinateBitCount → Block,
      ∑' b, PMF.uniformOfFintype ((Coord → Block) × (RestW input (posK scalar input K.1) → Block)) b *
        ∑' bd, viewWeight input (Sum.elim (visEquiv input vis) (desK scalar input K (ρ, Z, b).1 cells vis)) bd *
          ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
            onKWm input Ψ (cellsSource cells defaultKey).publicValue
              ((labelKey (ρ, Z, b).2.1 (ρ, Z, b).2.2.1).encode (BitInput.ofAffine input)) E H
              (xvO scalar input K off (ρ, Z, b).2.2.2 w) bd =
      ∑' Δ, PMF.uniformOfFintype (Coord → Block) Δ *
        ∑' rest, PMF.uniformOfFintype (RestW input (posK scalar input K.1) → Block) rest *
          ∑' bd, viewWeight input (Sum.elim (visEquiv input vis) (desK scalar input K ρ cells vis)) bd *
            ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
              onKWm input Ψ (cellsSource cells defaultKey).publicValue
                ((labelKey Z Δ).encode (BitInput.ofAffine input)) E H (xvO scalar input K off rest w) bd :=
    fun Z => tsum_uniform_prod (α := Coord → Block) (β := RestW input (posK scalar input K.1) → Block) _
  simp only [inner]
  rw [labels]
  refine tsum_congr fun key => congrArg _ ?_
  have perBd : ∀ bd : VLimbs input,
      ∑' rest, PMF.uniformOfFintype (RestW input (posK scalar input K.1) → Block) rest *
        ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
          onKWm input Ψ (cellsSource cells defaultKey).publicValue (key.encode (BitInput.ofAffine input)) E H
            (xvO scalar input K off rest w) bd =
      ∑' x, PMF.uniformOfFintype (VO input → Block) x *
        onKW input Ψ (cellsSource cells key).publicValue key E H x bd := fun bd =>
    tsum_view_answers scalar input K off (fun x => onKWm input Ψ (cellsSource cells defaultKey).publicValue
      (key.encode (BitInput.ofAffine input)) E H x bd)
  have regroupBd : ∑' rest, PMF.uniformOfFintype (RestW input (posK scalar input K.1) → Block) rest *
      ∑' bd, viewWeight input (Sum.elim (visEquiv input vis) (desK scalar input K ρ cells vis)) bd *
        ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
          onKWm input Ψ (cellsSource cells defaultKey).publicValue (key.encode (BitInput.ofAffine input)) E H
            (xvO scalar input K off rest w) bd =
      ∑' bd, viewWeight input (Sum.elim (visEquiv input vis) (desK scalar input K ρ cells vis)) bd *
        ∑' rest, PMF.uniformOfFintype (RestW input (posK scalar input K.1) → Block) rest *
          ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
            onKWm input Ψ (cellsSource cells defaultKey).publicValue (key.encode (BitInput.ofAffine input)) E H
              (xvO scalar input K off rest w) bd := tsum_swap_mul _ _ _
  rw [regroupBd, tsum_congr fun bd => congrArg _ (perBd bd)]
  exact tsum_swap_mul _ _ _

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
