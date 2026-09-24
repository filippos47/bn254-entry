/-
**Phase 3, P1r — `LawOn`, step (E), part 10: the garbler's side at fixed offsets, by F4's joint law.**

At fixed offsets `K` off `Exact0`, with the fold material hidden at the active parents' first gate
halves and the digests hidden at fresh positions (`posOf`), the garbler's randomness (the coins but
their offsets, the fixed-key answers, the masks) is the rest and F4's coins (`regroupW`); the
published value is F4's published cells at the context `ctxOn` (the pads read at the hash of the
bridge input), the view's masks are F4's visible and designated masks, and the view's fixed-key
answers are the rest's (fold gates, planted gadget positions) and the fresh answers (`xvO`).
**`jointLaw`** then replaces the designated masks by the simulator's solve, and the rest (`ρ`,
labels, fixed-key answers) is read off (`real_perK`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEReal

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
  (pos : Fin digitCount → Coord × Fin PlanB.coordinateBits)

noncomputable instance restWFintype : Fintype (RestW input pos) := Fintype.ofFinite _

/-- A row randomness is its four fields. -/
def rowRandEquiv : RowRandomness ≃
    NonZeroBase × Biquadratic.XRandomness × Biquadratic.YRandomness × Biquadratic.ZRandomness where
  toFun r := (r.rho, r.x, r.y, r.z)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance rowRandFintype : Fintype RowRandomness := Fintype.ofEquiv _ rowRandEquiv.symm

instance rowRandNonempty : Nonempty RowRandomness :=
  ⟨rowRandEquiv.symm (Classical.arbitrary _)⟩

/-! ### 1. The context with the pads at the bridge key -/

/-- **F4's context of the rest, the pads read at the hash of the bridge input.** -/
def ctxOn (E : PermutationOracle EncPRF.PermutationIndex Block) (H : OtherTable)
    (keys : OutputKeys) (o : OuterW input pos) : JointContext where
  rows := (ctxW input pos (padsOf E (bridgeOf H 0)) keys o).rows
  rho := (ctxW input pos (padsOf E (bridgeOf H 0)) keys o).rho
  foldVisible t := (ctxW input pos (padsOf E (bridgeOf H t)) keys o).foldVisible t
  gadgetVisible t := (ctxW input pos (padsOf E (bridgeOf H t)) keys o).gadgetVisible t
  gadgetSlot := (ctxW input pos (padsOf E (bridgeOf H 0)) keys o).gadgetSlot
  gadgetCode := (ctxW input pos (padsOf E (bridgeOf H 0)) keys o).gadgetCode

omit [GroupCertificate] in
/-- `publicOf` reads a context through its rows, `ρ`, its visible parts at the bridge key, its slots
and codes. -/
theorem publicOf_congr (first second : JointContext) (jc : JointCoins) (rows : first.rows = second.rows)
    (rho : first.rho = second.rho)
    (fold : first.foldVisible (bridgeKeyOf jc) = second.foldVisible (bridgeKeyOf jc))
    (gadget : first.gadgetVisible (bridgeKeyOf jc) = second.gadgetVisible (bridgeKeyOf jc))
    (slot : first.gadgetSlot = second.gadgetSlot) (code : first.gadgetCode = second.gadgetCode) :
    publicOf first jc = publicOf second jc := by
  unfold publicOf
  rw [rows, rho, fold, gadget, slot, code]

theorem publicOf_ctxOn (E : PermutationOracle EncPRF.PermutationIndex Block) (H : OtherTable)
    (keys : OutputKeys) (o : OuterW input pos) (jc : JointCoins) :
    publicOf (ctxOn input pos E H keys o) jc =
      publicOf (ctxW input pos (padsOf E (bridgeOf H (bridgeKeyOf jc))) keys o) jc :=
  publicOf_congr _ _ jc rfl rfl rfl rfl rfl rfl

/-! ### 2. The published value through the masks -/

/-- The published value of the coins, the pads, the fixed-key answers and the masks. -/
def pubM (pads : Programs.Pads) (coins : Coins) (v : FixedIndex → Block) (m : MaskCoord → BaseField) : Public :=
  (cellsSource (publicOf (ctxW input pos pads (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
      (regroupW input pos (coinsRest coins, v, m)).1) (regroupW input pos (coinsRest coins, v, m)).2)
    defaultKey).publicValue

theorem tablePub_masks (pads : Programs.Pads) (coins : Coins) (v : FixedIndex → Block) (T : Tape) :
    tablePub scalar coins pads v T =
      pubM scalar input pos pads coins v (maskCoordEquiv (masksOf VectorSite.lane T)) :=
  tablePub_cellsW input pos pads scalar coins v T defaultKey _ rfl

/-- **The garbler's tape at the view, the published value through the masks.** -/
theorem real_tapeK (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (pads : Programs.Pads)
    (coins : Coins) (v : FixedIndex → Block) (E : PermutationOracle EncPRF.PermutationIndex Block)
    (H : OtherTable) (x : (FixedIndex → Block) → VO input → Block) :
    ∑' T, uniformMaskTape T * ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
        onKW input Ψ (tablePub scalar coins pads v T) coins.inputMacKey E H (x w)
          (fun s limb => T ⟨s.1, limb⟩) =
      ∑' m, PMF.uniformOfFintype (MaskCoord → BaseField) m *
        ∑' bd, viewWeight input (m ∘ wSite input) bd * ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
          onKW input Ψ (pubM scalar input pos pads coins v m) coins.inputMacKey E H (x w) bd := by
  simp only [tablePub_masks scalar input pos]
  exact real_tape input (fun m bd => ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
    onKW input Ψ (pubM scalar input pos pads coins v m) coins.inputMacKey E H (x w) bd)

/-! ### 3. Regrouping -/

/-- **An average over the coins' rest, the fixed-key answers and the masks is one over the rest
and F4's coins.** -/
theorem regroup_sum (G : CoinsRest → (FixedIndex → Block) → (MaskCoord → BaseField) → ℝ≥0∞) :
    ∑' rest, PMF.uniformOfFintype CoinsRest rest * ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
        ∑' m, PMF.uniformOfFintype (MaskCoord → BaseField) m * G rest v m =
      ∑' o, PMF.uniformOfFintype (OuterW input pos) o * ∑' jc, PMF.uniformOfFintype JointCoins jc *
        G ((regroupW input pos).symm (o, jc)).1 ((regroupW input pos).symm (o, jc)).2.1
          ((regroupW input pos).symm (o, jc)).2.2 := by
  have inner : ∀ rest, ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
      ∑' m, PMF.uniformOfFintype (MaskCoord → BaseField) m * G rest v m =
      ∑' p, PMF.uniformOfFintype ((FixedIndex → Block) × (MaskCoord → BaseField)) p * G rest p.1 p.2 :=
    fun rest => (tsum_uniform_prod (α := FixedIndex → Block) (β := MaskCoord → BaseField)
      (fun p => G rest p.1 p.2)).symm
  simp only [inner]
  rw [← tsum_uniform_prod (α := CoinsRest) (β := (FixedIndex → Block) × (MaskCoord → BaseField))
    (fun ω => G ω.1 ω.2.1 ω.2.2)]
  rw [tsum_equiv_uniform (regroupW input pos) (fun ω => G ω.1 ω.2.1 ω.2.2),
    tsum_uniform_prod (α := OuterW input pos) (β := JointCoins)]

/-- **What the garbler's randomness is, read back from the rest and F4's coins.** -/
theorem regroup_facts (K : ClampedOffsets) (o : OuterW input pos) (jc : JointCoins) :
    coinsRest (coinsSplit.symm (K, ((regroupW input pos).symm (o, jc)).1)) =
        ((regroupW input pos).symm (o, jc)).1 ∧
      (coinsSplit.symm (K, ((regroupW input pos).symm (o, jc)).1)).bridgeKey = bridgeKeyOf jc ∧
      (coinsSplit.symm (K, ((regroupW input pos).symm (o, jc)).1)).inputMacKey = labelKey o.2.1 o.2.2.1 ∧
      maskSiteEquiv ((regroupW input pos).symm (o, jc)).2.2 = (fun d => (jc.1 d).1, jc.2.1.1) ∧
      (splitAlong (hidW input pos) (hidW_injective input pos) ((regroupW input pos).symm (o, jc)).2.1).2 =
        o.2.2.2 ∧
      regroupW input pos (((regroupW input pos).symm (o, jc)).1, ((regroupW input pos).symm (o, jc)).2.1,
        ((regroupW input pos).symm (o, jc)).2.2) = (o, jc) := by
  have back : regroupW input pos (((regroupW input pos).symm (o, jc)).1,
      ((regroupW input pos).symm (o, jc)).2.1, ((regroupW input pos).symm (o, jc)).2.2) = (o, jc) :=
    (regroupW input pos).apply_symm_apply (o, jc)
  refine ⟨congrArg Prod.snd (coinsSplit.apply_symm_apply (K, ((regroupW input pos).symm (o, jc)).1)),
    congrArg (fun p : OuterW input pos × JointCoins => bridgeKeyOf p.2) back, ?_,
    congrArg (fun p => ((fun d => (p.2.1 d).1, p.2.2.1.1) : (Fin digitCount → DigitMasks) × CurveMasks)) back,
    congrArg (fun p => p.1.2.2.2) back, back⟩
  have labels := congrArg (fun p => (p.1.2.1, p.1.2.2.1)) back
  simp only at labels
  obtain ⟨zero, delta⟩ := Prod.mk.inj labels
  show labelKey _ _ = _
  rw [← zero, ← delta]
  rfl

/-! ### 4. F4's joint law -/

/-- **F4's joint law, as an average**: the published cells, the visible masks and the designated
masks of uniform coins are uniform cells and visible masks with the simulator's solve. -/
theorem jointLaw_sum (ctx : JointContext) (valid : validate input = true)
    (F : PublicCells → VisibleCells (offShape input) → (Fin digitCount → Biquadratic.Element → BaseField) →
      ℝ≥0∞) :
    ∑' jc, PMF.uniformOfFintype JointCoins jc *
        F (publicOf ctx jc) (visibleOf (offShape input) jc) (designatedOf (offShape input) jc) =
      ∑' cells, PMF.uniformOfFintype PublicCells cells *
        ∑' vis, PMF.uniformOfFintype (VisibleCells (offShape input)) vis *
          F cells vis (simulatorDesignated (offShape input) ctx (cells, vis)) := by
  have law := jointLaw (offShape input) ctx ((validate_eq_true_iff input).mp valid)
  have first := tsum_map_mul (PMF.uniformOfFintype JointCoins) (fun coins =>
      ((publicOf ctx coins, visibleOf (offShape input) coins), designatedOf (offShape input) coins,
        bridgeKeyOf coins))
    (fun q : (PublicCells × VisibleCells (offShape input)) ×
      (Fin digitCount → Biquadratic.Element → BaseField) × BaseField => F q.1.1 q.1.2 q.2.1)
  have second := tsum_map_mul (PMF.uniformOfFintype (PublicCells × VisibleCells (offShape input)))
    (fun cells => (cells, simulatorDesignated (offShape input) ctx cells, simulatorKey (offShape input) cells))
    (fun q : (PublicCells × VisibleCells (offShape input)) ×
      (Fin digitCount → Biquadratic.Element → BaseField) × BaseField => F q.1.1 q.1.2 q.2.1)
  rw [law] at first
  refine first.symm.trans (second.trans ?_)
  exact tsum_uniform_prod (fun cv => F cv.1 cv.2 (simulatorDesignated (offShape input) ctx cv))

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
