/-
**Phase 3, P1r — `LawOn`, step (E), part 12: C's garbler form is `realTarget`.**

P1q's `onGarbForm` answers a fresh gadget question at `x` by the translation `x ⊕ v k`
(`OnLaw.freshAnswer`); `realTarget` by a fresh table value. The shadow asks each gadget position at
one point, the transformed label under the pads keyed by the hash of the bridge input of the curve
lanes' value (`gpt`, `shadow_gadAt`), so the translations are the table values `gpt ⊕ v`
(`freshAnswer_table`), uniform with `v` (`garbK_eq`). `freshPos` is `¬ Planted` (`freshPos_iff`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnECore
import Proof.Privacy.Phase3.PublicFirst.LawsOnCJoint

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState)
open Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw (GPos gIdx gIdx_injective freshAnswer freshPos
  garbK onGarbForm)
open scoped ENNReal

noncomputable section

theorem transcript_agree_asked {α : Type} {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}
    (a b : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) :
    ∀ {c : FreeQuery Programs.Spec α}, Guess.AsksOnly a S c → (∀ q, S q → a q = b q) →
      transcript a c = transcript b c
  | .pure _, _, _ => rfl
  | .query request next, only, same => by
      have head : S request := only ⟨request, a request⟩ List.mem_cons_self
      have tail : Guess.AsksOnly a S (next (a request)) := fun entry member =>
        only entry (List.mem_cons_of_mem _ member)
      have rest := transcript_agree_asked a b tail same
      show ⟨request, a request⟩ :: transcript a (next (a request)) =
        ⟨request, b request⟩ :: transcript b (next (b request))
      rw [rest, same request head]

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (input : AffineInput)

/-! ### 1. The gadget points on a table -/

/-- **The pads the evaluator reads**: keyed by the hash of the bridge input of the curve lanes'
value. -/
def padsAt (P : Public) (E : PermutationOracle EncPRF.PermutationIndex Block) (H : OtherTable) (T : Tape) :
    EncPRF.Coordinate → Fin coordinateBitCount → Block × Block :=
  Programs.realEvalPads E
    ⟨(bridgeOf H (curveKey P (BitInput.ofAffine input) T)).1,
      (bridgeOf H (curveKey P (BitInput.ofAffine input) T)).2⟩
    (BitInput.ofAffine input)

/-- The shadow's point at a gadget position, on a table. -/
def gpt (P : Public) (mac : InputMac) (A : Table) (k : GPos) : Block :=
  macAt (Programs.transformMacOf (padsAt input P A.1 A.2.1 A.2.2.2) mac) k.2.1 k.2.2.1

/-- A gadget question at its point, or any other forward or hash question. -/
def GadAt (P : Public) (mac : InputMac) (A : Table) : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward (.gadget o κ p b) x => x = gpt input P mac A (o, κ, p, b)
  | .fixedInverse _ _ => False
  | .encInverse _ _ => False
  | _ => True

theorem gadAt_of (P : Public) (mac : InputMac) (A : Table)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex) (h : OnQ input q ∧ OnLaw.NotGadget q) :
    GadAt input P mac A q := by
  cases q with
  | fixedForward index x =>
      cases index with
      | gadget o κ p b => exact absurd rfl (h.2 o κ p b x)
      | hot _ _ _ _ _ => trivial
  | fixedInverse _ _ => exact h.1.elim
  | encInverse _ _ => exact h.1.elim
  | _ => trivial

theorem queryOnly_and {α : Type} {S S' : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}
    {c : FreeQuery Programs.Spec α} (first : Hidden.QueryOnly S c) (second : Hidden.QueryOnly S' c) :
    Hidden.QueryOnly (fun q => S q ∧ S' q) c := by
  induction first with
  | pure value => exact .pure value
  | query request next holds rest ih =>
      cases second with
      | query _ _ holds' rest' => exact .query request next ⟨holds, holds'⟩ fun a => ih a (rest' a)

theorem preM_onQ (P : Public) (mac : InputMac) :
    Hidden.QueryOnly (OnQ input) (OnLaw.preM P (BitInput.ofAffine input) mac) := by
  rw [preM_eq]
  refine Hidden.QueryOnly.bind (curvePrefixM_onQ input P mac) fun hashed => ?_
  unfold restM
  refine Hidden.QueryOnly.bind (OnLaw.queryOnly_mono (Guess.evalPadsM_encOnly _ _) fun q ⟨_, _, _, same⟩ => by
    subst same
    trivial) fun _ => ?_
  exact Hidden.QueryOnly.bind (evalLaneM_onQ input .pointX _ _ _) fun _ =>
    Hidden.QueryOnly.bind (evalLaneM_onQ input .pointY _ _ _) fun _ => Hidden.QueryOnly.pure' _

theorem evalPadsM_enc (a : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (E : PermutationOracle EncPRF.PermutationIndex Block)
    (hE : ∀ i x, a (.encForward i x) = E.permutation i x) (keys : WhiteningKeys) (bits : BitInput) :
    (Programs.evalPadsM keys bits).eval a = Programs.realEvalPads E keys bits := by
  refine (eval_agree (Guess.evalPadsM_encOnly keys bits) a
    (publicAnswer (⟨fun _ => Equiv.refl Block⟩, E, fun _ => ((0 : Block), (0 : Block)))) ?_).trans
    (Programs.eval_evalPadsM _ _ _)
  rintro q ⟨c, i, b, rfl⟩
  exact hE _ _

theorem preM_pads (a : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) (A : Table)
    (reads : TapeOn a A.2.2.2) (hE : ∀ i x, a (.encForward i x) = A.1.permutation i x)
    (hH : ∀ t, a (.hash (bridgeInput t)) = bridgeOf A.2.1 t) (P : Public) (mac : InputMac) :
    ((OnLaw.preM P (BitInput.ofAffine input) mac).eval a).1 = padsAt input P A.1 A.2.1 A.2.2.2 := by
  unfold OnLaw.preM
  rw [FreeQuery.eval_bind, curvePrefixM_tape reads, hH]
  simp only [FreeQuery.eval_bind, FreeQuery.eval_pure]
  rw [evalPadsM_enc a A.1 hE]
  rfl

/-- **The shadow asks each gadget position at its point.** -/
theorem shadow_gadAt (a : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) (A : Table)
    (reads : TapeOn a A.2.2.2) (hE : ∀ i x, a (.encForward i x) = A.1.permutation i x)
    (hH : ∀ t, a (.hash (bridgeInput t)) = bridgeOf A.2.1 t) (P : Public) (mac : InputMac) :
    Guess.AsksOnly a (GadAt input P mac A) (shadowOnM P (BitInput.ofAffine input) mac) := by
  unfold shadowOnM
  refine Guess.AsksOnly.bind (Guess.AsksOnly.of_queryOnly (OnLaw.queryOnly_mono
    (queryOnly_and (curvePrefixM_onQ input P mac) (OnLaw.notGadget_prefix _ _ _))
    (gadAt_of input P mac A))) (Guess.AsksOnly.bind ?_ (Guess.AsksOnly.bind ?_ (Guess.AsksOnly.pure' _)))
  · refine Guess.AsksOnly.of_queryOnly ?_
    unfold truePadsM
    have pad : ∀ (keys : WhiteningKeys) c i b, Hidden.QueryOnly (GadAt input P mac A)
        (Programs.padM keys c i b) := fun _ _ _ _ =>
      Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ trivial) fun _ => Hidden.QueryOnly.pure' _
    exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _ _ _) fun _ =>
      Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _ _ _) fun _ =>
        Hidden.QueryOnly.pure' _
  · rw [OnLaw.onCurveM_split]
    refine Guess.AsksOnly.bind_eq _ (Guess.AsksOnly.of_queryOnly (OnLaw.queryOnly_mono
      (queryOnly_and (preM_onQ input P mac) (OnLaw.notGadget_preM _ _ _)) (gadAt_of input P mac A))) rfl ?_
    unfold OnLaw.gadgetPart
    refine Guess.AsksOnly.bind ((Guess.AsksOnly.of_queryOnly (Guess.masksM_asks _ _)).mono ?_)
      (Guess.AsksOnly.pure' _)
    rintro q ⟨o, κ, p, rfl⟩
    show _ = gpt input P mac A (o, κ, p, _)
    unfold gpt
    rw [preM_pads input a A reads hE hH P mac]

/-! ### 2. The translations are table values -/

/-- The fresh table values of the translations. -/
def wOf (P : Public) (mac : InputMac) (A : Table) (v : GPos → Block) : FixedIndex → Block
  | .gadget o κ p b => gpt input P mac A (o, κ, p, b) ^^^ v (o, κ, p, b)
  | _ => 0

theorem freshPos_iff (K : FieldMacToECMac.SuccessfulOffsets) (k : GPos) :
    freshPos scalar K input k = true ↔ ¬ Planted scalar input K k.1 k.2.1 k.2.2.1 k.2.2.2 := by
  obtain ⟨o, κ, p, b⟩ := k
  have planted : Planted scalar input K o κ p b ↔ freshPos scalar K input (o, κ, p, b) = false := by
    rw [OnLaw.freshPos_false]
    show _ ↔ (digitEndomorphismBase (outputKeyOf scalar K o).digit).isSome = true ∧
      (inputBits input κ).getLsb p = b
    unfold Planted
    rw [Option.isSome_iff_exists]
  rw [planted, Bool.not_eq_false]

open Classical in
theorem freshen_hot (K : FieldMacToECMac.SuccessfulOffsets) (A : Table) (w : FixedIndex → Block)
    (lane : Lane) (c : Fin chunkCount) (fold : Fin chunkBits) (entry : Fin (2 ^ chunkBits)) (half : Bool)
    (x : Block) :
    tableAnswer (freshen scalar input K A w) (.fixedForward (.hot lane c fold entry half) x) =
      tableAnswer A (.fixedForward (.hot lane c fold entry half) x) := by
  show (if FreshQ scalar input K (.hot lane c fold entry half) then w _ else A.2.2.1 _) = A.2.2.1 _
  rw [if_neg (show ¬ FreshQ scalar input K (.hot lane c fold entry half) from id)]

open Classical in
theorem freshAnswer_table (K : FieldMacToECMac.SuccessfulOffsets) (P : Public) (mac : InputMac) (A : Table)
    (v : GPos → Block) :
    transcript (freshAnswer (freshPos scalar K input) v (tableAnswer A)) (shadowOnM P (BitInput.ofAffine input) mac) =
      transcript (tableAnswer (freshen scalar input K A (wOf input P mac A v)))
        (shadowOnM P (BitInput.ofAffine input) mac) := by
  have reads : TapeOn (freshAnswer (freshPos scalar K input) v (tableAnswer A)) A.2.2.2 := fun cell label =>
    tapeOn_table A cell label
  have bridge : ∀ t, freshAnswer (freshPos scalar K input) v (tableAnswer A) (.hash (bridgeInput t)) =
      bridgeOf A.2.1 t := fun t =>
    tableAnswer_other A ⟨bridgeInput t, bridgeInput_not_lt t⟩
  refine transcript_agree_asked _ _ (shadow_gadAt input _ A reads (fun _ _ => rfl) bridge P mac)
    fun q agree => ?_
  cases q with
  | fixedForward index x =>
      cases index with
      | gadget o κ p b =>
          have point : x = gpt input P mac A (o, κ, p, b) := agree
          have lhs : freshAnswer (freshPos scalar K input) v (tableAnswer A) (.fixedForward (.gadget o κ p b) x) =
              if freshPos scalar K input (o, κ, p, b) then x ^^^ v (o, κ, p, b)
              else A.2.2.1 (.gadget o κ p b) := rfl
          have rhs : tableAnswer (freshen scalar input K A (wOf input P mac A v))
              (.fixedForward (.gadget o κ p b) x) =
              if FreshQ scalar input K (.gadget o κ p b) then gpt input P mac A (o, κ, p, b) ^^^ v (o, κ, p, b)
              else A.2.2.1 (.gadget o κ p b) := rfl
          have fresh : FreshQ scalar input K (.gadget o κ p b) ↔ freshPos scalar K input (o, κ, p, b) = true :=
            (freshPos_iff scalar input K (o, κ, p, b)).symm
          rw [lhs, rhs]
          by_cases hf : freshPos scalar K input (o, κ, p, b) = true
          · rw [if_pos (fresh.mpr hf), if_pos hf, point]
          · rw [if_neg (fun h => hf (fresh.mp h)), if_neg hf]
      | hot ℓ c f e h => exact (freshen_hot scalar input K A _ ℓ c f e h x).symm
  | fixedInverse _ _ => exact agree.elim
  | encInverse _ _ => exact agree.elim
  | encForward _ _ => rfl
  | hash _ => rfl

/-! ### 3. C's form is `realTarget` -/

/-- Fixed-key answers from gadget values. -/
def extG (u : GPos → Block) : FixedIndex → Block
  | .gadget o κ p b => u (o, κ, p, b)
  | _ => 0

open Classical in
theorem freshen_extG (K : FieldMacToECMac.SuccessfulOffsets) (A : Table) (w : FixedIndex → Block) :
    freshen scalar input K A w = freshen scalar input K A (extG (w ∘ gIdx)) := by
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl))
  show (if FreshQ scalar input K i then w i else A.2.2.1 i) =
    (if FreshQ scalar input K i then extG (w ∘ gIdx) i else A.2.2.1 i)
  cases i with
  | gadget o κ p b => rfl
  | hot lane c fold entry half =>
      rw [if_neg (show ¬ FreshQ scalar input K (.hot lane c fold entry half) from id),
        if_neg (show ¬ FreshQ scalar input K (.hot lane c fold entry half) from id)]

/-- Shifting gadget values by a fixed family. -/
def shiftG (c : GPos → Block) : (GPos → Block) ≃ (GPos → Block) where
  toFun v k := c k ^^^ v k
  invFun v k := c k ^^^ v k
  left_inv v := funext fun k => by simp
  right_inv v := funext fun k => by simp

theorem wOf_eq (P : Public) (mac : InputMac) (A : Table) (v : GPos → Block) :
    wOf input P mac A v = extG (shiftG (gpt input P mac A) v) := by
  funext i
  cases i <;> rfl

/-- **C's garbler kernel is `realTarget`'s**, fresh translations as fresh table values. -/
theorem garbK_eq (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (coins : Coins) (A : Table) :
    garbK scalar input Ψ coins A =
      ∑' w, PMF.uniformOfFintype (FixedIndex → Block) w *
        Ψ ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
          (Scheme.scheme.encode ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 input)
          (plantAll (transcript (tableAnswer (freshen scalar input coins.offsets A w))
            (shadowOnM ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 (BitInput.ofAffine input)
              (coins.inputMacKey.encode (BitInput.ofAffine input)))) LazyOracle.empty) := by
  have second : ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 = coins.inputMacKey := by
    rw [garbleM_table]
  rw [second]
  unfold garbK
  set P := ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
  set mac := coins.inputMacKey.encode (BitInput.ofAffine input)
  let F : (FixedIndex → Block) → ℝ≥0∞ := fun w => Ψ P (Scheme.scheme.encode coins.inputMacKey input)
    (plantAll (transcript (tableAnswer (freshen scalar input coins.offsets A w))
      (shadowOnM P (BitInput.ofAffine input) mac)) LazyOracle.empty)
  have lhs : ∀ v, Ψ P (Scheme.scheme.encode coins.inputMacKey input)
      (plantAll (transcript (freshAnswer (freshPos scalar coins.offsets input) v (tableAnswer A))
        (shadowOnM P (BitInput.ofAffine input) mac)) LazyOracle.empty) =
      F (extG (shiftG (gpt input P mac A) v)) := fun v => by
    show _ = Ψ P _ _
    rw [freshAnswer_table, wOf_eq]
  rw [tsum_congr fun v => congrArg _ (lhs v)]
  have shift := tsum_equiv_uniform (shiftG (gpt input P mac A)).symm (fun u => F (extG u))
  rw [Equiv.symm_symm] at shift
  rw [← shift]
  have rhs : ∀ w, F w = F (extG (w ∘ gIdx)) := fun w => by
    show Ψ P _ _ = Ψ P _ _
    rw [← freshen_extG]
  rw [tsum_congr fun w => congrArg _ (rhs w)]
  exact (tsum_restrict gIdx gIdx_injective (fun u => F (extG u))).symm

open Classical in
/-- **C's garbler form is `realTarget`.** -/
theorem onGarbForm_eq (Ψ : Public → LamportSignature → LState → ℝ≥0∞) :
    onGarbForm scalar input Ψ = realTarget scalar input Ψ := by
  unfold onGarbForm realTarget
  simp only [garbK_eq scalar input Ψ]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
