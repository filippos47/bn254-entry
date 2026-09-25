/-
**Phase 3, P1n — the off-curve law, step (ii), part 3: the published law on a table.**

`published_law`: for fixed pads, the garbler's published value on a table (`pubOf`, which is
`tablePub` read through the mask vectors, `tablePub_cells`), jointly with its selected labels' MAC,
the view's fold answers (`viewIdx`: the curve lanes' gate halves off the active parent, every paid
step) and the view's curve masks (the inactive curve masks), is a uniform source's published value,
an independent uniform key's MAC and independent uniform answers and masks. The proof reads the
garbler's randomness as the rest and F4's coins (`omegaEquiv`), applies **`jointExactness`** at the
context of the rest, and reads the rest's labels (`macs_uniform`) and view answers
(`tsum_restrict`) as uniform.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOffMatch

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape)
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source)
open scoped ENNReal

noncomputable section

/-! ### 1. Uniform averages along restrictions -/

variable [FieldCertificate]

/-- **A uniform function restricted along an injective map is uniform.** -/
theorem tsum_restrict {I J β : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype β] [Nonempty β] (ι : J → I) (inj : Function.Injective ι) (f : (J → β) → ℝ≥0∞) :
    ∑' g, PMF.uniformOfFintype (I → β) g * f (g ∘ ι) =
      ∑' a, PMF.uniformOfFintype (J → β) a * f a := by
  classical
  rw [tsum_equiv_uniform (splitAlong ι inj), tsum_uniform_prod]
  refine tsum_congr fun a => congrArg _ ?_
  have image : ∀ b, (splitAlong ι inj).symm (a, b) ∘ ι = a := fun b =>
    funext fun j => splitAlong_symm_image ι inj a b j
  simp only [image]
  exact tsum_const_uniform _

/-! ### 2. The selected labels' MAC is uniform, for a uniform key and for the coins' labels -/

section Macs

local instance vectorFinite' {α : Type} [Finite α] {n : Nat} : Finite (Vector α n) :=
  Finite.of_injective (fun v : Vector α n => fun i : Fin n => v[i]) (by
    intro a b same
    apply Vector.ext
    intro i bound
    exact congrFun same ⟨i, bound⟩)

instance inputMacFinite : Finite InputMac :=
  Finite.of_injective (fun m : InputMac => (m.x, m.y)) (by
    intro a b same
    exact InputMac.ext (congrArg Prod.fst same) (congrArg Prod.snd same))

noncomputable instance inputMacFintype : Fintype InputMac := Fintype.ofFinite _

instance inputMacNonempty : Nonempty InputMac := ⟨⟨Vector.replicate _ 0, Vector.replicate _ 0⟩⟩

/-- Positionwise XOR of two MACs. -/
def macXor (a b : InputMac) : InputMac :=
  ⟨Vector.ofFn fun i => a.x.get i ^^^ b.x.get i, Vector.ofFn fun i => a.y.get i ^^^ b.y.get i⟩

theorem macXor_cancel (a b : InputMac) : macXor a (macXor a b) = b := by
  refine InputMac.ext (Vector.ext fun i bound => ?_) (Vector.ext fun i bound => ?_) <;>
    simp [macXor, Vector.get_eq_getElem]

theorem macXor_comm (a b : InputMac) : macXor a b = macXor b a := by
  refine InputMac.ext (Vector.ext fun i bound => ?_) (Vector.ext fun i bound => ?_) <;>
    simp [macXor, Vector.get_eq_getElem, BitVec.xor_comm]

/-- Shift both labels of every position by a MAC. -/
def shiftKey (δ : InputMac) (key : InputMacKey) : InputMacKey :=
  ⟨Vector.ofFn fun i => ⟨(key.x.get i).falseLabel ^^^ δ.x.get i, (key.x.get i).trueLabel ^^^ δ.x.get i⟩,
   Vector.ofFn fun i => ⟨(key.y.get i).falseLabel ^^^ δ.y.get i, (key.y.get i).trueLabel ^^^ δ.y.get i⟩⟩

theorem encode_shiftKey (δ : InputMac) (key : InputMacKey) (bits : BitInput) :
    (shiftKey δ key).encode bits = macXor (key.encode bits) δ := by
  refine InputMac.ext (Vector.ext fun i bound => ?_) (Vector.ext fun i bound => ?_) <;>
    simp only [InputMacKey.encode, encodeCoordinate, shiftKey, macXor, BitAdaptor.encode,
      Vector.getElem_ofFn, Vector.get_eq_getElem] <;> split <;> rfl

theorem shiftKey_shiftKey (δ : InputMac) (key : InputMacKey) : shiftKey δ (shiftKey δ key) = key := by
  obtain ⟨x, y⟩ := key
  simp only [shiftKey, InputMacKey.mk.injEq]
  constructor <;> refine Vector.ext fun i bound => ?_ <;>
    simp [Vector.get_eq_getElem, BitVec.xor_assoc]

/-- **A uniform key's MAC at any input is uniform.** -/
theorem macs_uniform (bits : BitInput) :
    (PMF.uniformOfFintype InputMacKey).map (fun key => key.encode bits) =
      PMF.uniformOfFintype InputMac := by
  classical
  refine uniform_map_of_fibre_equiv _ fun first second => ?_
  exact {
    toFun := fun key => ⟨shiftKey (macXor first second) key.1, by
      rw [encode_shiftKey, key.2, macXor_cancel]⟩
    invFun := fun key => ⟨shiftKey (macXor first second) key.1, by
      rw [encode_shiftKey, key.2, macXor_comm first second, macXor_cancel]⟩
    left_inv := fun key => Subtype.ext (shiftKey_shiftKey _ _)
    right_inv := fun key => Subtype.ext (shiftKey_shiftKey _ _) }

/-- Shift zero labels by a MAC. -/
def shiftZ (δ : InputMac) (Z : Coord → Fin coordinateBitCount → Block) :
    Coord → Fin coordinateBitCount → Block
  | .x, p => Z .x p ^^^ δ.x.get p
  | .y, p => Z .y p ^^^ δ.y.get p

theorem labelKey_shiftZ (δ : InputMac) (Z : Coord → Fin coordinateBitCount → Block) (Δ : Coord → Block) :
    labelKey (shiftZ δ Z) Δ = shiftKey δ (labelKey Z Δ) := by
  have swap : ∀ a b c : Block, (a ^^^ b) ^^^ c = (a ^^^ c) ^^^ b := fun a b c => by
    rw [BitVec.xor_assoc, BitVec.xor_comm b c, ← BitVec.xor_assoc]
  simp only [labelKey, shiftKey, shiftZ, InputMacKey.mk.injEq]
  constructor <;> refine Vector.ext fun i bound => ?_ <;>
    simp only [Vector.getElem_ofFn, Vector.get_eq_getElem] <;>
    exact congrArg (BitAdaptor.Key.mk _) (swap _ _ _)

theorem shiftZ_shiftZ (δ : InputMac) (Z : Coord → Fin coordinateBitCount → Block) :
    shiftZ δ (shiftZ δ Z) = Z := by
  funext c p
  cases c <;> simp [shiftZ, BitVec.xor_assoc]

/-- **The coins' selected labels' MAC is uniform, for every `Δ`.** -/
theorem labelMacs_uniform (Δ : Coord → Block) (bits : BitInput) :
    (PMF.uniformOfFintype (Coord → Fin coordinateBitCount → Block)).map
        (fun Z => (labelKey Z Δ).encode bits) = PMF.uniformOfFintype InputMac := by
  classical
  refine uniform_map_of_fibre_equiv _ fun first second => ?_
  exact {
    toFun := fun Z => ⟨shiftZ (macXor first second) Z.1, by
      show (labelKey _ Δ).encode bits = second
      rw [labelKey_shiftZ, encode_shiftKey, Z.2, macXor_cancel]⟩
    invFun := fun Z => ⟨shiftZ (macXor first second) Z.1, by
      show (labelKey _ Δ).encode bits = first
      rw [labelKey_shiftZ, encode_shiftKey, Z.2, macXor_comm first second, macXor_cancel]⟩
    left_inv := fun Z => Subtype.ext (shiftZ_shiftZ _ _)
    right_inv := fun Z => Subtype.ext (shiftZ_shiftZ _ _) }

/-- **The coins' labels and a uniform key select alike-distributed MACs.** -/
theorem tsum_labels (bits : BitInput) (f : InputMac → ℝ≥0∞) :
    ∑' Z, PMF.uniformOfFintype (Coord → Fin coordinateBitCount → Block) Z *
        ∑' Δ, PMF.uniformOfFintype (Coord → Block) Δ * f ((labelKey Z Δ).encode bits) =
      ∑' key, PMF.uniformOfFintype InputMacKey key * f (key.encode bits) := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  have each : ∀ Δ : Coord → Block, ∑' Z, PMF.uniformOfFintype (Coord → Fin coordinateBitCount → Block) Z *
      (PMF.uniformOfFintype (Coord → Block) Δ * f ((labelKey Z Δ).encode bits)) =
      PMF.uniformOfFintype (Coord → Block) Δ *
        ∑' mac, PMF.uniformOfFintype InputMac mac * f mac := by
    intro Δ
    rw [← labelMacs_uniform Δ bits, tsum_map_mul, ← ENNReal.tsum_mul_left]
    exact tsum_congr fun Z => by ring
  simp only [each]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, ← macs_uniform bits, tsum_map_mul]

end Macs

/-! ### 3. The published law -/

section Law

variable [GroupCertificate] (scalar : NonZeroScalar) (input : AffineInput) (pads : Programs.Pads)

noncomputable instance clampedFintype : Fintype ClampedOffsets := Fintype.ofFinite _

instance clampedNonempty : Nonempty ClampedOffsets :=
  ⟨⟨Kriterion.ArgoMAC.Scheme.witness.offsets, Kriterion.ArgoMAC.Scheme.witness.offsetsClamped⟩⟩

noncomputable instance restFintype : Fintype (RestIdx input) := Fintype.ofFinite _

/-- The input's shape (its active switches). -/
abbrev offShape : JointShape := JointShape.ofInput input

/-- **The garbler's published value on a table, read through the mask vectors.** -/
def pubOf (coins : Coins) (v : FixedIndex → Block) (m : MaskVectors) : Public :=
  (cellsSource (publicOf (offContext input pads
      (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
      (omegaEquiv input scalar (coins, v, m)).1) (omegaEquiv input scalar (coins, v, m)).2) defaultKey).publicValue

/-- The garbler's randomness, read back from the rest and F4's coins. -/
theorem omega_symm (o : Outer input) (jc : JointCoins) :
    let ω := (omegaEquiv input scalar).symm (o, jc)
    pubOf scalar input pads ω.1 ω.2.1 ω.2.2 = (cellsSource (publicOf (offContext input pads
        (FieldMacToECMac.outputKeys construction scalar.value o.1.1) o) jc) defaultKey).publicValue ∧
      ω.1.inputMacKey.encode (BitInput.ofAffine input) =
        (labelKey o.2.2.1 o.2.2.2.1).encode (BitInput.ofAffine input) ∧
      ω.2.1 ∘ viewIdx input = o.2.2.2.2 ∘ viewRest input ∧
      curveVisible (offShape input) (maskSiteEquiv (maskCoordEquiv ω.2.2)).2 =
        (visibleOf (offShape input) jc).2 := by
  intro ω
  have back : omegaEquiv input scalar (ω.1, ω.2.1, ω.2.2) = (o, jc) := (omegaEquiv input scalar).apply_symm_apply _
  refine ⟨?_, rfl, funext fun w => ?_, ?_⟩
  · unfold pubOf
    rw [back]
    rfl
  · show ((regroup input).symm (o, jc)).2.1 (indexSwap _ (viewIdx input w)) = _
    rw [indexSwap_view]
    exact splitAlong_symm_rest (hiddenIdx input) (hiddenIdx_injective input) _ _ (viewRest input w)
  · show curveVisible (offShape input)
      (maskSiteEquiv (maskCoordEquiv (maskCoordEquiv.symm (maskSiteEquiv.symm _)))).2 = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl

/-- **The published law** on a table, for fixed pads: the published value, the selected labels'
MAC, the view's fold answers and the view's curve masks are a uniform source's published value, an
independent uniform key's MAC, and independent uniform answers and masks. -/
theorem published_law
    (F : Public → InputMac → (ViewIdx input → Block) → CurveVisible (offShape input) → ℝ≥0∞) :
    ∑' coins, PMF.uniformOfFintype Coins coins * ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
      ∑' m, PMF.uniformOfFintype MaskVectors m *
        F (pubOf scalar input pads coins v m) (coins.inputMacKey.encode (BitInput.ofAffine input))
          (v ∘ viewIdx input) (curveVisible (offShape input) (maskSiteEquiv (maskCoordEquiv m)).2) =
    ∑' cells, PMF.uniformOfFintype PublicCells cells *
      ∑' vis, PMF.uniformOfFintype (CurveVisible (offShape input)) vis *
        ∑' key, PMF.uniformOfFintype InputMacKey key *
          ∑' w, PMF.uniformOfFintype (ViewIdx input → Block) w *
            F (cellsSource cells defaultKey).publicValue (key.encode (BitInput.ofAffine input)) w
              vis := by
  classical
  let G : Omega → ℝ≥0∞ := fun ω => F (pubOf scalar input pads ω.1 ω.2.1 ω.2.2)
    (ω.1.inputMacKey.encode (BitInput.ofAffine input)) (ω.2.1 ∘ viewIdx input)
    (curveVisible (offShape input) (maskSiteEquiv (maskCoordEquiv ω.2.2)).2)
  let H : Outer input → PublicCells × VisibleCells (offShape input) → ℝ≥0∞ := fun o p =>
    F (cellsSource p.1 defaultKey).publicValue ((labelKey o.2.2.1 o.2.2.2.1).encode (BitInput.ofAffine input))
      (o.2.2.2.2 ∘ viewRest input) p.2.2
  have triple : ∑' coins, PMF.uniformOfFintype Coins coins *
      ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
        ∑' m, PMF.uniformOfFintype MaskVectors m * G (coins, v, m) =
      ∑' ω : Omega, PMF.uniformOfFintype Omega ω * G ω := by
    rw [tsum_uniform_prod (α := Coins) (β := (FixedIndex → Block) × MaskVectors) G]
    refine tsum_congr fun coins => congrArg _ ?_
    rw [tsum_uniform_prod (α := FixedIndex → Block) (β := MaskVectors) (fun p => G (coins, p))]
  have inner : ∀ o : Outer input, ∑' jc, PMF.uniformOfFintype JointCoins jc *
      G ((omegaEquiv input scalar).symm (o, jc)) =
      ∑' cells, PMF.uniformOfFintype PublicCells cells *
        ∑' vis, PMF.uniformOfFintype (CurveVisible (offShape input)) vis * H o (cells, ((fun _ => fun _ _ => 0), vis)) := by
    intro o
    have pointwise : ∀ jc, G ((omegaEquiv input scalar).symm (o, jc)) =
        H o ((publicOf (offContext input pads
          (FieldMacToECMac.outputKeys construction scalar.value o.1.1) o) jc, visibleOf (offShape input) jc)) := by
      intro jc
      obtain ⟨h1, h2, h3, h4⟩ := omega_symm scalar input pads o jc
      show F _ _ _ _ = F _ _ _ _
      rw [h1, h2, h3, h4]
    simp only [pointwise]
    rw [← tsum_map_mul (PMF.uniformOfFintype JointCoins) (fun jc => (publicOf (offContext input pads
      (FieldMacToECMac.outputKeys construction scalar.value o.1.1) o) jc, visibleOf (offShape input) jc))
      (H o), jointExactness, tsum_uniform_prod]
    refine tsum_congr fun cells => congrArg _ ?_
    rw [tsum_uniform_prod]
    simp only [H]
    exact tsum_const_uniform (X := Fin digitCount → DigitVisible (offShape input)) _
  have outer : ∀ (cells : PublicCells) (vis : CurveVisible (offShape input)),
      ∑' o, PMF.uniformOfFintype (Outer input) o * H o (cells, ((fun _ => fun _ _ => 0), vis)) =
        ∑' key, PMF.uniformOfFintype InputMacKey key *
          ∑' w, PMF.uniformOfFintype (ViewIdx input → Block) w *
            F (cellsSource cells defaultKey).publicValue (key.encode (BitInput.ofAffine input)) w
              vis := by
    intro cells vis
    rw [tsum_uniform_prod (α := ClampedOffsets)]
    simp only [H]
    rw [tsum_const_uniform, tsum_uniform_prod (α := Fin digitCount → NonZeroBase × NonZeroBase)]
    dsimp only
    rw [tsum_const_uniform, tsum_uniform_prod (α := Coord → Fin coordinateBitCount → Block)]
    dsimp only
    refine (tsum_congr fun Z => congrArg _ ?_).trans (tsum_labels (BitInput.ofAffine input) fun mac =>
      ∑' w, PMF.uniformOfFintype (ViewIdx input → Block) w *
        F (cellsSource cells defaultKey).publicValue mac w vis)
    rw [tsum_uniform_prod (α := Coord → Block)]
    dsimp only
    refine tsum_congr fun Δ => congrArg _ ?_
    exact tsum_restrict (viewRest input) (viewRest_injective input)
      (fun w => F (cellsSource cells defaultKey).publicValue
        ((labelKey Z Δ).encode (BitInput.ofAffine input)) w vis)
  calc _ = ∑' ω : Omega, PMF.uniformOfFintype Omega ω * G ω := triple
    _ = ∑' o, PMF.uniformOfFintype (Outer input) o * ∑' jc, PMF.uniformOfFintype JointCoins jc *
          G ((omegaEquiv input scalar).symm (o, jc)) := by
        rw [tsum_equiv_uniform (omegaEquiv input scalar) G,
          tsum_uniform_prod (α := Outer input) (β := JointCoins)]
    _ = ∑' o, PMF.uniformOfFintype (Outer input) o * ∑' cells, PMF.uniformOfFintype PublicCells cells *
          ∑' vis, PMF.uniformOfFintype (CurveVisible (offShape input)) vis *
            H o (cells, ((fun _ => fun _ _ => 0), vis)) := tsum_congr fun o => by rw [inner o]
    _ = _ := by
        rw [tsum_swap_mul]
        refine tsum_congr fun cells => congrArg _ ?_
        rw [tsum_swap_mul]
        exact tsum_congr fun vis => congrArg _ (outer cells vis)

end Law

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
