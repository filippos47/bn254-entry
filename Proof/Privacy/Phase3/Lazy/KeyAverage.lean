/-
**Phase 3, P4b — (c) the bit-0 label is uniform after key averaging.**

The Lamport key is uniform and independent of stage 1. Resampling the label pair of bit 0 of `x`
(`key_resample`) changes, in the whole run, only

* the raw level-1 label of chunk 0 of `curveX`, `W_c = raw₀` (`curveLabel_eq`), and
* the whitened level-1 label of chunk 0 of `pointX`, `W = pad₀ xor raw₀` (`pointLabel_eq`);

the rest of system A, the bridge hash and the pads (`curveRest`) never read `raw₀`
(`curveRest_setX0`). So `raw₀` is a uniform block independent of the pads' law, the fold hits of
both lanes cost `n(i₁ᶜ)/2^128` and `n(i₁)/2^128` (`key_sum_le`).
-/

import Proof.Privacy.Phase3.Lazy.FailCurve
import Proof.Privacy.Phase3.Lazy.AbortReduction

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### The label pair of one bit -/

/-- A bit key is its two labels. -/
def keyEquiv : BitAdaptor.Key ≃ Block × Block where
  toFun key := (key.falseLabel, key.trueLabel)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance bitKeyFintype : Fintype BitAdaptor.Key := Fintype.ofEquiv _ keyEquiv.symm

instance bitKeyNonempty : Nonempty BitAdaptor.Key := ⟨⟨0, 0⟩⟩

/-- **The selected label of a uniform bit key is a uniform block.** -/
theorem uniform_encode (bit : Bool) :
    (PMF.uniformOfFintype BitAdaptor.Key).map (fun key => BitAdaptor.encode key bit) =
      PMF.uniformOfFintype Block := by
  rw [← uniform_equiv keyEquiv.symm, PMF.map_comp]
  cases bit with
  | false =>
      have same : ((fun key => BitAdaptor.encode key false) ∘ keyEquiv.symm) = Prod.fst := by
        funext pair
        rfl
      rw [same, uniform_map_fst]
  | true =>
      have same : ((fun key => BitAdaptor.encode key true) ∘ keyEquiv.symm) =
          Prod.fst ∘ Equiv.prodComm Block Block := by
        funext pair
        rfl
      rw [same, ← PMF.map_comp, uniform_equiv, uniform_map_fst]

/-- The uniform block charges `1/2^128` per unit of an observable. -/
theorem uniform_block_apply (a : Block) :
    PMF.uniformOfFintype Block a = ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [PMF.uniformOfFintype_apply, card_block]

/-- **A uniform block hits a stage-1 domain, after any XOR shift, with mass `n/2^128`.** -/
theorem uniform_known_sum (state : SparsePermutation (2 ^ 128)) (c : Block) :
    ∑' a, PMF.uniformOfFintype Block a *
        (if state.knownInput (c ^^^ a).toFin then (1 : ℝ≥0∞) else 0) =
      ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * state.used := by
  simp only [uniform_block_apply]
  rw [ENNReal.tsum_mul_left, sum_knownInput_xor]

/-! ### Resampling the label pair of bit 0 of `x` -/

/-- The key with the label pair of bit 0 of `x` replaced. -/
def setX0 (key : InputMacKey) (pair : BitAdaptor.Key) : InputMacKey :=
  { key with x := key.x.set 0 pair }

/-- `(key, pair) ↦ (key[x₀ := pair], key.x₀)` is an involution. -/
def swapX0 : (InputMacKey × BitAdaptor.Key) ≃ (InputMacKey × BitAdaptor.Key) where
  toFun pair := (setX0 pair.1 pair.2, pair.1.x[0])
  invFun pair := (setX0 pair.1 pair.2, pair.1.x[0])
  left_inv pair := by
    obtain ⟨key, bitKey⟩ := pair
    simp only [setX0, Vector.getElem_set_self, Vector.set_set, Prod.mk.injEq, and_true]
    cases key
    simp only [InputMacKey.mk.injEq, and_true]
    exact Vector.set_getElem_self _
  right_inv pair := by
    obtain ⟨key, bitKey⟩ := pair
    simp only [setX0, Vector.getElem_set_self, Vector.set_set, Prod.mk.injEq, and_true]
    cases key
    simp only [InputMacKey.mk.injEq, and_true]
    exact Vector.set_getElem_self _

/-- **A uniform key is a uniform key with an independent uniform pair written at bit 0 of `x`.** -/
theorem uniform_setX0 :
    (PMF.uniformOfFintype InputMacKey).bind (fun key =>
        (PMF.uniformOfFintype BitAdaptor.Key).map (setX0 key)) =
      PMF.uniformOfFintype InputMacKey := by
  have product := uniform_product (A := InputMacKey) (B := BitAdaptor.Key)
  have swapped : (PMF.uniformOfFintype (InputMacKey × BitAdaptor.Key)).map
      (fun pair => setX0 pair.1 pair.2) = PMF.uniformOfFintype InputMacKey := by
    have factor : (fun pair : InputMacKey × BitAdaptor.Key => setX0 pair.1 pair.2) =
        Prod.fst ∘ swapX0 := rfl
    rw [factor, ← PMF.map_comp, uniform_equiv swapX0, uniform_map_fst]
  calc (PMF.uniformOfFintype InputMacKey).bind (fun key =>
        (PMF.uniformOfFintype BitAdaptor.Key).map (setX0 key))
      = ((PMF.uniformOfFintype InputMacKey).bind fun key =>
          (PMF.uniformOfFintype BitAdaptor.Key).map fun pair => (key, pair)).map
            (fun pair => setX0 pair.1 pair.2) := by
        rw [PMF.map_bind]
        refine congrArg _ (funext fun key => ?_)
        rw [PMF.map_comp]
        rfl
    _ = PMF.uniformOfFintype InputMacKey := by rw [product, swapped]

/-- **The key average, with bit 0 of `x` resampled.** -/
theorem key_resample (value : InputMacKey → ℝ≥0∞) :
    ∑' key, PMF.uniformOfFintype InputMacKey key * value key =
      ∑' key, PMF.uniformOfFintype InputMacKey key *
        ∑' pair, PMF.uniformOfFintype BitAdaptor.Key pair * value (setX0 key pair) := by
  conv_lhs => rw [← uniform_setX0]
  rw [tsum_bind_mul]
  exact tsum_congr fun key => by rw [tsum_map_mul]

/-! ### What resampling changes -/

theorem encode_setX0_zero (key : InputMacKey) (pair : BitAdaptor.Key) (bits : BitInput) :
    ((setX0 key pair).encode bits).x.get ⟨0, by decide⟩ =
      BitAdaptor.encode pair (bits.xBits.getLsb ⟨0, by decide⟩) := by
  simp only [setX0, InputMacKey.encode, encodeCoordinate, Vector.get_ofFn]
  show BitAdaptor.encode (key.x.set 0 pair (by decide))[0] _ = _
  rw [Vector.getElem_set_self]

theorem encode_setX0_ne (key : InputMacKey) (pair : BitAdaptor.Key) (bits : BitInput)
    (position : Fin coordinateBitCount) (away : position.val ≠ 0) :
    ((setX0 key pair).encode bits).x.get position = (key.encode bits).x.get position := by
  simp only [setX0, InputMacKey.encode, encodeCoordinate, Vector.get_ofFn]
  rw [Vector.getElem_set_ne _ _ (Ne.symm away)]

theorem encode_setX0_y (key : InputMacKey) (pair : BitAdaptor.Key) (bits : BitInput) :
    ((setX0 key pair).encode bits).y = (key.encode bits).y := rfl

/-- The level-1 label of chunk 0 is the bit-0 label. -/
theorem chunkLabel_eq (joins : Vector Block foldStepCount)
    (labels : Fin coordinateBitCount → Block) :
    chunkLabel joins labels = labels ⟨0, by decide⟩ := by
  have join0 : joinAt (hotSlice joins chunkZero) 0 = 0 := rfl
  have label0 : labelAt (chunkLabels labels chunkZero) 0 = labels ⟨0, by decide⟩ := rfl
  unfold chunkLabel
  rw [join0, label0]
  exact BitVec.zero_xor

variable [FieldCertificate]

theorem curveLabel_eq (table : Public) (mac : InputMac) :
    curveLabel table mac = mac.x.get ⟨0, by decide⟩ :=
  chunkLabel_eq _ _

theorem pointLabel_eq (table : Public) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    pointLabel table mac pads = (pads .x ⟨0, by decide⟩).1 ^^^ mac.x.get ⟨0, by decide⟩ := by
  unfold pointLabel
  rw [chunkLabel_eq]
  simp [Pipeline.macLabels, Programs.whitenMacOf, encrypt, Vector.get]
  rfl

theorem evalChunkM_congr (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels labels' : Fin coordinateBitCount → Block) (c : Fin chunkCount)
    (same : chunkLabels labels c = chunkLabels labels' c) :
    Programs.evalChunkM lane joins scale bits labels c =
      Programs.evalChunkM lane joins scale bits labels' c := by
  unfold Programs.evalChunkM
  rw [same]

/-- The chunks `1 … 55` of a lane read only their own labels. -/
theorem laneRest_congr {β : Type} (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels labels' : Fin coordinateBitCount → Block)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Vector BaseField (laneCount lane))
    (k : (Fin (laneCount lane) → BaseField) → FreeQuery Programs.Spec β)
    (same : ∀ index : Fin 55,
      chunkLabels labels (index.succ : Fin chunkCount) =
        chunkLabels labels' (index.succ : Fin chunkCount)) :
    laneRest lane joins scale bits labels masks k =
      laneRest lane joins scale bits labels' masks k := by
  have chunks : (fun index : Fin 55 =>
      Programs.evalChunkM lane joins scale bits labels index.succ) =
      fun index => Programs.evalChunkM lane joins scale bits labels' index.succ :=
    funext fun index => evalChunkM_congr _ _ _ _ _ _ _ (same index)
  unfold laneRest
  rw [chunks]

/-- **The rest of system A, the bridge hash and the pads do not read the bit-0 label of `x`.** -/
theorem curveRest_congr (table : Public) (bits : BitInput) (mac mac' : InputMac)
    (sameY : mac'.y = mac.y)
    (sameX : ∀ position : Fin coordinateBitCount, position.val ≠ 0 →
      mac'.x.get position = mac.x.get position)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Vector BaseField curveElementCountX) :
    curveRest table bits mac' masks = curveRest table bits mac masks := by
  have labelsY : Pipeline.macLabels mac' .y = Pipeline.macLabels mac .y := by
    funext position
    simp only [Pipeline.macLabels, sameY]
  have tail : curveTail table bits mac' = curveTail table bits mac := by
    funext curveX
    unfold curveTail
    rw [labelsY]
  unfold curveRest
  rw [tail]
  refine laneRest_congr _ _ _ _ _ _ _ _ fun index => funext fun position => ?_
  refine sameX _ ?_
  show chunkOffset (index.succ : Fin chunkCount) + position.val ≠ 0
  unfold chunkOffset
  rw [if_neg (by simp)]
  unfold firstChunkBits
  split_ifs <;> omega

theorem curveRest_setX0 (table : Public) (bits : BitInput) (key : InputMacKey)
    (pair : BitAdaptor.Key)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Vector BaseField curveElementCountX) :
    curveRest table bits ((setX0 key pair).encode bits) masks =
      curveRest table bits (key.encode bits) masks :=
  curveRest_congr table bits _ _ (encode_setX0_y key pair bits)
    (encode_setX0_ne key pair bits) masks

end

end Kriterion.ArgoMAC.Phase3.Lazy
