/-
**Phase 3, P1r — `LawOn`, step (E), part 8: the garbler's randomness at fixed offsets is F4's coins,
and its published value F4's cells (hidden fold material at every paid step, hidden gadget answers
at any position).**

* `regroupW`: the coins without their offsets (`CoinsRest`), the fixed-key answers and the masks are
  the rest (`OuterW`: `ρ`, the labels, the fixed-key answers off `hidW pos`) and F4's coins;
* `ctxW`: F4's context of the rest, at the output keys and the pads;
* **`tablePub_cellsW`**: the garbler's published value on a table is the source of F4's published
  cells `publicOf (ctxW …) jc` (the fold joins with their active parents' first gate halves hidden,
  the digests with their answers at `pos` hidden).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnECells

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate] (input : AffineInput)
  (pos : Fin digitCount → Coord × Fin PlanB.coordinateBits)

/-! ### 1. The coins without their offsets, the other answers and the masks -/

/-- The coins' fields but their offsets (`CoinsParts = ClampedOffsets × CoinsRest`). -/
abbrev CoinsRest := (Fin outputMacCount → RowRandomness) × (Fin outputMacCount → Exception.Entry) ×
  BaseField × NonZeroBase × BaseField × BaseField × (Coord → Fin coordinateBitCount → Block) × (Coord → Block)

/-- The coins' fields but their offsets. -/
def coinsRest (coins : Coins) : CoinsRest := (coinsSplit coins).2

/-- The fixed-key answers off the hidden ones. -/
abbrev RestW := {i : FixedIndex // i ∉ Set.range (hidW input pos)}

/-- **What F4's coins leave out, at fixed offsets**: `ρ`, the labels, the fixed-key answers off the
hidden ones. -/
abbrev OuterW := (Fin digitCount → NonZeroBase) × (Coord → Fin coordinateBitCount → Block) ×
  (Coord → Block) × (RestW input pos → Block)

/-- **The coins without their offsets, the fixed-key answers and the masks are the rest and F4's
coins.** -/
def regroupW : CoinsRest × (FixedIndex → Block) × (MaskCoord → BaseField) ≃ OuterW input pos × JointCoins where
  toFun ω :=
    ((fun d => (ω.1.1 d).rho, ω.1.2.2.2.2.2.2.1, ω.1.2.2.2.2.2.2.2,
        (splitAlong (hidW input pos) (hidW_injective input pos) ω.2.1).2),
      (fun d => ((maskSiteEquiv ω.2.2).1 d, ((ω.1.1 d).x, (ω.1.1 d).y, (ω.1.1 d).z)),
        ((maskSiteEquiv ω.2.2).2, ω.1.2.2.1, ⟨ω.1.2.2.2.1.value, ω.1.2.2.2.1.nonzero⟩,
          ω.1.2.2.2.2.1, ω.1.2.2.2.2.2.1),
        (fun ℓ c => ω.2.1 (hidW input pos (.inl (ℓ, c))),
          fun d => (ω.1.2.1 d, ω.2.1 (hidW input pos (.inr d))))))
  invFun p :=
    ((fun d => ⟨p.1.1 d, (p.2.1 d).2.1, (p.2.1 d).2.2.1, (p.2.1 d).2.2.2⟩,
        fun d => (p.2.2.2.2 d).1, p.2.2.1.2.1, ⟨p.2.2.1.2.2.1.1, p.2.2.1.2.2.1.2⟩,
        p.2.2.1.2.2.2.1, p.2.2.1.2.2.2.2, p.1.2.1, p.1.2.2.1),
      (splitAlong (hidW input pos) (hidW_injective input pos)).symm
        (Sum.elim (fun q => p.2.2.2.1 q.1 q.2) (fun d => (p.2.2.2.2 d).2), p.1.2.2.2),
      maskSiteEquiv.symm (fun d => (p.2.1 d).1, p.2.2.1.1))
  left_inv ω := by
    obtain ⟨⟨pR, pad, t, mask, r1, r2, Z, Δ⟩, v, m⟩ := ω
    have hidden : (Sum.elim (fun q : Lane × Fin foldStepCount => v (hidW input pos (.inl (q.1, q.2))))
        (fun d => v (hidW input pos (.inr d)))) =
        (splitAlong (hidW input pos) (hidW_injective input pos) v).1 := by
      funext q
      rcases q with ⟨ℓ, c⟩ | d <;> rfl
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · show (splitAlong (hidW input pos) (hidW_injective input pos)).symm
        (Sum.elim (fun q : Lane × Fin foldStepCount => v (hidW input pos (.inl (q.1, q.2))))
          (fun d => v (hidW input pos (.inr d))),
         (splitAlong (hidW input pos) (hidW_injective input pos) v).2) = v
      rw [hidden, Prod.mk.eta, Equiv.symm_apply_apply]
    · show maskSiteEquiv.symm ((maskSiteEquiv m).1, (maskSiteEquiv m).2) = m
      rw [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv p := by
    obtain ⟨⟨rho, Z, Δ, rest⟩, digits, ⟨cm, t, mask, r1, r2⟩, fold, gadget⟩ := p
    have masks : maskSiteEquiv (maskSiteEquiv.symm (fun d => (digits d).1, cm)) =
        (fun d => (digits d).1, cm) := Equiv.apply_symm_apply _ _
    refine Prod.ext (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_)))
      (Prod.ext (funext fun d => ?_) (Prod.ext (Prod.ext ?_ rfl) (Prod.ext
        (funext fun ℓ => funext fun c => ?_) (funext fun d => ?_))))
    · show ((splitAlong (hidW input pos) (hidW_injective input pos))
        ((splitAlong (hidW input pos) (hidW_injective input pos)).symm (_, rest))).2 = rest
      rw [Equiv.apply_symm_apply]
    · exact Prod.ext (congrFun (congrArg Prod.fst masks) d) rfl
    · exact congrArg Prod.snd masks
    · exact splitAlong_symm_image (hidW input pos) (hidW_injective input pos) _ _ (.inl (ℓ, c))
    · exact Prod.ext rfl
        (splitAlong_symm_image (hidW input pos) (hidW_injective input pos) _ _ (.inr d))

/-! ### 2. F4's context of the rest, and the matching -/

variable (pads : Programs.Pads)

/-- **F4's context of the rest**, at the output keys and the pads. -/
def ctxW (keys : OutputKeys) (o : OuterW input pos) : JointContext where
  rows d := Coordinates.rows (keys.get d).offset.coordinates
    (digitEndomorphismBase (keys.get d).digit) (o.1 d).value
  rho d := o.1 d
  foldVisible _ lane slot := foldJoin (zeroW input pos o.2.2.2) lane slot
    (zeroAt (laneKey pads (labelKey o.2.1 o.2.2.1) lane) slot)
  gadgetVisible _ d := match digitEndomorphismBase (keys.get d).digit with
    | none => 0
    | some phi => digest (zeroW input pos o.2.2.2) d
        ((Programs.transformKeyOf pads (labelKey o.2.1 o.2.2.1)).encodeAffine
          (Exception.exceptionalInput phi (keys.get d).offset.coordinates))
  gadgetSlot d := (digitEndomorphismBase (keys.get d).digit).map fun phi =>
    Exception.exceptionIndex (Exception.exceptionalInput phi (keys.get d).offset.coordinates)
  gadgetCode d := Exception.digitCode (keys.get d).digit

omit pads in
theorem entryOf_gadgetEntryW (v : FixedIndex → Block) (d : Fin digitCount) (key : OutputKey)
    (inputKey : InputMacKey) (pad : Exception.Entry) :
    entryOf v d key inputKey pad = gadgetEntry
      ((digitEndomorphismBase key.digit).map fun phi =>
        Exception.exceptionIndex (Exception.exceptionalInput phi key.offset.coordinates))
      (Exception.digitCode key.digit)
      (match digitEndomorphismBase key.digit with
        | none => 0
        | some phi => digest (zeroW input pos (splitAlong (hidW input pos)
            (hidW_injective input pos) v).2) d
              (inputKey.encodeAffine (Exception.exceptionalInput phi key.offset.coordinates)))
      pad (v (hidW input pos (.inr d))) := by
  unfold entryOf
  cases digitEndomorphismBase key.digit with
  | none => rfl
  | some phi =>
      show Exception.writeEntry pad _ (Exception.lowByte (digest v d _) ^^^ _) =
        Exception.writeEntry pad _ (Exception.lowByte (_ ^^^ _) ^^^ _)
      rw [digest_splitW input pos v d]

variable (scalar : NonZeroScalar)

/-- **The garbler's published value on a table is the source of F4's published cells**, with the
hidden gadget answers at `pos`. -/
theorem tablePub_cellsW (coins : Coins) (v : FixedIndex → Block) (T : Tape) (key : InputMacKey)
    (keys : OutputKeys) (keysEq : FieldMacToECMac.outputKeys construction scalar.value coins.offsets = keys) :
    tablePub scalar coins pads v T =
      (cellsSource (publicOf (ctxW input pos pads keys (regroupW input pos (coinsRest coins, v, maskCoordEquiv (masksOf VectorSite.lane T))).1)
        (regroupW input pos (coinsRest coins, v, maskCoordEquiv (masksOf VectorSite.lane T))).2) key).publicValue := by
  unfold tablePub
  rw [keysEq]
  have outerEq : (regroupW input pos (coinsRest coins, v, maskCoordEquiv (masksOf VectorSite.lane T))).1 =
      (fun d => (coins.pointRandomness.get d).rho, coins.inputZero, coins.inputDelta,
        (splitAlong (hidW input pos) (hidW_injective input pos) v).2) := rfl
  have coinsEq : (regroupW input pos (coinsRest coins, v, maskCoordEquiv (masksOf VectorSite.lane T))).2 =
      (fun d => ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d, ((coins.pointRandomness.get d).x,
          (coins.pointRandomness.get d).y, (coins.pointRandomness.get d).z)),
        ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).2, coins.bridgeKey,
          ⟨coins.curveMask.value, coins.curveMask.nonzero⟩, coins.curveR1, coins.curveR2),
        (fun ℓ c => v (hidW input pos (.inl (ℓ, c))),
          fun d => (coins.exceptionPad.get d, v (hidW input pos (.inr d))))) := rfl
  rw [outerEq, coinsEq]
  set O := tableOracle (fixedTable v T)
  set H := tableHash (fixedTable v T)
  set m := maskCoordEquiv (masksOf VectorSite.lane T)
  set PX := Programs.laneTables O H .pointX (coins.inputDelta .x)
    (Pipeline.bitKeyOf (Programs.whitenKeyOf pads coins.inputMacKey) .x)
  set PY := Programs.laneTables O H .pointY (coins.inputDelta .y)
    (Pipeline.bitKeyOf (Programs.whitenKeyOf pads coins.inputMacKey) .y)
  have digitK : ∀ d, Pipeline.digitValues PX.offsets PY.offsets d =
      digitOffsets ((maskSiteEquiv m).1 d) := fun d => digitValues_fixed v T _ _ _ _ d
  have curveK := curveValues_fixed v T (coins.inputDelta .x) (coins.inputDelta .y)
    (Pipeline.bitKeyOf coins.inputMacKey .x) (Pipeline.bitKeyOf coins.inputMacKey .y)
  apply public_ext
  · change CurveMembership.garble _ _ _ _ _ = CurveMembership.garble _ _ _ _ _
    rw [curveK]
  · change Vector.ofFn _ = Vector.ofFn _
    refine congrArg Vector.ofFn (funext fun d => ?_)
    change garbleRow _ _ _ = garbleRow _ _ _
    beta_reduce
    rw [digitK]
    have rowsGet : ∀ i : Fin outputMacCount,
        (FieldMacToECMac.rowsForOutputKeys keys coins.pointRandomness).get i =
          Coordinates.rows (keys.get i).offset.coordinates (digitEndomorphismBase (keys.get i).digit)
            (coins.pointRandomness.get i).rho.value := by
      intro i
      unfold FieldMacToECMac.rowsForOutputKeys
      exact Vector.get_ofFn _ i
    rw [rowsGet d]
    rfl
  · rw [assemble_exception, cellsSource_exception]
    unfold Programs.gadgetM
    rw [FreeQuery.eval_vector]
    refine ofFn_congr_digit _ _ fun d => ?_
    rw [garbleEntryM_table, entryOf_gadgetEntryW input pos v d]
    rfl
  · rw [(assemble_hot _ _ _ _ _ _ _ _ _ _ _).1, (cellsSource_hot _ _).1, laneHotJoins_fixed]
    exact congrArg Vector.ofFn (funext fun slot => foldJoin_splitW input pos v .curveX slot _)
  · rw [(assemble_hot _ _ _ _ _ _ _ _ _ _ _).2.1, (cellsSource_hot _ _).2.1, laneHotJoins_fixed]
    exact congrArg Vector.ofFn (funext fun slot => foldJoin_splitW input pos v .curveY slot _)
  · rw [(assemble_hot _ _ _ _ _ _ _ _ _ _ _).2.2.1, (cellsSource_hot _ _).2.2.1, laneHotJoins_fixed]
    exact congrArg Vector.ofFn (funext fun slot => foldJoin_splitW input pos v .pointX slot _)
  · rw [(assemble_hot _ _ _ _ _ _ _ _ _ _ _).2.2.2, (cellsSource_hot _ _).2.2.2, laneHotJoins_fixed]
    exact congrArg Vector.ofFn (funext fun slot => foldJoin_splitW input pos v .pointY slot _)
  · have pointSlopes : ∀ d : Fin digitCount, Biquadratic.slopes (coins.pointRandomness.get d).x
        (coins.pointRandomness.get d).y (coins.pointRandomness.get d).z
          (Pipeline.digitValues PX.offsets PY.offsets d) =
        digitSlopes ((maskSiteEquiv m).1 d) ((coins.pointRandomness.get d).x,
          (coins.pointRandomness.get d).y, (coins.pointRandomness.get d).z) := by
      intro d
      rw [digitK]
      rfl
    have curveSlopesEq : CurveMembership.slopes coins.curveR1 coins.curveR2
        (Pipeline.curveValues
          (Programs.laneTables O H .curveX (coins.inputDelta .x)
            (Pipeline.bitKeyOf coins.inputMacKey .x)).offsets
          (Programs.laneTables O H .curveY (coins.inputDelta .y)
            (Pipeline.bitKeyOf coins.inputMacKey .y)).offsets) =
        curveSlopes (maskSiteEquiv m).2 coins.curveR1 coins.curveR2 := by
      rw [curveK]
      rfl
    change Vector.ofFn _ = Vector.ofFn _
    refine congrArg Vector.ofFn (funext fun chunk => congrArg pack ?_)
    show Pipeline.assembleWord _ _ _ _ = Pipeline.assembleWord _ _ _ _
    exact congr (congr (congr (congrArg Pipeline.assembleWord
      (funext fun slot => pointXJoins_fixed v T _ _ _ _ pointSlopes chunk slot))
      (funext fun slot => curveXJoins_fixed v T _ _ _ _ _ curveSlopesEq chunk slot))
      (funext fun slot => pointYJoins_fixed v T _ _ _ _ pointSlopes chunk slot))
      (funext fun slot => curveYJoins_fixed v T _ _ _ _ _ curveSlopesEq chunk slot)

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
