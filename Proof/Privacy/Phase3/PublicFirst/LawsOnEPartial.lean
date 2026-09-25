/-
**Phase 3, P1r — `LawOn`, step (E), part 4: the private side's collector targets are F4's
designated solve.**

On the private side the designated vector's collectors are drawn at the collector targets
`κ · (W − R)`, `W` the true rows at `u`, `R` the evaluator's rows at the values its opening delivers
with the designated vector zeroed and its free coordinates filled back in (`Glue.freeFill`,
`targetsOf`). Here:

* `laneValue_eq`/`deliveredOf_eq`: a lane's delivered value is F4's `deliveredOf` (`ι(α)·J` plus
  the free fold of the inactive masks);
* `digitValues_freeFill`: on the source of F4's cells, with the designated vector zeroed and the
  tape's own free coordinates filled back in (`freeOf`), the opening's digit values are
  **`digitPartial`** of the cells' joins and the tape's visible masks (the designated collectors read
  `0`, F4 leaves them out);
* `targets_eq`: the collector target of `(d, c)` is `JointExactness.simDesignated` at the true rows
  (`κ = κ⁻¹`; the collector appears in its own row only, with coefficient one for `X` and `Z` and
  `x²` for `Y`, which `Glue.collectorScale` inverts at `x ≠ 0`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEPoints
import Proof.Privacy.Phase3.PublicFirst.LawsOff

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (openingQueriesM collectorTargets freeFill freeRows designatedVector
  designatedSwitch chunkZero collectorElement freeElement FreeSite)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState)
open scoped ENNReal

noncomputable section

/-! ### 1. A lane's value is F4's `deliveredOf` -/

theorem evalScaleOf_eq {count width : Nat} (masks : Fin (2 ^ width) → Vector BaseField count)
    (alpha : Fin (2 ^ width)) (join : Fin count → BaseField) (e : Fin count)
    (zero : (masks alpha).get e = 0) :
    Programs.evalScaleOf width masks alpha join e =
      iota _ alpha * join e + ∑ j, (iota _ j - iota _ alpha) * (masks j).get e := by
  unfold Programs.evalScaleOf
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ alpha),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ alpha), if_pos rfl, zero, mul_zero, zero_add]
  have rest : ∀ j ∈ Finset.univ.erase alpha, iota _ j * (if j = alpha then join e -
      ∑ other ∈ Finset.univ.erase alpha, (masks other).get e else (masks j).get e) =
        iota _ j * (masks j).get e :=
    fun j member => by rw [if_neg (Finset.ne_of_mem_erase member)]
  rw [Finset.sum_congr rfl rest, mul_sub, Finset.mul_sum]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

theorem laneValue_eq (lane : Lane) (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (bits : BitVec coordinateBitCount) (T : Tape) (e : Fin (laneCount lane)) :
    laneValue lane scale bits T e = ∑ c, iota _ (chunkOf bits c) * scale c e +
      ∑ c, ∑ j, (iota _ j - iota _ (chunkOf bits c)) *
        (chunkMasks lane c (chunkOf bits c) T j).get e := by
  unfold laneValue
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => evalScaleOf_eq _ _ _ e ?_
  unfold chunkMasks
  rw [if_pos rfl, Vector.get_ofFn]

theorem deliveredOf_eq (α : Alpha) (J : Fin chunkCount → BaseField)
    (Y : ChunkSwitch → BaseField) :
    deliveredOf α J Y = ∑ c, iota _ (α c) * J c +
      ∑ c, ∑ j, (iota _ j - iota _ (α c)) * (if j = α c then 0 else Y ⟨c, j⟩) := by
  unfold deliveredOf
  refine congrArg (_ + ·) ?_
  have split := sum_split_active α (fun cs =>
    (switchIota cs - iota _ (α cs.1)) * (if cs.2 = α cs.1 then 0 else Y cs))
  have active : ∑ c : Fin chunkCount, (switchIota (⟨c, α c⟩ : ChunkSwitch) - iota _ (α c)) *
      (if α c = α c then 0 else Y ⟨c, α c⟩) = 0 :=
    Finset.sum_eq_zero fun c _ => by rw [if_pos rfl, mul_zero]
  have inactive : ∀ cs : {cs : ChunkSwitch // ¬ Active α cs},
      (switchIota cs.1 - iota _ (α cs.1.1)) * (if cs.1.2 = α cs.1.1 then 0 else Y cs.1) =
        (switchIota cs.1 - iota _ (α cs.1.1)) * Y cs.1 := fun cs => by
    rw [if_neg (show ¬ (cs.1.2 = α cs.1.1) from cs.2)]
  dsimp only at split
  rw [active, zero_add] at split
  rw [← Fintype.sum_congr _ _ inactive, ← split, Fintype.sum_sigma]
  rfl

/-! ### 2. The designated vector site -/

theorem sampleLane_zeros (n k : Nat) :
    sampleLane n k (fun _ => ((0 : Block), (0 : Block))) = fun _ => 0 := by
  funext e
  simp [sampleLane, limbsToNat, limbValue]

variable [FieldCertificate] [GroupCertificate] (input : AffineInput)

theorem masksOf_zeroDesig (T : Tape) (v : VectorSite) :
    masksOf VectorSite.lane (OnLaw.zeroDesig (BitInput.ofAffine input) T) v =
      if v = OnLaw.designatedSite (BitInput.ofAffine input) then fun _ => 0
      else masksOf VectorSite.lane T v := by
  unfold masksOf
  split_ifs with here
  · rw [← sampleLane_zeros (laneCount v.lane) (limbCount v.lane)]
    congr 1
    funext limb
    unfold OnLaw.zeroDesig
    rw [if_pos here]
  · congr 1
    funext limb
    unfold OnLaw.zeroDesig
    rw [if_neg here]

/-- The designated (chunk, switch) is F4's. -/
theorem designated_eq :
    (offShape input).designated = ⟨chunkZero, designatedSwitch (BitInput.ofAffine input)⟩ := rfl

theorem isCollector_inl (xe : XElement) :
    IsCollector (.inl xe) ↔ ∃ c : Fin 3, collectorElement c = xe := by
  constructor
  · rintro (h | h | h) <;> simp only [Sum.inl.injEq] at h <;> subst h
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨c, rfl⟩
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- A `pointX` vector site is the designated one exactly at F4's designated (chunk, switch). -/
theorem pointX_designatedSite (cs : ChunkSwitch) :
    (⟨.pointX, cs.1, cs.2⟩ : VectorSite) = OnLaw.designatedSite (BitInput.ofAffine input) ↔
      cs = (offShape input).designated := by
  rw [designated_eq]
  obtain ⟨c, j⟩ := cs
  constructor
  · intro same
    unfold OnLaw.designatedSite at same
    simp only [VectorSite.mk.injEq, true_and] at same
    obtain ⟨rfl, same⟩ := same
    rw [eq_of_heq same]
  · intro same
    simp only [Sigma.mk.inj_iff] at same
    obtain ⟨rfl, same⟩ := same
    rw [eq_of_heq same]
    rfl

/-- **The designated site's free coordinates, read off a tape.** -/
def freeOf (T : Tape) : FreeSite → BaseField := fun p =>
  masksOf VectorSite.lane T (OnLaw.designatedSite (BitInput.ofAffine input)) (xElementIndex p.1 (freeElement p.2))

/-- The designated vector of a tape's free coordinates and zero collectors. -/
theorem designatedVector_freeOf (T : Tape) (d : Fin digitCount) (xe : XElement) :
    designatedVector (freeOf input T) 0 (xElementIndex d xe) =
      if IsCollector (.inl xe) then 0
      else masksOf VectorSite.lane T (OnLaw.designatedSite (BitInput.ofAffine input)) (xElementIndex d xe) := by
  cases xe with
  | rowX_x7 =>
      rw [if_neg (by simp [IsCollector, collectorX, collectorY, collectorZ])]
      exact Kriterion.ArgoMAC.Phase3.Glue.designatedVector_free _ _ d 0
  | rowX_x9 =>
      have collector : IsCollector (.inl XElement.rowX_x9) := Or.inl rfl
      rw [if_pos collector]
      exact Kriterion.ArgoMAC.Phase3.Glue.designatedVector_collector _ _ d 0
  | rowY_cubic =>
      have collector : IsCollector (.inl XElement.rowY_cubic) := Or.inr (Or.inl rfl)
      rw [if_pos collector]
      exact Kriterion.ArgoMAC.Phase3.Glue.designatedVector_collector _ _ d 1
  | rowZ_x9 =>
      have collector : IsCollector (.inl XElement.rowZ_x9) := Or.inr (Or.inr rfl)
      rw [if_pos collector]
      exact Kriterion.ArgoMAC.Phase3.Glue.designatedVector_collector _ _ d 2

/-! ### 3. The opening's digit values are F4's `digitPartial` -/

theorem readPointX_cells (cells : PublicCells) (key : InputMacKey) (c : Fin chunkCount)
    (d : Fin digitCount) (xe : XElement) :
    Pipeline.readPointX (unpack ((cellsSource cells key).publicValue.scale.get c)) (xElementIndex d xe) =
      (cells.1 d).1 (.inl xe) c := by
  rw [cellsSource_scale, Vector.get_ofFn, unpack_pack_eq]
  show Pipeline.readPointX (Pipeline.assembleWord _ _ _ _) _ = _
  rw [Pipeline.readPointX_assembleWord]
  show (cells.1 (pointXSlots.symm (pointXSlots (d, xe))).1).1
    (.inl (pointXSlots.symm (pointXSlots (d, xe))).2) c = _
  rw [Equiv.symm_apply_apply]

theorem readPointY_cells (cells : PublicCells) (key : InputMacKey) (c : Fin chunkCount)
    (d : Fin digitCount) (ye : YElement) :
    Pipeline.readPointY (unpack ((cellsSource cells key).publicValue.scale.get c)) (yElementIndex d ye) =
      (cells.1 d).1 (.inr ye) c := by
  rw [cellsSource_scale, Vector.get_ofFn, unpack_pack_eq]
  show Pipeline.readPointY (Pipeline.assembleWord _ _ _ _) _ = _
  rw [Pipeline.readPointY_assembleWord]
  show (cells.1 (pointYSlots.symm (pointYSlots (d, ye))).1).1
    (.inr (pointYSlots.symm (pointYSlots (d, ye))).2) c = _
  rw [Equiv.symm_apply_apply]

theorem digitValues_inl (xs : Fin pointElementCountX → BaseField) (ys : Fin pointElementCountY → BaseField)
    (d : Fin digitCount) (xe : XElement) : Pipeline.digitValues xs ys d (.inl xe) = xs (xElementIndex d xe) :=
  rfl

theorem digitValues_inr (xs : Fin pointElementCountX → BaseField) (ys : Fin pointElementCountY → BaseField)
    (d : Fin digitCount) (ye : YElement) : Pipeline.digitValues xs ys d (.inr ye) = ys (yElementIndex d ye) :=
  rfl

theorem alphaX_eq (c : Fin chunkCount) :
    chunkOf (Pipeline.coordBits (BitInput.ofAffine input) .x) c = (offShape input).alphaX c := rfl

theorem alphaY_eq (c : Fin chunkCount) :
    chunkOf (Pipeline.coordBits (BitInput.ofAffine input) .y) c = (offShape input).alphaY c := rfl

theorem maskCoordEquiv_apply (M : MaskVectors) (c : MaskCoord) : maskCoordEquiv M c = M c.1 c.2 := rfl

theorem pointValues_fst (P : Public) (bits : BitInput) (T : Tape) :
    (pointValues P bits T).1 = laneValue .pointX (fun chunk => Pipeline.readPointX (unpack (P.scale.get chunk)))
      (Pipeline.coordBits bits .x) T := rfl

theorem pointValues_snd (P : Public) (bits : BitInput) (T : Tape) :
    (pointValues P bits T).2 = laneValue .pointY (fun chunk => Pipeline.readPointY (unpack (P.scale.get chunk)))
      (Pipeline.coordBits bits .y) T := rfl

omit [GroupCertificate] in
theorem freeFill_apply (bits : BitInput) (xs : Fin pointElementCountX → BaseField)
    (free : FreeSite → BaseField) (e : Fin pointElementCountX) :
    freeFill bits xs free e = xs e + Kriterion.ArgoMAC.Phase3.Glue.kappa bits * designatedVector free 0 e :=
  rfl

/-- **The opening's digit values, the designated vector zeroed and the tape's free coordinates
filled back in, are F4's `digitPartial`** of the cells' joins and the tape's visible masks. -/
theorem digitValues_freeFill (cells : PublicCells) (key : InputMacKey) (T : Tape) (d : Fin digitCount) :
    Pipeline.digitValues
        (freeFill (BitInput.ofAffine input)
          (pointValues (cellsSource cells key).publicValue (BitInput.ofAffine input)
            (OnLaw.zeroDesig (BitInput.ofAffine input) T)).1 (freeOf input T))
        (pointValues (cellsSource cells key).publicValue (BitInput.ofAffine input)
          (OnLaw.zeroDesig (BitInput.ofAffine input) T)).2 d =
      digitPartial (offShape input) (cells.1 d).1
        (digitVisible (offShape input)
          ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d)) := by
  funext e
  unfold digitPartial
  rw [deliveredOf_eq]
  rcases e with xe | ye
  · rw [digitValues_inl, freeFill_apply, pointValues_fst, laneValue_eq, add_assoc]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun c _ => ?_) ?_
    · rw [readPointX_cells, alphaX_eq]
      rfl
    · have termwise : ∀ cs : ChunkSwitch,
          (switchIota cs - iota _ ((offShape input).alphaX cs.1)) *
            (if cs.2 = (offShape input).alphaX cs.1 then 0 else
              extendVisible (offShape input) (digitVisible (offShape input)
                ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d)) (.inl xe) cs) =
          (switchIota cs - iota _ ((offShape input).alphaX cs.1)) *
            (chunkMasks .pointX cs.1 ((offShape input).alphaX cs.1)
              (OnLaw.zeroDesig (BitInput.ofAffine input) T) cs.2).get (xElementIndex d xe) +
          (if cs = (offShape input).designated then
            Kriterion.ArgoMAC.Phase3.Glue.kappa (BitInput.ofAffine input) *
              designatedVector (freeOf input T) 0 (xElementIndex d xe) else 0) := by
        intro cs
        by_cases here : cs = (offShape input).designated
        · subst here
          have inactive : ¬ ((offShape input).designated.2 =
              (offShape input).alphaX (offShape input).designated.1) :=
            (offShape input).designated_inactive'
          rw [if_pos rfl, if_neg inactive]
          have zero : (chunkMasks .pointX (offShape input).designated.1
              ((offShape input).alphaX (offShape input).designated.1)
              (OnLaw.zeroDesig (BitInput.ofAffine input) T) (offShape input).designated.2).get
                (xElementIndex d xe) = 0 := by
            unfold chunkMasks
            rw [if_neg inactive, Vector.get_ofFn,
              masksOf_zeroDesig, if_pos ((pointX_designatedSite input _).mpr rfl)]
          rw [zero, mul_zero, zero_add, designatedVector_freeOf]
          show (switchIota (offShape input).designated - iota _ ((offShape input).alphaX
            (offShape input).designated.1)) * _ = Kriterion.ArgoMAC.Phase3.Glue.kappa
              (BitInput.ofAffine input) * _
          congr 1
          unfold extendVisible
          by_cases collector : IsCollector (.inl xe)
          · rw [if_pos collector, dif_neg fun visible => visible.2 ⟨collector, rfl⟩]
          · rw [if_neg collector, dif_pos ⟨(offShape input).designated_inactive',
              fun both => collector both.1⟩]
            show (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d (.inl xe)
              (offShape input).designated = _
            rw [maskSiteEquiv_pointX, maskCoordEquiv_apply]
            rfl
        · rw [if_neg here, add_zero]
          congr 1
          unfold chunkMasks
          by_cases active : cs.2 = (offShape input).alphaX cs.1
          · rw [if_pos active, if_pos active, Vector.get_ofFn]
          · rw [if_neg active, if_neg active, Vector.get_ofFn, masksOf_zeroDesig,
              if_neg (fun same => here ((pointX_designatedSite input cs).mp same))]
            unfold extendVisible
            rw [dif_pos ⟨active, fun both => here both.2⟩]
            show (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d (.inl xe) cs = _
            rw [maskSiteEquiv_pointX, maskCoordEquiv_apply]
      have lhs : ∑ c, ∑ j, (iota _ j - iota _ (chunkOf (Pipeline.coordBits (BitInput.ofAffine input) .x) c)) *
            (chunkMasks .pointX c (chunkOf (Pipeline.coordBits (BitInput.ofAffine input) .x) c)
              (OnLaw.zeroDesig (BitInput.ofAffine input) T) j).get (xElementIndex d xe) =
          ∑ cs : ChunkSwitch, (switchIota cs - iota _ ((offShape input).alphaX cs.1)) *
            (chunkMasks .pointX cs.1 ((offShape input).alphaX cs.1)
              (OnLaw.zeroDesig (BitInput.ofAffine input) T) cs.2).get (xElementIndex d xe) :=
        (Fintype.sum_sigma (fun cs : ChunkSwitch => (switchIota cs - iota _ ((offShape input).alphaX cs.1)) *
          (chunkMasks .pointX cs.1 ((offShape input).alphaX cs.1)
            (OnLaw.zeroDesig (BitInput.ofAffine input) T) cs.2).get (xElementIndex d xe))).symm
      have rhs : ∑ c, ∑ j, (iota _ j - iota _ ((offShape input).digitAlpha (.inl xe) c)) *
            (if j = (offShape input).digitAlpha (.inl xe) c then 0 else
              extendVisible (offShape input) (digitVisible (offShape input)
                ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d)) (.inl xe) ⟨c, j⟩) =
          ∑ cs : ChunkSwitch, (switchIota cs - iota _ ((offShape input).alphaX cs.1)) *
            (if cs.2 = (offShape input).alphaX cs.1 then 0 else
              extendVisible (offShape input) (digitVisible (offShape input)
                ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d)) (.inl xe) cs) :=
        (Fintype.sum_sigma (fun cs : ChunkSwitch => (switchIota cs - iota _ ((offShape input).alphaX cs.1)) *
          (if cs.2 = (offShape input).alphaX cs.1 then 0 else
            extendVisible (offShape input) (digitVisible (offShape input)
              ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d)) (.inl xe) cs))).symm
      have indicator : ∑ cs : ChunkSwitch, (if cs = (offShape input).designated then
          Kriterion.ArgoMAC.Phase3.Glue.kappa (BitInput.ofAffine input) *
            designatedVector (freeOf input T) 0 (xElementIndex d xe) else 0) =
          Kriterion.ArgoMAC.Phase3.Glue.kappa (BitInput.ofAffine input) *
            designatedVector (freeOf input T) 0 (xElementIndex d xe) := by
        rw [Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)]
      rw [lhs, rhs, ← indicator, ← Finset.sum_add_distrib]
      exact Fintype.sum_congr _ _ fun cs => (termwise cs).symm
  · rw [digitValues_inr, pointValues_snd, laneValue_eq]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun c _ => ?_)
      (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_)
    · rw [readPointY_cells, alphaY_eq]
      rfl
    · rw [alphaY_eq]
      unfold chunkMasks
      show _ * (_ : Vector BaseField _).get _ = _ * (if j = (offShape input).alphaY c then 0 else _)
      by_cases active : j = (offShape input).alphaY c
      · rw [if_pos active, if_pos active, Vector.get_ofFn, mul_zero, mul_zero]
      · have notDesignated : (⟨.pointY, c, j⟩ : VectorSite) ≠ OnLaw.designatedSite (BitInput.ofAffine input) :=
          fun same => by cases same
        rw [if_neg active, if_neg active, Vector.get_ofFn, masksOf_zeroDesig, if_neg notDesignated]
        congr 1
        unfold extendVisible
        have visible : (offShape input).DigitVisibleAt (.inr ye) ⟨c, j⟩ :=
          ⟨active, fun collector => by rcases collector.1 with h | h | h <;> cases h⟩
        rw [dif_pos visible]
        show _ = (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d (.inr ye) ⟨c, j⟩
        rw [maskSiteEquiv_pointY, maskCoordEquiv_apply]

/-! ### 4. The collector targets are F4's designated solve -/

/-- **The row gap of a collector, scaled by the inverse of its coefficient, is its solve gap**: the
collector appears in no other row, with coefficient one in the `X` and `Z` rows and `x²` in the `Y`
row, which `collectorScale` inverts (`x ≠ 0`). -/
theorem collector_gap (gamma : RowGamma) (u : AffineInput) (values : Biquadratic.Values)
    (target : HomogeneousValue) (c : Fin 3) (xNe : u.x ≠ 0) :
    (Kriterion.ArgoMAC.Phase3.Glue.collectorComponent c target -
        Kriterion.ArgoMAC.Phase3.Glue.collectorComponent c (evaluateGamma gamma u values)) *
        Kriterion.ArgoMAC.Phase3.Glue.collectorScale (BitInput.ofAffine u) c =
      collectorComponent (.inl (collectorElement c)) (collectorSolve gamma u values target) -
        values (.inl (collectorElement c)) := by
  rw [evaluateGamma_eq_affine]
  have toAffine : (BitInput.ofAffine u).toAffine = u := BitInput.toAffineOfAffine u
  have unit : u.x * u.x * (u.x * u.x)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero xNe xNe)
  fin_cases c
  · simp only [Kriterion.ArgoMAC.Phase3.Glue.collectorComponent, collectorComponent,
      collectorElement, collectorSolve, rowConstant, rowLinear,
      Kriterion.ArgoMAC.Phase3.Glue.collectorScale, toAffine]
    simp
    ring
  · simp only [Kriterion.ArgoMAC.Phase3.Glue.collectorComponent, collectorComponent,
      collectorElement, collectorSolve, rowConstant, rowLinear,
      Kriterion.ArgoMAC.Phase3.Glue.collectorScale, toAffine]
    simp
    linear_combination (-(values (.inl .rowY_cubic))) * unit
  · simp only [Kriterion.ArgoMAC.Phase3.Glue.collectorComponent, collectorComponent,
      collectorElement, collectorSolve, rowConstant, rowLinear,
      Kriterion.ArgoMAC.Phase3.Glue.collectorScale, toAffine]
    simp
    ring

theorem evaluateHomogeneous_get (table : FieldMacToECMac.Table) (values : FieldMacToECMac.DigitValues)
    (u : AffineInput) (d : Fin digitCount) :
    (FieldMacToECMac.evaluateHomogeneous table values u).get d = evaluateGamma (table.1.get d) u (values d) :=
  Vector.get_ofFn _ d

theorem rows_cellsSource (cells : PublicCells) (key : InputMacKey) (d : Fin digitCount) :
    (Pipeline.pointTable (cellsSource cells key).publicValue).1.get d = (cells.1 d).2 :=
  get_ofFn_digit (fun d => (cells.1 d).2) d

/-- The true rows of a coin at a digit. -/
def rowsAt (scalar : NonZeroScalar) (coins : Coins) (d : Fin digitCount) : Coordinates.Rows :=
  (FieldMacToECMac.rowsForOutputKeys (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
    coins.pointRandomness).get d

theorem trueRows_eq (scalar : NonZeroScalar) (coins : Coins) (d : Fin digitCount) :
    trueRows scalar coins input d = rowTarget (rowsAt scalar coins d) input :=
  (rowTarget_eq_evaluateRow _ _ (rowsForOutputKeysSparse _ _ d)).symm

/-- **The private side's collector targets**: `κ · (W − R)`, `R` the evaluator's rows at its
opening's values on the overlaid oracle with the designated vector zeroed, its free coordinates
filled in. -/
def targetsOf (scalar : NonZeroScalar) (P : Public) (mac : InputMac) (T : Tape) (O : Oracle)
    (coins : Coins) (free : FreeSite → BaseField) : Fin digitCount × Fin 3 → BaseField :=
  collectorTargets (BitInput.ofAffine input)
    (freeRows P (BitInput.ofAffine input)
      ((openingQueriesM P (BitInput.ofAffine input) mac).eval
        (publicAnswer (OnLaw.overlay (OnLaw.zeroDesig (BitInput.ofAffine input) T) O))).1
      ((openingQueriesM P (BitInput.ofAffine input) mac).eval
        (publicAnswer (OnLaw.overlay (OnLaw.zeroDesig (BitInput.ofAffine input) T) O))).2 free)
    (fun digit => trueRows scalar coins input digit)

/-- **The collector target of `(d, c)` is F4's designated solve** at the true rows, from the cells
and the tape's visible masks, when the free coordinates are the tape's own. -/
theorem targets_eq (scalar : NonZeroScalar) (cells : PublicCells) (key : InputMacKey) (mac : InputMac)
    (T : Tape) (O : Oracle) (coins : Coins) (d : Fin digitCount) (c : Fin 3) (xNe : input.x ≠ 0) :
    targetsOf input scalar (cellsSource cells key).publicValue mac T O coins (freeOf input T) (d, c) =
      simDesignated (offShape input) (rowTarget (rowsAt scalar coins d) input) (cells.1 d).1 (cells.1 d).2
        (digitVisible (offShape input) ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d))
        (.inl (collectorElement c)) := by
  unfold targetsOf
  rw [openingQueriesM_tape (tapeOn_overlay _ O)]
  unfold collectorTargets simDesignated
  rw [kappa_inv_ofInput, mul_assoc]
  congr 1
  have evalRow : (freeRows (cellsSource cells key).publicValue (BitInput.ofAffine input)
      (pointValues (cellsSource cells key).publicValue (BitInput.ofAffine input)
        (OnLaw.zeroDesig (BitInput.ofAffine input) T)).1
      (pointValues (cellsSource cells key).publicValue (BitInput.ofAffine input)
        (OnLaw.zeroDesig (BitInput.ofAffine input) T)).2 (freeOf input T)).get d =
      evaluateGamma (cells.1 d).2 input
        (digitPartial (offShape input) (cells.1 d).1
          (digitVisible (offShape input)
            ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d))) := by
    refine (evaluateHomogeneous_get _ _ _ d).trans ?_
    rw [rows_cellsSource cells key d, BitInput.toAffineOfAffine, digitValues_freeFill input cells key T d]
  show (Kriterion.ArgoMAC.Phase3.Glue.collectorComponent c (trueRows scalar coins input d) - _) * _ = _
  rw [evalRow, trueRows_eq, collector_gap _ _ _ _ _ xNe]
  rfl

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
