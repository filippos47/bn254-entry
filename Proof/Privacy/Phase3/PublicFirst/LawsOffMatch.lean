/-
**Phase 3, P1n — the off-curve law, step (ii), part 2: the garbler's published value is F4's
published cells.**

On a table the garbler's published value is `tablePub` of its coins, its pads, its fixed-key
answers and its limbs (`garbleM_tablePub`): a lane on a table reads its gates' answers and its
limbs only (`laneTables_table`), the gadget its gadget answers only (`gadgetM_table`). Read
through `LawsOffCells.omegaEquiv` (the coins, the fixed-key answers and the masks as the rest and
F4's coins), it is the source of F4's published cells `publicOf (offContext …) jc`
(`tablePub_cells`): the lanes' masks are the masks of the limbs (`laneMasks_fixed`), the lanes'
offsets and joins are F4's per-element offsets and joins, the fold join of a (lane, paid step) is
its hidden gate half XOR the rest (`foldJoin_split`: the step's `2 · 2^n` gate halves, one of them —
the active parent's first — hidden), and a digit's gadget entry is F4's `gadgetEntry` of its pad
and one hidden gadget answer (`digest_split`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOffCells

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape)
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source)
open scoped ENNReal

noncomputable section

/-! ### 1. The published value on a table -/

theorem get_ofFn_digit {α : Type} (f : Fin digitCount → α) (d : Fin digitCount) :
    (Vector.ofFn (n := outputMacCount) f).get d = f d :=
  Vector.get_ofFn f d

theorem ofFn_congr_digit {α : Type} (f : Fin outputMacCount → α) (g : Fin digitCount → α)
    (same : ∀ d : Fin digitCount, f d = g d) :
    Vector.ofFn (n := outputMacCount) f = Vector.ofFn (n := digitCount) g :=
  congrArg Vector.ofFn (funext same)

/-- The table with only fixed-key answers and limbs. -/
def fixedTable (v : FixedIndex → Block) (T : Tape) : Table :=
  (⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0), v, T)

/-- **A digit's gadget digest** at some labels, from the fixed-key answers. -/
def digest (v : FixedIndex → Block) (output : Fin digitCount) (mac : InputMac) : Block :=
  xorFold (fun index : Fin coordinateBitCount => v (.gadget output .x index) ^^^ mac.x.get index)
    ^^^
    xorFold (fun index : Fin coordinateBitCount => v (.gadget output .y index) ^^^ mac.y.get index)

/-- A digit's gadget entry from the fixed-key answers. -/
def entryOf (v : FixedIndex → Block) (output : Fin digitCount) (key : OutputKey)
    (inputKey : InputMacKey) (pad : Exception.Entry) : Exception.Entry :=
  match digitEndomorphismBase key.digit with
  | none => pad
  | some phi => Exception.writeEntry pad
      (Exception.exceptionIndex (Exception.exceptionalInput phi key.offset.coordinates))
      (Exception.lowByte (digest v output
        (inputKey.encodeAffine (Exception.exceptionalInput phi key.offset.coordinates))) ^^^
        Exception.digitCode key.digit)

theorem gadgetDigestM_table (A : Table) (output : Fin outputMacCount)
    (coordinate : EncPRF.Coordinate) (mac : CoordinateMac) :
    (Programs.gadgetDigestM output coordinate mac).eval (tableAnswer A) =
      xorFold (fun index : Fin coordinateBitCount =>
        A.2.2.1 (.gadget output (Pipeline.gadgetCoord coordinate) index) ^^^ mac.get index) := by
  simp only [Programs.gadgetDigestM, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_vector, Vector.get_ofFn]
  rfl

/-- **A gadget entry on a table** reads the table's gadget answers only. -/
theorem garbleEntryM_eval (A : Table) (output : Fin outputMacCount) (key : OutputKey)
    (inputKey : InputMacKey) (pad : Exception.Entry) :
    (Programs.garbleEntryM output key inputKey pad).eval (tableAnswer A) =
      entryOf A.2.2.1 output key inputKey pad := by
  unfold Programs.garbleEntryM entryOf
  cases digitEndomorphismBase key.digit with
  | none => rfl
  | some phi =>
      simp only [FreeQuery.eval_bind, FreeQuery.eval_pure, Programs.gadgetMaskM,
        gadgetDigestM_table]
      rfl

theorem garbleEntryM_table (v : FixedIndex → Block) (T : Tape) (output : Fin digitCount)
    (key : OutputKey) (inputKey : InputMacKey) (pad : Exception.Entry) :
    (Programs.garbleEntryM output key inputKey pad).eval (tableAnswer (fixedTable v T)) =
      entryOf v output key inputKey pad :=
  garbleEntryM_eval (fixedTable v T) output key inputKey pad

/-- **The gadget on a table** reads the table's gadget answers only. -/
theorem gadgetM_table (A : Table) (keys : OutputKeys) (inputKey : InputMacKey)
    (pads : ExceptionPad) :
    (Programs.gadgetM keys inputKey pads).eval (tableAnswer A) =
      (Programs.gadgetM keys inputKey pads).eval (tableAnswer (fixedTable A.2.2.1 A.2.2.2)) := by
  simp only [Programs.gadgetM, FreeQuery.eval_vector]
  exact congrArg Vector.ofFn (funext fun output => (garbleEntryM_eval A output _ _ _).trans
    (garbleEntryM_eval (fixedTable A.2.2.1 A.2.2.2) output _ _ _).symm)

/-- **A lane on a table** reads the table's gates and limbs only. -/
theorem laneTables_table (A : Table) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) :
    Programs.laneTables (tableOracle A) (tableHash A) lane delta bitKey =
      Programs.laneTables (tableOracle (fixedTable A.2.2.1 A.2.2.2))
        (tableHash (fixedTable A.2.2.1 A.2.2.2)) lane delta bitKey := by
  show Programs.LaneTables.mk (fun c => garbleChunk (tableOracle A) lane delta bitKey c)
      (fun c switch => switchMask (tableHash A) lane c switch.val
        ((garbleChunk (tableOracle A) lane delta bitKey c).1 switch)) =
    Programs.LaneTables.mk (fun c => garbleChunk (tableOracle A) lane delta bitKey c)
      (fun c switch => switchMask (tableHash (fixedTable A.2.2.1 A.2.2.2)) lane c switch.val
        ((garbleChunk (tableOracle A) lane delta bitKey c).1 switch))
  refine congrArg _ (funext fun c => funext fun switch => ?_)
  exact congrArg (sampleLane _ _) (funext fun limb =>
    (tableAnswer_cell A ⟨⟨lane, c, switch⟩, limb⟩ _).trans
      (tableAnswer_cell (fixedTable A.2.2.1 A.2.2.2) ⟨⟨lane, c, switch⟩, limb⟩ _).symm)

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)

/-- **The garbler's published value on a table**, from its coins, its pads, its fixed-key
answers and its limbs. -/
def tablePub (coins : Coins) (pads : Programs.Pads) (v : FixedIndex → Block) (T : Tape) : Public :=
  Programs.assemble (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
    coins.pointRandomness coins.bridgeKey coins.curveMask coins.curveR1 coins.curveR2
    (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) .curveX
      (coins.inputDelta .x) (Pipeline.bitKeyOf coins.inputMacKey .x))
    (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) .curveY
      (coins.inputDelta .y) (Pipeline.bitKeyOf coins.inputMacKey .y))
    (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) .pointX
      (coins.inputDelta .x) (Pipeline.bitKeyOf (Programs.whitenKeyOf pads coins.inputMacKey) .x))
    (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) .pointY
      (coins.inputDelta .y) (Pipeline.bitKeyOf (Programs.whitenKeyOf pads coins.inputMacKey) .y))
    ((Programs.gadgetM (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
      (Programs.transformKeyOf pads coins.inputMacKey) coins.exceptionPad).eval
        (tableAnswer (fixedTable v T)))

/-- **The garbler on a table publishes `tablePub`.** -/
theorem garbleM_tablePub (A : Table) (coins : Coins) :
    ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 =
      tablePub scalar coins (tablePads A coins) A.2.2.1 A.2.2.2 := by
  rw [garbleM_table]
  unfold tablePub
  simp only [laneTables_table A, gadgetM_table A]

/-! ### 2. The lanes on the table's oracles -/

section Lanes

variable (v : FixedIndex → Block) (T : Tape) (lane : Lane) (delta : Block)
  (bitKey : Fin coordinateBitCount → Block × Block)

theorem laneMasks_fixed (chunk : Fin chunkCount) (switch : Fin (2 ^ chunkWidth chunk))
    (element : Fin (laneCount lane)) :
    (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) lane delta
      bitKey).masks chunk switch element =
        masksOf VectorSite.lane T ⟨lane, chunk, switch⟩ element := by
  exact congrFun (congrArg (sampleLane _ _) (funext fun limb =>
    tableAnswer_cell (fixedTable v T) ⟨⟨lane, chunk, switch⟩, limb⟩ _)) element

theorem laneOffsets_fixed (element : Fin (laneCount lane)) :
    (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) lane delta
      bitKey).offsets element = ∑ c : Fin chunkCount, ∑ switch : Fin (2 ^ chunkWidth c),
        iota _ switch * masksOf VectorSite.lane T ⟨lane, c, switch⟩ element := by
  unfold Programs.LaneTables.offsets
  simp only [laneMasks_fixed]

theorem laneScaleJoins_fixed (slopes : Fin (laneCount lane) → BaseField) (chunk : Fin chunkCount)
    (element : Fin (laneCount lane)) :
    (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) lane delta
      bitKey).scaleJoins slopes chunk element = (∑ switch : Fin (2 ^ chunkWidth chunk),
        masksOf VectorSite.lane T ⟨lane, chunk, switch⟩ element) +
          slopes element * weight chunk := by
  unfold Programs.LaneTables.scaleJoins
  simp only [laneMasks_fixed]
  rfl

/-- **The fold join of a (lane, paid fold step)** from the fixed-key answers: the `2 · 2^n` gate
halves of the slot's step `n` and the step's zero bit label. -/
def foldJoin (slot : Fin foldStepCount) (zero : Block) : Block :=
  xorFold (fun entry : Fin (2 ^ (slotOffset slot + 1)) =>
    v (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry.val false) ^^^
      v (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) entry.val true)) ^^^ zero

/-- The zero bit label of a slot's step. -/
def zeroAt (slot : Fin foldStepCount) : Block :=
  labelAt (fun position => (chunkKey bitKey (slotChunk slot) position).1) (slotOffset slot + 1)

/-- **On a table every paid step's join is the XOR of its gate halves' answers and its zero
label**, whatever the labels. -/
theorem garbleFold_join (chunk : Fin chunkCount) (zeroLabel : Nat → Block) :
    ∀ w n, 0 < n → n < w →
      (garbleFold (tableOracle (fixedTable v T)) lane chunk delta zeroLabel w).2 n =
        xorFold (fun entry : Fin (2 ^ n) =>
          v (hotIndexNat lane chunk n entry.val false) ^^^
            v (hotIndexNat lane chunk n entry.val true)) ^^^ zeroLabel n
  | 0, n, _, below => absurd below (Nat.not_lt_zero n)
  | w + 1, n, positive, below => by
      show (if n = w then stepJoin w (zeroLabel w) (garbleStep (tableOracle (fixedTable v T)) lane
          chunk w (zeroLabel w) (garbleFold (tableOracle (fixedTable v T)) lane chunk delta
            zeroLabel w).1)
        else (garbleFold (tableOracle (fixedTable v T)) lane chunk delta zeroLabel w).2 n) = _
      by_cases same : n = w
      · subst same
        rw [if_pos rfl]
        unfold stepJoin
        refine congrArg (· ^^^ zeroLabel n) (congrArg xorFold (funext fun entry => ?_))
        unfold garbleStep foldMask
        rw [if_neg (Nat.pos_iff_ne_zero.mp positive), hash_tableOracle, hash_tableOracle]
        rfl
      · rw [if_neg same]
        exact garbleFold_join chunk zeroLabel w n positive (by omega)

/-- **A lane's published fold joins** on the table's oracles: one `foldJoin` per paid step. -/
theorem laneHotJoins_fixed :
    (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) lane delta
      bitKey).hotJoins = Vector.ofFn fun slot => foldJoin v lane slot (zeroAt bitKey slot) := by
  unfold Programs.LaneTables.hotJoins flattenHot
  refine congrArg Vector.ofFn (funext fun slot => ?_)
  have inRange := slotOffset_lt slot
  dsimp only
  rw [dif_pos inRange]
  show (Vector.ofFn fun position : Fin (chunkWidth (slotChunk slot) - 1) =>
    (garbleFold (tableOracle (fixedTable v T)) lane (slotChunk slot) delta
      (labelAt fun position => (chunkKey bitKey (slotChunk slot) position).1)
      (chunkWidth (slotChunk slot))).2 (position.val + 1)).get ⟨slotOffset slot, inRange⟩ = _
  rw [Vector.get_ofFn]
  exact garbleFold_join v T lane delta (slotChunk slot) _ _ _ (Nat.succ_pos _) (by omega)

end Lanes

/-! ### 3. The hidden answers split off -/

section Hidden

variable (input : AffineInput)

/-- The fixed-key answers with the hidden ones zeroed. -/
def zeroHidden (rest : RestIdx input → Block) : FixedIndex → Block :=
  (splitAlong (hiddenIdx input) (hiddenIdx_injective input)).symm (fun _ => 0, rest)

theorem zeroHidden_of_hidden (rest : RestIdx input → Block) (h : HiddenIdx) :
    zeroHidden input rest (hiddenIdx input h) = 0 :=
  splitAlong_symm_image _ _ _ _ h

theorem zeroHidden_of_rest (v : FixedIndex → Block) (i : FixedIndex)
    (notHidden : i ∉ Set.range (hiddenIdx input)) :
    zeroHidden input (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2 i = v i :=
  splitAlong_symm_rest _ _ _ _ ⟨i, notHidden⟩

theorem xor_bits (a b : Block) (same : ∀ i, a.getLsbD i = b.getLsbD i) : a = b :=
  BitVec.eq_of_getLsbD_eq fun i _ => same i

theorem xorFold_split {count : Nat} (skip : Fin count) (family : Fin count → Block) :
    xorFold family = xorFoldExcept skip family ^^^ family skip := by
  rw [xorFoldExcept_eq, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem xor_split_hidden (X A B A' B' z : Block) (zero : A' = 0) (same : B' = B) :
    (X ^^^ (A ^^^ B)) ^^^ z = A ^^^ ((X ^^^ (A' ^^^ B')) ^^^ z) := by
  have zeroXor : (0 : Block) ^^^ B = B := BitVec.zero_xor
  rw [zero, same, zeroXor]
  refine xor_bits _ _ fun i => ?_
  simp only [BitVec.getLsbD_xor]
  cases X.getLsbD i <;> cases A.getLsbD i <;> cases B.getLsbD i <;> cases z.getLsbD i <;> rfl

/-- **A fold join is its hidden gate half XOR the rest.** -/
theorem foldJoin_split (v : FixedIndex → Block) (lane : Lane) (slot : Fin foldStepCount)
    (zero : Block) :
    foldJoin v lane slot zero =
      v (hiddenIdx input (.inl (lane, slot))) ^^^
        foldJoin (zeroHidden input (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2)
          lane slot zero := by
  set w := zeroHidden input (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2
  let a : Fin (2 ^ (slotOffset slot + 1)) :=
    ⟨activeParent input lane slot, activeParent_lt input lane slot⟩
  have rest : ∀ (e : Fin (2 ^ (slotOffset slot + 1))) (half : Bool), ¬ (e = a ∧ half = false) →
      w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) e.val half) =
        v (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) e.val half) := by
    intro e half off
    refine zeroHidden_of_rest input v _ fun ⟨h, same⟩ => off ?_
    obtain ⟨-, entry, halfEq⟩ := hot_hidden input e.isLt same
    exact ⟨Fin.ext entry, halfEq⟩
  have hidden : w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) a.val false) = 0 :=
    zeroHidden_of_hidden input _ (.inl (lane, slot))
  have other : w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) a.val true) =
      v (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) a.val true) :=
    rest a true fun h => Bool.noConfusion h.2
  have except := Programs.xorFoldExcept_congr a
    (fun e : Fin (2 ^ (slotOffset slot + 1)) =>
      v (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) e.val false) ^^^
        v (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) e.val true))
    (fun e : Fin (2 ^ (slotOffset slot + 1)) =>
      w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) e.val false) ^^^
        w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) e.val true))
    fun e off => by
      rw [rest e false fun h => off h.1, rest e true fun h => Bool.noConfusion h.2]
  unfold foldJoin
  rw [xorFold_split a, xorFold_split a (fun e : Fin (2 ^ (slotOffset slot + 1)) =>
    w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) e.val false) ^^^
      w (hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) e.val true)), ← except]
  exact xor_split_hidden _ _ _ _ _ _ hidden other

theorem gadget_not_hidden (output : Fin digitCount) (κ : Coord) (index : Fin coordinateBitCount)
    (off : ¬ (κ = .x ∧ index.val = 0)) :
    FixedIndex.gadget output κ index ∉ Set.range (hiddenIdx input) := by
  rintro ⟨(⟨ℓ, s⟩ | d), same⟩
  · simp only [hiddenIdx, hotIndexNat, reduceCtorEq] at same
  · simp only [hiddenIdx, gadgetIdx] at same
    injection same with outputEq coordEq position
    subst coordEq
    exact off ⟨rfl, (congrArg Fin.val position).symm⟩

/-- **A digest is its hidden gadget answer XOR the rest.** -/
theorem digest_split (v : FixedIndex → Block) (output : Fin digitCount) (mac : InputMac) :
    digest v output mac = v (hiddenIdx input (.inr output)) ^^^
      digest (zeroHidden input (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2)
        output mac := by
  set w := zeroHidden input (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2
  have zeroIndex : (0 : Nat) < coordinateBitCount := by decide
  let first : Fin coordinateBitCount := ⟨0, zeroIndex⟩
  have hiddenAt : FixedIndex.gadget output .x first = hiddenIdx input (.inr output) := rfl
  have atHidden : w (FixedIndex.gadget output .x first) = 0 := by
    rw [hiddenAt]
    exact zeroHidden_of_hidden input _ _
  have restX : ∀ index : Fin coordinateBitCount, index ≠ first →
      w (FixedIndex.gadget output .x index) = v (FixedIndex.gadget output .x index) :=
    fun index off =>
    zeroHidden_of_rest input v _ (gadget_not_hidden input output .x index
      (fun h => off (Fin.ext h.2)))
  have restY : ∀ index : Fin coordinateBitCount,
      w (FixedIndex.gadget output .y index) = v (FixedIndex.gadget output .y index) := fun index =>
    zeroHidden_of_rest input v _ (gadget_not_hidden input output .y index (fun h => by cases h.1))
  unfold digest
  rw [xorFold_split first,
    xorFold_split first (fun index => w (FixedIndex.gadget output .x index) ^^^ _),
    Programs.xorFoldExcept_congr first (fun index => w (FixedIndex.gadget output .x index) ^^^ _)
      (fun index => v (FixedIndex.gadget output .x index) ^^^ mac.x.get index)
      (fun index off => by rw [restX index off])]
  simp only [atHidden, restY, ← hiddenAt]
  refine xor_bits _ _ fun i => ?_
  simp only [BitVec.getLsbD_xor]
  cases (v (FixedIndex.gadget output .x first)).getLsbD i <;> simp

end Hidden

/-! ### 4. The lanes' offsets and joins are F4's -/

section Elements

variable (v : FixedIndex → Block) (T : Tape)

theorem masks_curveX (m : MaskVectors) (element : CurveXElement) (cs : ChunkSwitch) :
    (maskSiteEquiv (maskCoordEquiv m)).2 (.inl element) cs =
      m ⟨.curveX, cs.1, cs.2⟩ (curveXSlots element) := by
  simp [maskCoordEquiv, maskSiteEquiv, maskSiteSplit, laneSlots, Equiv.arrowCongr_apply,
    Sigma.uncurry]

theorem masks_curveY (m : MaskVectors) (element : CurveYElement) (cs : ChunkSwitch) :
    (maskSiteEquiv (maskCoordEquiv m)).2 (.inr element) cs =
      m ⟨.curveY, cs.1, cs.2⟩ (curveYSlots element) := by
  simp [maskCoordEquiv, maskSiteEquiv, maskSiteSplit, laneSlots, Equiv.arrowCongr_apply,
    Sigma.uncurry]

theorem masks_pointX (m : MaskVectors) (d : Fin digitCount) (element : XElement)
    (cs : ChunkSwitch) :
    (maskSiteEquiv (maskCoordEquiv m)).1 d (.inl element) cs =
      m ⟨.pointX, cs.1, cs.2⟩ (pointXSlots (d, element)) :=
  maskSiteEquiv_pointX (maskCoordEquiv m) d element cs

theorem masks_pointY (m : MaskVectors) (d : Fin digitCount) (element : YElement)
    (cs : ChunkSwitch) :
    (maskSiteEquiv (maskCoordEquiv m)).1 d (.inr element) cs =
      m ⟨.pointY, cs.1, cs.2⟩ (pointYSlots (d, element)) :=
  maskSiteEquiv_pointY (maskCoordEquiv m) d element cs

/-- **The curve lanes' offsets are F4's curve offsets.** -/
theorem curveValues_fixed (dx dy : Block) (kx ky : Fin coordinateBitCount → Block × Block) :
    Pipeline.curveValues
        (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) .curveX dx
          kx).offsets
        (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) .curveY dy
          ky).offsets =
      curveOffsets (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).2 := by
  funext element
  rcases element with e | e
  · refine (laneOffsets_fixed v T .curveX dx kx (curveXSlots e)).trans ?_
    show _ = ∑ c : Fin chunkCount, ∑ j : Fin (2 ^ chunkWidth c),
      iota _ j * (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).2 (.inl e) ⟨c, j⟩
    simp only [masks_curveX]
  · refine (laneOffsets_fixed v T .curveY dy ky (curveYSlots e)).trans ?_
    show _ = ∑ c : Fin chunkCount, ∑ j : Fin (2 ^ chunkWidth c),
      iota _ j * (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).2 (.inr e) ⟨c, j⟩
    simp only [masks_curveY]

/-- **The point lanes' offsets are F4's digit offsets.** -/
theorem digitValues_fixed (dx dy : Block) (kx ky : Fin coordinateBitCount → Block × Block)
    (d : Fin digitCount) :
    Pipeline.digitValues
        (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) .pointX dx
          kx).offsets
        (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) .pointY dy
          ky).offsets d =
      digitOffsets ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d) := by
  funext element
  rcases element with e | e
  · refine (laneOffsets_fixed v T .pointX dx kx (pointXSlots (d, e))).trans ?_
    show _ = ∑ c : Fin chunkCount, ∑ j : Fin (2 ^ chunkWidth c),
      iota _ j * (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d (.inl e) ⟨c, j⟩
    simp only [masks_pointX]
  · refine (laneOffsets_fixed v T .pointY dy ky (pointYSlots (d, e))).trans ?_
    show _ = ∑ c : Fin chunkCount, ∑ j : Fin (2 ^ chunkWidth c),
      iota _ j * (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d (.inr e) ⟨c, j⟩
    simp only [masks_pointY]

theorem pointXJoins_fixed (dx : Block) (kx : Fin coordinateBitCount → Block × Block)
    (rand : Fin digitCount → RowRand) (slopes : Fin digitCount → Biquadratic.Values)
    (hs : ∀ d, slopes d =
      digitSlopes ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d) (rand d))
    (chunk : Fin chunkCount) (slot : Fin pointElementCountX) :
    (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) .pointX dx
        kx).scaleJoins (Pipeline.pointXAssemble slopes) chunk slot =
      digitJoins
        ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 (pointXSlots.symm slot).1)
        (rand (pointXSlots.symm slot).1) (.inl (pointXSlots.symm slot).2) chunk := by
  obtain ⟨⟨d, e⟩, rfl⟩ := pointXSlots.surjective slot
  rw [Equiv.symm_apply_apply]
  refine (laneScaleJoins_fixed v T .pointX dx kx _ chunk (pointXSlots (d, e))).trans ?_
  have slope : Pipeline.pointXAssemble slopes (pointXSlots (d, e)) = slopes d (.inl e) :=
    Pipeline.pointXAssemble_digit slopes d e
  show _ = (∑ j : Fin (2 ^ chunkWidth chunk),
      (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d (.inl e) ⟨chunk, j⟩) +
    digitSlopes ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d) (rand d)
      (.inl e) * weight chunk
  rw [slope, hs d]
  simp only [masks_pointX]

theorem pointYJoins_fixed (dy : Block) (ky : Fin coordinateBitCount → Block × Block)
    (rand : Fin digitCount → RowRand) (slopes : Fin digitCount → Biquadratic.Values)
    (hs : ∀ d, slopes d =
      digitSlopes ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d) (rand d))
    (chunk : Fin chunkCount) (slot : Fin pointElementCountY) :
    (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) .pointY dy
        ky).scaleJoins (Pipeline.pointYAssemble slopes) chunk slot =
      digitJoins
        ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 (pointYSlots.symm slot).1)
        (rand (pointYSlots.symm slot).1) (.inr (pointYSlots.symm slot).2) chunk := by
  obtain ⟨⟨d, e⟩, rfl⟩ := pointYSlots.surjective slot
  rw [Equiv.symm_apply_apply]
  refine (laneScaleJoins_fixed v T .pointY dy ky _ chunk (pointYSlots (d, e))).trans ?_
  have slope : Pipeline.pointYAssemble slopes (pointYSlots (d, e)) = slopes d (.inr e) :=
    Pipeline.pointYAssemble_digit slopes d e
  show _ = (∑ j : Fin (2 ^ chunkWidth chunk),
      (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d (.inr e) ⟨chunk, j⟩) +
    digitSlopes ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d) (rand d)
      (.inr e) * weight chunk
  rw [slope, hs d]
  simp only [masks_pointY]

theorem curveXJoins_fixed (dx : Block) (kx : Fin coordinateBitCount → Block × Block)
    (r1 r2 : BaseField) (slopes : CurveMembership.Values)
    (hs : slopes = curveSlopes (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).2 r1 r2)
    (chunk : Fin chunkCount) (slot : Fin curveElementCountX) :
    (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) .curveX dx
        kx).scaleJoins (Pipeline.curveXAssemble slopes) chunk slot =
      curveJoins (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).2 r1 r2
        (.inl (curveXSlots.symm slot))
        chunk := by
  obtain ⟨e, rfl⟩ := curveXSlots.surjective slot
  rw [Equiv.symm_apply_apply]
  refine (laneScaleJoins_fixed v T .curveX dx kx _ chunk (curveXSlots e)).trans ?_
  have slope : Pipeline.curveXAssemble slopes (curveXSlots e) = slopes (.inl e) :=
    Pipeline.curveXAssemble_slot slopes e
  show _ = (∑ j : Fin (2 ^ chunkWidth chunk),
      (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).2 (.inl e) ⟨chunk, j⟩) +
    curveSlopes (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).2 r1 r2 (.inl e) *
      weight chunk
  rw [slope, hs]
  simp only [masks_curveX]

theorem curveYJoins_fixed (dy : Block) (ky : Fin coordinateBitCount → Block × Block)
    (r1 r2 : BaseField) (slopes : CurveMembership.Values)
    (hs : slopes = curveSlopes (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).2 r1 r2)
    (chunk : Fin chunkCount) (slot : Fin curveElementCountY) :
    (Programs.laneTables (tableOracle (fixedTable v T)) (tableHash (fixedTable v T)) .curveY dy
        ky).scaleJoins (Pipeline.curveYAssemble slopes) chunk slot =
      curveJoins (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).2 r1 r2
        (.inr (curveYSlots.symm slot))
        chunk := by
  obtain ⟨e, rfl⟩ := curveYSlots.surjective slot
  rw [Equiv.symm_apply_apply]
  refine (laneScaleJoins_fixed v T .curveY dy ky _ chunk (curveYSlots e)).trans ?_
  have slope : Pipeline.curveYAssemble slopes (curveYSlots e) = slopes (.inr e) :=
    Pipeline.curveYAssemble_slot slopes e
  show _ = (∑ j : Fin (2 ^ chunkWidth chunk),
      (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).2 (.inr e) ⟨chunk, j⟩) +
    curveSlopes (maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).2 r1 r2 (.inr e) *
      weight chunk
  rw [slope, hs]
  simp only [masks_curveY]

end Elements

/-! ### 5. F4's context off the curve, and the matching -/

section Context

variable (input : AffineInput) (pads : Programs.Pads)

/-- The label pairs of some zero labels and offsets (the coins' `inputMacKey`). -/
def labelKey (Z : Coord → Fin coordinateBitCount → Block) (Δ : Coord → Block) : InputMacKey where
  x := Vector.ofFn fun position => { falseLabel := Z .x position, trueLabel := Z .x position ^^^ Δ .x }
  y := Vector.ofFn fun position => { falseLabel := Z .y position, trueLabel := Z .y position ^^^ Δ .y }

/-- A lane's bit keys. -/
def laneKey (key : InputMacKey) : Lane → Fin coordinateBitCount → Block × Block
  | .curveX => Pipeline.bitKeyOf key .x
  | .curveY => Pipeline.bitKeyOf key .y
  | .pointX => Pipeline.bitKeyOf (Programs.whitenKeyOf pads key) .x
  | .pointY => Pipeline.bitKeyOf (Programs.whitenKeyOf pads key) .y

/-- **F4's context off the curve**, from the output keys and the rest: the true rows and `ρ`, the
fold joins and the digests with the hidden answers zeroed, the gadget slots and codes. (The keys
are a parameter so that no proof ever unfolds the scalar's digits.) -/
def offContext (keys : OutputKeys) (o : Outer input) : JointContext where
  rows d := Coordinates.rows (keys.get d).offset.coordinates
    (digitEndomorphismBase (keys.get d).digit) (o.2.1 d).value
  rho d := o.2.1 d
  foldVisible _ lane slot := foldJoin (zeroHidden input o.2.2.2.2) lane slot
    (zeroAt (laneKey pads (labelKey o.2.2.1 o.2.2.2.1) lane) slot)
  gadgetVisible _ d := match digitEndomorphismBase (keys.get d).digit with
    | none => 0
    | some phi => digest (zeroHidden input o.2.2.2.2) d
        ((Programs.transformKeyOf pads (labelKey o.2.2.1 o.2.2.2.1)).encodeAffine
          (Exception.exceptionalInput phi (keys.get d).offset.coordinates))
  gadgetSlot d := (digitEndomorphismBase (keys.get d).digit).map fun phi =>
    Exception.exceptionIndex (Exception.exceptionalInput phi (keys.get d).offset.coordinates)
  gadgetCode d := Exception.digitCode (keys.get d).digit

theorem public_ext {a b : Public} (curve : a.curve = b.curve) (rows : a.rows = b.rows)
    (exception : a.exception = b.exception) (cx : a.curveXHot = b.curveXHot)
    (cy : a.curveYHot = b.curveYHot) (px : a.pointXHot = b.pointXHot) (py : a.pointYHot = b.pointYHot)
    (scale : a.scale = b.scale) : a = b := by
  cases a
  cases b
  simp only at curve rows exception cx cy px py scale
  subst curve rows exception cx cy px py scale
  rfl

theorem entryOf_gadgetEntry (v : FixedIndex → Block) (d : Fin digitCount) (key : OutputKey)
    (inputKey : InputMacKey) (pad : Exception.Entry) :
    entryOf v d key inputKey pad = gadgetEntry
      ((digitEndomorphismBase key.digit).map fun phi =>
        Exception.exceptionIndex (Exception.exceptionalInput phi key.offset.coordinates))
      (Exception.digitCode key.digit)
      (match digitEndomorphismBase key.digit with
        | none => 0
        | some phi => digest (zeroHidden input (splitAlong (hiddenIdx input)
            (hiddenIdx_injective input) v).2) d
              (inputKey.encodeAffine (Exception.exceptionalInput phi key.offset.coordinates)))
      pad (v (hiddenIdx input (.inr d))) := by
  unfold entryOf
  cases digitEndomorphismBase key.digit with
  | none => rfl
  | some phi =>
      show Exception.writeEntry pad _ (Exception.lowByte (digest v d _) ^^^ _) =
        Exception.writeEntry pad _ (Exception.lowByte (_ ^^^ _) ^^^ _)
      rw [digest_split input v d]

theorem cellsSource_exception (cells : PublicCells) (key : InputMacKey) :
    (cellsSource cells key).publicValue.exception = Vector.ofFn cells.2.2.2 := rfl

theorem cellsSource_hot (cells : PublicCells) (key : InputMacKey) :
    (cellsSource cells key).publicValue.curveXHot = Vector.ofFn (cells.2.2.1 .curveX) ∧
    (cellsSource cells key).publicValue.curveYHot = Vector.ofFn (cells.2.2.1 .curveY) ∧
    (cellsSource cells key).publicValue.pointXHot = Vector.ofFn (cells.2.2.1 .pointX) ∧
    (cellsSource cells key).publicValue.pointYHot = Vector.ofFn (cells.2.2.1 .pointY) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem cellsSource_scale (cells : PublicCells) (key : InputMacKey) :
    (cellsSource cells key).publicValue.scale =
      Vector.ofFn fun chunk => pack (cellsJoins cells chunk) := rfl

theorem assemble_exception (keys : OutputKeys) (pR : Randomness) (t : BaseField) (mask : NonZeroBase)
    (r1 r2 : BaseField) (cx : Programs.LaneTables curveElementCountX)
    (cy : Programs.LaneTables curveElementCountY) (px : Programs.LaneTables pointElementCountX)
    (py : Programs.LaneTables pointElementCountY) (g : Vector Exception.Entry outputMacCount) :
    (Programs.assemble keys pR t mask r1 r2 cx cy px py g).exception = g := rfl

theorem assemble_hot (keys : OutputKeys) (pR : Randomness) (t : BaseField) (mask : NonZeroBase)
    (r1 r2 : BaseField) (cx : Programs.LaneTables curveElementCountX)
    (cy : Programs.LaneTables curveElementCountY) (px : Programs.LaneTables pointElementCountX)
    (py : Programs.LaneTables pointElementCountY) (g : Vector Exception.Entry outputMacCount) :
    (Programs.assemble keys pR t mask r1 r2 cx cy px py g).curveXHot = cx.hotJoins ∧
    (Programs.assemble keys pR t mask r1 r2 cx cy px py g).curveYHot = cy.hotJoins ∧
    (Programs.assemble keys pR t mask r1 r2 cx cy px py g).pointXHot = px.hotJoins ∧
    (Programs.assemble keys pR t mask r1 r2 cx cy px py g).pointYHot = py.hotJoins :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The garbler's published value on a table is the source of F4's published cells.** -/
theorem tablePub_cells (coins : Coins) (v : FixedIndex → Block) (T : Tape) (key : InputMacKey)
    (keys : OutputKeys)
    (keysEq : FieldMacToECMac.outputKeys construction scalar.value coins.offsets = keys) :
    tablePub scalar coins pads v T =
      (cellsSource (publicOf (offContext input pads keys
          (omegaEquiv input (coins, v, masksOf VectorSite.lane T)).1)
        (omegaEquiv input (coins, v, masksOf VectorSite.lane T)).2) key).publicValue := by
  unfold tablePub
  rw [keysEq]
  have outerEq : (omegaEquiv input (coins, v, masksOf VectorSite.lane T)).1 =
      (⟨coins.offsets, coins.offsetsClamped⟩, fun d => (coins.pointRandomness.get d).rho,
        coins.inputZero, coins.inputDelta,
        (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2) := rfl
  have coinsEq : (omegaEquiv input (coins, v, masksOf VectorSite.lane T)).2 =
      (fun d => ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).1 d,
          ((coins.pointRandomness.get d).x,
          (coins.pointRandomness.get d).y, (coins.pointRandomness.get d).z)),
        ((maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))).2, coins.bridgeKey,
          ⟨coins.curveMask.value, coins.curveMask.nonzero⟩, coins.curveR1, coins.curveR2),
        (fun ℓ s => v (hiddenIdx input (.inl (ℓ, s))),
          fun d => (coins.exceptionPad.get d, v (hiddenIdx input (.inr d))))) := rfl
  rw [outerEq, coinsEq]
  set O := tableOracle (fixedTable v T)
  set H := tableHash (fixedTable v T)
  set m := maskSiteEquiv (maskCoordEquiv (masksOf VectorSite.lane T))
  set PX := Programs.laneTables O H .pointX (coins.inputDelta .x)
    (Pipeline.bitKeyOf (Programs.whitenKeyOf pads coins.inputMacKey) .x)
  set PY := Programs.laneTables O H .pointY (coins.inputDelta .y)
    (Pipeline.bitKeyOf (Programs.whitenKeyOf pads coins.inputMacKey) .y)
  have digitK : ∀ d, Pipeline.digitValues PX.offsets PY.offsets d =
      digitOffsets (m.1 d) := fun d => digitValues_fixed v T _ _ _ _ d
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
    rw [garbleEntryM_table, entryOf_gadgetEntry input v d]
    rfl
  · rw [(assemble_hot _ _ _ _ _ _ _ _ _ _ _).1, (cellsSource_hot _ _).1, laneHotJoins_fixed]
    exact congrArg Vector.ofFn (funext fun s => foldJoin_split input v .curveX s _)
  · rw [(assemble_hot _ _ _ _ _ _ _ _ _ _ _).2.1, (cellsSource_hot _ _).2.1, laneHotJoins_fixed]
    exact congrArg Vector.ofFn (funext fun s => foldJoin_split input v .curveY s _)
  · rw [(assemble_hot _ _ _ _ _ _ _ _ _ _ _).2.2.1, (cellsSource_hot _ _).2.2.1, laneHotJoins_fixed]
    exact congrArg Vector.ofFn (funext fun s => foldJoin_split input v .pointX s _)
  · rw [(assemble_hot _ _ _ _ _ _ _ _ _ _ _).2.2.2, (cellsSource_hot _ _).2.2.2, laneHotJoins_fixed]
    exact congrArg Vector.ofFn (funext fun s => foldJoin_split input v .pointY s _)
  · have pointSlopes : ∀ d : Fin digitCount, Biquadratic.slopes (coins.pointRandomness.get d).x
        (coins.pointRandomness.get d).y (coins.pointRandomness.get d).z
          (Pipeline.digitValues PX.offsets PY.offsets d) =
        digitSlopes (m.1 d) ((coins.pointRandomness.get d).x,
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
        curveSlopes m.2 coins.curveR1 coins.curveR2 := by
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

end Context

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
