/-
**Phase 3, P1n — the off-curve law, step (ii), part 1: the source is its published cells.**

A stage-1 source is, bijectively, F4's published cells (`JointExactness.PublicCells`: every digit's
joins on both point lanes and its row constants, the curve joins and constants, one fold join per
(lane, paid fold step), one gadget entry per digit) and its Lamport key (`cellsEquiv`): the scale
word of a chunk is its four lanes' joins (`Mismatch.wordEquiv`), whose element slots are the
digits' and the curve's elements (`pointXSlots`, `curveXSlots`, …), and a lane's
`foldStepCount` published fold joins (`b_c − 1` per chunk) are its cells in the flat slot order
(`slotChunk`, `slotOffset`: slot `s` is fold step `slotOffset s + 1` of chunk `slotChunk s`).

So a uniform source publishes `cellsSource` of uniform cells (`tsum_source_cells`).

Also here: **splitting a uniform function along an injective map** (`splitAlong`), the fixed-key
indices off the curve that hide a published cell (`hiddenIdx`: the active parent's first gate half
of every paid fold step, both bits of one gadget position per digit) and those system A reads
(`ViewIdx`: both halves of every curve-lane gate off the active parent, at every paid step), and
the garbler's randomness on a table as the rest and F4's coins (`omegaEquiv`). A digit's two
digests read different answers only where its two exceptional inputs differ, so `omegaEquiv`
first moves each digit's differing position to the hidden one (`indexSwap`, an involution that
depends on the offsets and fixes every fold gate).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOffTable
import Proof.Privacy.Phase3.PublicFirst.Mismatch
import Proof.Privacy.Phase3.PublicFirst.FlagBound

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source)
open scoped ENNReal

noncomputable section

theorem baseTwo_ne_zero : (2 : BaseField) ≠ 0 := by decide

/-! ### 1. The flat fold slots -/

/-- A slot's step is a paid step of its chunk. -/
theorem slotOffset_lt (slot : Fin foldStepCount) :
    slotOffset slot < chunkWidth (slotChunk slot) - 1 :=
  (slot_eq_foldBase_add slot).2

theorem slotStep_lt_chunkBits (slot : Fin foldStepCount) : slotOffset slot + 1 < chunkBits :=
  lt_of_lt_of_le (by have := slotOffset_lt slot; omega) (chunkWidth_le (slotChunk slot))

/-- **A slot is its (chunk, step).** -/
theorem slot_ext {slot slot' : Fin foldStepCount} (chunk : slotChunk slot = slotChunk slot')
    (offset : slotOffset slot = slotOffset slot') : slot = slot' :=
  slot_ext_of_eq chunk offset

theorem ofFn_get' {α : Type} {n : Nat} (v : Vector α n) : Vector.ofFn v.get = v := by
  apply Vector.ext
  intro i bound
  simp [Vector.get_eq_getElem]

/-! ### 2. The source and its cells -/

variable [FieldCertificate]

/-- The scale word of a chunk, from the cells. -/
def cellsJoins (cells : PublicCells) (chunk : Fin chunkCount) : Fin elementCount → BaseField :=
  wordEquiv (fun slot => (cells.1 (pointXSlots.symm slot).1).1 (.inl (pointXSlots.symm slot).2) chunk,
    fun slot => cells.2.1.1 (.inl (curveXSlots.symm slot)) chunk,
    fun slot => (cells.1 (pointYSlots.symm slot).1).1 (.inr (pointYSlots.symm slot).2) chunk,
    fun slot => cells.2.1.1 (.inr (curveYSlots.symm slot)) chunk)

/-- **The source of some cells and a key.** -/
def cellsSource (cells : PublicCells) (key : InputMacKey) : Stage1Source where
  curve := cells.2.1.2
  rows := Vector.ofFn fun d => (cells.1 d).2
  exception := Vector.ofFn cells.2.2.2
  curveXHot := Vector.ofFn (cells.2.2.1 .curveX)
  curveYHot := Vector.ofFn (cells.2.2.1 .curveY)
  pointXHot := Vector.ofFn (cells.2.2.1 .pointX)
  pointYHot := Vector.ofFn (cells.2.2.1 .pointY)
  joins := cellsJoins cells
  key := key

/-- A source's fold joins, by lane. -/
def sourceHot (source : Stage1Source) : Lane → Vector Block foldStepCount
  | .curveX => source.curveXHot
  | .curveY => source.curveYHot
  | .pointX => source.pointXHot
  | .pointY => source.pointYHot

/-- **The cells of a source.** -/
def sourceCells (source : Stage1Source) : PublicCells :=
  (fun d => (fun element c => Sum.elim
      (fun e => Pipeline.readPointX (source.joins c) (pointXSlots (d, e)))
      (fun e => Pipeline.readPointY (source.joins c) (pointYSlots (d, e))) element,
    source.rows.get d),
   (fun element c => Sum.elim (fun e => Pipeline.readCurveX (source.joins c) (curveXSlots e))
      (fun e => Pipeline.readCurveY (source.joins c) (curveYSlots e)) element, source.curve),
   fun lane slot => (sourceHot source lane).get slot,
   fun d => source.exception.get d)

theorem sourceCells_cellsSource (cells : PublicCells) (key : InputMacKey) :
    sourceCells (cellsSource cells key) = cells := by
  obtain ⟨digits, curve, fold, gadget⟩ := cells
  have word : ∀ c, cellsJoins (digits, curve, fold, gadget) c = Pipeline.assembleWord
      (fun slot => (digits (pointXSlots.symm slot).1).1 (.inl (pointXSlots.symm slot).2) c)
      (fun slot => curve.1 (.inl (curveXSlots.symm slot)) c)
      (fun slot => (digits (pointYSlots.symm slot).1).1 (.inr (pointYSlots.symm slot).2) c)
      (fun slot => curve.1 (.inr (curveYSlots.symm slot)) c) := fun _ => rfl
  refine Prod.ext (funext fun d => Prod.ext (funext fun element => funext fun c => ?_) ?_)
    (Prod.ext (Prod.ext (funext fun element => funext fun c => ?_) rfl)
      (Prod.ext (funext fun lane => funext fun slot => ?_) (funext fun d => ?_)))
  · show Sum.elim (fun e => Pipeline.readPointX (cellsJoins _ c) (pointXSlots (d, e)))
      (fun e => Pipeline.readPointY (cellsJoins _ c) (pointYSlots (d, e))) element = _
    rw [word]
    rcases element with e | e
    · show Pipeline.readPointX _ _ = _
      rw [Pipeline.readPointX_assembleWord, Equiv.symm_apply_apply]
    · show Pipeline.readPointY _ _ = _
      rw [Pipeline.readPointY_assembleWord, Equiv.symm_apply_apply]
  · exact Vector.get_ofFn _ d
  · show Sum.elim (fun e => Pipeline.readCurveX (cellsJoins _ c) (curveXSlots e))
      (fun e => Pipeline.readCurveY (cellsJoins _ c) (curveYSlots e)) element = _
    rw [word]
    rcases element with e | e
    · show Pipeline.readCurveX _ _ = _
      rw [Pipeline.readCurveX_assembleWord, Equiv.symm_apply_apply]
    · show Pipeline.readCurveY _ _ = _
      rw [Pipeline.readCurveY_assembleWord, Equiv.symm_apply_apply]
  · cases lane <;> exact Vector.get_ofFn _ slot
  · exact Vector.get_ofFn _ d

theorem cellsSource_sourceCells (source : Stage1Source) :
    cellsSource (sourceCells source) source.key = source := by
  obtain ⟨curve, rows, exception, cx, cy, px, py, joins, key⟩ := source
  have joinsEq : cellsJoins (sourceCells ⟨curve, rows, exception, cx, cy, px, py, joins, key⟩) =
      joins := by
    funext c
    show wordEquiv (fun slot => Pipeline.readPointX (joins c)
        (pointXSlots ((pointXSlots.symm slot).1, (pointXSlots.symm slot).2)),
      fun slot => Pipeline.readCurveX (joins c) (curveXSlots (curveXSlots.symm slot)),
      fun slot => Pipeline.readPointY (joins c)
        (pointYSlots ((pointYSlots.symm slot).1, (pointYSlots.symm slot).2)),
      fun slot => Pipeline.readCurveY (joins c) (curveYSlots (curveYSlots.symm slot))) = _
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    exact assembleWord_read (joins c)
  show Stage1Source.mk curve (Vector.ofFn fun d => rows.get d)
    (Vector.ofFn fun d => exception.get d) (Vector.ofFn cx.get) (Vector.ofFn cy.get)
    (Vector.ofFn px.get) (Vector.ofFn py.get)
    (cellsJoins (sourceCells ⟨curve, rows, exception, cx, cy, px, py, joins, key⟩)) key = _
  rw [ofFn_get', ofFn_get', ofFn_get', ofFn_get', ofFn_get', ofFn_get', joinsEq]

/-- **A source is its cells and its key.** -/
def cellsEquiv : PublicCells × InputMacKey ≃ Stage1Source where
  toFun pair := cellsSource pair.1 pair.2
  invFun source := (sourceCells source, source.key)
  left_inv pair := by
    obtain ⟨cells, key⟩ := pair
    exact Prod.ext (sourceCells_cellsSource cells key) rfl
  right_inv source := cellsSource_sourceCells source

/-- **A uniform source is uniform cells and an independent uniform key.** -/
theorem tsum_source_cells (F : Stage1Source → ℝ≥0∞) :
    ∑' source, PMF.uniformOfFintype Stage1Source source * F source =
      ∑' cells, PMF.uniformOfFintype PublicCells cells *
        ∑' key, PMF.uniformOfFintype InputMacKey key * F (cellsSource cells key) := by
  rw [← Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv cellsEquiv, tsum_map_mul,
    tsum_uniform_prod]
  rfl

/-! ### 3. Splitting a function along an injective map -/

section Split

variable {I J β : Type} (ι : J → I) (inj : Function.Injective ι)

open Classical in
/-- **A function is its values on the image of `ι` and its values elsewhere.** -/
def splitAlong : (I → β) ≃ (J → β) × ({i : I // i ∉ Set.range ι} → β) where
  toFun f := (f ∘ ι, fun i => f i.1)
  invFun p i := if h : i ∈ Set.range ι then p.1 (Classical.choose h) else p.2 ⟨i, h⟩
  left_inv f := by
    funext i
    by_cases h : i ∈ Set.range ι
    · simp only [dif_pos h, Function.comp]
      rw [Classical.choose_spec h]
    · simp only [dif_neg h]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext (funext fun j => ?_) (funext fun i => ?_)
    · have h : ι j ∈ Set.range ι := ⟨j, rfl⟩
      show (if h' : ι j ∈ Set.range ι then a (Classical.choose h') else b ⟨ι j, h'⟩) = a j
      rw [dif_pos h, inj (Classical.choose_spec h)]
    · show (if h' : i.1 ∈ Set.range ι then a (Classical.choose h') else b ⟨i.1, h'⟩) = b i
      rw [dif_neg i.2]

theorem splitAlong_symm_image (a : J → β) (b : {i : I // i ∉ Set.range ι} → β) (j : J) :
    (splitAlong ι inj).symm (a, b) (ι j) = a j :=
  congrFun (congrArg Prod.fst ((splitAlong ι inj).apply_symm_apply (a, b))) j

theorem splitAlong_symm_rest (a : J → β) (b : {i : I // i ∉ Set.range ι} → β)
    (i : {i : I // i ∉ Set.range ι}) : (splitAlong ι inj).symm (a, b) i.1 = b i :=
  congrFun (congrArg Prod.snd ((splitAlong ι inj).apply_symm_apply (a, b))) i

end Split

/-! ### 4. The hidden and the viewed fixed-key indices, off the curve -/

section Indices

variable (input : AffineInput)

/-- The active parent of a (lane, paid fold step) at the input: the low `n` bits of the chunk's
value, at the step's level `n = slotOffset slot + 1`. -/
def activeParent (lane : Lane) (slot : Fin foldStepCount) : Nat :=
  (chunkOf (inputBits input lane.coord) (slotChunk slot)).val % 2 ^ (slotOffset slot + 1)

theorem activeParent_lt (lane : Lane) (slot : Fin foldStepCount) :
    activeParent input lane slot < 2 ^ (slotOffset slot + 1) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The hidden coins among the fixed-key answers: the active parent's first gate half at every
(lane, paid step) (the fold join's hidden material) and both answers at one gadget position per
digit (the two digests' hidden parts). -/
abbrev HiddenIdx := (Lane × Fin foldStepCount) ⊕ (Fin digitCount × Bool)

/-- The gadget position whose two answers hide a digit's two digests (after `indexSwap`). -/
def gadgetIdx (d : Fin digitCount) (bit : Bool) : FixedIndex :=
  .gadget d .x ⟨0, by unfold PlanB.coordinateBits; omega⟩ bit

/-- The hidden coins' indices. -/
def hiddenIdx : HiddenIdx → FixedIndex
  | .inl p =>
    hotIndexNat p.1 (slotChunk p.2) (slotOffset p.2 + 1) (activeParent input p.1 p.2) false
  | .inr p => gadgetIdx p.1 p.2

theorem entry_lt_twoPow {n e : Nat} (small : n < chunkBits) (entry : e < 2 ^ n) :
    e < 2 ^ chunkBits :=
  lt_of_lt_of_le entry (Nat.pow_le_pow_right (by norm_num) small.le)

/-- **A paid gate of a slot's step is a hidden index only at the slot's active parent's first
half.** -/
theorem hot_hidden {lane : Lane} {slot : Fin foldStepCount} {e : Nat} {half : Bool}
    (small : e < 2 ^ (slotOffset slot + 1)) {h : HiddenIdx}
    (same : hiddenIdx input h = hotIndexNat lane (slotChunk slot) (slotOffset slot + 1) e half) :
    h = .inl (lane, slot) ∧ e = activeParent input lane slot ∧ half = false := by
  rcases h with ⟨ℓ, s⟩ | ⟨d, b⟩
  · obtain ⟨rfl, chunk, step, entry, rfl⟩ := hotIndexNat_inj (slotStep_lt_chunkBits s)
      (slotStep_lt_chunkBits slot)
      (entry_lt_twoPow (slotStep_lt_chunkBits s) (activeParent_lt input ℓ s))
      (entry_lt_twoPow (slotStep_lt_chunkBits slot) small) same
    obtain rfl := slot_ext chunk (Nat.add_right_cancel step)
    exact ⟨rfl, entry.symm, rfl⟩
  · simp only [hiddenIdx, gadgetIdx, hotIndexNat, reduceCtorEq] at same

theorem hiddenIdx_injective : Function.Injective (hiddenIdx input) := by
  rintro (⟨ℓ, s⟩ | ⟨d, b⟩) h' same
  · exact (hot_hidden input (activeParent_lt input ℓ s) same.symm).1.symm
  · rcases h' with ⟨ℓ', s'⟩ | ⟨d', b'⟩
    · simp only [hiddenIdx, gadgetIdx, hotIndexNat, reduceCtorEq] at same
    · simp only [hiddenIdx, gadgetIdx, FixedIndex.gadget.injEq, true_and] at same
      obtain ⟨rfl, rfl⟩ := same
      rfl

/-- **A view gate**: a half of a curve lane's gate at a paid fold step, off the step's active
parent — what system A asks off the curve. -/
def IsView (index : FixedIndex) : Prop :=
  ∃ (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat) (half : Bool),
    laneIsCurve lane = true ∧ 0 < step ∧ step < chunkWidth chunk ∧ entry < 2 ^ step ∧
      entry ≠ (chunkOf (inputBits input lane.coord) chunk).val % 2 ^ step ∧
      index = hotIndexNat lane chunk step entry half

/-- The view's fold gates. -/
abbrev ViewIdx := {index : FixedIndex // IsView input index}

noncomputable instance viewIdxFintype : Fintype (ViewIdx input) := Fintype.ofFinite _

/-- The view's fold gates, as fixed-key indices. -/
def viewIdx (w : ViewIdx input) : FixedIndex := w.1

theorem viewIdx_injective : Function.Injective (viewIdx input) := Subtype.val_injective

theorem viewIdx_not_hidden (w : ViewIdx input) :
    viewIdx input w ∉ Set.range (hiddenIdx input) := by
  rintro ⟨h, same⟩
  obtain ⟨lane, chunk, step, entry, half, -, positive, below, small, off, eq⟩ := w.2
  rw [show viewIdx input w = w.1 from rfl, eq] at same
  have width : step - 1 < chunkWidth chunk - 1 := by omega
  let slot := flatSlot chunk ⟨step - 1, width⟩
  have chunkEq : slotChunk slot = chunk := slotChunk_eq slot chunk (step - 1) width rfl
  have offsetEq : slotOffset slot + 1 = step := by
    rw [slotOffset_eq slot chunk (step - 1) width rfl]
    omega
  rw [← chunkEq, ← offsetEq] at same
  rw [← offsetEq] at small
  have hit := (hot_hidden input small same).2.1
  apply off
  rw [hit, activeParent, chunkEq, offsetEq]

/-- The view's fold gates among the rest. -/
def viewRest (w : ViewIdx input) : {i : FixedIndex // i ∉ Set.range (hiddenIdx input)} :=
  ⟨viewIdx input w, viewIdx_not_hidden input w⟩

theorem viewRest_injective : Function.Injective (viewRest input) := by
  intro a b same
  have values : (viewRest input a).1 = (viewRest input b).1 := congrArg Subtype.val same
  exact viewIdx_injective input values

end Indices

/-! ### 4b. Moving each digit's differing position to the hidden one -/

section Swap

/-- The origin position `(x, 0)`, where the hidden gadget answers sit. -/
def originPos : Coord × Fin PlanB.coordinateBits := (.x, ⟨0, by unfold PlanB.coordinateBits; omega⟩)

/-- A position where a key's two exceptional inputs differ (`originPos` if there is none, as for
digit zero). -/
def diffPos (key : OutputKey) : Coord × Fin PlanB.coordinateBits :=
  match digitEndomorphismBase key.digit with
  | none => originPos
  | some phi =>
    if h : ∃ q : Coord × Fin PlanB.coordinateBits,
        (inputBits (Exception.exceptionalInput phi key.offset.coordinates) q.1).getLsb q.2 ≠
          (inputBits (Exception.tripleInput phi key.offset.coordinates) q.1).getLsb q.2
    then Classical.choose h else originPos

/-- The doubling input's bit at the differing position (`false` for digit zero). -/
def diffBit (key : OutputKey) : Bool :=
  match digitEndomorphismBase key.digit with
  | none => false
  | some phi =>
    (inputBits (Exception.exceptionalInput phi key.offset.coordinates) (diffPos key).1).getLsb
      (diffPos key).2

/-- **One digit's gadget swap**: the origin and the differing position trade places, the bit
shifted by `diffBit`, so that the origin's two indices are the doubling and the sign-zero digests'
own answers at the differing position. -/
def gadgetSwap (key : OutputKey) (κ : Coord) (p : Fin PlanB.coordinateBits) (b : Bool) :
    Coord × Fin PlanB.coordinateBits × Bool :=
  if (κ, p) = originPos then ((diffPos key).1, (diffPos key).2, b ^^ diffBit key)
  else if (κ, p) = diffPos key then (originPos.1, originPos.2, b ^^ diffBit key)
  else (κ, p, b)

theorem gadgetSwap_twice (key : OutputKey) (κ : Coord) (p : Fin PlanB.coordinateBits) (b : Bool) :
    gadgetSwap key (gadgetSwap key κ p b).1 (gadgetSwap key κ p b).2.1 (gadgetSwap key κ p b).2.2 =
      (κ, p, b) := by
  unfold gadgetSwap
  by_cases origin : (κ, p) = originPos
  · rw [if_pos origin]
    dsimp only
    by_cases same : diffPos key = originPos
    · rw [if_pos (by rw [Prod.mk.eta, same]), same, ← origin]
      simp
    · rw [if_neg (by rw [Prod.mk.eta]; exact same), if_pos (Prod.mk.eta), ← origin]
      simp
  · rw [if_neg origin]
    by_cases target : (κ, p) = diffPos key
    · rw [if_pos target]
      dsimp only
      rw [if_pos (Prod.mk.eta), ← target]
      simp
    · rw [if_neg target]
      dsimp only
      rw [if_neg origin, if_neg target]

/-- Digit `d`'s key. -/
def keyOf (keys : OutputKeys) (d : Fin digitCount) : OutputKey := keys.get ⟨d.val, d.isLt⟩

/-- **The index swap** of the output keys: each digit's `gadgetSwap`; every fold gate is fixed. -/
def indexSwap (keys : OutputKeys) : FixedIndex → FixedIndex
  | .gadget d κ p b =>
    .gadget d (gadgetSwap (keyOf keys d) κ p b).1 (gadgetSwap (keyOf keys d) κ p b).2.1
      (gadgetSwap (keyOf keys d) κ p b).2.2
  | index => index

theorem indexSwap_involutive (keys : OutputKeys) : Function.Involutive (indexSwap keys) := by
  intro index
  cases index with
  | gadget d κ p b =>
    show FixedIndex.gadget d _ _ _ = _
    rw [gadgetSwap_twice]
  | hot lane c fold entry half => rfl

theorem indexSwap_hot (keys : OutputKeys) (lane : Lane) (c : Fin chunkCount) (fold : Fin chunkBits)
    (entry : Fin (2 ^ chunkBits)) (half : Bool) :
    indexSwap keys (.hot lane c fold entry half) = .hot lane c fold entry half := rfl

/-- The swap sends the origin's two indices to the differing position. -/
theorem indexSwap_origin (keys : OutputKeys) (d : Fin digitCount) (b : Bool) :
    indexSwap keys (gadgetIdx d b) =
      .gadget d (diffPos (keyOf keys d)).1 (diffPos (keyOf keys d)).2 (b ^^ diffBit (keyOf keys d)) := by
  show FixedIndex.gadget d _ _ _ = _
  unfold gadgetSwap
  rw [if_pos (show ((Coord.x, ⟨0, _⟩) : Coord × Fin PlanB.coordinateBits) = originPos from rfl)]

/-- The swap keeps each digit's other positions off the origin. -/
theorem indexSwap_off (keys : OutputKeys) (d : Fin digitCount) (κ : Coord)
    (p : Fin PlanB.coordinateBits) (b : Bool) (off : (κ, p) ≠ diffPos (keyOf keys d))
    (notOrigin : (κ, p) ≠ originPos) :
    indexSwap keys (.gadget d κ p b) = .gadget d κ p b := by
  show FixedIndex.gadget d _ _ _ = _
  unfold gadgetSwap
  rw [if_neg notOrigin, if_neg off]

/-- The two exceptional inputs of a nonzero digit differ: `2K ≠ K` as affine points, since
`K.y ≠ 0`. -/
theorem exceptionalInput_ne_triple [GroupCertificate] (phi : BaseField) (phiSix : phi ^ 6 = 1)
    (offset : AffineInput) (onCurve : OnCurve offset) :
    Exception.exceptionalInput phi offset ≠ Exception.tripleInput phi offset := by
  intro same
  have phiNe : phi ≠ 0 := fun zero => by
    rw [zero, zero_pow (by norm_num)] at phiSix
    exact zero_ne_one phiSix
  have yNe := JacobianMixed.noAffineYZero offset onCurve
  have xs := congrArg AffineInput.x same
  have ys := congrArg AffineInput.y same
  simp only [Exception.tripleInput, Exception.exceptionalInput, Exception.doubleOffset] at xs ys
  have xEq := mul_left_cancel₀ (pow_ne_zero 2 phiNe) xs
  have yEq := mul_left_cancel₀ (pow_ne_zero 3 phiNe) ys
  rw [← xEq, sub_self, mul_zero, zero_sub] at yEq
  have twice : (2 : BaseField) * offset.y = 0 := by linear_combination yEq
  exact yNe ((mul_eq_zero.mp twice).resolve_left baseTwo_ne_zero)

/-- Two inputs with the same bits everywhere are equal. -/
theorem affine_eq_of_bits {first second : AffineInput}
    (same : ∀ q : Coord × Fin PlanB.coordinateBits,
      (inputBits first q.1).getLsb q.2 = (inputBits second q.1).getLsb q.2) : first = second := by
  have coordinate : ∀ (a b : BaseField), (∀ p : Fin PlanB.coordinateBits,
      (coordinateBits a).getLsb p = (coordinateBits b).getLsb p) → a = b := by
    intro a b bits
    have vectors : coordinateBits a = coordinateBits b :=
      BitVec.eq_of_getLsbD_eq fun i small => bits ⟨i, small⟩
    have values := congrArg BitVec.toNat vectors
    rw [coordinateBitsToNat, coordinateBitsToNat] at values
    exact ZMod.val_injective _ values
  obtain ⟨x₁, y₁⟩ := first
  obtain ⟨x₂, y₂⟩ := second
  rw [coordinate x₁ x₂ fun p => same (.x, p), coordinate y₁ y₂ fun p => same (.y, p)]

/-- **At the differing position the two exceptional inputs have different bits.** -/
theorem diffPos_spec [GroupCertificate] (key : OutputKey) (phi : BaseField)
    (found : digitEndomorphismBase key.digit = some phi) :
    (inputBits (Exception.tripleInput phi key.offset.coordinates) (diffPos key).1).getLsb
        (diffPos key).2 = !diffBit key := by
  have exists_diff : ∃ q : Coord × Fin PlanB.coordinateBits,
      (inputBits (Exception.exceptionalInput phi key.offset.coordinates) q.1).getLsb q.2 ≠
        (inputBits (Exception.tripleInput phi key.offset.coordinates) q.1).getLsb q.2 := by
    by_contra none
    push Not at none
    exact exceptionalInput_ne_triple phi (digitEndomorphismBasePowSix _ _ found) _
      key.offset.onCurve (affine_eq_of_bits none)
  unfold diffBit diffPos
  rw [found]
  dsimp only
  rw [dif_pos exists_diff]
  have spec := Classical.choose_spec exists_diff
  revert spec
  cases (inputBits (Exception.exceptionalInput phi key.offset.coordinates)
      (Classical.choose exists_diff).1).getLsb (Classical.choose exists_diff).2 <;>
    cases (inputBits (Exception.tripleInput phi key.offset.coordinates)
      (Classical.choose exists_diff).1).getLsb (Classical.choose exists_diff).2 <;> simp

end Swap

/-! ### 5. The coins of the off-curve garbler on a table, as F4's coins and the rest -/

section Omega

open Kriterion.ArgoMAC.Scheme (Coins)

variable (input : AffineInput)

/-- The offsets the coins may carry. -/
abbrev ClampedOffsets :=
  {offsets : SuccessfulOffsets // ∀ [FieldCertificate] [GroupCertificate], offsets.IsClamped}

/-- The coins, field by field, the vectors read as functions. -/
abbrev CoinsParts := ClampedOffsets × (Fin outputMacCount → RowRandomness) ×
  (Fin outputMacCount → Exception.Entry) × BaseField × NonZeroBase × BaseField × BaseField ×
  (Coord → Fin coordinateBitCount → Block) × (Coord → Block)

/-- **The coins are their fields.** -/
def coinsSplit : Coins ≃ CoinsParts where
  toFun c := (⟨c.offsets, c.offsetsClamped⟩, c.pointRandomness.get, c.exceptionPad.get, c.bridgeKey,
    c.curveMask, c.curveR1, c.curveR2, c.inputZero, c.inputDelta)
  invFun p := ⟨p.1.1, p.1.2, Vector.ofFn p.2.1, Vector.ofFn p.2.2.1, p.2.2.2.1, p.2.2.2.2.1,
    p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩
  left_inv c := by
    obtain ⟨offsets, clamped, pR, pad, t, mask, r1, r2, Z, Δ⟩ := c
    show Kriterion.ArgoMAC.Scheme.Coins.mk offsets clamped (Vector.ofFn pR.get) (Vector.ofFn pad.get)
      t mask r1 r2 Z Δ = _
    rw [ofFn_get', ofFn_get']
  right_inv p := by
    obtain ⟨offsets, pR, pad, t, mask, r1, r2, Z, Δ⟩ := p
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
    · exact funext fun d => Vector.get_ofFn pR d
    · exact funext fun d => Vector.get_ofFn pad d

/-- The fixed-key indices that hide nothing. -/
abbrev RestIdx := {i : FixedIndex // i ∉ Set.range (hiddenIdx input)}

/-- **What F4's coins leave out**: the offsets, the `(ρ, τ)`s, the labels and `Δ`, the other
answers. -/
abbrev Outer := ClampedOffsets × (Fin digitCount → NonZeroBase × NonZeroBase) ×
  (Coord → Fin coordinateBitCount → Block) × (Coord → Block) × (RestIdx input → Block)

/-- **The coins' fields, the fixed-key answers and the masks are the rest and F4's coins.** -/
def regroup : CoinsParts × (FixedIndex → Block) × MaskVectors ≃ Outer input × JointCoins where
  toFun ω :=
    ((ω.1.1, fun d => ((ω.1.2.1 d).rho, (ω.1.2.1 d).tau), ω.1.2.2.2.2.2.2.2.1,
        ω.1.2.2.2.2.2.2.2.2, (splitAlong (hiddenIdx input) (hiddenIdx_injective input) ω.2.1).2),
      (fun d => ((maskSiteEquiv (maskCoordEquiv ω.2.2)).1 d,
          ((ω.1.2.1 d).x, (ω.1.2.1 d).y, (ω.1.2.1 d).z)),
        ((maskSiteEquiv (maskCoordEquiv ω.2.2)).2, ω.1.2.2.2.1,
          ⟨ω.1.2.2.2.2.1.value, ω.1.2.2.2.2.1.nonzero⟩,
          ω.1.2.2.2.2.2.1, ω.1.2.2.2.2.2.2.1),
        (fun ℓ s => ω.2.1 (hiddenIdx input (.inl (ℓ, s))),
          fun d => (ω.1.2.2.1 d, (ω.2.1 (hiddenIdx input (.inr (d, false))),
            ω.2.1 (hiddenIdx input (.inr (d, true))))))))
  invFun p :=
    ((p.1.1, fun d => ⟨(p.1.2.1 d).1, (p.1.2.1 d).2, (p.2.1 d).2.1, (p.2.1 d).2.2.1,
          (p.2.1 d).2.2.2⟩,
        fun d => (p.2.2.2.2 d).1, p.2.2.1.2.1, ⟨p.2.2.1.2.2.1.1, p.2.2.1.2.2.1.2⟩,
        p.2.2.1.2.2.2.1, p.2.2.1.2.2.2.2, p.1.2.2.1, p.1.2.2.2.1),
      (splitAlong (hiddenIdx input) (hiddenIdx_injective input)).symm
        (Sum.elim (fun q => p.2.2.2.1 q.1 q.2)
          (fun q => if q.2 then (p.2.2.2.2 q.1).2.2 else (p.2.2.2.2 q.1).2.1), p.1.2.2.2.2),
      maskCoordEquiv.symm (maskSiteEquiv.symm (fun d => (p.2.1 d).1, p.2.2.1.1)))
  left_inv ω := by
    obtain ⟨⟨offsets, pR, pad, t, mask, r1, r2, Z, Δ⟩, v, m⟩ := ω
    have hidden : (Sum.elim
        (fun q : Lane × Fin foldStepCount => v (hiddenIdx input (.inl (q.1, q.2))))
        (fun q : Fin digitCount × Bool => if q.2 then v (hiddenIdx input (.inr (q.1, true)))
          else v (hiddenIdx input (.inr (q.1, false))))) =
        (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).1 := by
      funext q
      rcases q with ⟨ℓ, s⟩ | ⟨d, b⟩
      · rfl
      · cases b <;> rfl
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · show (splitAlong (hiddenIdx input) (hiddenIdx_injective input)).symm
        (Sum.elim (fun q : Lane × Fin foldStepCount => v (hiddenIdx input (.inl (q.1, q.2))))
          (fun q : Fin digitCount × Bool => if q.2 then v (hiddenIdx input (.inr (q.1, true)))
            else v (hiddenIdx input (.inr (q.1, false)))),
         (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2) = v
      rw [hidden, Prod.mk.eta, Equiv.symm_apply_apply]
    · show maskCoordEquiv.symm (maskSiteEquiv.symm ((maskSiteEquiv (maskCoordEquiv m)).1,
        (maskSiteEquiv (maskCoordEquiv m)).2)) = m
      rw [Prod.mk.eta, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv p := by
    obtain ⟨⟨offsets, rho, Z, Δ, rest⟩, digits, ⟨cm, t, mask, r1, r2⟩, fold, gadget⟩ := p
    have masks : maskSiteEquiv (maskCoordEquiv (maskCoordEquiv.symm
        (maskSiteEquiv.symm (fun d => (digits d).1, cm)))) = (fun d => (digits d).1, cm) := by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine Prod.ext (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))))
      (Prod.ext (funext fun d => ?_) (Prod.ext (Prod.ext ?_ rfl) (Prod.ext
        (funext fun ℓ => funext fun s => ?_) (funext fun d => ?_))))
    · show ((splitAlong (hiddenIdx input) (hiddenIdx_injective input))
        ((splitAlong (hiddenIdx input) (hiddenIdx_injective input)).symm (_, rest))).2 = rest
      rw [Equiv.apply_symm_apply]
    · exact Prod.ext (congrFun (congrArg Prod.fst masks) d) rfl
    · exact congrArg Prod.snd masks
    · exact splitAlong_symm_image (hiddenIdx input) (hiddenIdx_injective input) _ _ (.inl (ℓ, s))
    · exact Prod.ext rfl (Prod.ext
        (splitAlong_symm_image (hiddenIdx input) (hiddenIdx_injective input) _ _ (.inr (d, false)))
        (splitAlong_symm_image (hiddenIdx input) (hiddenIdx_injective input) _ _ (.inr (d, true))))

/-- The garbler's coins on a table, its fixed-key answers and the masks of its limbs. -/
abbrev Omega := Coins × (FixedIndex → Block) × MaskVectors

variable [GroupCertificate] (scalar : NonZeroScalar)

/-- The output keys of some coins' fields. -/
def coinKeys (parts : CoinsParts) : OutputKeys :=
  FieldMacToECMac.outputKeys construction scalar.value parts.1.1

/-- The swap fixes every view gate. -/
theorem indexSwap_view (keys : OutputKeys) (w : ViewIdx input) :
    indexSwap keys (viewIdx input w) = viewIdx input w := by
  obtain ⟨lane, chunk, step, entry, half, -, -, -, -, -, eq⟩ := w.2
  rw [show viewIdx input w = w.1 from rfl, eq]
  rfl

theorem coinKeys_coinsSplit (coins : Kriterion.ArgoMAC.Scheme.Coins) :
    coinKeys scalar (coinsSplit coins) =
      FieldMacToECMac.outputKeys construction scalar.value coins.offsets := rfl

/-- **The answers read through the index swap** of the coins' keys (an involution). -/
def twist : CoinsParts × (FixedIndex → Block) × MaskVectors ≃
    CoinsParts × (FixedIndex → Block) × MaskVectors where
  toFun ω := (ω.1, ω.2.1 ∘ indexSwap (coinKeys scalar ω.1), ω.2.2)
  invFun ω := (ω.1, ω.2.1 ∘ indexSwap (coinKeys scalar ω.1), ω.2.2)
  left_inv ω := by
    obtain ⟨parts, v, m⟩ := ω
    refine Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl)
    show v (indexSwap _ (indexSwap _ i)) = v i
    rw [indexSwap_involutive]
  right_inv ω := by
    obtain ⟨parts, v, m⟩ := ω
    refine Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl)
    show v (indexSwap _ (indexSwap _ i)) = v i
    rw [indexSwap_involutive]

/-- **The garbler's randomness is the rest and F4's coins**, the answers read through the index
swap. -/
def omegaEquiv : Omega ≃ Outer input × JointCoins :=
  (coinsSplit.prodCongr (Equiv.refl _)).trans ((twist scalar).trans (regroup input))

end Omega

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
