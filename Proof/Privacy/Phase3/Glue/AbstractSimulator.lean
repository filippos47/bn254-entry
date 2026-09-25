/-
Phase 3 glue, step 3 (design note B §3, review B-review; note C T09; phase-4 brief A1 §4): **the
output-aware Plan B simulator at PMF level**, in the form the library's
`LazySimulatorProtocol.idealGame` consumes for its abstract half (`LazyIdeal.lean`: a pair of
kernels over the shared lazy oracle).

**Stage 1** makes no oracle call. It draws a `Stage1Source` -- every published field in source
form (the curve triple, the 91 row-constant records, the gadget bytes, the four fold-join vectors,
and the `52 × 642` scale joins as *canonical* field elements) together with the Lamport key
(508 label pairs) -- and publishes `publicValue` of it: the scale joins packed by the construction's
own `pack`, never a uniform `BitVec` word (design note B, F7). With every switch mask vector swapped
to uniform before the game starts (P1's `G0 → G0U`), this is the construction's published law.

**Stage 2** receives the selected input `u` and `f_k(u)`:

* `none` (invalid input): return the selected labels, no oracle call (§1.7);
* `some Q`: return the selected labels after the **opening** (A1 §4):
  1. run the honest evaluator's system A, the bridge hash (at `bridgeInput t`), the 508 whitening
     pads and system B on the lazy oracle (`openingQueriesM`), *skipping* the **362 designated
     hash queries** `hash (scaleInput pointX 0 j* i E*)`, `i < 362`, `j* = α₀ xor 1`
     (`designatedInput`): each is answered virtually by `(0, 0)` and its label `E*` is recorded
     (`runIntercept`, `DesignatedRecord`). The designated vector `Y*` of `(pointX, chunk 0, j*)`
     is therefore `sampleLane` of zeros, i.e. `0`, during the replay: the replay's `pointX`
     values are the designated-free `rest_e`, and the evaluator later sees
     `v_e = rest_e + κ · Y*[e]` with `κ = ι(j*) − ι(α₀) = ±1`;
  2. draw the 90 tail digit points exactly as the construction's garbler draws its mask points --
     the `free` offsets of a uniform coin (`coinOffsetsLaw`), so no group-order fact is needed --
     then the head clamp `D_0 = Q − β • H(tail)` (group law only; it is `Q + clampedFirst tail`),
     and the 91 lift randomiser pairs `(λ_d, t_d)`; the target rows are
     `W_d = lift(D_d, λ_d, t_d) = (λ_d² x, t_d² y, λ_d)` (`targetRows`);
  3. draw the designated vector's **91 free coordinates** (the non-collector `rowX_x7` of each
     digit, `FreeSite`) uniformly, install them in the replay's values
     (`freeFill`), and **solve the 273 collectors** `rowX_x9, rowY_cubic, rowZ_x9` against the
     evaluator's rows on those values (`freeRows`): `Y*[c] = κ · (W_d.c − R_d.c) · s_c`, where
     `s_c` inverts the collector's coefficient in its own row: `1` for `X` and `Z`, `(x · x)⁻¹`
     for the sign row, whose collector `rowY_cubic` rides on `x²` (`collectorScale`,
     `collectorTargets`);
     `Y*` is `solvedVector`;
  4. draw the designated switch's **362 hash answers** uniformly on the `sampleLane` fibre over
     `Y*` (`idealPreimage`; the machine draws `V = enc(Y*) + p^364·t`, `t` uniform on the fibre);
  5. **program** `hash (designatedInput j* i E*) := answer i` for `i < 362`, in order
     (`programRequests`, `programAll`, `LazyOracle.program (.hash _)`). Programming the hash
     oracle needs only a fresh *input*; a used input, or a limb the replay never asked, aborts.

The samplers are a parameter (`Samplers`), exactly as the baseline's abstract ideal
(`sharedStrictSourceDecision offlineLaw onlineLaw`) takes its sampler laws: `idealSamplers` are the
exact uniform laws; a machine realises bounded ones (rejection with a cutoff, `none` on failure).

**The designated sites.** The input selects `j*` among the four switches of chunk 0, so a stage-1
hash query can hit the designated inputs only at one of the `4 · 362` **candidate sites**
(`CandidateSite`: limb × chunk-0 switch) at the label `E*`; the candidate inputs
`candidateIndex site label` are pairwise distinct over (site, label) (`candidateIndex_injective`,
from `PlanB.scaleInput_injective`), so each stage-1 query is charged to one candidate site only.

**The interface P2's machine must match** is `MachineLaw` at the end of this file.
-/

import Construction.PGS.Encoding
import Proof.Privacy.Phase3.Glue.LazyIdeal
import Proof.Privacy.Phase3.Basic

namespace Kriterion.ArgoMAC.Phase3.Glue

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Scheme (Coins Oracle)

noncomputable section

/-! ### Stage 1: the published value in source form -/

/-- Every published field in source form, and the Lamport key. -/
structure Stage1Source where
  /-- The curve-membership constants. -/
  curve : BaseField × BaseField × BaseField
  /-- The three row constants of each digit. -/
  rows : Vector RowGamma digitCount
  /-- The gadget bytes. -/
  exception : Vector Exception.Entry digitCount
  /-- System A's fold joins, `x` lane. -/
  curveXHot : Vector Block foldStepCount
  /-- System A's fold joins, `y` lane. -/
  curveYHot : Vector Block foldStepCount
  /-- System B's fold joins, `x` lane. -/
  pointXHot : Vector Block foldStepCount
  /-- System B's fold joins, `y` lane. -/
  pointYHot : Vector Block foldStepCount
  /-- The scale joins of every chunk, as canonical field elements. -/
  joins : Fin chunkCount → Fin elementCount → BaseField
  /-- The 508 Lamport label pairs; stage 2 selects one of each. -/
  key : InputMacKey

/-- The published value of a stage-1 source: the scale joins are packed by `pack`. -/
def Stage1Source.publicValue (source : Stage1Source) : Public where
  curve := source.curve
  rows := source.rows
  exception := source.exception
  curveXHot := source.curveXHot
  curveYHot := source.curveYHot
  pointXHot := source.pointXHot
  pointYHot := source.pointYHot
  scale := Vector.ofFn fun chunk => pack (source.joins chunk)

/-! ### Finiteness (no cardinality is computed) -/

/-- A vector is determined by its entries. -/
local instance vectorFinite {α : Type} [Finite α] {count : Nat} : Finite (Vector α count) :=
  Finite.of_injective (fun values : Vector α count => fun index : Fin count => values[index])
    (by
      intro first second equal
      apply Vector.ext
      intro index bound
      exact congrFun equal ⟨index, bound⟩)

instance rowGammaFinite : Finite RowGamma :=
  Finite.of_injective (fun row : RowGamma => (row.gX, row.gY, row.gZ)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance bitAdaptorKeyFinite : Finite BitAdaptor.Key :=
  Finite.of_injective (fun key : BitAdaptor.Key => (key.falseLabel, key.trueLabel)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance inputMacKeyFinite : Finite InputMacKey :=
  Finite.of_injective (fun key : InputMacKey => (key.x, key.y)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance nonZeroScalarFinite : Finite NonZeroScalar :=
  Finite.of_injective (fun value : NonZeroScalar => value.value) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance stage1SourceFinite : Finite Stage1Source :=
  Finite.of_injective (fun source : Stage1Source => (source.curve, source.rows, source.exception,
      source.curveXHot, source.curveYHot, source.pointXHot, source.pointYHot, source.joins,
      source.key)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

noncomputable instance stage1SourceFintype : Fintype Stage1Source := Fintype.ofFinite _

noncomputable instance nonZeroScalarFintype : Fintype NonZeroScalar := Fintype.ofFinite _

noncomputable instance nonZeroBaseFintype : Fintype NonZeroBase := Fintype.ofFinite _

instance stage1SourceNonempty : Nonempty Stage1Source :=
  ⟨{ curve := (0, 0, 0)
     rows := Vector.replicate _ ⟨0, 0, 0⟩
     exception := Vector.replicate _ (Vector.replicate _ 0)
     curveXHot := Vector.replicate _ 0
     curveYHot := Vector.replicate _ 0
     pointXHot := Vector.replicate _ 0
     pointYHot := Vector.replicate _ 0
     joins := fun _ _ => 0
     key := ⟨Vector.replicate _ ⟨0, 0⟩, Vector.replicate _ ⟨0, 0⟩⟩ }⟩

/-- The scalar modulus exceeds one. -/
instance scalarModulusFact : Fact (1 < scalarFieldModulus) := ⟨by unfold scalarFieldModulus; norm_num⟩

/-- The base modulus exceeds one. -/
instance baseModulusFact : Fact (1 < baseFieldModulus) := ⟨by unfold baseFieldModulus; norm_num⟩

instance nonZeroScalarNonempty : Nonempty NonZeroScalar := ⟨⟨1, one_ne_zero⟩⟩

instance nonZeroBaseNonempty : Nonempty NonZeroBase := ⟨⟨1, one_ne_zero⟩⟩

/-! ### The designated vector's coordinates

The designated vector `Y*` is one `pointX` switch-mask vector, `364 = 91 · 4` coordinates. Per
digit, the three **collectors** `rowX_x9, rowY_cubic, rowZ_x9` (coefficients `1`, `x²`, `1` in
their own rows) are solved from the target rows; the one **free** coordinate `rowX_x7` is
drawn. -/

/-- The three collectors of a digit, one per row: `rowX_x9`, `rowY_cubic`, `rowZ_x9`. -/
def collectorElement : Fin 3 → XElement := ![.rowX_x9, .rowY_cubic, .rowZ_x9]

/-- The free (non-collector) element of a digit: `rowX_x7`. -/
def freeElement : Fin 1 → XElement := ![.rowX_x7]

/-- The three collectors are distinct elements. -/
theorem collectorElement_injective : Function.Injective collectorElement := by decide

/-- The free element map is injective (it has one point). -/
theorem freeElement_injective : Function.Injective freeElement :=
  fun first second _ => Subsingleton.elim first second

/-- A free coordinate of the designated vector: a digit and its free element. -/
abbrev FreeSite := Fin digitCount × Fin 1

/-- The x-type element in each slot of a digit (the inverse of `XElement.slot`). -/
def slotElement : Fin xSlotsPerDigit → XElement :=
  ![.rowX_x7, .rowX_x9, .rowY_cubic, .rowZ_x9]

theorem slotElement_slot (element : XElement) : slotElement element.slot = element := by
  cases element <;> rfl

theorem slot_slotElement (slot : Fin xSlotsPerDigit) : (slotElement slot).slot = slot := by
  fin_cases slot <;> rfl

/-- The digit of a `pointX` element. -/
def elementDigit (element : Fin pointElementCountX) : Fin digitCount :=
  ⟨element.val / xSlotsPerDigit, by
    have bound := element.isLt
    unfold pointElementCountX at bound
    unfold digitCount xSlotsPerDigit
    omega⟩

/-- The x-type element (the slot inside its digit) of a `pointX` element. -/
def elementKind (element : Fin pointElementCountX) : XElement :=
  slotElement ⟨element.val % xSlotsPerDigit, Nat.mod_lt _ (by decide)⟩

theorem elementDigit_xElementIndex (digit : Fin digitCount) (element : XElement) :
    elementDigit (xElementIndex digit element) = digit := by
  have slot := element.slot.isLt
  apply Fin.ext
  simp only [elementDigit, xElementIndex]
  unfold xSlotsPerDigit at slot ⊢
  omega

theorem elementKind_xElementIndex (digit : Fin digitCount) (element : XElement) :
    elementKind (xElementIndex digit element) = element := by
  have slot := element.slot.isLt
  have same : (⟨(xElementIndex digit element).val % xSlotsPerDigit, Nat.mod_lt _ (by decide)⟩ :
      Fin xSlotsPerDigit) = element.slot := by
    apply Fin.ext
    simp only [xElementIndex]
    unfold xSlotsPerDigit at slot ⊢
    omega
  rw [elementKind, same, slotElement_slot]

/-- Every `pointX` element is its digit's element of its kind: `xElementIndex` is a bijection
`Fin digitCount × XElement ≃ Fin pointElementCountX`. -/
theorem xElementIndex_elementDigit_elementKind (element : Fin pointElementCountX) :
    xElementIndex (elementDigit element) (elementKind element) = element := by
  apply Fin.ext
  simp only [xElementIndex, elementDigit, elementKind, slot_slotElement]
  exact Nat.div_add_mod element.val xSlotsPerDigit

/-- **The designated vector** from its free coordinates and its collector values: coordinate
`xElementIndex d e` is `free (d, ·)` at a free element and `collectors (d, ·)` at a collector. -/
def designatedVector (free : FreeSite → BaseField)
    (collectors : Fin digitCount × Fin 3 → BaseField) (element : Fin pointElementCountX) :
    BaseField :=
  match elementKind element with
  | .rowX_x7 => free (elementDigit element, 0)
  | .rowX_x9 => collectors (elementDigit element, 0)
  | .rowY_cubic => collectors (elementDigit element, 1)
  | .rowZ_x9 => collectors (elementDigit element, 2)

/-- The designated vector at a collector is the collector's value. -/
theorem designatedVector_collector (free : FreeSite → BaseField)
    (collectors : Fin digitCount × Fin 3 → BaseField) (digit : Fin digitCount)
    (collector : Fin 3) :
    designatedVector free collectors (xElementIndex digit (collectorElement collector)) =
      collectors (digit, collector) := by
  unfold designatedVector
  rw [elementKind_xElementIndex, elementDigit_xElementIndex]
  fin_cases collector <;> rfl

/-- The designated vector at a free element is the free coordinate. -/
theorem designatedVector_free (free : FreeSite → BaseField)
    (collectors : Fin digitCount × Fin 3 → BaseField) (digit : Fin digitCount) (slot : Fin 1) :
    designatedVector free collectors (xElementIndex digit (freeElement slot)) =
      free (digit, slot) := by
  unfold designatedVector
  rw [elementKind_xElementIndex, elementDigit_xElementIndex]
  fin_cases slot <;> rfl

/-! ### The samplers -/

/-- The designated switch's `362` hash answers, one per limb. -/
abbrev DesignatedLimbs := Fin (limbCount .pointX) → Block × Block

/-- `362` limbs carry the `364` digits of the designated vector (`p^364 ≤ 2^(254·364)`). -/
theorem designated_fits : 254 * pointElementCountX ≤ 256 * limbCount .pointX := by decide

/-- Every designated vector has a preimage among the `362` hash answers. -/
theorem sampleLane_designated_surjective :
    Function.Surjective (sampleLane pointElementCountX (limbCount .pointX)) :=
  sampleLane_surjective_of_le _ _ designated_fits

/-- **A uniform preimage of the designated vector**: the `362` hash answers drawn uniformly on the
`sampleLane` fibre over the vector. It is the conditional law of `362` fresh uniform answers given
their vector (`Security.Phase3.uniform_eq_bind_fibreLaw`). It is, by `rfl`, the mask swap's
per-site fibre law `siteFibreLaw .pointX`, the law of the designated site's limbs given its vector
in the swapped tape (`MaskSwap.fibreLaw_masksOf_eq`: given all the vectors, the sites' limbs are
independent, each uniform on its own fibre). -/
def idealPreimage (vector : Fin pointElementCountX → BaseField) : PMF DesignatedLimbs :=
  Security.Phase3.fibreLaw (sampleLane pointElementCountX (limbCount .pointX))
    sampleLane_designated_surjective vector

/-- The five sampler laws of the simulator; `none` is a sampler abort. -/
structure Samplers where
  /-- Stage 1: the published source and the Lamport key. -/
  source : PMF (Option Stage1Source)
  /-- The 90 tail digit points, as the construction's free offsets. -/
  tail : PMF (Option (Vector FieldMacToECMac.AffineOffset 90))
  /-- The 91 lift randomiser pairs `(λ_d, t_d) ∈ (F_p^*)²`: `λ_d` scales the `X` and `Z` rows,
  `t_d` the sign row. -/
  lift : PMF (Option (Fin digitCount → NonZeroBase × NonZeroBase))
  /-- The designated vector's 91 free coordinates. -/
  free : PMF (Option (FreeSite → BaseField))
  /-- The designated switch's 362 hash answers, given the designated vector. -/
  preimage : (Fin pointElementCountX → BaseField) → PMF (Option DesignatedLimbs)

/-- **The construction's law of its mask points**: the offsets of a uniform coin. The garbler reads
its 91 `K` points from exactly these offsets (`FieldMacToECMac.outputKeys … coins.offsets`). -/
def coinOffsetsLaw : PMF FieldMacToECMac.SuccessfulOffsets :=
  letI : Fintype Coins := Fintype.ofFinite Coins
  (PMF.uniformOfFintype Coins).map Coins.offsets

/-- The exact samplers of the abstract simulator: uniform sources, lifts and free coordinates, the
uniform fibre preimage, and the tail points drawn by the construction's own offset law. -/
def idealSamplers : Samplers where
  source := (PMF.uniformOfFintype Stage1Source).map some
  tail := coinOffsetsLaw.map fun offsets => some offsets.free
  lift := (PMF.uniformOfFintype (Fin digitCount → NonZeroBase × NonZeroBase)).map some
  free := (PMF.uniformOfFintype (FreeSite → BaseField)).map some
  preimage vector := (idealPreimage vector).map some

/-- Independent draws from a finite family of abort-or-value samplers; any abort aborts. -/
def optionProduct {α : Type} : (count : Nat) → (Fin count → PMF (Option α)) →
    PMF (Option (Fin count → α))
  | 0, _ => PMF.pure (some Fin.elim0)
  | count + 1, sample => (sample 0).bind fun head => match head with
    | none => PMF.pure none
    | some head => (optionProduct count fun index => sample index.succ).map
        (Option.map fun tail => Fin.cons (α := fun _ => α) head tail)

/-! ### The designated switch -/

/-- Chunk `0`. -/
def chunkZero : Fin chunkCount := ⟨0, chunkCount_pos⟩

/-- Chunk `0` has four switches (it is `firstChunkBits = 2` wide). -/
theorem twoPow_chunkWidth_chunkZero : 2 ^ chunkWidth chunkZero = 4 := by decide

/-- The active switch `α₀` of chunk `0` of lane `pointX` (the low bits of `x`). -/
def activeSwitch (bits : BitInput) : Fin (2 ^ chunkWidth chunkZero) :=
  chunkOf (Pipeline.coordBits bits .x) chunkZero

/-- The designated switch `j* = α₀ xor 1`: inactive, queried by the evaluator, and with an
inactive last-step fold parent (B-review (2)). -/
def designatedSwitch (bits : BitInput) : Fin (2 ^ chunkWidth chunkZero) :=
  ⟨(activeSwitch bits).val ^^^ 1, by
    have := chunkWidth_pos chunkZero
    exact Nat.xor_lt_two_pow (activeSwitch bits).isLt (Nat.one_lt_two_pow (by omega))⟩

/-- `κ = ι(j*) − ι(α₀)`, the designated mask's coefficient in the evaluator's free fold (`±1`). -/
def kappa (bits : BitInput) : BaseField :=
  iota _ (designatedSwitch bits) - iota _ (activeSwitch bits)

/-- The row coordinate each collector controls. -/
def collectorComponent : Fin 3 → FieldMacToECMac.HomogeneousValue → BaseField :=
  ![fun value => value.x, fun value => value.y, fun value => value.z]

/-! ### The designated hash inputs and the candidate sites -/

/-- The label of a hash input: its low 128 bits. For a scale input it is the one-hot label the
input was formed with (`scaleLabel_scaleInput`). -/
def scaleLabel (input : BaseField) : Block := BitVec.ofNat 128 input.val

/-- A scale input's label is its low 128 bits. -/
theorem scaleLabel_scaleInput (lane : Lane) (chunk : Fin chunkCount) (switch limb : Nat)
    (label : Block) : scaleLabel (scaleInput lane chunk switch limb label) = label := by
  apply BitVec.eq_of_toNat_eq
  rw [scaleLabel, BitVec.toNat_ofNat, scaleInput_val, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt label.isLt]

/-- **The designated hash input** of limb `i` at label `E*`: `scaleInput pointX 0 j* i E*`. -/
def designatedInput (bits : BitInput) (limb : Fin (limbCount .pointX)) (label : Block) :
    BaseField :=
  scaleInput .pointX chunkZero (designatedSwitch bits).val limb.val label

/-- A designated input's label is its label. -/
theorem scaleLabel_designatedInput (bits : BitInput) (limb : Fin (limbCount .pointX))
    (label : Block) : scaleLabel (designatedInput bits limb label) = label :=
  scaleLabel_scaleInput _ _ _ _ _

/-- A hash input is **designated** if it is the designated input of some limb at its own label. -/
def IsDesignated (bits : BitInput) (input : BaseField) : Prop :=
  ∃ limb : Fin (limbCount .pointX), designatedInput bits limb (scaleLabel input) = input

instance isDesignatedDecidable (bits : BitInput) : DecidablePred (IsDesignated bits) :=
  fun input => by unfold IsDesignated; infer_instance

/-- A hash input is designated iff it is the designated input of some limb at some label. -/
theorem isDesignated_iff (bits : BitInput) (input : BaseField) :
    IsDesignated bits input ↔ ∃ limb label, designatedInput bits limb label = input := by
  constructor
  · rintro ⟨limb, same⟩
    exact ⟨limb, _, same⟩
  · rintro ⟨limb, label, rfl⟩
    exact ⟨limb, by rw [scaleLabel_designatedInput]⟩

/-- Every designated input is designated. -/
theorem isDesignated_designatedInput (bits : BitInput) (limb : Fin (limbCount .pointX))
    (label : Block) : IsDesignated bits (designatedInput bits limb label) :=
  (isDesignated_iff bits _).mpr ⟨limb, label, rfl⟩

/-- A candidate designated site: a limb of the designated vector and a candidate switch of chunk
`0`. The input selects one switch (`j* = α₀ xor 1` ranges over all four switches). -/
abbrev CandidateSite := Fin (limbCount .pointX) × Fin (2 ^ chunkWidth chunkZero)

/-- The hash input of a candidate site at a label: the site's limb of the `pointX` chunk-0
vector of the site's switch. -/
def candidateIndex (site : CandidateSite) (label : Block) : BaseField :=
  scaleInput .pointX chunkZero site.2.val site.1.val label

/-- **The candidate inputs are pairwise distinct** over (site, label) (`scaleInput_injective`): a
hash input names its switch, limb and label, so a stage-1 hash query is charged to one candidate
site only, and there only through the label `E*`. -/
theorem candidateIndex_injective :
    Function.Injective fun pair : CandidateSite × Block => candidateIndex pair.1 pair.2 := by
  rintro ⟨⟨limb, switch⟩, label⟩ ⟨⟨limb', switch'⟩, label'⟩ same
  simp only [candidateIndex] at same
  have widthBound : 2 ^ chunkWidth chunkZero ≤ 2 ^ chunkBits :=
    Nat.pow_le_pow_right (by norm_num) (chunkWidth_le chunkZero)
  obtain ⟨-, -, sameSwitch, sameLimb, sameLabel⟩ := scaleInput_injective
    (lt_of_lt_of_le switch.isLt widthBound) (lt_of_lt_of_le switch'.isLt widthBound)
    (lt_trans limb.isLt (limbCount_lt _)) (lt_trans limb'.isLt (limbCount_lt _)) same
  rw [Fin.ext sameLimb, Fin.ext sameSwitch, sameLabel]

/-- The designated inputs of one input are pairwise distinct over (limb, label). -/
theorem designatedInput_injective (bits : BitInput) :
    Function.Injective fun pair : Fin (limbCount .pointX) × Block =>
      designatedInput bits pair.1 pair.2 := by
  rintro ⟨limb, label⟩ ⟨limb', label'⟩ same
  have pair := candidateIndex_injective (a₁ := ((limb, designatedSwitch bits), label))
    (a₂ := ((limb', designatedSwitch bits), label')) same
  simp only [Prod.mk.injEq] at pair
  rw [pair.1.1, pair.2]

/-! ### The honest queries with the designated ones skipped -/

/-- The labels `E*` recorded so far, one per limb of the designated vector. -/
abbrev DesignatedRecord := Fin (limbCount .pointX) → Option Block

/-- Nothing recorded. -/
def noRecord : DesignatedRecord := fun _ => none

/-- A designated hash query is answered virtually by `(0, 0)` (the limb reads `0`), without
touching the oracle; every other query goes to the lazy oracle. -/
def interceptAnswer (bits : BitInput) :
    (request : PublicQuery FixedIndex EncPRF.PermutationIndex) → Option request.Answer
  | .fixedForward _ _ => none
  | .fixedInverse _ _ => none
  | .encForward _ _ => none
  | .encInverse _ _ => none
  | .hash input => if IsDesignated bits input then some (0, 0) else none

/-- The designated labels `E*` seen so far: a designated hash query records its label at its
limb. -/
def recordAfter (bits : BitInput) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (record : DesignatedRecord) : DesignatedRecord :=
  match request with
  | .hash input => fun limb =>
      if designatedInput bits limb (scaleLabel input) = input then some (scaleLabel input)
      else record limb
  | _ => record

/-- A designated query records its label at its limb. -/
theorem recordAfter_designatedInput (bits : BitInput) (limb : Fin (limbCount .pointX))
    (label : Block) (record : DesignatedRecord) :
    recordAfter bits (.hash (designatedInput bits limb label)) record =
      Function.update record limb (some label) := by
  funext other
  simp only [recordAfter, designatedInput, scaleLabel_scaleInput]
  by_cases same : other = limb
  · subst same
    simp
  · rw [if_neg, Function.update_of_ne same]
    intro equal
    exact same (congrArg Prod.fst (designatedInput_injective bits (a₁ := (other, label))
      (a₂ := (limb, label)) equal))

/-- A non-designated hash query records nothing. -/
theorem recordAfter_of_not_isDesignated (bits : BitInput) (input : BaseField)
    (record : DesignatedRecord) (notDesignated : ¬ IsDesignated bits input) :
    recordAfter bits (.hash input) record = record := by
  funext limb
  simp only [recordAfter]
  rw [if_neg fun same => notDesignated ⟨limb, same⟩]

/-- Run a Plan B query computation on the lazy oracle, skipping the designated queries and
recording their labels. -/
def runIntercept [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex] {α : Type}
    (bits : BitInput) :
    FreeQuery Programs.Spec α → LazyOracle.State FixedIndex EncPRF.PermutationIndex →
      DesignatedRecord →
        PMF (α × LazyOracle.State FixedIndex EncPRF.PermutationIndex × DesignatedRecord)
  | .pure value, oracle, record => PMF.pure (value, oracle, record)
  | .query request next, oracle, record =>
      match interceptAnswer bits request with
      | some answer => runIntercept bits (next answer) oracle (recordAfter bits request record)
      | none => (LazyOracle.query request oracle).bind fun answer =>
          runIntercept bits (next answer.1) answer.2 record

/-- The bit-`false` whitening pads only: `508` EncPRF queries (design note B §1.6). -/
def whitePadsM (keys : WhiteningKeys) :
    Programs.M (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :=
  FreeQuery.vector coordinateBitCount (fun index => Programs.padM keys .x index false) >>= fun xs =>
    FreeQuery.vector coordinateBitCount (fun index => Programs.padM keys .y index false) >>= fun ys =>
      pure fun which index => match which with
        | .x => (xs.get index, xs.get index)
        | .y => (ys.get index, ys.get index)

/-- The simulator's honest evaluation, in the evaluator's order: system A, the bridge hash (at
`bridgeInput`, as `Programs.onCurveM` asks it), the whitening pads, system B. It returns system B's
two lane vectors. -/
def openingQueriesM [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac) :
    Programs.M ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) :=
  Programs.evalLaneM .curveX table.curveXHot
      (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x) >>= fun curveX =>
    Programs.evalLaneM .curveY table.curveYHot
        (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
        (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y) >>= fun curveY =>
      Programs.askHash (bridgeInput (CurveMembership.evaluate table.curve bits.toAffine
          (Pipeline.curveValues curveX curveY))) >>= fun hashed =>
        whitePadsM ⟨hashed.1, hashed.2⟩ >>= fun pads =>
          Programs.evalLaneM .pointX table.pointXHot
              (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
              (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)
            >>= fun pointX =>
          Programs.evalLaneM .pointY table.pointYHot
              (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
              (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
            >>= fun pointY =>
          pure (pointX, pointY)

/-! ### The output kernel: target rows from `f_k(u)` -/

/-- The BN254 point `(1, 2)`. Not used by the simulator: the tail points are the construction's
offsets, so no generator (and no `#Point = r` fact) is needed. -/
def generator [FieldCertificate] : Point := (decodePoint ⟨1, 2⟩).getD 0

/-- The sign-row lift `(λ²X, t²Y, λ)`, and `(λ², 0, 0)` at the identity (the sign row vanishes
at `T = -K`, where the tangent at `-K` passes). -/
def liftRow [FieldCertificate] (point : Point) (scale signScale : BaseField) :
    FieldMacToECMac.HomogeneousValue :=
  match point with
  | .zero => ⟨scale ^ 2, 0, 0⟩
  | .some (x := x) (y := y) _ => ⟨scale ^ 2 * x, signScale ^ 2 * y, scale⟩

/-- The 91 digit points: the 90 tail points are the given offsets' points, and the head is the
clamp `Q − β • H(tail)`, stated with the group law only, so that `pointHorner β (D_0 :: tail) = Q`
(design note B §1.2). -/
def digitPoints [FieldCertificate] [GroupCertificate] (target : Point)
    (tail : Vector FieldMacToECMac.AffineOffset 90) (digit : Fin digitCount) : Point :=
  if head : digit.val = 0 then target - radix • pointHorner radix (FieldMacToECMac.freeOffsetPoints tail)
  else (tail.get ⟨digit.val - 1, by
    have bound := digit.isLt
    unfold digitCount at bound
    omega⟩).point

/-- The head digit point is the target plus the construction's own clamp of the tail. -/
theorem digitPoints_head [FieldCertificate] [GroupCertificate] (target : Point)
    (tail : Vector FieldMacToECMac.AffineOffset 90) :
    digitPoints target tail ⟨0, by unfold digitCount; omega⟩ =
      target + FieldMacToECMac.clampedFirst tail := by
  simp only [digitPoints, dif_pos, FieldMacToECMac.clampedFirst, sub_eq_add_neg]

/-- The target rows `W_d = lift(D_d, λ_d, t_d)`. -/
def targetRows [FieldCertificate] [GroupCertificate] (target : Point)
    (tail : Vector FieldMacToECMac.AffineOffset 90)
    (lift : Fin digitCount → NonZeroBase × NonZeroBase)
    (digit : Fin digitCount) : FieldMacToECMac.HomogeneousValue :=
  liftRow (digitPoints target tail digit) (lift digit).1.value (lift digit).2.value

/-! ### The designated vector: free coordinates, collector solve -/

/-- The inverse of a collector's coefficient in its row: `1` for `X` and `Z`, `(x · x)⁻¹` for `Y`,
whose collector `rowY_cubic` enters the row with coefficient `x²` (the machine's
`Opening.finishScaled` multiplies by the same `(x · x)⁻¹`). -/
def collectorScale (bits : BitInput) (collector : Fin 3) : BaseField :=
  if collector.val = 1 then (bits.toAffine.x * bits.toAffine.x)⁻¹ else 1

/-- The designated value each collector needs: `y* = κ · (W_d.c − R_d.c) · s_c`, where `R_d` is
the evaluator's row with the collectors' designated masks at `0` and `s_c = collectorScale`. -/
def collectorTargets (bits : BitInput)
    (evalRows : Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount)
    (targets : Fin digitCount → FieldMacToECMac.HomogeneousValue) :
    Fin digitCount × Fin 3 → BaseField :=
  fun site => kappa bits *
    (collectorComponent site.2 (targets site.1) - collectorComponent site.2 (evalRows.get site.1)) *
      collectorScale bits site.2

/-- The replay's `pointX` values with the designated vector's free coordinates installed: the
evaluator sees `rest_e + κ · Y*[e]`, here with `Y*` at its free coordinates and `0` at the
collectors. -/
def freeFill (bits : BitInput) (pointX : Fin pointElementCountX → BaseField)
    (free : FreeSite → BaseField) : Fin pointElementCountX → BaseField :=
  fun element => pointX element + kappa bits * designatedVector free 0 element

/-- The evaluator's rows on the free-filled values (collectors designated-free). -/
def freeRows (table : Public) (bits : BitInput) (pointX : Fin pointElementCountX → BaseField)
    (pointY : Fin pointElementCountY → BaseField) (free : FreeSite → BaseField) :
    Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount :=
  FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable table)
    (Pipeline.digitValues (freeFill bits pointX free) pointY) bits.toAffine

/-- **The solved designated vector `Y*`**: the free coordinates as drawn, each collector solved
against the free-filled rows (`collectorTargets`). -/
def solvedVector (table : Public) (bits : BitInput) (pointX : Fin pointElementCountX → BaseField)
    (pointY : Fin pointElementCountY → BaseField) (free : FreeSite → BaseField)
    (targets : Fin digitCount → FieldMacToECMac.HomogeneousValue) :
    Fin pointElementCountX → BaseField :=
  designatedVector free (collectorTargets bits (freeRows table bits pointX pointY free) targets)

/-- **The designated draws after the target rows**: the 91 free coordinates, the collector
solve, and the 362 hash answers of the solved vector. -/
def designatedLimbs (samplers : Samplers) (table : Public) (bits : BitInput)
    (pointX : Fin pointElementCountX → BaseField) (pointY : Fin pointElementCountY → BaseField)
    (targets : Fin digitCount → FieldMacToECMac.HomogeneousValue) :
    PMF (Option DesignatedLimbs) :=
  samplers.free.bind fun free => match free with
  | none => PMF.pure none
  | some free => samplers.preimage (solvedVector table bits pointX pointY free targets)

/-- **The opening's draws between the replay and the programs**: the tail points and the lifts
(the target rows), then `designatedLimbs`. This is the abstract counterpart of the machine's
oracle-free opening. -/
def openingLimbs [FieldCertificate] [GroupCertificate] (samplers : Samplers) (table : Public)
    (bits : BitInput) (target : Point) (pointX : Fin pointElementCountX → BaseField)
    (pointY : Fin pointElementCountY → BaseField) : PMF (Option DesignatedLimbs) :=
  samplers.tail.bind fun tail => match tail with
  | none => PMF.pure none
  | some tail => samplers.lift.bind fun lift => match lift with
    | none => PMF.pure none
    | some lift => designatedLimbs samplers table bits pointX pointY (targetRows target tail lift)

/-! ### The programs -/

/-- The `362` program requests, limb by limb: the designated input at the limb's recorded label
(`none` if the replay never asked that limb) and the limb's drawn hash answer. -/
def programRequests (bits : BitInput) (record : DesignatedRecord) (answers : DesignatedLimbs) :
    List (Option BaseField × (Block × Block)) :=
  (List.finRange (limbCount .pointX)).map fun limb =>
    ((record limb).map (designatedInput bits limb), answers limb)

/-- The programmed inputs are pairwise distinct (`designatedInput_injective`). -/
theorem programRequests_inputs_nodup (bits : BitInput) (record : DesignatedRecord)
    (answers : DesignatedLimbs) :
    ((programRequests bits record answers).filterMap Prod.fst).Nodup := by
  unfold programRequests
  rw [List.filterMap_map]
  refine List.Nodup.filterMap ?_ (List.nodup_finRange _)
  intro limb limb' input first second
  simp only [Function.comp_apply, Option.mem_def, Option.map_eq_some_iff] at first second
  obtain ⟨label, -, rfl⟩ := first
  obtain ⟨label', -, same⟩ := second
  exact (congrArg Prod.fst (designatedInput_injective bits (a₁ := (limb', label'))
    (a₂ := (limb, label)) same)).symm

/-- Program every request `hash input := answer`; a missing input or a failed program (an input
already stored) aborts. -/
def programAll [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex] :
    List (Option BaseField × (Block × Block)) →
      LazyOracle.State FixedIndex EncPRF.PermutationIndex →
        Option (LazyOracle.State FixedIndex EncPRF.PermutationIndex)
  | [], oracle => some oracle
  | (input, answer) :: rest, oracle => match input with
    | none => none
    | some input => (LazyOracle.program (.hash input) answer oracle).bind (programAll rest)

/-- **The opening** of a valid input to `target = f_k(u)` (steps 1–5 of the header). -/
def opening [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (samplers : Samplers) (table : Public)
    (input : AffineInput) (labels : LamportSignature) (target : Point)
    (oracle : LazyOracle.State FixedIndex EncPRF.PermutationIndex) :
    PMF (Option (LazyOracle.State FixedIndex EncPRF.PermutationIndex)) :=
  let restored := Lamport.restore input labels
  (runIntercept restored.input (openingQueriesM table restored.input restored.inputMac) oracle
      noRecord).bind fun ran =>
    (openingLimbs samplers table restored.input target ran.1.1 ran.1.2).bind fun answers =>
      match answers with
      | none => PMF.pure none
      | some answers =>
          PMF.pure (programAll (programRequests restored.input ran.2.2 answers) ran.2.1)

/-- **The output-aware Plan B abstract simulator.** -/
def planBAbstractSimulator [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (samplers : Samplers) :
    LazyAbstractSimulator FixedIndex EncPRF.PermutationIndex Public where
  State := Stage1Source
  stage1 _ oracle := samplers.source.map (Option.map fun source => (source.publicValue, source, oracle))
  stage2 source input output oracle :=
    let labels := Lamport.selectedLabels (source.key.encode (BitInput.ofAffine input))
    match output with
    | none => PMF.pure (some (labels, oracle))
    | some target => (opening samplers source.publicValue input labels target oracle).map
        (Option.map fun updated => (labels, updated))

/-- **`I`, the abstract ideal game** of the Plan B simulator (design note B §3, `absIdeal`). -/
def planBIdealGame [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] {Aux : Type} (samplers : Samplers)
    (adversary : PlanBAdversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) : PMF Bool :=
  abstractIdealGame Scheme.scheme (planBAbstractSimulator samplers) adversary parameter scalar
    auxiliary

/-! ### The chain games at the `Solution` instances -/

/-- A game of the Plan B chain: one for every certificate pair and every choice of the index
instances, against every `Unit`-auxiliary Plan B adversary. The proof-only hybrids of P1 are
values of this type. -/
abbrev HybridGame : Type 1 :=
  ∀ [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
    [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex],
    PlanBAdversary Unit → Nat → NonZeroScalar → PMF Bool

/-- A chain game at the instances `Solution.adaptivePrivacy` installs: `Fintype.ofFinite` and
`Classical.decEq` on both index types. -/
def atSolution (game : HybridGame) (field : FieldCertificate) (group : @GroupCertificate field) :
    PlanBAdversary Unit → Nat → NonZeroScalar → PMF Bool :=
  @game field group (Fintype.ofFinite FixedIndex) (Fintype.ofFinite EncPRF.PermutationIndex)
    (Classical.decEq FixedIndex) (Classical.decEq EncPRF.PermutationIndex)

/-- `I`: the abstract ideal game of the exact samplers, as a chain game. -/
def idealHybrid : HybridGame := fun adversary parameter scalar =>
  planBIdealGame idealSamplers adversary parameter scalar ()

/-- `M`: the library's ideal game with a closed machine, as a chain game. The byte count is the
Plan B ciphertext size, `1,082,820` (`PlanB.Wire.ciphertextSize`). -/
def machineHybrid (simulator : BoundedMachine.Simulator) : HybridGame :=
  fun adversary parameter scalar =>
    LazySimulatorProtocol.idealGame Scheme.scheme Wire.encoding 1082820 simulator adversary
      parameter scalar ()

/-! ### The interface P2's machine must match -/

/-- The machine's sampling-cutoff allowance, `I → M`. The planned samplers cut off far below it:
the designated preimage's `t` sampler (80 attempts, each rejecting with mass `≤ 3/10`) aborts with
mass `≤ 2^-138`, the source, tail, lift and 91 free-coordinate field samplers with far less. The
allowance is relaxed to `2^-128`, so a machine has ample slack, and the budget still closes. -/
def machineCutoffError : ℝ := 1 / 2 ^ 128

/-- **The machine law (P2, design note B theorems 23–27).** Against every adversary, at the
instances `Solution.adaptivePrivacy` installs, the library's ideal game with the closed machine is
within `error` of the abstract ideal game `I` of the exact samplers.

The cost bound `size + 1 + firstFuel + secondFuel ≤ 2^60` is the `within` field of
`BoundedMachine.Simulator` itself. The expected route to this law is kernel-level:
`idealGame_eq_machineAbstract` makes the library game the abstract game of the machine's
kernels, `abstractIdealGame_eq_of_simulation` identifies those kernels with
`planBAbstractSimulator bounded` for the machine's bounded samplers, and the sampler cutoffs
bound the distance to `idealSamplers`. -/
def MachineLaw (simulator : BoundedMachine.Simulator) (error : ℝ) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : Nat) (scalar : NonZeroScalar),
    Assumptions.advantage (atSolution idealHybrid field group adversary parameter scalar)
      (atSolution (machineHybrid simulator) field group adversary parameter scalar) ≤ error

end

end Kriterion.ArgoMAC.Phase3.Glue
