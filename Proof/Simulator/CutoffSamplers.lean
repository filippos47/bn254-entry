/-
**The rejection samplers against their exact laws.**

`rejectLaw_close`: a bounded rejection sampler read through a decoding `φ` (`none` off its domain) that is a
bijection from the accepted draws onto a finite type `β` is abort-close to the uniform law on `β`,
with extra abort mass the sampler's cutoff `rejectLaw … none`. Instances:

* `fieldCell_close`: a field cell against the uniform field element;
* `lambda_close`: a lift randomiser against the uniform `NonZeroBase`, and `pair_close`: a
  randomiser pair against the uniform pair;
* `preimage_close`: the designated vector's `t` sampler against `idealPreimage` (the uniform
  point of the `sampleLane` fibre);
* `free_close`: the `91` free coordinates against the uniform free part.

`optionProduct_uniform`: independent uniform draws are the uniform law on the product.
-/

import Proof.Simulator.AbortClose
import Proof.Simulator.AbortMass
import Proof.Simulator.Law

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### The kept draw of bounded rejection has at most the uniform mass -/

/-- The accepted `width`-bit draws. -/
def acceptedSet (width : Nat) (accept : Nat → Bool) : Finset (Fin (2 ^ width)) :=
  Finset.univ.filter fun value => accept value.val = true

/-- Every accepted draw has mass at most `1 / #accepted`. -/
theorem rejectLaw_some_mul_le (width : Nat) (accept : Nat → Bool) (count value : Nat)
    (good : accept value = true ∧ value < 2 ^ width) :
    rejectLaw width accept count (some value) * (acceptedSet width accept).card ≤ 1 := by
  have each : ∀ other ∈ acceptedSet width accept,
      rejectLaw width accept count (some other.val) = rejectLaw width accept count (some value) := by
    intro other member
    simp only [acceptedSet, Finset.mem_filter, Finset.mem_univ, true_and] at member
    exact rejectLaw_uniform width accept count other.val value ⟨member, other.isLt⟩ good
  have sumEq : ∑ other ∈ acceptedSet width accept, rejectLaw width accept count (some other.val) =
      (acceptedSet width accept).card * rejectLaw width accept count (some value) := by
    rw [Finset.sum_congr rfl each, Finset.sum_const, nsmul_eq_mul]
  have sumLe : ∑ other ∈ acceptedSet width accept, rejectLaw width accept count (some other.val) ≤
      ∑' candidate : Nat, rejectLaw width accept count (some candidate) := by
    rw [← Finset.sum_image (f := fun candidate : Nat => rejectLaw width accept count (some candidate))
      (fun first _ second _ same => Fin.ext same)]
    exact ENNReal.sum_le_tsum _
  rw [mul_comm, ← sumEq]
  exact sumLe.trans (tsum_some_le_one _)

/-- **Bounded rejection through a bijective decoding is abort-close to the uniform law.** The
decoding `φ` sends every accepted draw to a value (`total`), is injective on the accepted draws
with inverse `ψ` (`unique`), and `ψ` lands in the accepted draws (`encode`). -/
theorem rejectLaw_close {β : Type} [Fintype β] [Nonempty β] (width : Nat) (accept : Nat → Bool)
    (count : Nat) (φ : Nat → Option β) (ψ : β → Nat)
    (encode : ∀ b, accept (ψ b) = true ∧ ψ b < 2 ^ width ∧ φ (ψ b) = some b)
    (unique : ∀ value b, accept value = true → value < 2 ^ width → φ value = some b → value = ψ b)
    (total : ∀ value, accept value = true → value < 2 ^ width → φ value ≠ none) :
    AbortClose (rejectLaw width accept count none)
      ((rejectLaw width accept count).map fun drawn => drawn.bind φ)
      ((PMF.uniformOfFintype β).map some) := by
  classical
  refine ⟨fun b => ?_, ?_⟩
  · rw [PMF.map_apply, tsum_option]
    simp only [Option.bind_none, reduceCtorEq, if_false, zero_add, Option.bind_some]
    rw [tsum_eq_single (ψ b)]
    · rw [if_pos (encode b).2.2.symm, PMF.map_apply, tsum_eq_single b]
      · simp only [if_true, PMF.uniformOfFintype_apply]
        have cardLe : Fintype.card β ≤ (acceptedSet width accept).card := by
          rw [← Finset.card_univ]
          refine Finset.card_le_card_of_injOn (fun b => (⟨ψ b, (encode b).2.1⟩ : Fin (2 ^ width)))
            (fun b _ => ?_) (fun first _ second _ same => ?_)
          · simp only [acceptedSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
            exact (encode b).1
          · have := congrArg Fin.val same
            simp only at this
            have firstEq := (encode first).2.2
            rw [this, (encode second).2.2] at firstEq
            exact (Option.some_injective _ firstEq).symm
        have mass := rejectLaw_some_mul_le width accept count (ψ b) ⟨(encode b).1, (encode b).2.1⟩
        have positive : (0 : ENNReal) < (acceptedSet width accept).card := by
          have : 0 < Fintype.card β := Fintype.card_pos
          exact_mod_cast lt_of_lt_of_le this cardLe
        calc rejectLaw width accept count (some (ψ b))
            ≤ ((acceptedSet width accept).card : ENNReal)⁻¹ := by
              rw [ENNReal.le_inv_iff_mul_le]
              exact mass
          _ ≤ (Fintype.card β : ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr (by exact_mod_cast cardLe)
      · intro other different
        rw [if_neg (fun same => different (Option.some_injective _ same).symm)]
    · intro value different
      split
      · rename_i hit
        by_cases good : accept value = true ∧ value < 2 ^ width
        · exact absurd (unique value b good.1 good.2 hit.symm) different
        · exact rejectLaw_off width accept count value good
      · rfl
  · rw [PMF.map_apply, tsum_option]
    simp only [Option.bind_none, if_true, Option.bind_some]
    have idealNone : ((PMF.uniformOfFintype β).map some) none = 0 := by
      rw [PMF.map_apply]
      simp
    rw [idealNone, zero_add]
    apply le_of_eq
    convert add_zero (rejectLaw width accept count none) using 2
    apply ENNReal.tsum_eq_zero.mpr
    intro value
    split
    · rename_i miss
      by_cases good : accept value = true ∧ value < 2 ^ width
      · exact absurd miss.symm (total value good.1 good.2)
      · exact rejectLaw_off width accept count value good
    · rfl

/-! ### The field cell, the randomiser, the free coordinates, the preimage -/

/-- `p` as the library's modulus. -/
theorem pNat_eq : pNat = baseFieldModulus := rfl

theorem pNat_lt : pNat < 2 ^ fieldWidth := by unfold pNat fieldWidth; norm_num

/-- The field cell is `rejectLaw` read through the cast. -/
theorem fieldCellLaw_eq : fieldCellLaw = (rejectLaw fieldWidth (fun value => decide (value < pNat))
    attempts).map fun drawn => drawn.bind fun value => some ((value : Nat) : BaseField) := by
  unfold fieldCellLaw
  congr 1
  funext drawn
  cases drawn <;> rfl

/-- **A field cell is abort-close to the uniform field element.** -/
theorem fieldCell_close [FieldCertificate] :
    AbortClose (rejectLaw fieldWidth (fun value => decide (value < pNat)) attempts none)
      fieldCellLaw ((PMF.uniformOfFintype BaseField).map some) := by
  rw [fieldCellLaw_eq]
  refine rejectLaw_close _ _ _ _ (fun x : BaseField => x.val) (fun x => ⟨?_, ?_, ?_⟩) ?_ ?_
  · simp only [decide_eq_true_eq]
    exact x.val_lt
  · exact lt_trans x.val_lt pNat_lt
  · simp
  · intro value x below _ equal
    simp only [decide_eq_true_eq, Option.some.injEq] at below equal
    rw [← equal, ZMod.val_natCast]
    exact (Nat.mod_eq_of_lt below).symm
  · intro value _ _
    simp

/-- The randomiser law is `rejectLaw` read through the nonzero cast. -/
theorem lambdaLaw_eq : lambdaLaw = (rejectLaw fieldWidth
    (fun value => decide (1 ≤ value ∧ value < pNat)) attempts).map fun drawn =>
      drawn.bind fun value =>
        if nonzero : ((value : Nat) : BaseField) ≠ 0 then some ⟨value, nonzero⟩ else none := rfl

/-- **A lift randomiser is abort-close to the uniform nonzero field element.** -/
theorem lambda_close [FieldCertificate] :
    AbortClose (rejectLaw fieldWidth (fun value => decide (1 ≤ value ∧ value < pNat)) attempts none)
      lambdaLaw ((PMF.uniformOfFintype NonZeroBase).map some) := by
  rw [lambdaLaw_eq]
  refine rejectLaw_close _ _ _ _ (fun x : NonZeroBase => x.value.val) (fun x => ⟨?_, ?_, ?_⟩) ?_ ?_
  · simp only [decide_eq_true_eq]
    refine ⟨Nat.one_le_iff_ne_zero.mpr fun zero => x.nonzero ?_, x.value.val_lt⟩
    exact (ZMod.val_eq_zero _).mp zero
  · exact lt_trans x.value.val_lt pNat_lt
  · simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    rw [dif_pos x.nonzero]
  · intro value x below _ equal
    simp only [decide_eq_true_eq] at below
    split at equal
    · simp only [Option.some.injEq] at equal
      rw [← equal]
      simp only [ZMod.val_natCast]
      exact (Nat.mod_eq_of_lt below.2).symm
    · exact absurd equal (by simp)
  · intro value below _
    simp only [decide_eq_true_eq] at below
    have nonzero : ((value : Nat) : BaseField) ≠ 0 := by
      intro zero
      rw [ZMod.natCast_eq_zero_iff] at zero
      have := Nat.le_of_dvd (by omega) zero
      rw [← pNat_eq] at this
      omega
    simp [nonzero]

/-- The support of bounded rejection: only accepted draws are kept. -/
theorem rejectLaw_support (width : Nat) (accept : Nat → Bool) (count value : Nat)
    (member : some value ∈ (rejectLaw width accept count).support) :
    accept value = true ∧ value < 2 ^ width := by
  by_contra bad
  exact (PMF.mem_support_iff _ _).mp member (rejectLaw_off width accept count value bad)

/-- The preimage sampler's encoding is the batched sampler's `enc(Y*)`. -/
theorem vectorEnc_eq (vector : Fin pointElementCountX → BaseField) :
    vectorEnc vector = laneEncode vector := by
  unfold vectorEnc BigInt.encNat laneEncode
  rw [show BigInt.samplerDigits = pointElementCountX from rfl,
    ← Fin.sum_univ_eq_sum_range (fun e => vectorDigits vector e * pNat ^ e) pointElementCountX]
  refine Finset.sum_congr rfl fun element _ => ?_
  unfold vectorDigits
  rw [dif_pos element.isLt, pNat_eq]

/-- `enc(Y*) < p^364`: the preimage sampler's abort bound applies to every vector. -/
theorem vectorEnc_lt (vector : Fin pointElementCountX → BaseField) :
    vectorEnc vector < pNat ^ BigInt.samplerDigits := by
  rw [vectorEnc_eq, pNat_eq]
  exact laneEncode_lt vector

/-- The fibre bound `2^92672` is `2^(256 · 362)`, by its exponent (no power is evaluated). -/
theorem pow_designated : (2 : Nat) ^ 92672 = 2 ^ (256 * limbCount .pointX) := by
  rw [show 256 * limbCount .pointX = 92672 from rfl]

/-- The sampler's value `t · p^364 + enc` in the fibre's form `enc + p^364 · t`. -/
theorem samplerValue_eq (enc t : Nat) :
    BigInt.samplerValue BigInt.samplerDigits enc t = enc + pNat ^ BigInt.samplerDigits * t := by
  unfold BigInt.samplerValue
  rw [Nat.add_comm, Nat.mul_comm]

/-- An accepted `t` gives the `362` hash answers of a point of the fibre over `Y*`. -/
theorem sampleLane_natToLimbs_fibre (vector : Fin pointElementCountX → BaseField) (t : Nat)
    (inFibre : vectorEnc vector + pNat ^ BigInt.samplerDigits * t < 2 ^ 92672) :
    sampleLane pointElementCountX (limbCount .pointX) (natToLimbs (limbCount .pointX)
      (BigInt.samplerValue BigInt.samplerDigits (vectorEnc vector) t)) = vector := by
  have encSmall := vectorEnc_lt vector
  rw [pow_designated] at inFibre
  rw [sampleLane_eq_iff, samplerValue_eq, limbsToNat_natToLimbs_of_lt _ _ inFibre,
    show baseFieldModulus ^ pointElementCountX = pNat ^ BigInt.samplerDigits from rfl,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt encSmall, vectorEnc_eq]

/-- The designated fibre over a vector. -/
abbrev DesignatedFibre (vector : Fin pointElementCountX → BaseField) : Type :=
  {limbs : DesignatedLimbs // sampleLane pointElementCountX (limbCount .pointX) limbs = vector}

/-- The kept `t` read as a point of the fibre (`none` off the fibre). The test is decided
classically: its instance never reduces, so no defeq check evaluates the comparison with
`2^92672`. -/
def fibrePoint (vector : Fin pointElementCountX → BaseField) (t : Nat) :
    Option (DesignatedFibre vector) :=
  haveI := Classical.propDecidable
  if inFibre : vectorEnc vector + pNat ^ BigInt.samplerDigits * t < 2 ^ 92672 then
    some ⟨natToLimbs (limbCount .pointX)
      (BigInt.samplerValue BigInt.samplerDigits (vectorEnc vector) t),
      sampleLane_natToLimbs_fibre vector t inFibre⟩
  else none

/-- An accepted `t` is its point of the fibre. -/
theorem fibrePoint_of (vector : Fin pointElementCountX → BaseField) (t : Nat)
    (inFibre : vectorEnc vector + pNat ^ BigInt.samplerDigits * t < 2 ^ 92672) :
    fibrePoint vector t = some ⟨natToLimbs (limbCount .pointX)
      (BigInt.samplerValue BigInt.samplerDigits (vectorEnc vector) t),
      sampleLane_natToLimbs_fibre vector t inFibre⟩ := by
  unfold fibrePoint
  split
  · rfl
  · exact absurd inFibre ‹_›

/-- The draw of a point of the fibre: `V / p^364`. -/
def fibreDraw (vector : Fin pointElementCountX → BaseField) (point : DesignatedFibre vector) :
    Nat :=
  limbsToNat (limbCount .pointX) point.1 / pNat ^ BigInt.samplerDigits

/-- A point of the fibre is `enc(Y*) + p^364 · (V / p^364)`, below `2^92672`. -/
theorem fibreDraw_spec (vector : Fin pointElementCountX → BaseField)
    (point : DesignatedFibre vector) :
    limbsToNat (limbCount .pointX) point.1 =
        vectorEnc vector + pNat ^ BigInt.samplerDigits * fibreDraw vector point ∧
      vectorEnc vector + pNat ^ BigInt.samplerDigits * fibreDraw vector point < 2 ^ 92672 := by
  have residue : limbsToNat (limbCount .pointX) point.1 % pNat ^ BigInt.samplerDigits =
      vectorEnc vector := by
    have same := (sampleLane_eq_iff _ _ point.1 vector).mp point.2
    rw [← vectorEnc_eq] at same
    exact same
  have split := Nat.mod_add_div (limbsToNat (limbCount .pointX) point.1)
    (pNat ^ BigInt.samplerDigits)
  rw [residue] at split
  have below := limbsToNat_lt (limbCount .pointX) point.1
  rw [← pow_designated] at below
  unfold fibreDraw
  exact ⟨split.symm, by rw [split]; exact below⟩

/-- The preimage law, factored through the fibre. -/
theorem preimageLaw_eq (vector : Fin pointElementCountX → BaseField) : preimageLaw vector =
    ((rejectLaw (BigInt.hiWidth + 256) (BigInt.samplerAccept (vectorEnc vector))
        BigInt.samplerAttempts).map fun drawn => drawn.bind (fibrePoint vector)).map
      (Option.map Subtype.val) := by
  unfold preimageLaw
  rw [PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  apply PMF.bind_congr
  intro drawn member
  cases drawn with
  | none => rfl
  | some t =>
      have inFibre := (BigInt.accepted_iff_fibre _ t).mp (rejectLaw_support _ _ _ _ member)
      simp only [Function.comp_apply, Option.map_some, Option.bind_some]
      rw [fibrePoint_of vector t inFibre]
      rfl

/-- **A preimage draw is abort-close to the uniform point of the fibre** (`idealPreimage`, the
mask swap's per-site fibre law): the kept `t` is uniform on the accepted draws, which are
exactly the fibre `{t : enc(Y*) + p^364 · t < 2^92672}` (`accepted_iff_fibre`), in bijection
with the `sampleLane` fibre over `Y*` through `limbsToNat`. -/
theorem preimage_close [FieldCertificate] (vector : Fin pointElementCountX → BaseField) :
    AbortClose (rejectLaw (BigInt.hiWidth + 256) (BigInt.samplerAccept (vectorEnc vector))
        BigInt.samplerAttempts none)
      (preimageLaw vector) ((idealPreimage vector).map some) := by
  have : Nonempty (DesignatedFibre vector) :=
    ⟨⟨_, Classical.choose_spec (sampleLane_designated_surjective vector)⟩⟩
  have idealEq : (idealPreimage vector).map some =
      ((PMF.uniformOfFintype (DesignatedFibre vector)).map some).map (Option.map Subtype.val) := by
    unfold idealPreimage Security.Phase3.fibreLaw
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  rw [preimageLaw_eq, idealEq]
  refine AbortClose.map_opt ?_ _ rfl
  refine rejectLaw_close _ _ _ (fibrePoint vector) (fibreDraw vector) (fun point => ?_) ?_ ?_
  · obtain ⟨value, inFibre⟩ := fibreDraw_spec vector point
    refine ⟨((BigInt.accepted_iff_fibre _ _).mpr inFibre).1,
      ((BigInt.accepted_iff_fibre _ _).mpr inFibre).2, ?_⟩
    rw [fibrePoint_of vector _ inFibre]
    refine congrArg some (Subtype.ext ?_)
    show natToLimbs (limbCount .pointX) (BigInt.samplerValue BigInt.samplerDigits (vectorEnc vector)
      (fibreDraw vector point)) = point.1
    rw [samplerValue_eq, ← value, natToLimbs_limbsToNat]
  · intro t point accepted small hit
    have inFibre := (BigInt.accepted_iff_fibre _ t).mp ⟨accepted, small⟩
    rw [fibrePoint_of vector t inFibre] at hit
    cases hit
    change t = limbsToNat (limbCount .pointX) (natToLimbs (limbCount .pointX)
      (BigInt.samplerValue BigInt.samplerDigits (vectorEnc vector) t)) / pNat ^ BigInt.samplerDigits
    rw [pow_designated] at inFibre
    rw [samplerValue_eq, limbsToNat_natToLimbs_of_lt _ _ inFibre, Nat.mul_comm,
      Nat.add_mul_div_right _ _ (pow_pos BigInt.pNat_pos _),
      Nat.div_eq_of_lt (vectorEnc_lt vector), Nat.zero_add]
  · intro t accepted small
    have inFibre := (BigInt.accepted_iff_fibre _ t).mp ⟨accepted, small⟩
    rw [fibrePoint_of vector t inFibre]
    exact Option.some_ne_none _

/-! ### Independent uniform draws -/

/-- Independent draws commute with a map of their values. -/
theorem optionProduct_map {α β : Type} (f : α → β) :
    ∀ (count : Nat) (sample : Fin count → PMF (Option α)),
      optionProduct count (fun index => (sample index).map (Option.map f)) =
        (optionProduct count sample).map (Option.map fun values => f ∘ values)
  | 0, sample => by
      simp only [optionProduct, PMF.pure_map, Option.map_some]
      congr 2
      funext index
      exact index.elim0
  | count + 1, sample => by
      simp only [optionProduct]
      rw [PMF.bind_map, PMF.map_bind]
      congr 1
      funext head
      cases head with
      | none => simp [PMF.pure_map]
      | some head =>
          simp only [Function.comp_apply, Option.map_some]
          rw [optionProduct_map f count, PMF.map_comp, PMF.map_comp]
          congr 1
          funext values
          cases values with
          | none => rfl
          | some values =>
              simp only [Function.comp_apply, Option.map_some, Option.some.injEq]
              funext index
              cases index using Fin.cases <;> rfl

/-- **Independent uniform draws are uniform on the product.** -/
theorem optionProduct_uniform [FieldCertificate] {α : Type} [Fintype α] [Nonempty α] :
    ∀ (count : Nat),
      optionProduct count (fun _ => (PMF.uniformOfFintype α).map some) =
        (PMF.uniformOfFintype (Fin count → α)).map some
  | 0 => by
      simp only [optionProduct]
      have single : PMF.uniformOfFintype (Fin 0 → α) = PMF.pure Fin.elim0 := by
        apply PMF.ext
        intro values
        have : values = Fin.elim0 := funext fun index => index.elim0
        subst this
        simp [PMF.uniformOfFintype_apply]
      rw [single, PMF.pure_map]
  | count + 1 => by
      simp only [optionProduct]
      rw [PMF.bind_map]
      have rest := optionProduct_uniform (α := α) count
      have step : (fun head => match (some head : Option α) with
          | none => PMF.pure none
          | some head => (optionProduct count fun _ => (PMF.uniformOfFintype α).map some).map
              (Option.map fun tail => Fin.cons (α := fun _ => α) head tail)) =
          fun head : α => (PMF.uniformOfFintype (Fin count → α)).map
            fun tail => some (Fin.cons (α := fun _ => α) head tail) := by
        funext head
        simp only
        rw [rest, PMF.map_comp]
        rfl
      simp only [Function.comp_def]
      rw [show (fun head : α => match (some head : Option α) with
          | none => PMF.pure none
          | some head => (optionProduct count fun _ => (PMF.uniformOfFintype α).map some).map
              (Option.map fun tail => Fin.cons (α := fun _ => α) head tail)) =
          fun head : α => (PMF.uniformOfFintype (Fin count → α)).map
            fun tail => some (Fin.cons (α := fun _ => α) head tail) from step]
      have product := uniform_product (A := α) (B := Fin count → α)
      have cons := uniform_equiv (Fin.consEquiv fun _ : Fin (count + 1) => α)
      rw [← cons, ← product, PMF.map_comp, PMF.map_bind]
      congr 1
      funext head
      rw [PMF.map_comp]
      rfl

/-- **A randomiser pair is abort-close to the uniform pair**: two randomisers, read as the pair
`(draw 0, draw 1)` (a bijection `piFinTwoEquiv`). -/
theorem pair_close [FieldCertificate] :
    AbortClose (((2 : Nat) : ENNReal) *
        rejectLaw fieldWidth (fun value => decide (1 ≤ value ∧ value < pNat)) attempts none)
      pairLaw ((PMF.uniformOfFintype (NonZeroBase × NonZeroBase)).map some) := by
  have draws := AbortClose.optionProduct 2 (fun _ => lambdaLaw)
    (fun _ => (PMF.uniformOfFintype NonZeroBase).map some) (fun _ => lambda_close)
  rw [optionProduct_uniform] at draws
  have reindex : (PMF.uniformOfFintype (NonZeroBase × NonZeroBase)).map some =
      ((PMF.uniformOfFintype (Fin 2 → NonZeroBase)).map some).map
        (Option.map fun pair => (pair 0, pair 1)) := by
    rw [PMF.map_comp, ← uniform_equiv (piFinTwoEquiv fun _ => NonZeroBase), PMF.map_comp]
    rfl
  rw [reindex]
  exact draws.map_opt _ rfl

/-- **The free coordinates are abort-close to the uniform free part**: `91` field cells, read in
the machine's order `d` (a bijection `finProdFinEquiv`). -/
theorem free_close [FieldCertificate] :
    AbortClose (((digitCount * 1 : Nat) : ENNReal) *
        rejectLaw fieldWidth (fun value => decide (value < pNat)) attempts none)
      freeLaw ((PMF.uniformOfFintype (FreeSite → BaseField)).map some) := by
  have cells := AbortClose.optionProduct (digitCount * 1) (fun _ => fieldCellLaw)
    (fun _ => (PMF.uniformOfFintype BaseField).map some) (fun _ => fieldCell_close)
  rw [optionProduct_uniform] at cells
  have reindex : (PMF.uniformOfFintype (FreeSite → BaseField)).map some =
      ((PMF.uniformOfFintype (Fin (digitCount * 1) → BaseField)).map some).map
        (Option.map fun draws site => draws (finProdFinEquiv site)) := by
    rw [PMF.map_comp, ← uniform_equiv (finProdFinEquiv.symm.arrowCongr (Equiv.refl BaseField)),
      PMF.map_comp]
    rfl
  rw [reindex]
  exact cells.map_opt _ rfl

end

end Kriterion.ArgoMAC.PlanB.SimMachine
