/-
**The machine's tail sampler against the construction's offset law.**

`idealSamplers.tail` is the law of the free offsets of a uniform coin (`coinOffsetsLaw`). A coin
is exactly a tail with a nonzero clamp, the head point it clamps to, and the independent rest of
the coin (`coinSplit`, a bijection at the given certificates), so the free offsets of a uniform
coin are uniform on the tails with a nonzero clamp (`coinTail_law`).

The machine draws `90` independent uniform affine offsets and aborts on a zero clamp. The head
offset of a zero-clamp tail is determined by the other `89` (`radix` is invertible), so a zero
clamp has probability at most `1 / #A` (`clampFilter_close`). With the `90` rejection cutoffs:
`tail_close`.
-/

import Proof.Simulator.CutoffPoint

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Scheme (Coins)
open WeierstrassCurve.Affine

noncomputable section

/-- A vector is determined by its entries. -/
local instance vectorFiniteLocal {α : Type} [Finite α] {count : Nat} :
    Finite (Vector α count) :=
  Finite.of_injective (fun values : Vector α count => fun index : Fin count => values[index.val])
    (by
      intro first second equal
      apply Vector.ext
      intro index bound
      exact congrFun equal ⟨index, bound⟩)

/-- Vectors are functions on `Fin`. -/
def vectorEquiv (α : Type) (count : Nat) : (Fin count → α) ≃ Vector α count where
  toFun := Vector.ofFn
  invFun values index := values[index.val]
  left_inv values := by
    funext index
    simp
  right_inv values := Vector.ofFn_getElem

section Tail

variable [FieldCertificate] [GroupCertificate]

theorem radix_ne_zero : radix ≠ 0 := by decide

/-- The offset of a nonzero point. -/
def offsetOf : (point : Point) → point ≠ 0 → FieldMacToECMac.AffineOffset
  | .zero, nonzero => absurd rfl nonzero
  | .some x y h, _ => ⟨⟨x, y⟩, (equation_iff_onCurve ⟨x, y⟩).mp h.1⟩

theorem offsetOf_point (point : Point) (nonzero : point ≠ 0) :
    (offsetOf point nonzero).point = point := by
  cases point with
  | zero => exact absurd rfl nonzero
  | some x y h =>
      rw [offsetOf, affineOffset_point]

/-! ### The coins -/

/-- The tails with a nonzero clamp. -/
abbrev GoodTail := {tail : Vector FieldMacToECMac.AffineOffset 90 //
  FieldMacToECMac.clampedFirst tail ≠ 0}

/-- A coin without its offsets. -/
abbrev CoinRest := FieldMacToECMac.Randomness × FieldMacToECMac.ExceptionPad × BaseField ×
  NonZeroBase × (PlanB.Coord → Fin coordinateBitCount → Block) ×
  (PlanB.Coord → Block)

noncomputable instance goodTailFintype : Fintype GoodTail := Fintype.ofFinite _

noncomputable instance coinRestFintype : Fintype CoinRest := Fintype.ofFinite _

/-- A coin's free offsets have a nonzero clamp: the clamp is the coin's head offset. -/
theorem coin_clamp_ne (coin : Coins) : FieldMacToECMac.clampedFirst coin.offsets.free ≠ 0 := by
  have clamped : coin.offsets.IsClamped := coin.offsetsClamped
  unfold FieldMacToECMac.SuccessfulOffsets.IsClamped at clamped
  rw [← clamped, affineOffset_point]
  exact Point.some_ne_zero _

/-- The head offset a nonzero clamp determines is clamped. -/
theorem clamped_offsetOf (free : Vector FieldMacToECMac.AffineOffset 90)
    (nonzero : FieldMacToECMac.clampedFirst free ≠ 0) :
    (⟨offsetOf _ nonzero, free⟩ : FieldMacToECMac.SuccessfulOffsets).IsClamped := by
  unfold FieldMacToECMac.SuccessfulOffsets.IsClamped
  dsimp only
  exact offsetOf_point (FieldMacToECMac.clampedFirst free) nonzero

/-- **The coin split**: a coin is a tail with a nonzero clamp and the rest of the coin. -/
def coinSplit (coin : Coins) : GoodTail × CoinRest :=
  (⟨coin.offsets.free, coin_clamp_ne coin⟩, (coin.pointRandomness, coin.exceptionPad,
    coin.bridgeKey, coin.curveMask, coin.inputZero, coin.inputDelta))

theorem coinSplit_bijective : Function.Bijective coinSplit := by
  constructor
  · intro first second same
    have clampedFirst : first.offsets.IsClamped := first.offsetsClamped
    have clampedSecond : second.offsets.IsClamped := second.offsetsClamped
    rcases first with ⟨⟨head, free⟩, clamped, randomness, pad, bridge, mask, zero, delta⟩
    rcases second with ⟨⟨head', free'⟩, clamped', randomness', pad', bridge', mask', zero', delta'⟩
    simp only [coinSplit, Prod.mk.injEq, Subtype.mk.injEq] at same
    obtain ⟨sameFree, sameRandomness, samePad, sameBridge, sameMask, sameZero, sameDelta⟩ := same
    subst sameFree sameRandomness samePad sameBridge sameMask sameZero sameDelta
    unfold FieldMacToECMac.SuccessfulOffsets.IsClamped at clampedFirst clampedSecond
    simp only at clampedFirst clampedSecond
    have sameHead : head = head' := affineOffset_point_injective
      (clampedFirst.trans clampedSecond.symm)
    subst sameHead
    rfl
  · rintro ⟨⟨free, nonzero⟩, randomness, pad, bridge, mask, zero, delta⟩
    refine ⟨{ offsets := ⟨offsetOf _ nonzero, free⟩
              offsetsClamped := fun {_} {_} => clamped_offsetOf free nonzero
              pointRandomness := randomness
              exceptionPad := pad
              bridgeKey := bridge
              curveMask := mask
              inputZero := zero
              inputDelta := delta }, rfl⟩

instance goodTailNonempty : Nonempty GoodTail := ⟨(coinSplit Scheme.witness).1⟩

instance coinRestNonempty : Nonempty CoinRest := ⟨(coinSplit Scheme.witness).2⟩

/-- **The free offsets of a uniform coin are uniform on the tails with a nonzero clamp.** -/
theorem coinTail_law : coinOffsetsLaw.map (fun offsets => some offsets.free) =
    (PMF.uniformOfFintype GoodTail).map fun tail => some tail.val := by
  unfold coinOffsetsLaw
  letI : Fintype Coins := Fintype.ofFinite Coins
  have : Nonempty Coins := ⟨Scheme.witness⟩
  rw [PMF.map_comp]
  have split : (PMF.uniformOfFintype Coins).map coinSplit =
      PMF.uniformOfFintype (GoodTail × CoinRest) :=
    PMF.uniformOfFintype_map_of_bijective _ coinSplit_bijective
  have factor : ((fun offsets : FieldMacToECMac.SuccessfulOffsets => some offsets.free) ∘
      Coins.offsets) = (fun pair : GoodTail × CoinRest => some pair.1.val) ∘ coinSplit := rfl
  rw [factor, ← PMF.map_comp, split, ← uniform_product, PMF.map_bind, ← PMF.bind_pure_comp]
  congr 1
  funext tail
  rw [PMF.map_comp]
  exact PMF.map_const (PMF.uniformOfFintype CoinRest) (some tail.val)

/-! ### A zero clamp is rare -/

/-- The clamp of a tail, with its head point separated. -/
theorem clampedFirst_ofFn (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    FieldMacToECMac.clampedFirst (Vector.ofFn points) =
      -(radix • ((points 0).point + radix • pointHorner radix
        ((List.ofFn (Fin.tail points)).map fun offset => offset.point))) := by
  unfold FieldMacToECMac.clampedFirst FieldMacToECMac.freeOffsetPoints
  rw [Vector.toList_ofFn, List.ofFn_succ, List.map_cons, pointHorner]
  rfl

/-- A zero clamp determines the head offset from the other `89`. -/
theorem head_of_clamp_zero (points : Fin 90 → FieldMacToECMac.AffineOffset)
    (zero : FieldMacToECMac.clampedFirst (Vector.ofFn points) = 0) :
    (points 0).point = -(radix • pointHorner radix
      ((List.ofFn (Fin.tail points)).map fun offset => offset.point)) := by
  rw [clampedFirst_ofFn, neg_eq_zero] at zero
  exact eq_neg_of_add_eq_zero_left (smul_eq_zero_of_ne radix_ne_zero zero)

/-- The draws with a zero clamp. -/
def badDraws : Finset (Fin 90 → FieldMacToECMac.AffineOffset) :=
  Finset.univ.filter fun points => FieldMacToECMac.clampedFirst (Vector.ofFn points) = 0

theorem badDraws_card : badDraws.card ≤ affineCount ^ 89 := by
  have tailCard : Fintype.card (Fin 89 → FieldMacToECMac.AffineOffset) = affineCount ^ 89 := by
    rw [Fintype.card_fun, Fintype.card_fin, affineCount_eq]
  rw [← tailCard, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn Fin.tail (fun _ _ => Finset.mem_univ _) ?_
  intro first firstBad second secondBad sameTail
  simp only [badDraws, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    at firstBad secondBad
  have sameHead : first 0 = second 0 := by
    apply affineOffset_point_injective
    simp only
    rw [head_of_clamp_zero first firstBad, head_of_clamp_zero second secondBad, sameTail]
  rw [← Fin.cons_self_tail first, ← Fin.cons_self_tail second, sameHead, sameTail]

/-- The number of tail draws. -/
theorem drawCount : Fintype.card (Fin 90 → FieldMacToECMac.AffineOffset) = affineCount ^ 90 := by
  rw [Fintype.card_fun, Fintype.card_fin, affineCount_eq]

theorem affineCount_pos : 0 < affineCount := by
  rw [← affineCount_eq]
  exact Fintype.card_pos

/-- The filter the machine applies to its `90` draws. -/
def clampFilter (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    Option (Vector FieldMacToECMac.AffineOffset 90) :=
  if FieldMacToECMac.clampedFirst (Vector.ofFn points) = 0 then none else some (Vector.ofFn points)

/-- **Uniform draws with the clamp filter are `1 / #A`-close to the coin's tail law.** -/
theorem clampFilter_close :
    AbortClose (affineCount : ENNReal)⁻¹
      ((PMF.uniformOfFintype (Fin 90 → FieldMacToECMac.AffineOffset)).map clampFilter)
      ((PMF.uniformOfFintype GoodTail).map fun tail => some tail.val) := by
  classical
  have countPos : (0 : ENNReal) < affineCount := by exact_mod_cast affineCount_pos
  refine ⟨fun tail => ?_, ?_⟩
  · rw [PMF.map_apply, PMF.map_apply]
    by_cases zero : FieldMacToECMac.clampedFirst tail = 0
    · refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun points => ?_)) zero_le
      rw [if_neg]
      unfold clampFilter
      split
      · simp
      · rename_i nonzero
        intro same
        apply nonzero
        rw [← Option.some_injective _ same]
        exact zero
    · rw [tsum_eq_single (fun index : Fin 90 => tail[index.val]),
        tsum_eq_single (⟨tail, zero⟩ : GoodTail)]
      · simp only [if_true, PMF.uniformOfFintype_apply]
        have hit : clampFilter (fun index : Fin 90 => tail[index.val]) = some tail := by
          unfold clampFilter
          rw [Vector.ofFn_getElem, if_neg zero]
        rw [if_pos hit.symm]
        apply ENNReal.inv_le_inv.mpr
        exact_mod_cast Fintype.card_le_of_injective
          (fun good : GoodTail => (vectorEquiv _ _).symm good.val)
          (fun first second same => Subtype.ext ((vectorEquiv _ _).symm.injective same))
      · intro other different
        rw [if_neg]
        intro same
        exact different (Subtype.ext (Option.some_injective _ same).symm)
      · intro points different
        rw [if_neg]
        unfold clampFilter
        split
        · simp
        · intro same
          apply different
          rw [Option.some_injective _ same]
          funext index
          simp
  · rw [PMF.map_apply, PMF.map_apply]
    simp only [reduceCtorEq, if_false, tsum_zero, zero_add]
    rw [tsum_fintype]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun points _ =>
      (?_ : _ = if points ∈ badDraws then
        (Fintype.card (Fin 90 → FieldMacToECMac.AffineOffset) : ENNReal)⁻¹ else 0)) ?_
    · by_cases bad : FieldMacToECMac.clampedFirst (Vector.ofFn points) = 0
      · simp [clampFilter, badDraws, bad, PMF.uniformOfFintype_apply]
      · simp [clampFilter, badDraws, bad]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, drawCount]
    calc (badDraws.card : ENNReal) * ((affineCount ^ 90 : Nat) : ENNReal)⁻¹
        ≤ ((affineCount ^ 89 : Nat) : ENNReal) * ((affineCount ^ 90 : Nat) : ENNReal)⁻¹ :=
          mul_le_mul' (by exact_mod_cast badDraws_card) le_rfl
      _ = (affineCount : ENNReal)⁻¹ := by
          push_cast
          have ne0 : (affineCount : ENNReal) ^ 89 ≠ 0 := pow_ne_zero _ countPos.ne'
          have neTop : (affineCount : ENNReal) ^ 89 ≠ ⊤ :=
            ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
          rw [show (affineCount : ENNReal) ^ 90 = (affineCount : ENNReal) ^ 89 * affineCount from
              pow_succ _ _, ENNReal.mul_inv (Or.inl ne0) (Or.inl neTop), ← mul_assoc,
            ENNReal.mul_inv_cancel ne0 neTop, one_mul]

/-- **The machine's tail sampler is abort-close to the construction's offset law.** -/
theorem tail_close :
    AbortClose (90 * rejectLaw fieldWidth curveXAccept attempts none + (affineCount : ENNReal)⁻¹)
      tailLaw idealSamplers.tail := by
  have points := AbortClose.optionProduct 90 (fun _ => curvePointLaw)
    (fun _ => (PMF.uniformOfFintype FieldMacToECMac.AffineOffset).map some)
    (fun _ => curvePoint_close)
  rw [optionProduct_uniform] at points
  have filtered := points.map_opt (fun drawn => drawn.bind clampFilter) rfl
  have tailEq : tailLaw = (optionProduct 90 fun _ => curvePointLaw).map
      (fun drawn => drawn.bind clampFilter) := rfl
  have idealEq : idealSamplers.tail =
      (PMF.uniformOfFintype GoodTail).map fun tail => some tail.val := coinTail_law
  have mapped : ((PMF.uniformOfFintype (Fin 90 → FieldMacToECMac.AffineOffset)).map some).map
      (fun drawn => drawn.bind clampFilter) =
      (PMF.uniformOfFintype (Fin 90 → FieldMacToECMac.AffineOffset)).map clampFilter := by
    have function : ((fun drawn : Option (Fin 90 → FieldMacToECMac.AffineOffset) =>
        drawn.bind clampFilter) ∘ some) = clampFilter :=
      by
        funext points
        rw [Function.comp_apply, Option.bind_some]
    rw [PMF.map_comp, function]
  rw [tailEq, idealEq]
  rw [mapped] at filtered
  exact filtered.trans clampFilter_close

end Tail

end

end Kriterion.ArgoMAC.PlanB.SimMachine
