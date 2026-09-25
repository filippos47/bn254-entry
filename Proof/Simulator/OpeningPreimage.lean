/-
**The opening, the preimage** (`Opening.preimage`, the batched sampler's `t` step).

* `memSem_preimage`: from a memory whose designated cells hold a vector `Y*`, the preimage
  sampler is the rejection law of `t` on the fibre of `enc(Y*)`, its accepted draw leaving
  `BigInt.samplerFinal` (`BigInt.memSem_preimageSampler_A1` on the phase-4 layout
  `samplerLayout`);
* `samplerFinal_half`: afterwards half cell `i` holds half `i` of the limbs of
  `V = enc(Y*) + p^364 · t` (`halfValue_limbHalf`: the halves of `natToLimbs 362 V`);
* `samplerFinal_sameOff`, `samplerFinal_bits`: nothing off the sampler's region changes.
-/

import Proof.Simulator.OpeningFree
import Proof.Simulator.Stage2Spec

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

omit [FieldCertificate] in
/-- The phase-4 layout of the preimage sampler: its region at `samplerBase`, the designated
digits at `designatedBase`, above it. -/
theorem samplerLayout :
    BigInt.SamplerLayout samplerBase BigInt.samplerLimbs BigInt.samplerDigits designatedBase where
  two := by decide
  fits := by unfold samplerBase BigInt.samplerLimbs; norm_num
  apart := Or.inr (by unfold samplerBase designatedBase BigInt.samplerLimbs; norm_num)
  yFits := by unfold designatedBase BigInt.samplerDigits; norm_num

/-- **The preimage sampler** on a designated vector held in its cells. -/
theorem memSem_preimage (memory : Memory) (vector : Fin pointElementCountX → BaseField)
    (cells : ∀ element : Fin pointElementCountX,
      memory.ram (word (designatedCell element.val)) = fieldWord (vector element)) :
    Opening.preimage.memSem memory =
      (rejectLaw (BigInt.hiWidth + 256) (BigInt.samplerAccept (vectorEnc vector))
          BigInt.samplerAttempts).map
        (Option.map (BigInt.samplerFinal samplerBase BigInt.samplerLimbs BigInt.samplerDigits
          (vectorEnc vector) memory)) := by
  unfold Opening.preimage
  exact BigInt.memSem_preimageSampler_A1 samplerBase designatedBase samplerLayout memory
    (vectorDigits vector)
    (fun element bound => by
      unfold vectorDigits
      rw [dif_pos (show element < pointElementCountX from bound)]
      exact lt_of_lt_of_eq (vector _).val_lt (by unfold pNat baseFieldModulus; rfl))
    (fun element bound => by
      unfold vectorDigits
      rw [dif_pos (show element < pointElementCountX from bound)]
      exact cells ⟨element, bound⟩)

omit [FieldCertificate] in
theorem samplerFinal_ram (enc : Nat) (memory : Memory) (t : Nat) :
    (BigInt.samplerFinal samplerBase BigInt.samplerLimbs BigInt.samplerDigits enc memory t).ram =
      BigInt.finalRam samplerBase BigInt.samplerLimbs BigInt.samplerDigits enc memory.ram t := by
  unfold BigInt.samplerFinal
  rw [(clearRegs_other _ _).1]
  rfl

omit [FieldCertificate] in
theorem samplerFinal_bits (enc : Nat) (memory : Memory) (t : Nat) :
    (BigInt.samplerFinal samplerBase BigInt.samplerLimbs BigInt.samplerDigits enc memory t).bits =
      memory.bits := by
  unfold BigInt.samplerFinal
  rw [(clearRegs_other _ _).2]
  rfl

omit [FieldCertificate] in
/-- **The half cells** hold the halves of `V`. -/
theorem samplerFinal_half (enc : Nat) (memory : Memory) (t : Nat) (half : Nat)
    (small : half < 2 * limbCount .pointX) :
    (BigInt.samplerFinal samplerBase BigInt.samplerLimbs BigInt.samplerDigits enc memory t).ram
        (word (halfCell half)) =
      word (BigInt.halfValue (BigInt.samplerValue BigInt.samplerDigits enc t) half) := by
  have bound : half < 724 := small
  rw [samplerFinal_ram]
  unfold BigInt.finalRam halfCell
  rw [BigInt.writeCells_out _ _ _ _ _ (by unfold BigInt.halfBase samplerBase BigInt.samplerLimbs; omega)
      (Or.inr (by unfold BigInt.halfBase BigInt.samplerLimbs; omega)),
    BigInt.writeCells_in _ _ _ _ _ (by unfold BigInt.samplerLimbs; omega)
      (by unfold BigInt.halfBase samplerBase BigInt.samplerLimbs; omega)]

omit [FieldCertificate] in
/-- **Nothing off the sampler's region changes.** -/
theorem samplerFinal_sameOff (enc : Nat) (memory : Memory) (t : Nat) :
    SameOff memory.ram
      (BigInt.samplerFinal samplerBase BigInt.samplerLimbs BigInt.samplerDigits enc memory t).ram := by
  intro address outside
  have notSampler : ¬ (samplerBase ≤ address.toNat ∧ address.toNat < samplerBase + 2 ^ 11) :=
    fun inside => outside (Or.inr (Or.inr inside))
  have outer : ¬ (samplerBase ≤ address.toNat ∧ address.toNat < samplerBase + 5) := by
    intro inside
    exact notSampler ⟨inside.1, by omega⟩
  have middle : ¬ (BigInt.halfBase samplerBase BigInt.samplerLimbs ≤ address.toNat ∧
      address.toNat < BigInt.halfBase samplerBase BigInt.samplerLimbs +
        2 * (BigInt.samplerLimbs - 1)) := by
    intro inside
    unfold BigInt.halfBase BigInt.samplerLimbs at inside
    exact notSampler ⟨by omega, by omega⟩
  have inner : ¬ (BigInt.limbBase samplerBase ≤ address.toNat ∧
      address.toNat < BigInt.limbBase samplerBase + BigInt.samplerLimbs) := by
    intro inside
    unfold BigInt.limbBase BigInt.samplerLimbs at inside
    exact notSampler ⟨by omega, by omega⟩
  rw [samplerFinal_ram]
  simp only [BigInt.finalRam, BigInt.writeCells]
  rw [if_neg outer, if_neg middle, if_neg inner]

omit [FieldCertificate] in
theorem blockWord_ofNat_mod (value : Nat) :
    blockWord (BitVec.ofNat 128 value) = word (value % 2 ^ 128) := by
  unfold blockWord
  rw [BitVec.toNat_ofNat]

omit [FieldCertificate] in
/-- **The halves are the limbs' blocks.** -/
theorem halfValue_limbHalf (value : Nat) (half : Fin (2 * limbCount .pointX)) :
    word (BigInt.halfValue value half.val) =
      blockWord (limbHalf (natToLimbs (limbCount .pointX) value) half) := by
  unfold BigInt.halfValue limbHalf natToLimbs limbOfNat BigInt.limb
  split
  · rw [blockWord_ofNat_mod, Nat.mod_mod_of_dvd _ (by norm_num)]
  · rw [blockWord_ofNat_mod, show (2 : Nat) ^ 256 = 2 ^ 128 * 2 ^ 128 by norm_num,
      Nat.mod_mul_right_div_self]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
