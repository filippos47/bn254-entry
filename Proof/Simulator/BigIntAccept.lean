/-
**The preimage sampler's acceptance, uniformity and abort mass** at the phase-4 parameters
(`K = 363` working limbs, `n = 364` digits, `363 = 107 + 256` coins, `R = 80` attempts).

* `acceptTop_eq`: the machine's test (top working limb `0`) is `samplerAccept`:
  `enc + p^364 · t < 2^92672` (`= 2^(256 · 362)`), for every `t < 2^363` and `enc < p^364`;
* `memSem_preimageSampler_A1`: the sampler's law with that acceptance;
* `kept_below`: every kept `t` gives `V = enc + p^364 · t < 2^92672`;
* `fibre_below`, `accepted_iff_fibre`: the fibre `{t : enc + p^364 · t < 2^92672}` (with `t`
  unrestricted, as the swap kernel's fibre) lies below `2^363`, so it is exactly the set of
  accepted `363`-bit draws (from `preimageComplete_nat : 2^92672 ≤ 2^363 · p^364`);
* `kept_uniform`, `kept_off`: conditioned on acceptance, `t` is uniform on the **whole** fibre
  `{t : enc + p^364 · t < 2^92672}` (A1 §4 item 4);
* `rejectedCount_sampler`: at most `3/10` of the draws are rejected, from the single inequality
  `preimageAccept_nat : (7 · 2^363 + 10) · p^364 ≤ 10 · 2^92672`;
* `samplerAbort_le`: the abort mass over `80` attempts is below `2^-138` (`(3/10)^80 < 2^-138.9`),
  in the `((2 : ENNReal) ^ k)⁻¹` form `CutoffMass` consumes.

No power of two is evaluated here except by the two facts of `BigIntBound` (their own module) and
the `3^80 · 2^138 ≤ 10^80` comparison (266-bit).
-/

import Proof.Simulator.BigIntSampler
import Proof.Simulator.BigIntBound
import Proof.Simulator.CutoffPow

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine Blocks

namespace BigInt

/-- **The acceptance predicate of A1 §4.4**: `enc + p^364 · t < 2^92672`. -/
def samplerAccept (enc t : Nat) : Bool :=
  decide (enc + pNat ^ samplerDigits * t < 2 ^ (256 * (samplerLimbs - 1)))

theorem samplerWidth_eq : hiWidth + 256 = 363 := rfl
theorem samplerBoundary_eq : 256 * (samplerLimbs - 1) = 92672 := rfl

/-- `p^364 < 2^(254 · 364)`, by exponent arithmetic. -/
theorem pow_samplerDigits_lt : pNat ^ samplerDigits < 2 ^ (254 * samplerDigits) := by
  rw [Nat.pow_mul]
  exact Nat.pow_lt_pow_left pNat_lt_254 (by decide)

/-- Every attempt's value fits the `363` working limbs. -/
theorem samplerValue_lt (enc t : Nat) (encSmall : enc < pNat ^ samplerDigits)
    (tSmall : t < 2 ^ (hiWidth + 256)) :
    samplerValue samplerDigits enc t < 2 ^ (256 * samplerLimbs) := by
  unfold samplerValue
  calc t * pNat ^ samplerDigits + enc < t * pNat ^ samplerDigits + pNat ^ samplerDigits := by omega
    _ = (t + 1) * pNat ^ samplerDigits := by ring
    _ ≤ 2 ^ (hiWidth + 256) * pNat ^ samplerDigits := Nat.mul_le_mul_right _ tSmall
    _ < 2 ^ (hiWidth + 256) * 2 ^ (254 * samplerDigits) :=
        Nat.mul_lt_mul_of_pos_left pow_samplerDigits_lt (Nat.two_pow_pos _)
    _ = 2 ^ (hiWidth + 256 + 254 * samplerDigits) := by rw [← Nat.pow_add]
    _ ≤ 2 ^ (256 * samplerLimbs) :=
        Nat.pow_le_pow_right (by norm_num) (by unfold hiWidth samplerDigits samplerLimbs; norm_num)

/-- **The machine's test is the acceptance predicate**: the top working limb of
`t · p^364 + enc` is `0` iff `enc + p^364 · t < 2^92672`. -/
theorem acceptTop_eq (enc t : Nat) (encSmall : enc < pNat ^ samplerDigits)
    (tSmall : t < 2 ^ (hiWidth + 256)) :
    acceptTop samplerLimbs samplerDigits enc t = samplerAccept enc t := by
  have fits := samplerValue_lt enc t encSmall tSmall
  have exponent : 256 * samplerLimbs = 256 + 256 * (samplerLimbs - 1) := by
    unfold samplerLimbs; norm_num
  have split : 2 ^ (256 * samplerLimbs) = 2 ^ 256 * 2 ^ (256 * (samplerLimbs - 1)) := by
    rw [exponent, Nat.pow_add]
  unfold acceptTop samplerAccept
  rw [decide_eq_decide]
  unfold limb
  rw [Nat.mod_eq_of_lt (by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← split]; exact fits),
    Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
  unfold samplerValue
  rw [Nat.add_comm, Nat.mul_comm]

/-- Two acceptance tests that agree on the draws give the same bounded rejection. -/
theorem rejectLaw_congr (width : Nat) (first second : Nat → Bool)
    (same : ∀ value, value < 2 ^ width → first value = second value) (count : Nat) :
    rejectLaw width first count = rejectLaw width second count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [rejectLaw]
      congr 1
      funext value
      rw [same value.val value.isLt, ih]

/-- **The preimage sampler at the phase-4 parameters** (A1 §4 item 5): bounded rejection of
`363`-bit draws `t` accepted iff `enc + p^364 · t < 2^92672`, `80` attempts, the kept `t` mapped to
the halves of `V = enc + p^364 · t`. -/
theorem memSem_preimageSampler_A1 [BN254.FieldCertificate] (work yBase : Nat)
    (layout : SamplerLayout work samplerLimbs samplerDigits yBase) (memory : Memory)
    (digitValues : Nat → Nat) (digitsSmall : ∀ e, e < samplerDigits → digitValues e < pNat)
    (cellsIn : DigitsIn yBase samplerDigits digitValues memory) :
    (preimageSampler work samplerLimbs samplerDigits yBase samplerAttempts).memSem memory =
      (rejectLaw (hiWidth + 256) (samplerAccept (encNat digitValues samplerDigits))
          samplerAttempts).map
        (Option.map (samplerFinal work samplerLimbs samplerDigits
          (encNat digitValues samplerDigits) memory)) := by
  rw [memSem_preimageSampler work samplerLimbs samplerDigits yBase samplerAttempts layout memory
      digitValues digitsSmall cellsIn,
    rejectLaw_congr _ _ _ (fun t small => acceptTop_eq _ t
      (encNat_lt digitValues samplerDigits digitsSmall) small)]

/-- **On acceptance** `V = enc + p^364 · t < 2^92672` (the `362` programmed limbs hold `V`). -/
theorem kept_below (enc t : Nat)
    (member : some t ∈ (rejectLaw (hiWidth + 256) (samplerAccept enc) samplerAttempts).support) :
    enc + pNat ^ samplerDigits * t < 2 ^ 92672 ∧ t < 2 ^ 363 := by
  obtain ⟨accepted, small⟩ := kept_accepted _ _ _ _ member
  unfold samplerAccept at accepted
  have below := of_decide_eq_true accepted
  rw [samplerBoundary_eq] at below
  rw [samplerWidth_eq] at small
  exact ⟨below, small⟩

/-- The fibre bound on variables: from `B ≤ 2^w · P`, every `t` with `enc + P t < B` is below
`2^w`. -/
theorem fibre_below_generic (enc power bound width t : Nat) (key : bound ≤ 2 ^ width * power)
    (inFibre : enc + power * t < bound) : t < 2 ^ width := by
  by_contra big
  have scaled : power * 2 ^ width ≤ power * t := Nat.mul_le_mul_left _ (Nat.le_of_not_lt big)
  rw [Nat.mul_comm] at key
  generalize power * 2 ^ width = low at key scaled
  generalize power * t = high at scaled inFibre
  omega

/-- **The fibre lies below `2^363`**: every `t ∈ ℕ` with `enc + p^364 · t < 2^92672` has
`t < 2^363` (`T ≤ 2^363`), for every `enc`. -/
theorem fibre_below (enc t : Nat) (inFibre : enc + pNat ^ samplerDigits * t < 2 ^ 92672) :
    t < 2 ^ (hiWidth + 256) := by
  have key := preimageComplete_nat
  rw [show (363 : Nat) = hiWidth + 256 from rfl, show (364 : Nat) = samplerDigits from rfl] at key
  exact fibre_below_generic enc _ _ _ t key inFibre

/-- **The accepted `363`-bit draws are exactly the fibre** `{t : enc + p^364 · t < 2^92672}`. -/
theorem accepted_iff_fibre (enc t : Nat) :
    (samplerAccept enc t = true ∧ t < 2 ^ (hiWidth + 256)) ↔
      enc + pNat ^ samplerDigits * t < 2 ^ 92672 := by
  unfold samplerAccept
  simp only [decide_eq_true_eq]
  rw [samplerBoundary_eq]
  exact ⟨fun both => both.1, fun inFibre => ⟨inFibre, fibre_below enc t inFibre⟩⟩

/-- **Conditioned on acceptance, `t` is uniform on the whole fibre** (A1 §4 item 4): any two
`t, t' ∈ ℕ` with `enc + p^364 · t < 2^92672` have the same mass, for every `enc`. -/
theorem kept_uniform (enc first second : Nat)
    (firstIn : enc + pNat ^ samplerDigits * first < 2 ^ 92672)
    (secondIn : enc + pNat ^ samplerDigits * second < 2 ^ 92672) :
    rejectLaw (hiWidth + 256) (samplerAccept enc) samplerAttempts (some first) =
      rejectLaw (hiWidth + 256) (samplerAccept enc) samplerAttempts (some second) :=
  rejectLaw_uniform _ _ _ _ _ ((accepted_iff_fibre enc first).mpr firstIn)
    ((accepted_iff_fibre enc second).mpr secondIn)

/-- **No mass off the fibre.** -/
theorem kept_off (enc value : Nat)
    (outside : ¬ enc + pNat ^ samplerDigits * value < 2 ^ 92672) :
    rejectLaw (hiWidth + 256) (samplerAccept enc) samplerAttempts (some value) = 0 :=
  rejectLaw_off _ _ _ _ fun good => outside ((accepted_iff_fibre enc value).mp good)

/-- The counting argument behind the acceptance rate, on variables: if
`(7 · 2^w + 10) · P ≤ 10 · B` and `enc < P`, at most `3/10` of the `w`-bit draws `t` have
`enc + P t ≥ B`. -/
theorem rejectedCount_generic (enc power boundary width : Nat) (encSmall : enc < power)
    (wide : 4 ≤ 2 ^ width) (key : (7 * 2 ^ width + 10) * power ≤ 10 * boundary) :
    10 * rejectedCount width (fun t => decide (enc + power * t < boundary)) ≤ 3 * 2 ^ width := by
  unfold rejectedCount
  beta_reduce
  have accepts : ∀ value : Nat, 10 * value < 7 * 2 ^ width → enc + power * value < boundary := by
    intro value small
    have scaled : power * (10 * value + 1) ≤ power * (7 * 2 ^ width) :=
      Nat.mul_le_mul_left _ (by omega)
    have expand : power * (7 * 2 ^ width) + 10 * power = (7 * 2 ^ width + 10) * power := by ring
    have expand2 : power * (10 * value + 1) = 10 * (power * value) + power := by ring
    omega
  have thresholdSmall : (7 * 2 ^ width + 9) / 10 < 2 ^ width := by omega
  have subset : (Finset.univ.filter fun value : Fin (2 ^ width) =>
      decide (enc + power * value.val < boundary) = false) ⊆
        Finset.Ici ⟨(7 * 2 ^ width + 9) / 10, thresholdSmall⟩ := by
    intro value member
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_false_iff_not] at member
    simp only [Finset.mem_Ici, Fin.le_def]
    by_contra below
    exact member (accepts value.val (by omega))
  have card := Finset.card_le_card subset
  rw [Fin.card_Ici, Fin.val_mk] at card
  omega

/-- **At most `3/10` of the draws are rejected**, for every `enc < p^364`: the per-attempt
acceptance probability is at least `7/10`. -/
theorem rejectedCount_sampler (enc : Nat) (encSmall : enc < pNat ^ samplerDigits) :
    10 * rejectedCount (hiWidth + 256) (samplerAccept enc) ≤ 3 * 2 ^ (hiWidth + 256) := by
  have key := preimageAccept_nat
  rw [show (363 : Nat) = hiWidth + 256 from rfl, show (364 : Nat) = samplerDigits from rfl,
    show (92672 : Nat) = 256 * (samplerLimbs - 1) from rfl] at key
  have wide : 4 ≤ 2 ^ (hiWidth + 256) :=
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (hiWidth + 256) := Nat.pow_le_pow_right (by norm_num) (by decide)
  exact rejectedCount_generic enc (pNat ^ samplerDigits) (2 ^ (256 * (samplerLimbs - 1)))
    (hiWidth + 256) encSmall wide key

/-- `(3 total / 10)^80 · 2^138 ≤ total^80`, on a variable, from `3^80 · 2^138 ≤ 10^80`. -/
theorem abort_generic (total : Nat) :
    (3 * total / 10) ^ samplerAttempts * 2 ^ 138 ≤ total ^ samplerAttempts := by
  unfold samplerAttempts
  have scaled : (10 * (3 * total / 10)) ^ 80 ≤ (3 * total) ^ 80 :=
    Nat.pow_le_pow_left (Nat.mul_div_le _ _) 80
  rw [Nat.mul_pow, Nat.mul_pow] at scaled
  have small : 3 ^ 80 * 2 ^ 138 ≤ 10 ^ 80 := Nat.le_of_ble_eq_true rfl
  have chain : 10 ^ 80 * ((3 * total / 10) ^ 80 * 2 ^ 138) ≤ 10 ^ 80 * total ^ 80 :=
    calc 10 ^ 80 * ((3 * total / 10) ^ 80 * 2 ^ 138)
        = 10 ^ 80 * (3 * total / 10) ^ 80 * 2 ^ 138 := by ring
      _ ≤ 3 ^ 80 * total ^ 80 * 2 ^ 138 := Nat.mul_le_mul_right _ scaled
      _ = 3 ^ 80 * 2 ^ 138 * total ^ 80 := by ring
      _ ≤ 10 ^ 80 * total ^ 80 := Nat.mul_le_mul_right _ small
  exact Nat.le_of_mul_le_mul_left chain (by positivity)

/-- **The abort mass of the `80` attempts is below `2^-138`** (`(3/10)^80 ≈ 2^-138.97`), for every
`enc < p^364`. -/
theorem samplerAbort_le (enc : Nat) (encSmall : enc < pNat ^ samplerDigits) :
    rejectLaw (hiWidth + 256) (samplerAccept enc) samplerAttempts none ≤ ((2 : ENNReal) ^ 138)⁻¹ := by
  have rejected := rejectedCount_sampler enc encSmall
  exact (rejectLaw_none_le _ _ _ (3 * 2 ^ (hiWidth + 256) / 10) (by omega)).trans
    (ratio_pow_le (3 * 2 ^ (hiWidth + 256) / 10) (hiWidth + 256) samplerAttempts 138
      (abort_generic (2 ^ (hiWidth + 256))))

end BigInt

end Kriterion.ArgoMAC.PlanB.SimMachine
