/-
This file defines the phase-4 batched hash-vector sampler of Plan B (brief A1, sections 1.1 to 1.3)
and proves its combinatorial facts.

**The sampler.** One lane's whole switch-mask vector `Y ∈ F_p ^ n` comes from `k` hash answers at
once. Each answer is a pair of 128-bit blocks, read as a number below `2 ^ 256`; the `k` answers
are read as the mixed-radix number `V = limbsToNat k h < 2 ^ (256 k)`; and `Y` is the vector of the
`n` little-endian base-`p` digits of `V mod p ^ n`.

**The hash inputs.** Hash input `i` of the vector of `(lane, chunk, switch)` at `label` is
`scaleInput lane chunk switch i label`, a number below `2 ^ 150` whose fields are the label
(bits `0..127`), the limb `i` (`128..136`), the switch (`137..141`, radix `2 ^ chunkBits = 32` for
every chunk), and the pair (lane, chunk) as the mixed-radix digit `laneCode · 56 + chunk < 224`
(`142..149`). The bridge hash input `bridgeInput t` is moved to `[2 ^ 150, p)`, so it never meets
a scale input.

The definitions come first, exactly as the brief states them. Everything below the `LEMMAS`
marker is a proof about them, or a helper those proofs need. The tag and input lemmas are stated
generically in the chunk count `C` and the switch count `W`, so they hold for every profile.
-/

import Construction.PGS.Params
import Cryptography.Primitives

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-- The value of one hash answer: the little-endian number of its two blocks, below `2 ^ 256`. -/
def limbValue (a : Block × Block) : Nat := a.1.toNat + 2 ^ 128 * a.2.toNat

/-- The mixed-radix-`2 ^ 128` number `V` of `k` hash answers, below `2 ^ (256 k)`. -/
def limbsToNat (k : Nat) (h : Fin k → Block × Block) : Nat :=
  ∑ i : Fin k, limbValue (h i) * 2 ^ (256 * i.val)

/-- Little-endian base-p digits of `V mod p^n`; the `ZMod` cast does the final `mod p`. -/
def sampleLane (n k : Nat) (h : Fin k → Block × Block) : Fin n → BaseField :=
  fun e => ((limbsToNat k h / baseFieldModulus ^ e.val : Nat) : BaseField)

/-- The number `k` of hash answers per mask vector of each lane. -/
def limbCount : Lane → Nat
  | .curveX => 4
  | .curveY => 3
  | .pointX => 452
  | .pointY => 272

/-- Every lane's limb count fits the scale tag's `512`-limb radix, so the `limb % 512` clamp of
`scaleInput` is the identity at every limb the sampler asks. -/
theorem limbCount_lt (lane : Lane) : limbCount lane < 512 := by
  cases lane <;> decide

/-- The lane's code in the scale tag. It replaces the former `Seed.laneCode`. -/
def laneCode : Lane → Nat
  | .curveX => 0
  | .curveY => 1
  | .pointX => 2
  | .pointY => 3

/-- The mixed-radix scale tag for `C` chunks of `W` switches each. -/
def scaleTagWith (C W : Nat) (lane : Lane) (chunk switch limb : Nat) : Nat :=
  ((laneCode lane * C + chunk) * W + switch) * 512 + limb

/-- The scale tag of one hash input: (lane, chunk, switch, limb) in mixed radix. -/
def scaleTag (lane : Lane) (chunk switch limb : Nat) : Nat :=
  scaleTagWith chunkCount (2 ^ chunkBits) lane chunk switch limb

/-- Hash input `limb` of the mask vector of `(lane, chunk, switch)` at `label`: the label in the
low 128 bits and the scale tag above it. -/
def scaleInput (lane : Lane) (chunk : Fin chunkCount) (switch limb : Nat) (label : Block) :
    BaseField :=
  ((label.toNat + 2 ^ 128 * scaleTag lane chunk.val (switch % 2 ^ chunkBits) (limb % 512) : Nat) :
    BaseField)

/-- Every scale input lies below `2 ^ 150 = 2 ^ 128 * 2 ^ 22`: its tag is below
`4 * 56 * 32 * 512 = 3,670,016 < 2 ^ 22`. -/
def scaleRange : Nat := 2 ^ 150

/-- The bridge hash input: `t` moved out of the scale range `[0, 2 ^ 150)`. -/
def bridgeInput (t : BaseField) : BaseField :=
  if t.val < scaleRange then t + (scaleRange : BaseField) else t

-- LEMMAS

/-! ## One hash answer -/

/-- One hash answer carries 256 bits. -/
theorem limbValue_lt (a : Block × Block) : limbValue a < 2 ^ 256 := by
  have first := a.1.isLt
  have second := a.2.isLt
  unfold limbValue
  omega

/-- The hash answer carrying a number below `2 ^ 256` (the number's low 256 bits). -/
def limbOfNat (value : Nat) : Block × Block :=
  (BitVec.ofNat 128 value, BitVec.ofNat 128 (value / 2 ^ 128))

theorem limbValue_limbOfNat (value : Nat) : limbValue (limbOfNat value) = value % 2 ^ 256 := by
  simp only [limbValue, limbOfNat, BitVec.toNat_ofNat]
  omega

/-- `limbOfNat` reads only the low 256 bits. -/
theorem limbOfNat_add_mul (low high : Nat) :
    limbOfNat (low + 2 ^ 256 * high) = limbOfNat low := by
  simp only [limbOfNat, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem limbOfNat_limbValue (a : Block × Block) : limbOfNat (limbValue a) = a := by
  obtain ⟨first, second⟩ := a
  have firstLt := first.isLt
  have secondLt := second.isLt
  simp only [limbOfNat, limbValue, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat] <;> omega

/-! ## `k` hash answers: the bijection with `[0, 2 ^ (256 k))` -/

/-- The mixed-radix recursion: the first answer is the low 256 bits. -/
theorem limbsToNat_succ (k : Nat) (h : Fin (k + 1) → Block × Block) :
    limbsToNat (k + 1) h = limbValue (h 0) + 2 ^ 256 * limbsToNat k (fun i => h i.succ) := by
  rw [limbsToNat, limbsToNat, Fin.sum_univ_succ, Finset.mul_sum, Fin.val_zero, Nat.mul_zero,
    Nat.pow_zero, Nat.mul_one]
  refine congrArg (limbValue (h 0) + ·) (Finset.sum_congr rfl fun i _ => ?_)
  rw [Fin.val_succ, Nat.mul_add, Nat.mul_one, Nat.pow_add]
  ring

/-- `V < 2 ^ (256 k)`. -/
theorem limbsToNat_lt (k : Nat) (h : Fin k → Block × Block) : limbsToNat k h < 2 ^ (256 * k) := by
  induction k with
  | zero => simp [limbsToNat]
  | succ k ih =>
      rw [limbsToNat_succ, mul_add, mul_one, pow_add]
      have low := limbValue_lt (h 0)
      have rest := ih (fun i => h i.succ)
      generalize limbsToNat k (fun i => h i.succ) = tail at rest ⊢
      generalize 2 ^ (256 * k) = bound at rest ⊢
      generalize limbValue (h 0) = head at low ⊢
      omega

/-- The `k` hash answers of a number: answer `i` carries bits `256 i .. 256 i + 255`. -/
def natToLimbs (k value : Nat) : Fin k → Block × Block :=
  fun i => limbOfNat (value / 2 ^ (256 * i.val))

theorem natToLimbs_zero_index (k value : Nat) :
    natToLimbs (k + 1) value 0 = limbOfNat value := by
  simp [natToLimbs]

theorem natToLimbs_succ (k value : Nat) (i : Fin k) :
    natToLimbs (k + 1) value i.succ = natToLimbs k (value / 2 ^ 256) i := by
  unfold natToLimbs
  rw [Nat.div_div_eq_div_mul, ← pow_add, Fin.val_succ]
  have exponent : 256 * (i.val + 1) = 256 + 256 * i.val := by ring
  rw [exponent]

/-- Reading the answers of `V` back gives `V mod 2 ^ (256 k)`. -/
theorem limbsToNat_natToLimbs (k value : Nat) :
    limbsToNat k (natToLimbs k value) = value % 2 ^ (256 * k) := by
  induction k generalizing value with
  | zero => simp [limbsToNat, Nat.mod_one]
  | succ k ih =>
      rw [limbsToNat_succ]
      have tail : (fun i : Fin k => natToLimbs (k + 1) value i.succ)
          = natToLimbs k (value / 2 ^ 256) := funext (natToLimbs_succ k value)
      rw [tail, ih, natToLimbs_zero_index, limbValue_limbOfNat, mul_add, mul_one, pow_add,
        mul_comm (2 ^ (256 * k)), Nat.mod_mul]

/-- Decomposing `V` recovers the answers. -/
theorem natToLimbs_limbsToNat (k : Nat) (h : Fin k → Block × Block) :
    natToLimbs k (limbsToNat k h) = h := by
  induction k with
  | zero => exact funext fun i => i.elim0
  | succ k ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [natToLimbs_zero_index, limbsToNat_succ, limbOfNat_add_mul, limbOfNat_limbValue]
      · rw [natToLimbs_succ, limbsToNat_succ]
        have low := limbValue_lt (h 0)
        have drop : (limbValue (h 0) + 2 ^ 256 * limbsToNat k (fun i => h i.succ)) / 2 ^ 256
            = limbsToNat k (fun i => h i.succ) := by
          generalize limbsToNat k (fun i => h i.succ) = tail
          generalize limbValue (h 0) = head at low ⊢
          omega
        rw [drop, ih]

/-- **The limb bijection.** `k` hash answers are exactly the numbers below `2 ^ (256 k)`, in mixed
radix `2 ^ 128` (two blocks per answer). -/
def limbsEquiv (k : Nat) : (Fin k → Block × Block) ≃ Fin (2 ^ (256 * k)) where
  toFun h := ⟨limbsToNat k h, limbsToNat_lt k h⟩
  invFun value := natToLimbs k value.val
  left_inv h := natToLimbs_limbsToNat k h
  right_inv value := Fin.ext (by
    show limbsToNat k (natToLimbs k value.val) = value.val
    rw [limbsToNat_natToLimbs, Nat.mod_eq_of_lt value.isLt])

/-- Every number below `2 ^ (256 k)` is the number of some `k` answers. -/
theorem limbsToNat_natToLimbs_of_lt (k value : Nat) (small : value < 2 ^ (256 * k)) :
    limbsToNat k (natToLimbs k value) = value := by
  rw [limbsToNat_natToLimbs, Nat.mod_eq_of_lt small]

/-! ## Base-`p` digits -/

theorem baseFieldModulus_pos : 0 < baseFieldModulus :=
  Nat.pos_of_ne_zero (NeZero.ne baseFieldModulus)

theorem baseFieldModulus_pow_pos (n : Nat) : 0 < baseFieldModulus ^ n :=
  pow_pos baseFieldModulus_pos n

/-- The first `n` little-endian base-`p` digits of a number, each cast into the field. -/
def laneDigits (n value : Nat) : Fin n → BaseField :=
  fun e => ((value / baseFieldModulus ^ e.val : Nat) : BaseField)

theorem sampleLane_eq_laneDigits (n k : Nat) (h : Fin k → Block × Block) :
    sampleLane n k h = laneDigits n (limbsToNat k h) := rfl

/-- The vector's digits as `Fin p` digits. -/
def laneFinDigits {n : Nat} (vector : Fin n → BaseField) : Fin n → Fin baseFieldModulus :=
  fun e => ⟨(vector e).val, ZMod.val_lt (vector e)⟩

/-- The base-`p` number `enc(Y) = Σ_e Y_e.val · p ^ e` of a vector. -/
def laneEncode {n : Nat} (vector : Fin n → BaseField) : Nat :=
  ∑ e : Fin n, (vector e).val * baseFieldModulus ^ e.val

theorem laneEncode_eq {n : Nat} (vector : Fin n → BaseField) :
    laneEncode vector = (finFunctionFinEquiv (laneFinDigits vector) : Nat) := by
  rw [finFunctionFinEquiv_apply]
  rfl

theorem laneEncode_lt {n : Nat} (vector : Fin n → BaseField) :
    laneEncode vector < baseFieldModulus ^ n := by
  rw [laneEncode_eq]
  exact (finFunctionFinEquiv (laneFinDigits vector)).isLt

/-- Digit `e` of `enc(Y)` is `Y_e`. -/
theorem laneEncode_digit {n : Nat} (vector : Fin n → BaseField) (e : Fin n) :
    laneEncode vector / baseFieldModulus ^ e.val % baseFieldModulus = (vector e).val := by
  have key := congrArg (fun digits => (digits e : Nat))
    (finFunctionFinEquiv.symm_apply_apply (laneFinDigits vector))
  simp only [finFunctionFinEquiv_symm_apply_val] at key
  rw [laneEncode_eq]
  exact key

/-- Digit `e < n` of `V` is digit `e` of `V mod p ^ n`. -/
theorem digit_mod_pow (value n e : Nat) (small : e < n) :
    value % baseFieldModulus ^ n / baseFieldModulus ^ e % baseFieldModulus
      = value / baseFieldModulus ^ e % baseFieldModulus := by
  have split : baseFieldModulus ^ n = baseFieldModulus ^ e * baseFieldModulus ^ (n - e) := by
    rw [← pow_add, Nat.add_sub_cancel' small.le]
  rw [split, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact dvd_pow_self _ (by omega)

/-- The digits of `V` are the digits of `V mod p ^ n`. -/
theorem laneDigits_mod (n value : Nat) :
    laneDigits n (value % baseFieldModulus ^ n) = laneDigits n value := by
  funext e
  simp only [laneDigits]
  rw [ZMod.natCast_eq_natCast_iff']
  exact digit_mod_pow value n e.val e.isLt

theorem laneDigits_laneEncode {n : Nat} (vector : Fin n → BaseField) :
    laneDigits n (laneEncode vector) = vector := by
  funext e
  simp only [laneDigits]
  rw [← ZMod.natCast_mod, laneEncode_digit, ZMod.natCast_zmod_val]

/-- Two numbers below `p ^ n` with the same digits are equal. -/
theorem laneDigits_injOn {n first second : Nat} (firstLt : first < baseFieldModulus ^ n)
    (secondLt : second < baseFieldModulus ^ n) (same : laneDigits n first = laneDigits n second) :
    first = second := by
  have digits : ∀ e : Fin n, first / baseFieldModulus ^ e.val % baseFieldModulus
      = second / baseFieldModulus ^ e.val % baseFieldModulus := fun e =>
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp (congrFun same e)
  have symmEq : (finFunctionFinEquiv (m := baseFieldModulus) (n := n)).symm ⟨first, firstLt⟩
      = (finFunctionFinEquiv (m := baseFieldModulus) (n := n)).symm ⟨second, secondLt⟩ := by
    funext e
    apply Fin.ext
    simp only [finFunctionFinEquiv_symm_apply_val]
    exact digits e
  exact congrArg Fin.val ((finFunctionFinEquiv (m := baseFieldModulus) (n := n)).symm.injective
    symmEq)

/-- **The digit fibre.** `V` has digits `Y` exactly when `V mod p ^ n = enc(Y)`. -/
theorem laneDigits_eq_iff {n value : Nat} (vector : Fin n → BaseField) :
    laneDigits n value = vector ↔ value % baseFieldModulus ^ n = laneEncode vector := by
  constructor
  · intro same
    refine laneDigits_injOn (Nat.mod_lt _ (baseFieldModulus_pow_pos n)) (laneEncode_lt vector) ?_
    rw [laneDigits_mod, same, laneDigits_laneEncode]
  · intro same
    rw [← laneDigits_mod, same, laneDigits_laneEncode]

/-- **The sampler's fibre.** `h` samples `Y` exactly when `V(h) mod p ^ n = enc(Y)`; through
`limbsEquiv`, the fibre is `{enc(Y) + p ^ n · t < 2 ^ (256 k)}`. -/
theorem sampleLane_eq_iff (n k : Nat) (h : Fin k → Block × Block) (vector : Fin n → BaseField) :
    sampleLane n k h = vector ↔ limbsToNat k h % baseFieldModulus ^ n = laneEncode vector :=
  laneDigits_eq_iff vector

/-- The answers the simulator programs for a number `V < 2 ^ (256 k)` sample `V`'s digits. -/
theorem sampleLane_natToLimbs (n k value : Nat) (small : value < 2 ^ (256 * k)) :
    sampleLane n k (natToLimbs k value) = laneDigits n value := by
  rw [sampleLane_eq_laneDigits, limbsToNat_natToLimbs_of_lt k value small]

/-- The sampler is onto as soon as `p ^ n ≤ 2 ^ (256 k)`: `natToLimbs k (enc Y)` samples `Y`. -/
theorem sampleLane_surjective (n k : Nat) (big : baseFieldModulus ^ n ≤ 2 ^ (256 * k)) :
    Function.Surjective (sampleLane n k) := by
  intro vector
  refine ⟨natToLimbs k (laneEncode vector), ?_⟩
  rw [sampleLane_natToLimbs n k _ (lt_of_lt_of_le (laneEncode_lt vector) big),
    laneDigits_laneEncode]

/-- `p ^ n ≤ 2 ^ (254 n)`, from `p < 2 ^ 254`; no power is evaluated. -/
theorem baseFieldModulus_pow_le_two_pow (n : Nat) : baseFieldModulus ^ n ≤ 2 ^ (254 * n) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (le_of_lt baseFieldModulus_lt_two_pow) n

/-- The sampler is onto whenever `254 n ≤ 256 k` (all four lanes). -/
theorem sampleLane_surjective_of_le (n k : Nat) (exponents : 254 * n ≤ 256 * k) :
    Function.Surjective (sampleLane n k) :=
  sampleLane_surjective n k (le_trans (baseFieldModulus_pow_le_two_pow n)
    (Nat.pow_le_pow_right (by norm_num) exponents))

/-! ## The iterative digit extraction -/

/-- The iterative digit extraction: `Y_0 = V mod p`, then the rest from `V / p`. -/
def sampleLaneIter : (n : Nat) → Nat → Fin n → BaseField
  | 0, _ => Fin.elim0
  | n + 1, value =>
      Fin.cons ((value % baseFieldModulus : Nat) : BaseField)
        (sampleLaneIter n (value / baseFieldModulus))

theorem sampleLaneIter_eq (n value : Nat) : sampleLaneIter n value = laneDigits n value := by
  induction n generalizing value with
  | zero => exact funext fun e => e.elim0
  | succ n ih =>
      funext e
      refine Fin.cases ?_ (fun j => ?_) e
      · simp only [sampleLaneIter, Fin.cons_zero, laneDigits, Fin.val_zero, pow_zero,
          Nat.div_one, ZMod.natCast_mod]
      · simp only [sampleLaneIter, Fin.cons_succ, ih, laneDigits, Fin.val_succ, pow_succ',
          Nat.div_div_eq_div_mul]

/-- **Iterative = closed form.** Extracting `Y_e = V_e mod p`, `V_{e+1} = V_e / p` from
`V = limbsToNat k h` gives `sampleLane n k h`. -/
theorem sampleLane_iter_eq (n k : Nat) (h : Fin k → Block × Block) :
    sampleLaneIter n (limbsToNat k h) = sampleLane n k h :=
  sampleLaneIter_eq n _

/-! ## Scale tags -/

theorem laneCode_lt (lane : Lane) : laneCode lane < 4 := by
  cases lane <;> decide

theorem laneCode_injective : Function.Injective laneCode := by
  intro first second same
  cases first <;> cases second <;> first | rfl | exact absurd same (by decide)

/-- Mixed radix, the bound: `a * B + b < A * B` for `a < A` and `b < B`. -/
theorem mixedRadix_lt {a b A B : Nat} (aLt : a < A) (bLt : b < B) : a * B + b < A * B :=
  calc a * B + b < a * B + B := by omega
    _ = (a + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right _ aLt

/-- Mixed radix, uniqueness. -/
theorem mixedRadix_inj {a b a' b' B : Nat} (bLt : b < B) (bLt' : b' < B)
    (same : a * B + b = a' * B + b') : a = a' ∧ b = b' := by
  have low : b = b' := by
    have first : (a * B + b) % B = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt bLt]
    have second : (a' * B + b') % B = b' := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt bLt']
    rw [← first, same, second]
  subst low
  exact ⟨Nat.eq_of_mul_eq_mul_right (m := B) (by omega) (by omega), rfl⟩

/-- The exact tag bound: `4 · C · W · 512` tags. -/
theorem scaleTagWith_lt_mul {C W : Nat} (lane : Lane) {chunk switch limb : Nat}
    (chunkLt : chunk < C) (switchLt : switch < W) (limbLt : limb < 512) :
    scaleTagWith C W lane chunk switch limb < 4 * C * W * 512 := by
  unfold scaleTagWith
  exact mixedRadix_lt (mixedRadix_lt (mixedRadix_lt (laneCode_lt lane) chunkLt) switchLt) limbLt

theorem four_mul_le_of_mul_le {C W : Nat} (area : C * W ≤ 64 * 32) :
    4 * C * W * 512 ≤ 4 * 64 * 32 * 512 := by
  have step : 4 * (C * W) * 512 ≤ 4 * (64 * 32) * 512 :=
    Nat.mul_le_mul_right 512 (Nat.mul_le_mul_left 4 area)
  simpa only [Nat.mul_assoc] using step

/-- **The tag bound** under the product hypothesis `C * W ≤ 64 * 32`, which the profile
(`56 * 32`) meets. -/
theorem scaleTagWith_lt_of_mul_le {C W : Nat} (area : C * W ≤ 64 * 32) (lane : Lane)
    {chunk switch limb : Nat} (chunkLt : chunk < C) (switchLt : switch < W) (limbLt : limb < 512) :
    scaleTagWith C W lane chunk switch limb < 4 * 64 * 32 * 512 :=
  lt_of_lt_of_le (scaleTagWith_lt_mul lane chunkLt switchLt limbLt) (four_mul_le_of_mul_le area)

/-- **Tag injectivity**, on `(lane, chunk < C, switch < W, limb < 512)`. -/
theorem scaleTagWith_injective {C W : Nat} {lane lane' : Lane}
    {chunk chunk' switch switch' limb limb' : Nat}
    (chunkLt : chunk < C) (chunkLt' : chunk' < C) (switchLt : switch < W) (switchLt' : switch' < W)
    (limbLt : limb < 512) (limbLt' : limb' < 512)
    (same : scaleTagWith C W lane chunk switch limb = scaleTagWith C W lane' chunk' switch' limb') :
    lane = lane' ∧ chunk = chunk' ∧ switch = switch' ∧ limb = limb' := by
  unfold scaleTagWith at same
  obtain ⟨upper, limbEq⟩ := mixedRadix_inj limbLt limbLt' same
  obtain ⟨middle, switchEq⟩ := mixedRadix_inj switchLt switchLt' upper
  obtain ⟨laneEq, chunkEq⟩ := mixedRadix_inj chunkLt chunkLt' middle
  exact ⟨laneCode_injective laneEq, chunkEq, switchEq, limbEq⟩

/-! ## Scale inputs -/

/-- `scaleInput` for `C` chunks of `W` switches each. -/
def scaleInputWith (C W : Nat) (lane : Lane) (chunk switch limb : Nat) (label : Block) :
    BaseField :=
  ((label.toNat + 2 ^ 128 * scaleTagWith C W lane chunk (switch % W) (limb % 512) : Nat) :
    BaseField)

/-- `2 ^ 150 < p`. -/
theorem two_pow_150_lt_baseFieldModulus : 2 ^ 150 < baseFieldModulus := by
  unfold baseFieldModulus
  norm_num

/-- `2 ^ 151 < p`: a scale input plus `2 ^ 150` never wraps. -/
theorem two_pow_151_lt_baseFieldModulus : 2 ^ 151 < baseFieldModulus := by
  unfold baseFieldModulus
  norm_num

theorem scaleRange_lt_baseFieldModulus : scaleRange < baseFieldModulus := by
  have big := two_pow_150_lt_baseFieldModulus
  unfold scaleRange
  omega

/-- The number a scale input carries is below `2 ^ 150`. -/
theorem scaleInputWith_nat_lt {C W : Nat} (area : C * W ≤ 64 * 32) (switchPos : 0 < W)
    (lane : Lane) {chunk : Nat} (chunkLt : chunk < C) (switch limb : Nat) (label : Block) :
    label.toNat + 2 ^ 128 * scaleTagWith C W lane chunk (switch % W) (limb % 512) < 2 ^ 150 := by
  have tag := scaleTagWith_lt_of_mul_le area lane chunkLt (Nat.mod_lt switch switchPos)
    (Nat.mod_lt limb (by norm_num))
  have labelLt := label.isLt
  generalize scaleTagWith C W lane chunk (switch % W) (limb % 512) = value at tag ⊢
  omega

/-- The cast into the field is exact: a scale input's value is its number. -/
theorem scaleInputWith_val {C W : Nat} (area : C * W ≤ 64 * 32) (switchPos : 0 < W)
    (lane : Lane) {chunk : Nat} (chunkLt : chunk < C) (switch limb : Nat) (label : Block) :
    (scaleInputWith C W lane chunk switch limb label).val
      = label.toNat + 2 ^ 128 * scaleTagWith C W lane chunk (switch % W) (limb % 512) := by
  have small := scaleInputWith_nat_lt area switchPos lane chunkLt switch limb label
  have range := scaleRange_lt_baseFieldModulus
  unfold scaleRange at range
  exact ZMod.val_cast_of_lt (by omega)

/-- **The scale-input bound**, under the product hypothesis. -/
theorem scaleInputWith_val_lt_of_mul_le {C W : Nat} (area : C * W ≤ 64 * 32) (switchPos : 0 < W)
    (lane : Lane) {chunk : Nat} (chunkLt : chunk < C) (switch limb : Nat) (label : Block) :
    (scaleInputWith C W lane chunk switch limb label).val < 2 ^ 150 := by
  rw [scaleInputWith_val area switchPos lane chunkLt]
  exact scaleInputWith_nat_lt area switchPos lane chunkLt switch limb label

/-- **Scale-input injectivity**, under the product hypothesis, on
`(lane, chunk < C, switch < W, limb < 512, label)`. -/
theorem scaleInputWith_injective_of_mul_le {C W : Nat} (area : C * W ≤ 64 * 32)
    {lane lane' : Lane} {chunk chunk' switch switch' limb limb' : Nat} {label label' : Block}
    (chunkLt : chunk < C) (chunkLt' : chunk' < C) (switchLt : switch < W) (switchLt' : switch' < W)
    (limbLt : limb < 512) (limbLt' : limb' < 512)
    (same : scaleInputWith C W lane chunk switch limb label
      = scaleInputWith C W lane' chunk' switch' limb' label') :
    lane = lane' ∧ chunk = chunk' ∧ switch = switch' ∧ limb = limb' ∧ label = label' := by
  have switchPos : 0 < W := by omega
  have values := congrArg ZMod.val same
  rw [scaleInputWith_val area switchPos lane chunkLt,
    scaleInputWith_val area switchPos lane' chunkLt', Nat.mod_eq_of_lt switchLt,
    Nat.mod_eq_of_lt switchLt', Nat.mod_eq_of_lt limbLt, Nat.mod_eq_of_lt limbLt',
    Nat.add_comm label.toNat, Nat.add_comm label'.toNat, Nat.mul_comm (2 ^ 128),
    Nat.mul_comm (2 ^ 128)] at values
  obtain ⟨tagEq, labelEq⟩ := mixedRadix_inj label.isLt label'.isLt values
  obtain ⟨laneEq, chunkEq, switchEq, limbEq⟩ :=
    scaleTagWith_injective chunkLt chunkLt' switchLt switchLt' limbLt limbLt' tagEq
  exact ⟨laneEq, chunkEq, switchEq, limbEq, BitVec.eq_of_toNat_eq labelEq⟩

/-! ### The concrete profile

The profile (`56` chunks of at most `32` switches) meets `chunkCount * 2 ^ chunkBits ≤ 64 * 32`,
so the generic lemmas above apply at `C = chunkCount`, `W = 2 ^ chunkBits`. -/

theorem chunkCount_mul_twoPowChunkBits_le : chunkCount * 2 ^ chunkBits ≤ 64 * 32 := by
  unfold chunkCount chunkBits
  norm_num

theorem scaleTag_lt (lane : Lane) {chunk switch limb : Nat} (chunkLt : chunk < chunkCount)
    (switchLt : switch < 2 ^ chunkBits) (limbLt : limb < 512) :
    scaleTag lane chunk switch limb < 4 * 64 * 32 * 512 :=
  scaleTagWith_lt_of_mul_le chunkCount_mul_twoPowChunkBits_le lane chunkLt switchLt limbLt

theorem scaleInput_val (lane : Lane) (chunk : Fin chunkCount) (switch limb : Nat) (label : Block) :
    (scaleInput lane chunk switch limb label).val
      = label.toNat + 2 ^ 128 * scaleTag lane chunk.val (switch % 2 ^ chunkBits) (limb % 512) :=
  scaleInputWith_val chunkCount_mul_twoPowChunkBits_le (Nat.two_pow_pos chunkBits) lane chunk.isLt switch
    limb label

/-- **`scaleInput_val_lt`**: every scale input is below `2 ^ 150`. -/
theorem scaleInput_val_lt (lane : Lane) (chunk : Fin chunkCount) (switch limb : Nat)
    (label : Block) : (scaleInput lane chunk switch limb label).val < 2 ^ 150 :=
  scaleInputWith_val_lt_of_mul_le chunkCount_mul_twoPowChunkBits_le (Nat.two_pow_pos chunkBits) lane
    chunk.isLt switch limb label

theorem scaleInput_val_lt_scaleRange (lane : Lane) (chunk : Fin chunkCount) (switch limb : Nat)
    (label : Block) : (scaleInput lane chunk switch limb label).val < scaleRange :=
  scaleInput_val_lt lane chunk switch limb label

/-- **`scaleInput_injective`**: distinct `(lane, chunk, switch < 2 ^ chunkBits, limb < 512, label)`
never share a hash input. -/
theorem scaleInput_injective {lane lane' : Lane} {chunk chunk' : Fin chunkCount}
    {switch switch' limb limb' : Nat} {label label' : Block}
    (switchLt : switch < 2 ^ chunkBits) (switchLt' : switch' < 2 ^ chunkBits)
    (limbLt : limb < 512) (limbLt' : limb' < 512)
    (same : scaleInput lane chunk switch limb label = scaleInput lane' chunk' switch' limb' label') :
    lane = lane' ∧ chunk = chunk' ∧ switch = switch' ∧ limb = limb' ∧ label = label' := by
  obtain ⟨laneEq, chunkEq, switchEq, limbEq, labelEq⟩ :=
    scaleInputWith_injective_of_mul_le chunkCount_mul_twoPowChunkBits_le chunk.isLt chunk'.isLt
      switchLt switchLt' limbLt limbLt' same
  exact ⟨laneEq, Fin.ext chunkEq, switchEq, limbEq, labelEq⟩

/-! ## The bridge input -/

/-- The bridge input's value: `t + 2 ^ 150` on the scale range, `t` above it. -/
theorem bridgeInput_val (t : BaseField) :
    (bridgeInput t).val = if t.val < scaleRange then t.val + scaleRange else t.val := by
  unfold bridgeInput
  split_ifs with low
  · have big := two_pow_151_lt_baseFieldModulus
    rw [ZMod.val_add, ZMod.val_cast_of_lt scaleRange_lt_baseFieldModulus]
    refine Nat.mod_eq_of_lt ?_
    unfold scaleRange at low ⊢
    omega
  · rfl

/-- **`bridgeInput_val_ge`**: the bridge input is never in the scale range. -/
theorem bridgeInput_val_ge (t : BaseField) : 2 ^ 150 ≤ (bridgeInput t).val := by
  rw [bridgeInput_val]
  unfold scaleRange
  split_ifs with low <;> omega

theorem scaleRange_le_bridgeInput_val (t : BaseField) : scaleRange ≤ (bridgeInput t).val :=
  bridgeInput_val_ge t

/-- **Disjointness.** No bridge input is a scale input. -/
theorem bridgeInput_ne_scaleInput (t : BaseField) (lane : Lane) (chunk : Fin chunkCount)
    (switch limb : Nat) (label : Block) :
    bridgeInput t ≠ scaleInput lane chunk switch limb label := by
  intro same
  have high := bridgeInput_val_ge t
  have low := scaleInput_val_lt lane chunk switch limb label
  rw [same] at high
  omega

/-- On each branch, `bridgeInput` is injective. -/
theorem bridgeInput_branch_injective {t t' : BaseField} (same : bridgeInput t = bridgeInput t')
    (branch : (t.val < scaleRange ↔ t'.val < scaleRange)) : t = t' := by
  unfold bridgeInput at same
  by_cases low : t.val < scaleRange
  · rw [if_pos low, if_pos (branch.mp low)] at same
    exact add_right_cancel same
  · rw [if_neg low, if_neg (fun low' => low (branch.mpr low'))] at same
    exact same

/-- **`bridgeInput_fibre_card_le_two`**: every value has at most two bridge preimages. -/
theorem bridgeInput_fibre_card_le_two (key : BaseField) :
    Fintype.card {t : BaseField // bridgeInput t = key} ≤ 2 := by
  let branch : {t : BaseField // bridgeInput t = key} → Bool :=
    fun t => decide (t.1.val < scaleRange)
  have injective : Function.Injective branch := by
    intro first second same
    refine Subtype.ext (bridgeInput_branch_injective (first.2.trans second.2.symm) ?_)
    simpa only [branch, decide_eq_decide] using same
  simpa using Fintype.card_le_of_injective branch injective

/-- The fibre bound as a filter count. -/
theorem bridgeInput_filter_card_le_two (key : BaseField) :
    (Finset.univ.filter fun t : BaseField => bridgeInput t = key).card ≤ 2 := by
  rw [← Fintype.card_subtype]
  exact bridgeInput_fibre_card_le_two key

end Kriterion.ArgoMAC.PlanB
