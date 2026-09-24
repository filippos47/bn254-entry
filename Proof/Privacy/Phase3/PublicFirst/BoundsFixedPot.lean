/-
**Phase 3, P1m — (B1) the fixed-key part: three potentials.**

A forward lazy question at a permutation index draws its answer uniformly among the unused outputs;
each potential below is not raised in expectation by any forward question (`*_step`, lifted to the
lazy state by `fixed_lift_step`, `fixedAll_lift_step`, `enc_lift_step`), reads only the fixed-key or
only the EncPRF part (so the refill run's consumed questions and the designated installation, which
are hash programs, leave it unchanged), and bounds the corresponding indicator at a state with the
right number of pairs:

* `singleF y` — the mass with which `y` becomes the (only) output of a permutation: `1/2^128`
  before the first pair, the indicator after, `0` beyond;
* `xorF idx J z` — the mass with which the (only) outputs at the indices `idx p`, `p ∈ J`, xor to
  `z`: `1/2^128` until all are drawn, the indicator after, `0` beyond one pair at any (the fold
  material of a level of a `bin-to-hot` fold is such a xor, at every chunk width);
* `padF w t` — the mass with which an EncPRF permutation maps `w` to `t`: `1/(2^128 − 1)` while `w`
  is unasked and at most one other input is, the indicator after (at most two pairs), `0` beyond.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsEncBound

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (LState Request)
open scoped ENNReal

noncomputable section

/-! ### One fresh forward answer -/

section Perm

/-- `1/2^128`. -/
abbrev delta : ℝ≥0∞ := ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹

/-- A fresh answer at a permutation with `n` pairs hits a point with mass `≤ 1/(2^128 − n)`. -/
theorem fresh_hit_le (S : SparsePermutation (2 ^ 128)) [Nonempty (Unknown S)] (y : Fin (2 ^ 128)) :
    ∑' out : Unknown S, PMF.uniformOfFintype (Unknown S) out * ind (out.val = y) ≤
      ((2 ^ 128 - S.used : ℕ) : ℝ≥0∞)⁻¹ :=
  unknown_single_le S y

theorem fresh_hit_le_delta (S : SparsePermutation (2 ^ 128)) [Nonempty (Unknown S)]
    (zero : S.used = 0) (y : Fin (2 ^ 128)) :
    ∑' out : Unknown S, PMF.uniformOfFintype (Unknown S) out * ind (out.val = y) ≤ delta := by
  refine le_trans (fresh_hit_le S y) (le_of_eq ?_)
  rw [zero, Nat.sub_zero]

theorem fresh_hit_le_eps (S : SparsePermutation (2 ^ 128)) [Nonempty (Unknown S)]
    (small : S.used ≤ 1) (y : Fin (2 ^ 128)) :
    ∑' out : Unknown S, PMF.uniformOfFintype (Unknown S) out * ind (out.val = y) ≤ epsOne := by
  refine le_trans (fresh_hit_le S y) (ENNReal.inv_le_inv.mpr ?_)
  exact_mod_cast Nat.sub_le_sub_left small _

/-- **The effect of a forward question on one permutation**: a stored input changes nothing; a new
one adds one pair with a uniform unused output. -/
theorem perm_step (F : SparsePermutation (2 ^ 128) → ℝ≥0∞) (S : SparsePermutation (2 ^ 128))
    (x : Fin (2 ^ 128))
    (fresh : ∀ (_ : ¬ S.knownInput x) (room : S.used < 2 ^ 128) [Nonempty (Unknown S)],
      ∑' out : Unknown S, PMF.uniformOfFintype (Unknown S) out *
        F (S.extend room (S.input.symm x) (S.output.symm out.val)) ≤ F S) :
    ∑' answer, (S.forward x).distribution answer * F answer.2 ≤ F S := by
  by_cases known : S.knownInput x
  · have pure : (S.forward x).distribution = PMF.pure (S.output (S.input.symm x), S) := by
      unfold SparsePermutation.forward
      simp only [SparsePermutation.knownInput] at known
      rw [dif_pos known]
      rfl
    rw [pure, tsum_pure_mul]
  · obtain ⟨room, nonempty, law⟩ := forward_fresh_eq S x known
    rw [law, tsum_map_mul]
    exact fresh known room

/-- A permutation with one pair knows exactly one output. -/
theorem knownOutput_one (S : SparsePermutation (2 ^ 128)) (one : S.used = 1) (b : Fin (2 ^ 128)) :
    S.knownOutput b ↔ b = S.output ⟨0, Nat.two_pow_pos 128⟩ := by
  unfold SparsePermutation.knownOutput
  rw [one]
  constructor
  · intro small
    have zero : S.output.symm b = ⟨0, Nat.two_pow_pos 128⟩ := Fin.ext (Nat.lt_one_iff.mp small)
    rw [← zero, Equiv.apply_symm_apply]
  · rintro rfl
    rw [Equiv.symm_apply_apply]
    exact Nat.zero_lt_one

theorem knownInput_extend (S : SparsePermutation (2 ^ 128)) (x y : Fin (2 ^ 128))
    (freshX : ¬ S.knownInput x) (freshY : ¬ S.knownOutput y) (room : S.used < 2 ^ 128)
    (z : Fin (2 ^ 128)) :
    (S.extend room (S.input.symm x) (S.output.symm y)).knownInput z ↔ S.knownInput z ∨ z = x := by
  rw [knownInput_iff, knownInput_iff, lookup_extend S x y freshX freshY room z]
  by_cases same : z = x
  · simp [same]
  · simp [same]

/-! #### The single-output potential -/

open Classical in
/-- **The single-output potential of one permutation.** -/
def singleF (y : Fin (2 ^ 128)) (S : SparsePermutation (2 ^ 128)) : ℝ≥0∞ :=
  if S.used = 0 then delta else if S.used = 1 then ind (S.knownOutput y) else 0

theorem singleF_step (y : Fin (2 ^ 128)) (S : SparsePermutation (2 ^ 128)) (x : Fin (2 ^ 128)) :
    ∑' answer, (S.forward x).distribution answer * singleF y answer.2 ≤ singleF y S := by
  refine perm_step _ S x fun notKnown room _ => ?_
  have outputs : ∀ out : Unknown S, (S.extend room (S.input.symm x)
      (S.output.symm out.val)).knownOutput y ↔ S.knownOutput y ∨ y = out.val :=
    fun out => knownOutput_extend _ _ _ notKnown out.2 room y
  simp only [singleF, extend_used, outputs]
  have n0 : S.used + 1 ≠ 0 := by omega
  by_cases h0 : S.used = 0
  · have noneKnown : ¬ S.knownOutput y := by
      unfold SparsePermutation.knownOutput
      omega
    have n1 : S.used + 1 = 1 := by omega
    rw [if_pos h0]
    simp only [n1, if_true, noneKnown, false_or]
    refine le_trans (le_of_eq (tsum_congr fun out => ?_)) (fresh_hit_le_delta S h0 y)
    congr 1
    exact congrArg ind (propext ⟨fun h => h.symm, fun h => h.symm⟩)
  · have n1 : S.used + 1 ≠ 1 := by omega
    by_cases h1 : S.used = 1
    · simp only [n0, n1, if_false, mul_zero, tsum_zero]
      exact zero_le
    · simp only [n0, n1, if_false, mul_zero, tsum_zero]
      exact zero_le

/-- At a state with at most one pair, the output indicator is below the potential. -/
theorem singleF_bound (y : Fin (2 ^ 128)) (S : SparsePermutation (2 ^ 128)) (small : S.used ≤ 1) :
    ind (∃ x, lk S x = some y) ≤ singleF y S := by
  by_cases hit : ∃ x, lk S x = some y
  · rw [ind_pos hit]
    have known : S.knownOutput y := (knownOutput_iff _ _).mpr hit
    have positive : S.used ≠ 0 := by
      intro zero
      unfold SparsePermutation.knownOutput at known
      omega
    have one : S.used = 1 := by omega
    unfold singleF
    rw [if_neg positive, if_pos one, ind_pos known]
  · rw [ind_neg hit]
    exact zero_le

/-! #### The xor potential -/

/-- Block xor, named (a commutative associative operation, for `Finset.fold`). -/
def xorOp (a b : Block) : Block := a ^^^ b

instance : Std.Commutative xorOp := ⟨BitVec.xor_comm⟩

instance : Std.Associative xorOp := ⟨BitVec.xor_assoc⟩

/-- The xor of a finite family of blocks. -/
def bigXor {ι : Type} (J : Finset ι) (f : ι → Block) : Block := J.fold xorOp 0 f

theorem bigXor_congr {ι : Type} (J : Finset ι) {f g : ι → Block} (same : ∀ p ∈ J, f p = g p) :
    bigXor J f = bigXor J g :=
  Finset.fold_congr same

theorem bigXor_insert {ι : Type} [DecidableEq ι] {J : Finset ι} {p : ι} (outside : p ∉ J)
    (f : ι → Block) : bigXor (insert p J) f = f p ^^^ bigXor J f :=
  Finset.fold_insert outside

theorem bigXor_erase {ι : Type} [DecidableEq ι] {J : Finset ι} {p : ι} (inside : p ∈ J)
    (f : ι → Block) : bigXor J f = f p ^^^ bigXor (J.erase p) f := by
  conv_lhs => rw [← Finset.insert_erase inside]
  exact bigXor_insert (Finset.notMem_erase p J) f

/-- The output of a permutation's first pair. -/
def firstOut (S : SparsePermutation (2 ^ 128)) : Block :=
  BitVec.ofFin (S.output ⟨0, Nat.two_pow_pos 128⟩)

/-- A single-pair permutation's first output is its known output. -/
theorem firstOut_of_known (S : SparsePermutation (2 ^ 128)) (one : S.used = 1) {b : Fin (2 ^ 128)}
    (known : S.knownOutput b) : firstOut S = BitVec.ofFin b := by
  rw [firstOut, ← (knownOutput_one S one b).mp known]

theorem xor_left_cancel' (a b : Block) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem zero_xor_block (a : Block) : (0 : Block) ^^^ a = a := BitVec.zero_xor

theorem xor_zero_block (a : Block) : a ^^^ (0 : Block) = a := BitVec.xor_zero

open Classical in
/-- **The xor potential seen from one permutation**: `A`, `B` say that the other permutations hold
at most one, respectively exactly one, pair, and `R` is the xor of their outputs. -/
def xorPart (A B : Prop) (R z : Block) (T : SparsePermutation (2 ^ 128)) : ℝ≥0∞ :=
  if T.used ≤ 1 ∧ A then (if T.used = 1 ∧ B then ind (firstOut T ^^^ R = z) else delta) else 0

theorem xorPart_step (A B : Prop) (R z : Block) (T : SparsePermutation (2 ^ 128))
    (x : Fin (2 ^ 128)) :
    ∑' answer, (T.forward x).distribution answer * xorPart A B R z answer.2 ≤
      xorPart A B R z T := by
  classical
  refine perm_step _ T x fun notKnown room _ => ?_
  have usedAfter : ∀ out : Unknown T,
      (T.extend room (T.input.symm x) (T.output.symm out.val)).used = T.used + 1 :=
    fun _ => extend_used _ _ _ _
  by_cases hA : A
  · by_cases h0 : T.used = 0
    · have before : xorPart A B R z T = delta := by
        unfold xorPart
        rw [if_pos ⟨by omega, hA⟩, if_neg fun h => by omega]
      rw [before]
      by_cases hB : B
      · have after : ∀ out : Unknown T,
            xorPart A B R z (T.extend room (T.input.symm x) (T.output.symm out.val)) =
              ind (out.val = (z ^^^ R).toFin) := by
          intro out
          have one : (T.extend room (T.input.symm x) (T.output.symm out.val)).used = 1 := by
            rw [usedAfter, h0]
          unfold xorPart
          rw [if_pos ⟨one.le, hA⟩, if_pos ⟨one, hB⟩, firstOut_of_known _ one
            ((knownOutput_extend _ _ _ notKnown out.2 room out.val).mpr (Or.inr rfl))]
          congr 1
          apply propext
          constructor
          · intro same
            rw [← same, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.toFin_ofFin]
          · intro same
            rw [same, BitVec.ofFin_toFin, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
        simp only [after]
        exact fresh_hit_le_delta T h0 _
      · have after : ∀ out : Unknown T,
            xorPart A B R z (T.extend room (T.input.symm x) (T.output.symm out.val)) = delta := by
          intro out
          have one : (T.extend room (T.input.symm x) (T.output.symm out.val)).used = 1 := by
            rw [usedAfter, h0]
          unfold xorPart
          rw [if_pos ⟨one.le, hA⟩, if_neg fun h => hB h.2]
        simp only [after]
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    · have after : ∀ out : Unknown T,
          xorPart A B R z (T.extend room (T.input.symm x) (T.output.symm out.val)) = 0 := by
        intro out
        unfold xorPart
        rw [if_neg fun h => by rw [usedAfter] at h; omega]
      simp only [after, mul_zero, tsum_zero]
      exact zero_le
  · have after : ∀ out : Unknown T,
        xorPart A B R z (T.extend room (T.input.symm x) (T.output.symm out.val)) = 0 := by
      intro out
      unfold xorPart
      rw [if_neg fun h => hA h.2]
    simp only [after, mul_zero, tsum_zero]
    exact zero_le

section Xor

variable {ι : Type} [DecidableEq FixedIndex]

open Classical in
/-- **The xor potential**: the mass with which the (only) outputs at the indices `idx p`, `p ∈ J`,
xor to `z`. -/
def xorF (idx : ι → FixedIndex) (J : Finset ι) (z : Block)
    (fixed : FixedIndex → SparsePermutation (2 ^ 128)) : ℝ≥0∞ :=
  if ∀ p ∈ J, (fixed (idx p)).used ≤ 1 then
    (if ∀ p ∈ J, (fixed (idx p)).used = 1 then
      ind (bigXor J (fun p => firstOut (fixed (idx p))) = z)
    else delta)
  else 0

/-- The xor potential reads the permutations at `idx '' J` only. -/
theorem xorF_congr (idx : ι → FixedIndex) (J : Finset ι) (z : Block)
    {fixed other : FixedIndex → SparsePermutation (2 ^ 128)}
    (same : ∀ p ∈ J, fixed (idx p) = other (idx p)) :
    xorF idx J z fixed = xorF idx J z other := by
  unfold xorF
  by_cases small : ∀ p ∈ J, (other (idx p)).used ≤ 1
  · rw [if_pos fun p inside => by rw [same p inside]; exact small p inside, if_pos small]
    by_cases one : ∀ p ∈ J, (other (idx p)).used = 1
    · rw [if_pos fun p inside => by rw [same p inside]; exact one p inside, if_pos one,
        bigXor_congr J fun p inside => by rw [same p inside]]
    · rw [if_neg fun all => one fun p inside => by rw [← same p inside]; exact all p inside,
        if_neg one]
  · rw [if_neg fun all => small fun p inside => by rw [← same p inside]; exact all p inside,
      if_neg small]

/-- **The xor potential after updating one of its permutations.** -/
theorem xorF_update [DecidableEq ι] (idx : ι → FixedIndex) (inj : Function.Injective idx)
    (J : Finset ι) (z : Block) (fixed : FixedIndex → SparsePermutation (2 ^ 128)) {p₀ : ι}
    (inside : p₀ ∈ J) (T : SparsePermutation (2 ^ 128)) :
    xorF idx J z (Function.update fixed (idx p₀) T) =
      xorPart (∀ p ∈ J.erase p₀, (fixed (idx p)).used ≤ 1)
        (∀ p ∈ J.erase p₀, (fixed (idx p)).used = 1)
        (bigXor (J.erase p₀) fun p => firstOut (fixed (idx p))) z T := by
  classical
  have other : ∀ p ∈ J.erase p₀, Function.update fixed (idx p₀) T (idx p) = fixed (idx p) :=
    fun p member => Function.update_of_ne
      (fun same => Finset.ne_of_mem_erase member (inj same)) _ _
  have split : ∀ Q : SparsePermutation (2 ^ 128) → Prop,
      (∀ p ∈ J, Q (Function.update fixed (idx p₀) T (idx p))) ↔
        Q T ∧ ∀ p ∈ J.erase p₀, Q (fixed (idx p)) := by
    intro Q
    constructor
    · intro all
      refine ⟨?_, fun p member => ?_⟩
      · have := all p₀ inside
        rwa [Function.update_self] at this
      · have := all p (Finset.mem_of_mem_erase member)
        rwa [other p member] at this
    · rintro ⟨here, rest⟩ p member
      by_cases same : p = p₀
      · subst same
        rw [Function.update_self]
        exact here
      · rw [other p (Finset.mem_erase.mpr ⟨same, member⟩)]
        exact rest p (Finset.mem_erase.mpr ⟨same, member⟩)
  have fold : bigXor J (fun p => firstOut (Function.update fixed (idx p₀) T (idx p))) =
      firstOut T ^^^ bigXor (J.erase p₀) fun p => firstOut (fixed (idx p)) := by
    rw [bigXor_erase inside, Function.update_self]
    exact congrArg _ (bigXor_congr _ fun p member => by rw [other p member])
  unfold xorF xorPart
  by_cases small : T.used ≤ 1 ∧ ∀ p ∈ J.erase p₀, (fixed (idx p)).used ≤ 1
  · rw [if_pos ((split fun S => S.used ≤ 1).mpr small), if_pos small]
    by_cases one : T.used = 1 ∧ ∀ p ∈ J.erase p₀, (fixed (idx p)).used = 1
    · rw [if_pos ((split fun S => S.used = 1).mpr one), if_pos one, fold]
    · rw [if_neg fun all => one ((split fun S => S.used = 1).mp all), if_neg one]
  · rw [if_neg fun all => small ((split fun S => S.used ≤ 1).mp all), if_neg small]

/-- **The xor potential is not raised by a forward question at any index.** -/
theorem xorF_step (idx : ι → FixedIndex) (inj : Function.Injective idx) (J : Finset ι) (z : Block)
    (fixed : FixedIndex → SparsePermutation (2 ^ 128)) (j : FixedIndex) (x : Fin (2 ^ 128)) :
    ∑' answer, ((fixed j).forward x).distribution answer *
        xorF idx J z (Function.update fixed j answer.2) ≤ xorF idx J z fixed := by
  classical
  by_cases hit : ∃ p ∈ J, idx p = j
  · obtain ⟨p₀, inside, rfl⟩ := hit
    simp only [xorF_update idx inj J z fixed inside]
    have self := xorF_update idx inj J z fixed inside (fixed (idx p₀))
    rw [Function.update_eq_self] at self
    rw [self]
    exact xorPart_step _ _ _ _ _ _
  · have same : ∀ S : SparsePermutation (2 ^ 128),
        xorF idx J z (Function.update fixed j S) = xorF idx J z fixed := fun S =>
      xorF_congr idx J z fun p inside => Function.update_of_ne (fun h => hit ⟨p, inside, h⟩) _ _
    simp only [same]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **At a state where every index of `J` holds one pair**, the xor indicator of their outputs is
the potential. -/
theorem xorF_bound (idx : ι → FixedIndex) (J : Finset ι) (z : Block)
    (fixed : FixedIndex → SparsePermutation (2 ^ 128)) (one : ∀ p ∈ J, (fixed (idx p)).used = 1)
    (x a : ι → Fin (2 ^ 128)) (found : ∀ p ∈ J, lk (fixed (idx p)) (x p) = some (a p)) :
    ind (bigXor J (fun p => BitVec.ofFin (a p)) = z) ≤ xorF idx J z fixed := by
  unfold xorF
  rw [if_pos fun p inside => (one p inside).le, if_pos one]
  refine le_of_eq (congrArg ind (congrArg (· = z) (bigXor_congr J fun p inside => ?_)))
  exact (firstOut_of_known _ (one p inside) ((knownOutput_iff _ _).mpr ⟨x p, found p inside⟩)).symm

/-- **Before any of its indices is asked**, the xor potential of a nonempty set is `1/2^128`. -/
theorem xorF_fresh (idx : ι → FixedIndex) (J : Finset ι) (nonempty : J.Nonempty) (z : Block)
    (fixed : FixedIndex → SparsePermutation (2 ^ 128)) (zero : ∀ p ∈ J, (fixed (idx p)).used = 0) :
    xorF idx J z fixed = delta := by
  obtain ⟨p, inside⟩ := nonempty
  unfold xorF
  rw [if_pos fun q member => by rw [zero q member]; exact Nat.zero_le _, if_neg]
  intro allOne
  have one := allOne p inside
  have none := zero p inside
  omega

end Xor

/-! #### The pad potential -/

open Classical in
/-- **The pad potential of one EncPRF permutation**: `w` is mapped to `t`. -/
def padF (w t : Fin (2 ^ 128)) (S : SparsePermutation (2 ^ 128)) : ℝ≥0∞ :=
  if S.knownInput w then (if S.used ≤ 2 then ind (lk S w = some t) else 0)
  else (if S.used ≤ 1 then epsOne else 0)

theorem padF_step (w t : Fin (2 ^ 128)) (S : SparsePermutation (2 ^ 128)) (x : Fin (2 ^ 128)) :
    ∑' answer, (S.forward x).distribution answer * padF w t answer.2 ≤ padF w t S := by
  refine perm_step _ S x fun notKnown room _ => ?_
  have inputs : ∀ out : Unknown S, (S.extend room (S.input.symm x)
      (S.output.symm out.val)).knownInput w ↔ S.knownInput w ∨ w = x :=
    fun out => knownInput_extend _ _ _ notKnown out.2 room w
  have lookups : ∀ out : Unknown S, lk (S.extend room (S.input.symm x) (S.output.symm out.val)) w =
      if w = x then some out.val else lk S w :=
    fun out => lookup_extend S x out.val notKnown out.2 room w
  simp only [padF, extend_used, inputs, lookups]
  by_cases same : w = x
  · subst same
    simp only [notKnown, or_true, if_true, if_false]
    by_cases small : S.used ≤ 1
    · have small' : S.used + 1 ≤ 2 := by omega
      simp only [small', if_true, small, Option.some.injEq]
      exact fresh_hit_le_eps S small t
    · have big : ¬ S.used + 1 ≤ 2 := by omega
      simp only [big, if_false, small, mul_zero, tsum_zero, le_refl]
  · simp only [same, or_false, if_false]
    by_cases known : S.knownInput w
    · simp only [known, if_true]
      by_cases small : S.used + 1 ≤ 2
      · have small' : S.used ≤ 2 := by omega
        simp only [small, small', if_true]
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      · simp only [small, if_false, mul_zero, tsum_zero]
        exact zero_le
    · simp only [known, if_false]
      by_cases zero : S.used = 0
      · have small : S.used + 1 ≤ 1 := by omega
        have small' : S.used ≤ 1 := by omega
        simp only [small, small', if_true]
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      · have big : ¬ S.used + 1 ≤ 1 := by omega
        simp only [big, if_false, mul_zero, tsum_zero]
        exact zero_le

/-- With `w` stored and at most two pairs, the indicator of `w ↦ t` is the potential. -/
theorem padF_bound (w t v : Fin (2 ^ 128)) (S : SparsePermutation (2 ^ 128))
    (found : lk S w = some v) (small : S.used ≤ 2) : ind (v = t) ≤ padF w t S := by
  have known : S.knownInput w :=
    (knownInput_iff _ _).mpr (by rw [found]; exact Option.some_ne_none _)
  unfold padF
  rw [if_pos known, if_pos small, found]
  exact ind_mono fun same => by rw [same]

end Perm

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Lifting a permutation potential to the lazy state -/

section Lift

/-- **A potential of the fixed-key part, not raised by a forward question at any of its
permutations, is not raised by any forward question.** -/
theorem fixedAll_lift_step (Φ : (FixedIndex → SparsePermutation (2 ^ 128)) → ℝ≥0∞)
    (step : ∀ fixed (j : FixedIndex) (x : Fin (2 ^ 128)), ∑' answer,
      ((fixed j).forward x).distribution answer * Φ (Function.update fixed j answer.2) ≤ Φ fixed)
    (request : Request) (forward : ForwardOnly request) (state : LState) :
    ∑' answer, LazyOracle.query request state answer * Φ answer.2.fixed ≤ Φ state.fixed := by
  cases request with
  | fixedInverse _ _ => exact forward.elim
  | encInverse _ _ => exact forward.elim
  | fixedForward index input =>
    change ∑' answer, (((state.fixed index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1,
        { state with fixed := Function.update state.fixed index answer.2 }))) answer *
      Φ answer.2.fixed ≤ _
    rw [tsum_map_mul]
    exact step _ _ _
  | encForward index input =>
    change ∑' answer, (((state.enc index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1,
        { state with enc := Function.update state.enc index answer.2 }))) answer *
      Φ answer.2.fixed ≤ _
    rw [tsum_map_mul]
    dsimp only
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | hash input =>
    change ∑' answer, ((state.hash.query (Fintype.card_pos) input).distribution.map
      (fun answer => (_, { state with hash := answer.2 }))) answer * Φ answer.2.fixed ≤ _
    rw [tsum_map_mul]
    dsimp only
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **A potential of one fixed-key permutation, not raised by its forward questions, is not raised
by any forward question.** -/
theorem fixed_lift_step (i : FixedIndex) (F : SparsePermutation (2 ^ 128) → ℝ≥0∞)
    (step : ∀ S x, ∑' answer, (S.forward x).distribution answer * F answer.2 ≤ F S)
    (request : Request) (forward : ForwardOnly request) (state : LState) :
    ∑' answer, LazyOracle.query request state answer * F (answer.2.fixed i) ≤
      F (state.fixed i) := by
  refine fixedAll_lift_step (fun fixed => F (fixed i)) (fun fixed j x => ?_) request forward state
  by_cases same : i = j
  · subst same
    simp only [Function.update_self]
    exact step _ _
  · simp only [Function.update_of_ne same]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The same for one EncPRF permutation. -/
theorem enc_lift_step (j : EncPRF.PermutationIndex) (F : SparsePermutation (2 ^ 128) → ℝ≥0∞)
    (step : ∀ S x, ∑' answer, (S.forward x).distribution answer * F answer.2 ≤ F S)
    (request : Request) (forward : ForwardOnly request) (state : LState) :
    ∑' answer, LazyOracle.query request state answer * F (answer.2.enc j) ≤ F (state.enc j) := by
  cases request with
  | fixedInverse _ _ => exact forward.elim
  | encInverse _ _ => exact forward.elim
  | encForward index input =>
    change ∑' answer, (((state.enc index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1,
        { state with enc := Function.update state.enc index answer.2 }))) answer *
      F (answer.2.enc j) ≤ _
    rw [tsum_map_mul]
    by_cases same : j = index
    · subst same
      simp only [Function.update_self]
      exact step _ _
    · simp only [Function.update_of_ne same]
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | fixedForward index input =>
    change ∑' answer, (((state.fixed index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1,
        { state with fixed := Function.update state.fixed index answer.2 }))) answer *
      F (answer.2.enc j) ≤ _
    rw [tsum_map_mul]
    dsimp only
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | hash input =>
    change ∑' answer, ((state.hash.query (Fintype.card_pos) input).distribution.map
      (fun answer => (_, { state with hash := answer.2 }))) answer * F (answer.2.enc j) ≤ _
    rw [tsum_map_mul]
    dsimp only
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Lift

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
