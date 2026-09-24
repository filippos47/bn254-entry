/-
**Phase 3, P4 — the designated label `E*` is NOT exactly uniform given the stage-1 view.**

The instance fact (ii) was requested as `max_e Pr[E* = e | stage-1 view] ≤ 1/2^128` in `I^U` ("the
labels are drawn fresh, so `E*` is exactly uniform"). **It is false**, and so is the weaker
per-view `≤ 1/(2^128 − q₁)`. `E*` is not a key label plus a tweak: it passes through the lazy
fixed-key oracle at the chunk-0 fold of lane `pointX`.

* `evalFold_two_high` — **what `E*` is.** For a width-2 chunk with cleartext value `α`, an entry
  `j ∈ {2, 3}` whose level-1 parent `j − 2` is inactive (`j − 2 ≠ α mod 2`) carries the fold
  material `foldMask(1, j − 2, W)` of the level-1 label `W = join₀ xor bitLabel₀` (= the whitened
  bit-0 label, `join₀ = joinAt _ 0 = 0`). The designated switch `j* = α₀ xor 1` is such an entry
  whenever `α₀ ∈ {2, 3}` (it flips bit 0, so `j* − 2 = (α₀ mod 2) xor 1`): then
  `E* = foldMask(1, j* − 2, W) = π_{i₀}(W) xor π_{i₁}(W)`, two lazy answers at the hot indices
  `i₀ = hot(pointX, 0, 1, j* − 2, false)`, `i₁ = …true` (`foldMask_eq_xor`).
* `foldLaw` — the law of that fold material on the lazy oracle (`runRefill_foldMaskM`: it is what
  `I`'s, `I^U`'s, `H`'s run computes; a fixed-key query is never intercepted and never consumed,
  since the designated and the mask queries are hash queries).

**Counter-shape A (`foldLaw_single_apply`): off every input hit, the constant is `1/(2^128 − 1)`,
not `1/2^128`.** One stage-1 entry at each hot index (`x₀ ↦ v`, `x₁ ↦ v'`), `W` fresh at both: the
fold material equals `v xor v'` with mass exactly `1/(2^128 − 1) > 1/2^128`.

**Counter-shape B (`foldHit_counterShape`): with a fold hit, even `1/(2^128 − q₁)` fails.** One
label `x` queried in stage 1 at **both** hot indices (answers `v`, `v'`), and `W` exactly uniform
(the best case for the claim): `Pr[E* = v xor v'] = 2/2^128 > 1/(2^128 − 3)` — two stage-1 queries
at hot indices plus one hash query at the designated input `scaleInput pointX 0 j* i (v xor v')`
(`q₁ = 3`). The fold hit is **not** a stage-1 hash entry at a designated input, so P1's per-query
hypothesis (`Freshness.perQuery_hit_le` at `ε = 1/(2^128 − q₁)` per designated query) is false for
Plan B; the fold hit (`W` among the stage-1 inputs at both hot indices) must be charged to the
stage-1 **hot** queries (`1/2^128` each).

**What is true (`foldLaw_apply_le`)**: at a label fresh at both hot indices, the fold material has
point masses at most `1/(2^128 − used(i₁))` — the off-hit form of P3's `1/(2^128 − q₁)`.
-/

import Proof.Privacy.Phase3.Lazy.StepBound

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### XOR by a fixed block -/

/-- XOR by a fixed block, as a bijection of `Block`. -/
def xorEquiv (mask : Block) : Block ≃ Block where
  toFun value := value ^^^ mask
  invFun value := value ^^^ mask
  left_inv value := by simp [BitVec.xor_assoc]
  right_inv value := by simp [BitVec.xor_assoc]

/-- One point of an XOR-shifted law is one point of the law. -/
theorem map_xor_apply (law : PMF Block) (mask target : Block) :
    (law.map fun value => value ^^^ mask) target = law (target ^^^ mask) := by
  have image : (fun value : Block => value ^^^ mask) = xorEquiv mask := rfl
  rw [image, PMF.map_apply]
  rw [tsum_eq_single (target ^^^ mask)]
  · simp [xorEquiv, BitVec.xor_assoc]
  · intro other miss
    refine if_neg fun same => miss ?_
    rw [same]
    simp [xorEquiv, BitVec.xor_assoc]

/-! ### What `E*` is: the chunk-0 fold -/

/-- `xorFoldExcept` over one entry skipping it is `0`. -/
theorem xorFoldExcept_one (family : Fin 1 → Block) : xorFoldExcept 0 family = 0 := by
  simp [xorFoldExcept, Fin.foldl_succ]

/-- **The inactive high entries of a width-2 fold.** An entry `j ∈ {2, 3}` whose level-1 parent
`j − 2` is inactive is the fold material of the level-1 label `join 0 xor bitLabel 0`. -/
theorem evalFold_two_high (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (value : Nat) (bitLabel join : Nat → Block) (j : Fin (2 ^ 2))
    (high : 2 ≤ j.val) (inactive : j.val - 2 ≠ value % 2) :
    evalFold oracle lane chunk value bitLabel join 2 j =
      foldMask oracle lane chunk 1 (j.val - 2) (join 0 ^^^ bitLabel 0) := by
  have jLt : j.val < 4 := j.isLt
  have parentLt : j.val - 2 < 2 ^ 1 := by norm_num; omega
  simp only [evalFold, extendLevel]
  rw [dif_neg (by norm_num; omega)]
  simp only [evalStep]
  have notActive : (⟨j.val - 2 ^ 1, by norm_num; omega⟩ : Fin (2 ^ 1)) ≠ activeAt value 1 := by
    intro same
    have := congrArg Fin.val same
    simp only [activeAt, pow_one] at this
    omega
  rw [if_neg notActive]
  congr 1
  -- the level-1 label is `join 0 xor bitLabel 0` at either entry
  · have levelOne : ∀ entry : Fin (2 ^ 1),
        extendLevel 0 (fun _ => 0)
          (evalStep oracle lane chunk 0 (bitLabel 0) (join 0) (activeAt value 0)
            fun _ => 0) entry = join 0 ^^^ bitLabel 0 := by
      intro entry
      have zeroActive : ∀ other : Fin (2 ^ 0), other = activeAt value 0 := fun other =>
        Fin.ext (by
          have first := other.isLt
          have second := (activeAt value 0).isLt
          simp only [pow_zero] at first second
          omega)
      have skip : ∀ family : Fin (2 ^ 0) → Block, xorFoldExcept (activeAt value 0) family = 0 := by
        intro family
        have : activeAt value 0 = (0 : Fin 1) := Fin.ext (by simp [activeAt])
        rw [this]
        exact xorFoldExcept_one _
      simp only [extendLevel, evalStep, if_pos (zeroActive _)]
      split <;> rw [skip] <;> simp
    exact levelOne _

/-- **The designated switch is such an entry when `α₀ ∈ {2, 3}`**: `j* = α₀ xor 1` is `≥ 2` and its
level-1 parent `j* − 2` is not the active one `α₀ mod 2`. -/
theorem designated_high (alpha : ℕ) (small : alpha < 4) (high : 2 ≤ alpha) :
    2 ≤ alpha ^^^ 1 ∧ (alpha ^^^ 1) - 2 ≠ alpha % 2 := by
  interval_cases alpha <;> decide

/-- The fold material is the XOR of the two raw permutation images (the Davies–Meyer
feed-forwards cancel). -/
theorem foldMask_eq_xor (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (step entry : Nat) (label : Block) :
    foldMask oracle lane chunk step entry label =
      oracle.permutation (hotIndexNat lane chunk step entry false) label ^^^
        oracle.permutation (hotIndexNat lane chunk step entry true) label := by
  simp only [foldMask, Kriterion.ArgoMAC.PlanB.hash, daviesMeyer]
  show ((oracle.permutation _ label) ^^^ label) ^^^ ((oracle.permutation _ label) ^^^ label) = _
  rw [BitVec.xor_assoc, BitVec.xor_comm label, BitVec.xor_assoc, BitVec.xor_self,
    BitVec.xor_zero]

/-! ### The fold material on the lazy oracle -/

/-- A lazy forward query, its answer typed as a block. -/
def forwardAnswer [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (index : FixedIndex) (label : Block) (oracle : LState) : PMF (Block × LState) :=
  LazyOracle.query (.fixedForward index label) oracle

/-- **The fold material at a label, on the lazy oracle**: two forward queries at the two hot
indices, XORed. -/
def foldLaw [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (first second : FixedIndex) (oracle : LState) (label : Block) : PMF Block :=
  (forwardAnswer first label oracle).bind fun one =>
    (forwardAnswer second label one.2).map fun two => one.1 ^^^ two.1

section Lazy

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A query that is neither intercepted nor consumed goes to the lazy oracle. -/
theorem runRefill_query_lazy (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (request : Request) (next : request.Answer → FreeQuery Programs.Spec α) (oracle : LState)
    (record : Record) (touched : Set Cell) (intercept : interceptAnswer bits request = none)
    (consume : consumeCell touched oracle request = none) :
    runRefill bits draw (.query request next) oracle record touched =
      (LazyOracle.query request oracle).bind fun answer =>
        runRefill bits draw (next answer.1) answer.2 record (touch request touched) := by
  simp only [runRefill]
  split
  · rename_i answer hit
    rw [intercept] at hit
    cases hit
  · split
    · rename_i cell hit
      rw [consume] at hit
      cases hit
    · rfl

/-- The forward case of `runRefill_query_lazy`, with the answer typed as a block: a fixed-key query
is never intercepted and never consumed. -/
theorem runRefill_forward_lazy (bits : BitInput) (draw : Cell → PMF (Block × Block)) {α : Type}
    (index : FixedIndex) (label : Block) (next : Block → FreeQuery Programs.Spec α)
    (oracle : LState) (record : Record) (touched : Set Cell) :
    runRefill bits draw (.query (.fixedForward index label) next) oracle record touched =
      (forwardAnswer index label oracle).bind fun answer =>
        runRefill bits draw (next answer.1) answer.2 record
          (touch (.fixedForward index label) touched) :=
  runRefill_query_lazy bits draw (.fixedForward index label) next oracle record touched rfl rfl

/-- **The runs compute the fold material with `foldLaw`**: `I^U`'s (and `H`'s) refill runner on the
construction's `foldMaskM`, whatever the tape law. -/
theorem runRefill_foldMaskM (bits : BitInput) (draw : Cell → PMF (Block × Block)) (lane : Lane)
    (chunk : Fin chunkCount) (step entry : Nat) (label : Block) (oracle : LState)
    (record : Record) (touched : Set Cell) :
    (runRefill bits draw (Programs.foldMaskM lane chunk step entry label) oracle record
        touched).map (Option.map Prod.fst) =
      (foldLaw (hotIndexNat lane chunk step entry false) (hotIndexNat lane chunk step entry true)
        oracle label).map some := by
  show (runRefill bits draw (.query (.fixedForward (hotIndexNat lane chunk step entry false) label)
      fun (first : Block) => .query (.fixedForward (hotIndexNat lane chunk step entry true) label)
        fun (second : Block) => .pure ((first ^^^ label) ^^^ (second ^^^ label))) oracle record
        touched).map (Option.map Prod.fst) = _
  rw [runRefill_forward_lazy]
  unfold foldLaw
  rw [PMF.map_bind, PMF.map_bind]
  refine congrArg _ (funext fun one => ?_)
  rw [runRefill_forward_lazy]
  simp only [runRefill, PMF.map_bind, PMF.pure_map, Option.map_some, PMF.map_comp]
  rw [← PMF.bind_pure_comp]
  refine congrArg _ (funext fun two => ?_)
  show PMF.pure (some ((one.1 ^^^ label) ^^^ (two.1 ^^^ label))) = PMF.pure (some _)
  congr 2
  show (one.1 ^^^ label) ^^^ (two.1 ^^^ label) = one.1 ^^^ two.1
  rw [BitVec.xor_assoc, BitVec.xor_comm label, BitVec.xor_assoc, BitVec.xor_self,
    BitVec.xor_zero]

/-! ### The answer law of one forward query -/

/-- The answer of a lazy forward query is read from the index's sparse permutation only. -/
theorem query_answer (index : FixedIndex) (label : Block) (oracle : LState) :
    (LazyOracle.query (.fixedForward index label) oracle).map Prod.fst =
      ((oracle.fixed index).forward label.toFin).distribution.map fun answer =>
        BitVec.ofFin answer.1 := by
  simp only [LazyOracle.query, PMF.map_comp]
  rfl

/-- The unused outputs of a sparse permutation number `size − used`. -/
theorem card_unusedOutput {size : ℕ} (state : SparsePermutation size) :
    Fintype.card {output : Fin size // ¬ state.knownOutput output} = size - state.used := by
  rw [← Fintype.card_congr state.unusedOutputEquiv, Fintype.card_fin]

/-- **A fresh forward answer is uniform on the unused outputs.** -/
theorem fresh_answer_apply (state : SparsePermutation (2 ^ 128)) (label : Block)
    (fresh : ¬ state.knownInput label.toFin) (target : Block) :
    ((state.forward label.toFin).distribution.map fun answer => BitVec.ofFin answer.1) target =
      if state.knownOutput target.toFin then 0 else (((2 ^ 128 - state.used : ℕ) : ℝ≥0∞))⁻¹ := by
  classical
  have unknown : ¬ (state.input.symm label.toFin).val < state.used := fresh
  have room : state.used < 2 ^ 128 := by
    have := (state.input.symm label.toFin).isLt; omega
  have : Nonempty {output : Fin (2 ^ 128) // ¬ state.knownOutput output} :=
    ⟨state.unusedOutputEquiv ⟨0, by omega⟩⟩
  have law : ((state.forward label.toFin).distribution.map fun answer => BitVec.ofFin answer.1) =
      (PMF.uniformOfFintype {output : Fin (2 ^ 128) // ¬ state.knownOutput output}).map
        fun output => BitVec.ofFin output.val := by
    rw [← state.unusedOutput_uniform room, PMF.map_comp]
    unfold SparsePermutation.forward
    simp only [dif_neg unknown, Draw.distribution, PMF.map_comp]
    rfl
  rw [law, PMF.map_apply]
  by_cases used : state.knownOutput target.toFin
  · rw [if_pos used]
    refine ENNReal.tsum_eq_zero.mpr fun output => if_neg fun same => output.2 ?_
    have back : output.1 = target.toFin := by rw [same]
    rw [back]
    exact used
  · rw [if_neg used, tsum_eq_single ⟨target.toFin, used⟩]
    · rw [if_pos rfl, PMF.uniformOfFintype_apply, card_unusedOutput]
    · intro other different
      refine if_neg fun same => different (Subtype.ext ?_)
      have back : target.toFin = other.1 := by rw [same]
      exact back.symm

/-- The answer of a forward query as a block law. -/
theorem forwardAnswer_fst (index : FixedIndex) (label : Block) (oracle : LState) :
    (forwardAnswer index label oracle).map Prod.fst =
      ((oracle.fixed index).forward label.toFin).distribution.map fun answer =>
        BitVec.ofFin answer.1 := query_answer index label oracle

/-- A forward query at one index leaves every other index alone. -/
theorem forwardAnswer_frame (index : FixedIndex) (label : Block) (oracle : LState)
    (one : Block × LState) (member : one ∈ (forwardAnswer index label oracle).support)
    (other : FixedIndex) (different : index ≠ other) : one.2.fixed other = oracle.fixed other :=
  query_frame (.fixedForward index label) oracle one member other
    fun same => different (Option.some.inj same)

/-- The second answer XORed into the first: one point of it is one point of the answer law. -/
theorem xor_second_apply (second : FixedIndex) (label : Block) (one : Block × LState)
    (target : Block) :
    ((forwardAnswer second label one.2).map fun two => one.1 ^^^ two.1) target =
      ((one.2.fixed second).forward label.toFin).distribution.map
        (fun answer => BitVec.ofFin answer.1) (target ^^^ one.1) := by
  have reshape : ((forwardAnswer second label one.2).map fun two => one.1 ^^^ two.1) =
      (((forwardAnswer second label one.2).map Prod.fst).map fun two => two ^^^ one.1) := by
    rw [PMF.map_comp]
    congr 1
    funext two
    exact BitVec.xor_comm _ _
  rw [reshape, map_xor_apply, forwardAnswer_fst]

/-- **The fold material at a fresh label has point masses `≤ 1/(2^128 − used(second))`.** The
second answer is uniform on the unused outputs of the second index, whatever the first. -/
theorem foldLaw_apply_le (first second : FixedIndex) (different : first ≠ second)
    (oracle : LState) (label : Block)
    (freshSecond : ¬ (oracle.fixed second).knownInput label.toFin) (target : Block) :
    foldLaw first second oracle label target ≤
      (((2 ^ 128 - (oracle.fixed second).used : ℕ) : ℝ≥0∞))⁻¹ := by
  unfold foldLaw
  rw [PMF.bind_apply]
  calc (∑' one, (forwardAnswer first label oracle) one *
        ((forwardAnswer second label one.2).map fun two => one.1 ^^^ two.1) target)
      ≤ ∑' one, (forwardAnswer first label oracle) one *
          (((2 ^ 128 - (oracle.fixed second).used : ℕ) : ℝ≥0∞))⁻¹ := by
        refine ENNReal.tsum_le_tsum fun one => ?_
        by_cases zero : (forwardAnswer first label oracle) one = 0
        · rw [zero, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left ?_ zero_le
          have frame := forwardAnswer_frame first label oracle one
            ((PMF.mem_support_iff _ _).mpr zero) second different
          rw [xor_second_apply, frame, fresh_answer_apply _ _ freshSecond]
          split
          · exact zero_le
          · exact le_rfl
    _ = (((2 ^ 128 - (oracle.fixed second).used : ℕ) : ℝ≥0∞))⁻¹ := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Lazy

/-! ### The counter-shapes -/

/-- One stored pair `input ↦ output`. -/
def single (input output : Block) : SparsePermutation (2 ^ 128) where
  used := 1
  within := Nat.one_le_two_pow
  inputs := [(⟨0, Nat.two_pow_pos 128⟩, input.toFin)]
  outputs := [(⟨0, Nat.two_pow_pos 128⟩, output.toFin)]
  inputLength := by simp
  outputLength := by simp

theorem single_input_symm (input output : Block) (value : Fin (2 ^ 128)) :
    (single input output).input.symm value = Equiv.swap ⟨0, Nat.two_pow_pos 128⟩ input.toFin value := by
  simp [single, SparsePermutation.input, swaps]

theorem single_output_symm (input output : Block) (value : Fin (2 ^ 128)) :
    (single input output).output.symm value =
      Equiv.swap ⟨0, Nat.two_pow_pos 128⟩ output.toFin value := by
  simp [single, SparsePermutation.output, swaps]

/-- The only known input of `single` is its own. -/
theorem single_knownInput (input output : Block) (value : Fin (2 ^ 128)) :
    (single input output).knownInput value ↔ value = input.toFin := by
  unfold SparsePermutation.knownInput
  rw [single_input_symm]
  show (Equiv.swap _ _ value).val < 1 ↔ _
  constructor
  · intro small
    have zero : Equiv.swap (⟨0, Nat.two_pow_pos 128⟩ : Fin (2 ^ 128)) input.toFin value =
        ⟨0, Nat.two_pow_pos 128⟩ := Fin.ext (Nat.lt_one_iff.mp small)
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at zero
    exact zero
  · rintro rfl
    rw [Equiv.swap_apply_right]
    show 0 < 1
    omega

/-- The only known output of `single` is its own. -/
theorem single_knownOutput (input output : Block) (value : Fin (2 ^ 128)) :
    (single input output).knownOutput value ↔ value = output.toFin := by
  unfold SparsePermutation.knownOutput
  rw [single_output_symm]
  show (Equiv.swap _ _ value).val < 1 ↔ _
  constructor
  · intro small
    have zero : Equiv.swap (⟨0, Nat.two_pow_pos 128⟩ : Fin (2 ^ 128)) output.toFin value =
        ⟨0, Nat.two_pow_pos 128⟩ := Fin.ext (Nat.lt_one_iff.mp small)
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at zero
    exact zero
  · rintro rfl
    rw [Equiv.swap_apply_right]
    show 0 < 1
    omega

/-- `single` answers its own input with its own output. -/
theorem single_forward (input output : Block) :
    (single input output).forward input.toFin = Draw.pure (output.toFin, single input output) := by
  refine LazyOracle.lookup_forward _ _ _ ?_
  unfold LazyOracle.permutationLookup
  rw [if_pos ((single_knownInput _ _ _).mpr rfl), single_input_symm, Equiv.swap_apply_right]
  simp [single, SparsePermutation.output, swaps]

/-- The lazy state with one stored pair at each of two indices. -/
def twoEntries [DecidableEq FixedIndex] (first second : FixedIndex) (firstPair secondPair : Block × Block) :
    LState where
  fixed := Function.update (Function.update (fun _ => .empty _) first
    (single firstPair.1 firstPair.2)) second (single secondPair.1 secondPair.2)
  enc := fun _ => .empty _
  hash := []

section Counter

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

theorem twoEntries_first (first second : FixedIndex) (different : first ≠ second)
    (firstPair secondPair : Block × Block) :
    (twoEntries first second firstPair secondPair).fixed first = single firstPair.1 firstPair.2 := by
  simp [twoEntries, Function.update_of_ne different]

theorem twoEntries_second (first second : FixedIndex) (firstPair secondPair : Block × Block) :
    (twoEntries first second firstPair secondPair).fixed second =
      single secondPair.1 secondPair.2 := by
  simp [twoEntries]

/-- `Block` has `2^128` elements. -/
theorem card_block : Fintype.card Block = 2 ^ 128 :=
  (Fintype.card_congr (⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩ :
    Block ≃ Fin (2 ^ 128))).trans (Fintype.card_fin _)

/-- `a xor b xor c = b` forces `c = a`. -/
theorem xor_solve (a b c : Block) (equal : a ^^^ b ^^^ c = b) : c = a :=
  calc c = ((a ^^^ b) ^^^ (a ^^^ b)) ^^^ c := by rw [BitVec.xor_self, BitVec.zero_xor]
    _ = (a ^^^ b) ^^^ ((a ^^^ b) ^^^ c) := BitVec.xor_assoc _ _ _
    _ = (a ^^^ b) ^^^ b := by rw [equal]
    _ = a := by rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- **Counter-shape A, exactly.** One stored pair at each hot index (`x₀ ↦ v`, `x₁ ↦ v'`) and a
label fresh at both: the fold material is `v xor v'` with mass `1/(2^128 − 1)`. -/
theorem foldLaw_single_apply (first second : FixedIndex) (different : first ≠ second)
    (firstPair secondPair : Block × Block) (label : Block)
    (freshFirst : label ≠ firstPair.1) (freshSecond : label ≠ secondPair.1) :
    foldLaw first second (twoEntries first second firstPair secondPair) label
        (firstPair.2 ^^^ secondPair.2) = (((2 ^ 128 - 1 : ℕ) : ℝ≥0∞))⁻¹ := by
  classical
  set oracle := twoEntries first second firstPair secondPair with oracleDef
  have toFinNe : ∀ a b : Block, a ≠ b → a.toFin ≠ b.toFin := fun a b ne same =>
    ne (BitVec.eq_of_toFin_eq same)
  have freshAtFirst : ¬ (oracle.fixed first).knownInput label.toFin := by
    rw [oracleDef, twoEntries_first _ _ different, single_knownInput]
    exact toFinNe _ _ freshFirst
  have freshAtSecond : ¬ (oracle.fixed second).knownInput label.toFin := by
    rw [oracleDef, twoEntries_second, single_knownInput]
    exact toFinNe _ _ freshSecond
  have usedSecond : (oracle.fixed second).used = 1 := by
    rw [oracleDef, twoEntries_second]; rfl
  unfold foldLaw
  rw [PMF.bind_apply]
  -- on the support of the first answer the inner mass is the constant `1/(2^128 − 1)`
  have inner : ∀ one ∈ (forwardAnswer first label oracle).support,
      ((forwardAnswer second label one.2).map fun two => one.1 ^^^ two.1)
        (firstPair.2 ^^^ secondPair.2) = (((2 ^ 128 - 1 : ℕ) : ℝ≥0∞))⁻¹ := by
    intro one member
    have frame := forwardAnswer_frame first label oracle one member second different
    -- the first answer is an unused output of `first`: not `v`
    have firstAnswer : one.1 ≠ firstPair.2 := by
      intro same
      have mass : ((forwardAnswer first label oracle).map Prod.fst) one.1 ≠ 0 :=
        (PMF.mem_support_iff _ _).mp ((PMF.mem_support_map_iff _ _ _).mpr ⟨one, member, rfl⟩)
      rw [forwardAnswer_fst, fresh_answer_apply _ _ freshAtFirst, same, oracleDef,
        twoEntries_first _ _ different, if_pos ((single_knownOutput _ _ _).mpr rfl)] at mass
      exact mass rfl
    rw [xor_second_apply, frame, fresh_answer_apply _ _ freshAtSecond, usedSecond]
    rw [if_neg]
    rw [oracleDef, twoEntries_second, single_knownOutput]
    intro same
    apply firstAnswer
    have blocks : firstPair.2 ^^^ secondPair.2 ^^^ one.1 = secondPair.2 :=
      BitVec.eq_of_toFin_eq same
    exact xor_solve _ _ _ blocks
  calc (∑' one, (forwardAnswer first label oracle) one *
        ((forwardAnswer second label one.2).map fun two => one.1 ^^^ two.1)
          (firstPair.2 ^^^ secondPair.2))
      = ∑' one, (forwardAnswer first label oracle) one *
          (((2 ^ 128 - 1 : ℕ) : ℝ≥0∞))⁻¹ := by
        refine tsum_congr fun one => ?_
        by_cases zero : (forwardAnswer first label oracle) one = 0
        · rw [zero, zero_mul, zero_mul]
        · rw [inner one ((PMF.mem_support_iff _ _).mpr zero)]
    _ = (((2 ^ 128 - 1 : ℕ) : ℝ≥0∞))⁻¹ := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- `1/2^128 < 1/(2^128 − 1)`. -/
theorem inv_lt_inv_pred : ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ < (((2 ^ 128 - 1 : ℕ) : ℝ≥0∞))⁻¹ :=
  ENNReal.inv_lt_inv.mpr (Nat.cast_lt.mpr (by norm_num))

/-- **Counter-shape A.** Off every input hit (the label fresh at both hot indices), the fold
material -- `E*` when `α₀ ∈ {2, 3}` -- puts mass `1/(2^128 − 1) > 1/2^128` on a value the stage-1
view names: `E*` is not exactly uniform, and `1/2^128` is not a valid charge. -/
theorem freshFold_counterShape (first second : FixedIndex) (different : first ≠ second)
    (firstPair secondPair : Block × Block) (label : Block)
    (freshFirst : label ≠ firstPair.1) (freshSecond : label ≠ secondPair.1) :
    ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ <
      foldLaw first second (twoEntries first second firstPair secondPair) label
        (firstPair.2 ^^^ secondPair.2) := by
  rw [foldLaw_single_apply first second different firstPair secondPair label freshFirst
    freshSecond]
  exact inv_lt_inv_pred

/-- A forward query at a stored input returns the stored output and leaves the oracle as it is. -/
theorem forwardAnswer_known (index : FixedIndex) (label : Block) (oracle : LState)
    (output : Fin (2 ^ 128))
    (stored : (oracle.fixed index).forward label.toFin = Draw.pure (output, oracle.fixed index)) :
    forwardAnswer index label oracle = PMF.pure (BitVec.ofFin output, oracle) := by
  unfold forwardAnswer
  simp only [LazyOracle.query]
  rw [stored]
  simp only [Draw.distribution, PMF.pure_map, Function.update_eq_self]
  rfl

/-- At the label a stage-1 query stored at both hot indices, the fold material is determined. -/
theorem foldLaw_hit (first second : FixedIndex) (different : first ≠ second)
    (input firstOutput secondOutput : Block) :
    foldLaw first second (twoEntries first second (input, firstOutput) (input, secondOutput))
        input = PMF.pure (firstOutput ^^^ secondOutput) := by
  unfold foldLaw
  rw [forwardAnswer_known first input _ firstOutput.toFin (by
      rw [twoEntries_first _ _ different]; exact single_forward _ _), PMF.pure_bind,
    forwardAnswer_known second input _ secondOutput.toFin (by
      rw [twoEntries_second]; exact single_forward _ _), PMF.pure_map]

/-- **Counter-shape B (the fold hit).** One label `x` stored at both hot indices by stage 1
(answers `v`, `v'`) and the level-1 label `W` exactly uniform: the fold material equals
`v xor v'` with mass exactly `2/2^128`. -/
theorem foldHit_apply (first second : FixedIndex) (different : first ≠ second)
    (input firstOutput secondOutput : Block) :
    ((PMF.uniformOfFintype Block).bind fun label =>
        foldLaw first second (twoEntries first second (input, firstOutput) (input, secondOutput))
          label) (firstOutput ^^^ secondOutput) =
      2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  rw [PMF.bind_apply, tsum_fintype, ← Finset.add_sum_erase _ _ (Finset.mem_univ input),
    foldLaw_hit first second different, PMF.pure_apply, if_pos rfl, mul_one,
    PMF.uniformOfFintype_apply, card_block]
  rw [Finset.sum_congr rfl fun label member => by
    rw [PMF.uniformOfFintype_apply, card_block,
      foldLaw_single_apply first second different (input, firstOutput) (input, secondOutput)
        label (Finset.ne_of_mem_erase member) (Finset.ne_of_mem_erase member)]]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    card_block, nsmul_eq_mul]
  have pred : ((2 ^ 128 - 1 : ℕ) : ℝ≥0∞) * (((2 ^ 128 - 1 : ℕ) : ℝ≥0∞))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (by norm_num)) (ENNReal.natCast_ne_top _)
  calc ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ + ((2 ^ 128 - 1 : ℕ) : ℝ≥0∞) *
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * (((2 ^ 128 - 1 : ℕ) : ℝ≥0∞))⁻¹)
      = ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ + ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ *
          (((2 ^ 128 - 1 : ℕ) : ℝ≥0∞) * (((2 ^ 128 - 1 : ℕ) : ℝ≥0∞))⁻¹) := by ring
    _ = 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by rw [pred, mul_one, two_mul]

/-- `1/(2^128 − 3) < 2/2^128`. -/
theorem inv_sub_three_lt : (((2 ^ 128 - 3 : ℕ) : ℝ≥0∞))⁻¹ < 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [show (2 : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ = (((2 ^ 127 : ℕ) : ℝ≥0∞))⁻¹ by
    rw [show (2 ^ 128 : ℕ) = 2 * 2 ^ 127 by norm_num, Nat.cast_mul, Nat.cast_ofNat,
      ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]]
  exact ENNReal.inv_lt_inv.mpr (Nat.cast_lt.mpr (by norm_num))

/-- **Counter-shape B.** With a fold hit in the stage-1 view -- two stage-1 queries at the hot
indices at one label, then one designated query at the XOR of their answers (`q₁ = 3`) -- `E*`
hits that designated query's input with mass `2/2^128 > 1/(2^128 − 3)`: neither `1/2^128` nor
P3's/P1's per-designated-query `1/(2^128 − q₁)` bounds it. -/
theorem foldHit_counterShape (first second : FixedIndex) (different : first ≠ second)
    (input firstOutput secondOutput : Block) :
    (((2 ^ 128 - 3 : ℕ) : ℝ≥0∞))⁻¹ <
      ((PMF.uniformOfFintype Block).bind fun label =>
        foldLaw first second (twoEntries first second (input, firstOutput) (input, secondOutput))
          label) (firstOutput ^^^ secondOutput) := by
  rw [foldHit_apply first second different]
  exact inv_sub_three_lt

end Counter

end

end Kriterion.ArgoMAC.Phase3.Lazy
