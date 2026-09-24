/-
The laws of the machine's fair-coin samplers.

* `memSem_coinBit`: one coin, pushed and popped on the private stack, is a uniform bit in `rBit`
  and leaves the stacks as they were.
* `memSem_bitStep`: `rAcc ← 2 · rAcc + coin`.
* `memSem_bitSteps` / `memSem_sampleWord`: `width` coins give a uniform `width`-bit word in
  `rAcc` (big-endian), exactly.
-/

import Proof.Simulator.OracleUse

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine Blocks

section Coins

variable [BN254.FieldCertificate]

/-- A bit as a word. -/
def bitWord (bit : Bool) : Word := if bit then 1 else 0

theorem popInto_pushOn (memory : Memory) (stack : Fin 4) (target : Register) (bit : Bool) :
    popInto (pushOn memory stack bit) stack target = setReg memory target (bitWord bit) := by
  simp only [popInto, pushOn, Function.update_self, bitWord]
  congr 1
  cases memory
  simp only [Memory.mk.injEq, and_true, true_and]
  funext index
  by_cases same : index = stack
  · subst same; simp
  · simp [Function.update_of_ne same]

/-- **One coin.** -/
theorem memSem_coinBit (target : Register) (memory : Memory) :
    (coinBit target).memSem memory =
      (PMF.uniformOfFintype Bool).map fun bit => some (setReg memory target (bitWord bit)) := by
  simp only [coinBit, Prog.memSem, Op.memSem, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.map]
  congr 1
  funext bit
  simp only [Function.comp_apply, popInto_pushOn]

/-- The memory after one big-endian coin step. -/
def stepMem (memory : Memory) (bit : Bool) : Memory :=
  setReg (setReg memory rBit (bitWord bit)) rAcc
    (memory.registers rAcc + memory.registers rAcc + bitWord bit)

theorem memSem_bitStep (memory : Memory) :
    bitStep.memSem memory = (PMF.uniformOfFintype Bool).map fun bit => some (stepMem memory bit) := by
  simp only [bitStep, Prog.memSem, memSem_coinBit, PMF.bind_map]
  rw [PMF.map]
  congr 1
  funext bit
  simp only [Function.comp_apply, ar, Prog.memSem, Op.memSem, PMF.pure_bind, stepMem, setReg,
    Arithmetic.eval]
  congr 3
  · funext index
    by_cases same : index = rAcc
    · subst same
      simp [Function.update_self, Function.update_of_ne (show rBit ≠ rAcc by decide),
        Function.update_of_ne (show rAcc ≠ rBit by decide)]
    · simp [Function.update_of_ne same]

/-- A product of uniform finite samples is uniform (as P3's `Glue.uniform_product`). -/
theorem uniform_product {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (PMF.uniformOfFintype A).bind (fun a => (PMF.uniformOfFintype B).map (fun b => (a, b))) =
      PMF.uniformOfFintype (A × B) := by
  classical
  apply PMF.ext
  rintro ⟨a, b⟩
  simp only [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply, Prod.mk.injEq,
    ite_and, Fintype.card_prod, Nat.cast_mul]
  have inner (a' : A) :
      (∑' b' : B, if a = a' then if b = b' then (Fintype.card B : ENNReal)⁻¹ else 0 else 0) =
        if a = a' then (Fintype.card B : ENNReal)⁻¹ else 0 := by
    by_cases equal : a = a'
    · simp only [if_pos equal]
      simp_rw [@eq_comm B b]
      exact tsum_ite_eq _ _
    · simp only [if_neg equal, tsum_zero]
  simp_rw [inner]
  simp_rw [mul_ite, mul_zero, @eq_comm A a]
  rw [tsum_ite_eq]
  exact (ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))).symm

/-- A finite bijection preserves the uniform law. -/
theorem uniform_equiv {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (equiv : A ≃ B) : (PMF.uniformOfFintype A).map equiv = PMF.uniformOfFintype B :=
  PMF.uniformOfFintype_map_of_bijective equiv equiv.bijective

/-- The memory after `steps` big-endian coin steps that drew the word `value`. -/
def wordMem (memory : Memory) (steps value : Nat) : Memory :=
  setReg (setReg memory rBit (if steps = 0 then memory.registers rBit else bitWord (value % 2 == 1)))
    rAcc (memory.registers rAcc * BitVec.ofNat 256 (2 ^ steps) + BitVec.ofNat 256 value)

theorem uniform_nonempty_pow (steps : Nat) : Nonempty (Fin (2 ^ steps)) :=
  ⟨⟨0, Nat.two_pow_pos steps⟩⟩

/-- `(c, b) ↦ 2c + b`, the big-endian extension of a word by one bit. -/
def extendEquiv (steps : Nat) : Fin (2 ^ steps) × Bool ≃ Fin (2 ^ (steps + 1)) :=
  ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv).trans
    (finCongr (by rw [pow_succ]))

theorem extendEquiv_val (steps : Nat) (value : Fin (2 ^ steps)) (bit : Bool) :
    (extendEquiv steps (value, bit)).val = 2 * value.val + (if bit then 1 else 0) := by
  simp only [extendEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
    id_eq, finProdFinEquiv_apply_val, finCongr_apply, Fin.val_cast]
  cases bit <;> simp [finTwoEquiv] <;> omega

theorem stepMem_wordMem (memory : Memory) (steps : Nat) (value : Fin (2 ^ steps)) (bit : Bool) :
    stepMem (wordMem memory steps value.val) bit =
      wordMem memory (steps + 1) (extendEquiv steps (value, bit)).val := by
  rw [extendEquiv_val]
  simp only [stepMem, wordMem, setReg]
  congr 1
  funext index
  by_cases isAcc : index = rAcc
  · subst isAcc
    simp only [Function.update_self]
    rw [pow_succ, BitVec.ofNat_mul, BitVec.ofNat_add, BitVec.ofNat_mul]
    have two : BitVec.ofNat 256 2 = 2 := rfl
    have one : BitVec.ofNat 256 1 = 1 := rfl
    have zero : BitVec.ofNat 256 0 = 0 := rfl
    cases bit <;> simp only [bitWord, Bool.false_eq_true, if_false, if_true, two, one, zero] <;>
      ring
  · by_cases isBit : index = rBit
    · subst isBit
      rw [Function.update_of_ne (show rBit ≠ rAcc by decide), Function.update_self,
        Function.update_of_ne (show rBit ≠ rAcc by decide), Function.update_self]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
      cases bit <;> simp [bitWord] <;> omega
    · rw [Function.update_of_ne isAcc, Function.update_of_ne isBit, Function.update_of_ne isAcc,
        Function.update_of_ne isBit, Function.update_of_ne isAcc, Function.update_of_ne isBit]

/-- **`steps` coins make a uniform `steps`-bit word.** -/
theorem memSem_bitSteps (steps : Nat) (memory : Memory) :
    (Prog.rep steps fun _ => bitStep).memSem memory =
      (PMF.uniformOfFintype (Fin (2 ^ steps))).map fun value =>
        some (wordMem memory steps value.val) := by
  induction steps with
  | zero =>
      rw [Prog.rep]
      simp only [Prog.memSem]
      have single : PMF.uniformOfFintype (Fin (2 ^ 0)) = PMF.pure 0 := by
        apply PMF.ext; intro value
        simp [PMF.uniformOfFintype_apply, Fin.fin_one_eq_zero value]
      rw [single, PMF.pure_map]
      congr 2
      simp [wordMem, setReg]
  | succ steps ih =>
      have := uniform_nonempty_pow steps
      have := uniform_nonempty_pow (steps + 1)
      rw [Prog.rep]
      simp only [Prog.memSem]
      rw [ih]
      conv_rhs => rw [← uniform_equiv (extendEquiv steps), ← uniform_product]
      simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp]
      congr 1
      funext value
      simp only [Function.comp_apply, memSem_bitStep, stepMem_wordMem]
      rfl

theorem memSem_sampleWord (width : Nat) (memory : Memory) :
    (sampleWord width).memSem memory =
      (PMF.uniformOfFintype (Fin (2 ^ width))).map fun value =>
        some (wordMem (setReg memory rAcc 0) width value.val) := by
  simp only [sampleWord, Prog.memSem, cst, Op.memSem, PMF.pure_bind, memSem_bitSteps]
  rfl

/-! ### Bounded rejection -/

/-- **The law of bounded rejection**: up to `count` uniform `width`-bit draws, the first
accepted one; `none` when all are rejected. -/
noncomputable def rejectLaw (width : Nat) (accept : Nat → Bool) : Nat → PMF (Option Nat)
  | 0 => PMF.pure none
  | count + 1 => (PMF.uniformOfFintype (Fin (2 ^ width))).bind fun value =>
      if accept value.val then PMF.pure (some value.val) else rejectLaw width accept count

/-- A test block: it sets `rBit` to the acceptance bit of `rAcc` and may clobber `rAddr`. -/
def IsTest (test : Prog) (accept : Nat → Bool) : Prop :=
  ∀ memory : Memory, ∃ junk : Word, test.memSem memory =
    PMF.pure (some (setReg (setReg memory rAddr junk) rBit
      (bitWord (accept (memory.registers rAcc).toNat))))

/-- The sampler's observable state: the kept draw, the flag, and the memory with the
attempt scratch (`rAcc`, `rBit`, `rAddr`, `rSel`) cleared. -/
def scrubAttempt (memory : Memory) : Memory :=
  setReg (setReg (setReg (setReg memory rAcc 0) rBit 0) rAddr 0) rSel 0

end Coins

end Kriterion.ArgoMAC.PlanB.SimMachine
