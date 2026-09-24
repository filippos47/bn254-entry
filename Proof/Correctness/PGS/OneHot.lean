/-
This file proves the correctness of the Plan B `bin-to-hot` switch system.

Three statements land here (plan `2026-09-17-planB.md`, Task 7):

* `binToHot_eq_ite` -- the cleartext one-hot has exactly one live entry;
* `sum_truthTable_binToHot` -- Lemma 6.1, the free truth-table fold, proved by
  `Finset.sum_eq_single` (Rule O: no `decide`, no `Finset.sum` unfolding, no `Vector`
  enumeration over a `2 ^ width`-entry object);
* `evalHot_garbleHot` -- for every tape, every chunk, every width and every input, the
  evaluator's label vector satisfies the free-XOR invariant `E_t = Z_t ^^^ h_t * delta`
  against the garbler's.

The third is stated against the landed definitions of `Construction/PGS/OneHot.lean`, whose
`evalHot` takes the cleartext chunk value as a trailing argument (the evaluator cannot run the
fold without knowing which parent is active at each step; see the Task 3--6 report,
deviation 6.1, and plan D.9 item 5).
-/

import Construction.PGS.OneHot

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-! ### XOR algebra over `Block`

`Block = BitVec 128` is a commutative group under `^^^` in which every element is its own
inverse. Mathlib carries no such instance, so the handful of rearrangements the fold needs are
proved once, bit by bit. -/

private theorem xor_zero' (a : Block) : a ^^^ (0 : Block) = a := by
  apply BitVec.eq_of_getLsbD_eq; intro index _; simp

private theorem xor_self' (a : Block) : a ^^^ a = (0 : Block) := by
  apply BitVec.eq_of_getLsbD_eq; intro index _; simp

/-- `((a ^^^ b) ^^^ (b ^^^ c)) ^^^ (a ^^^ d) = d ^^^ c`: the shape of the evaluator's recovery
of the open switch label from the published join. -/
private theorem xor_join_recovery (a b c d : Block) :
    ((a ^^^ b) ^^^ (b ^^^ c)) ^^^ (a ^^^ d) = d ^^^ c := by
  apply BitVec.eq_of_getLsbD_eq; intro index _
  simp only [BitVec.getLsbD_xor]
  generalize a.getLsbD index = A; generalize b.getLsbD index = B
  generalize c.getLsbD index = C; generalize d.getLsbD index = D
  revert A B C D; decide

/-- `(p ^^^ d) ^^^ (r ^^^ c) = ((p ^^^ r) ^^^ d) ^^^ c`: the shape of one `extendLevel` step. -/
private theorem xor_extend (p d r c : Block) :
    (p ^^^ d) ^^^ (r ^^^ c) = ((p ^^^ r) ^^^ d) ^^^ c := by
  apply BitVec.eq_of_getLsbD_eq; intro index _
  simp only [BitVec.getLsbD_xor]
  generalize p.getLsbD index = P; generalize d.getLsbD index = D
  generalize r.getLsbD index = R; generalize c.getLsbD index = C
  revert P D R C; decide

/-! ### The XOR fold -/

/-- Skipping an entry is XOR-folding the family with that entry zeroed. -/
private theorem xorFoldExcept_eq_update {count : Nat} (skip : Fin count)
    (family : Fin count → Block) :
    xorFoldExcept skip family = xorFold (Function.update family skip 0) := by
  unfold xorFoldExcept xorFold
  have body : (fun (acc : Block) (entry : Fin count) =>
        if entry = skip then acc else acc ^^^ family entry)
      = fun (acc : Block) (entry : Fin count) => acc ^^^ Function.update family skip 0 entry := by
    funext acc entry
    by_cases hit : entry = skip
    · subst hit; simp
    · simp [hit]
  rw [body]

/-- The skipped fold only sees the family off the skipped entry. -/
theorem xorFoldExcept_congr {count : Nat} (skip : Fin count) (first second : Fin count → Block)
    (agree : ∀ entry, entry ≠ skip → first entry = second entry) :
    xorFoldExcept skip first = xorFoldExcept skip second := by
  rw [xorFoldExcept_eq_update, xorFoldExcept_eq_update]
  congr 1
  funext entry
  by_cases hit : entry = skip
  · subst hit; simp
  · simp [Function.update_of_ne hit, agree entry hit]

/-- Restoring the skipped entry recovers the full fold. -/
theorem xorFoldExcept_xor {count : Nat} :
    ∀ (skip : Fin count) (family : Fin count → Block),
      xorFoldExcept skip family ^^^ family skip = xorFold family := by
  induction count with
  | zero => intro skip; exact skip.elim0
  | succ n ih =>
    intro skip family
    induction skip using Fin.lastCases with
    | last =>
      rw [xorFoldExcept, xorFold, Fin.foldl_succ_last, Fin.foldl_succ_last]
      simp only [if_neg (Fin.castSucc_ne_last _)]
      rfl
    | cast j =>
      rw [xorFoldExcept, xorFold, Fin.foldl_succ_last, Fin.foldl_succ_last]
      simp only [Fin.castSucc_inj, if_neg (Ne.symm (Fin.castSucc_ne_last j))]
      have restore := ih j (fun entry : Fin n => family entry.castSucc)
      rw [xorFoldExcept, xorFold] at restore
      rw [BitVec.xor_assoc, BitVec.xor_comm (family (Fin.last n)) (family j.castSucc),
        ← BitVec.xor_assoc, restore]

/-- The skipped fold is the full fold with the skipped entry XORed back out. -/
theorem xorFoldExcept_eq {count : Nat} (skip : Fin count) (family : Fin count → Block) :
    xorFoldExcept skip family = xorFold family ^^^ family skip := by
  conv_rhs => rw [← xorFoldExcept_xor skip family]
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-! ### The cleartext one-hot -/

/-- The cleartext one-hot has exactly one live entry. -/
theorem binToHot_eq_ite (width : Nat) (value : BitVec width) (entry : Fin (2 ^ width)) :
    binToHot width value entry = decide (entry.val = value.toNat) := rfl

/-- **Lemma 6.1 (one-hot truth-table evaluation).** For any commutative ring `R`, any
`f : Fin (2 ^ n) -> R` and any `value`, folding the truth table against the one-hot returns
`f value`. Rule O: `Finset.sum_eq_single`, never an enumeration. -/
theorem sum_truthTable_binToHot {R : Type*} [CommRing R] (width : Nat) (value : BitVec width)
    (f : Fin (2 ^ width) → R) :
    (∑ entry : Fin (2 ^ width), (if binToHot width value entry then f entry else 0))
      = f ⟨value.toNat, value.isLt⟩ := by
  rw [Finset.sum_eq_single (⟨value.toNat, value.isLt⟩ : Fin (2 ^ width))
    (fun other _ different => by
      have off : other.val ≠ value.toNat := fun hit => different (Fin.ext hit)
      simp [binToHot, off])
    (fun absent => absurd (Finset.mem_univ _) absent)]
  simp [binToHot]

/-! ### The fold is correct for every tape -/

/-- The published join of the free step `0` is zero. -/
theorem garbleFold_join_zero (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (delta : Block) (zeroLabel : Nat → Block) :
    ∀ steps : Nat, 0 < steps →
      (garbleFold oracle lane chunk delta zeroLabel steps).2 0 = 0 := by
  intro steps
  induction steps with
  | zero => intro contradiction; exact absurd contradiction (by omega)
  | succ n ih =>
    intro _
    show (if (0 : Nat) = n then
        stepJoin n (zeroLabel n)
          (garbleStep oracle lane chunk n (zeroLabel n)
            (garbleFold oracle lane chunk delta zeroLabel n).1)
      else (garbleFold oracle lane chunk delta zeroLabel n).2 0) = 0
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [if_pos rfl]
      show xorFold (garbleStep oracle lane chunk 0 (zeroLabel 0)
        (garbleFold oracle lane chunk delta zeroLabel 0).1) ^^^ zeroLabel 0 = 0
      have single : xorFold (garbleStep oracle lane chunk 0 (zeroLabel 0)
          (garbleFold oracle lane chunk delta zeroLabel 0).1) = zeroLabel 0 := by
        show Fin.foldl 1 _ 0 = _
        rw [Fin.foldl_succ_last]
        simp [garbleStep]
      rw [single, BitVec.xor_self]
      rfl
    · rw [if_neg (by omega)]
      exact ih hn

/-- **The `bin-to-hot` fold invariant.** At every level of the fold the evaluator's label
agrees with the garbler's on the closed entries and differs by `delta` on the live one. -/
theorem evalFold_garbleFold (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (delta : Block) (zeroLabel bitLabel : Nat → Block) (value : Nat) :
    ∀ (steps : Nat) (join : Nat → Block),
      (∀ step, step < steps →
        bitLabel step = zeroLabel step ^^^ (if value.testBit step then delta else 0)) →
      (∀ step, step < steps →
        join step = (garbleFold oracle lane chunk delta zeroLabel steps).2 step) →
      ∀ entry : Fin (2 ^ steps),
        evalFold oracle lane chunk value bitLabel join steps entry
          = (garbleFold oracle lane chunk delta zeroLabel steps).1 entry
            ^^^ (if entry.val = value % 2 ^ steps then delta else 0) := by
  intro steps
  induction steps with
  | zero =>
    intro join _ _ entry
    show (0 : Block) = _
    simp [garbleFold, Nat.mod_one]
  | succ n ih =>
    intro join hbit hjoin entry
    -- the two sides of the fold at level `n`
    set prevG := (garbleFold oracle lane chunk delta zeroLabel n).1 with hprevG
    set rightG := garbleStep oracle lane chunk n (zeroLabel n) prevG with hrightG
    set prevE := evalFold oracle lane chunk value bitLabel join n with hprevE
    set active := activeAt value n with hactive
    set rightE :=
      evalStep oracle lane chunk n (bitLabel n) (join n) active prevE with hrightE
    have expandJoin : ∀ step,
        (garbleFold oracle lane chunk delta zeroLabel (n + 1)).2 step
          = if step = n then stepJoin n (zeroLabel n) rightG
            else (garbleFold oracle lane chunk delta zeroLabel n).2 step := fun _ => rfl
    have hjoinPrev : ∀ step, step < n →
        join step = (garbleFold oracle lane chunk delta zeroLabel n).2 step := by
      intro step hstep
      rw [hjoin step (by omega), expandJoin step, if_neg (by omega)]
    have hjoinTop : join n = xorFold rightG ^^^ zeroLabel n := by
      rw [hjoin n (by omega), expandJoin n, if_pos rfl]
      rfl
    have level : ∀ r : Fin (2 ^ n),
        prevE r = prevG r ^^^ (if r.val = value % 2 ^ n then delta else 0) :=
      ih join (fun step hstep => hbit step (by omega)) hjoinPrev
    have activeVal : (active : Fin (2 ^ n)).val = value % 2 ^ n := rfl
    have hoff : ∀ r : Fin (2 ^ n), r ≠ active → prevE r = prevG r := by
      intro r off
      rw [level r, if_neg (fun hit => off (Fin.ext (hit.trans activeVal.symm))), xor_zero']
    have hon : prevE active = prevG active ^^^ delta := by
      rw [level active, if_pos activeVal]
    have positive : ∀ r : Fin (2 ^ n), r ≠ active → 0 < n := by
      intro r off
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exfalso
        subst hn
        have small : r.val = 0 := by
          have bound := r.isLt; simp only [pow_zero, Nat.lt_one_iff] at bound; exact bound
        have smallActive : (active : Fin (2 ^ 0)).val = 0 := by
          have bound := active.isLt; simp only [pow_zero, Nat.lt_one_iff] at bound; exact bound
        exact off (Fin.ext (small.trans smallActive.symm))
      · exact hn
    have hrightOff : ∀ r : Fin (2 ^ n), r ≠ active → rightE r = rightG r := by
      intro r off
      have hn := positive r off
      show (if r = active then _ else
        foldMask oracle lane chunk n r.val (prevE r)) = _
      rw [if_neg off, hoff r off]
      show _ = if n = 0 then zeroLabel n
        else foldMask oracle lane chunk n r.val (prevG r)
      rw [if_neg (by omega)]
    have hrightOn : rightE active
        = rightG active ^^^ (if value.testBit n then delta else 0) := by
      have swap : (xorFoldExcept active fun other =>
            foldMask oracle lane chunk n other.val (prevE other))
          = xorFoldExcept active rightG := by
        refine xorFoldExcept_congr _ _ _ ?_
        intro other off
        have hn := positive other off
        rw [hoff other off]
        show _ = if n = 0 then zeroLabel n
          else foldMask oracle lane chunk n other.val (prevG other)
        rw [if_neg (by omega)]
      show (if active = active then join n ^^^ bitLabel n ^^^
        (xorFoldExcept active fun other =>
          foldMask oracle lane chunk n other.val (prevE other)) else _) = _
      rw [if_pos rfl, swap, xorFoldExcept_eq, hjoinTop, hbit n (by omega)]
      exact xor_join_recovery _ _ _ _
    have rightRel : ∀ r : Fin (2 ^ n),
        rightE r = rightG r
          ^^^ (if r.val = value % 2 ^ n then (if value.testBit n then delta else 0) else 0) := by
      intro r
      by_cases hitLow : r.val = value % 2 ^ n
      · have same : r = active := Fin.ext (hitLow.trans activeVal.symm)
        rw [if_pos hitLow, same, hrightOn]
      · rw [if_neg hitLow, xor_zero',
          hrightOff r (fun same => hitLow (by rw [same]; exact activeVal))]
    -- the level-`n + 1` modulus
    have hmod : value % 2 ^ (n + 1)
        = value % 2 ^ n + (if value.testBit n then 2 ^ n else 0) := by
      rw [pow_succ, Nat.mod_mul, Nat.testBit_eq_decide_div_mod_eq]
      have split : value / 2 ^ n % 2 = 0 ∨ value / 2 ^ n % 2 = 1 := by omega
      rcases split with hit | hit <;> simp [hit]
    have twoPos : 0 < 2 ^ n := Nat.two_pow_pos n
    have modLt : value % 2 ^ n < 2 ^ n := Nat.mod_lt _ twoPos
    show extendLevel n prevE rightE entry
      = extendLevel n prevG rightG entry ^^^ (if entry.val = value % 2 ^ (n + 1) then delta else 0)
    by_cases below : entry.val < 2 ^ n
    · have combine : (if entry.val = value % 2 ^ n then delta else (0 : Block))
            ^^^ (if entry.val = value % 2 ^ n then
                  (if value.testBit n then delta else (0 : Block)) else 0)
          = (if entry.val = value % 2 ^ (n + 1) then delta else 0) := by
        rw [hmod]
        by_cases bit : value.testBit n
        · simp only [bit, if_true]
          by_cases hitLow : entry.val = value % 2 ^ n
          · have hhigh : ¬(entry.val = value % 2 ^ n + 2 ^ n) := by omega
            rw [if_pos hitLow, if_neg hhigh, xor_self']
          · have hhigh : ¬(entry.val = value % 2 ^ n + 2 ^ n) := by omega
            rw [if_neg hitLow, if_neg hhigh, xor_zero']
        · simp only [Bool.not_eq_true] at bit
          simp only [bit, Bool.false_eq_true, if_false, ite_self, Nat.add_zero]
          exact xor_zero' _
      simp only [extendLevel, dif_pos below]
      rw [level, rightRel]
      dsimp only
      rw [xor_extend]
      conv_lhs => rw [BitVec.xor_assoc]
      rw [combine]
    · have combine : (if entry.val - 2 ^ n = value % 2 ^ n then
              (if value.testBit n then delta else (0 : Block)) else 0)
          = (if entry.val = value % 2 ^ (n + 1) then delta else 0) := by
        rw [hmod]
        by_cases bit : value.testBit n
        · simp only [bit, if_true]
          by_cases hitLow : entry.val - 2 ^ n = value % 2 ^ n
          · have hhigh : entry.val = value % 2 ^ n + 2 ^ n := by omega
            rw [if_pos hitLow, if_pos hhigh]
          · have hhigh : ¬(entry.val = value % 2 ^ n + 2 ^ n) := by omega
            rw [if_neg hitLow, if_neg hhigh]
        · simp only [Bool.not_eq_true] at bit
          simp only [bit, Bool.false_eq_true, if_false, ite_self, Nat.add_zero]
          have hhigh : ¬(entry.val = value % 2 ^ n) := by omega
          rw [if_neg hhigh]
      simp only [extendLevel, dif_neg below]
      rw [rightRel]
      dsimp only
      rw [combine]


/-- The published join vector reads back the fold's own joins: step `0` is free and occupies no
slot, and step `j >= 1` sits at position `j - 1`. -/
theorem joinAt_garbleHot (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (width : Nat) (delta : Block) (bitLabels : Fin width → Block)
    (step : Nat) (inRange : step < width) :
    joinAt (garbleHot oracle lane chunk width delta bitLabels).2 step
      = (garbleFold oracle lane chunk delta (labelAt bitLabels) width).2 step := by
  rcases Nat.eq_zero_or_pos step with hstep | hstep
  · subst hstep
    rw [joinAt, if_pos rfl]
    exact (garbleFold_join_zero oracle lane chunk delta (labelAt bitLabels) width
      (by omega)).symm
  · have slot : step - 1 < width - 1 := by omega
    rw [joinAt, if_neg (by omega), dif_pos slot]
    show (Vector.ofFn fun position : Fin (width - 1) =>
      (garbleFold oracle lane chunk delta (labelAt bitLabels) width).2
        (position.val + 1))[step - 1] = _
    have reduce : ((⟨step - 1, slot⟩ : Fin (width - 1)) : Nat) + 1 = step := by
      show step - 1 + 1 = step
      omega
    rw [Vector.getElem_ofFn slot, reduce]

/-- **Correctness of `bin-to-hot` evaluation.** For every tape, every chunk, every width and
every input, the labels the evaluator reconstructs from the published fold joins agree with the
garbler's labels on the closed entries, and on the live entry they differ by the correlation
`delta`.

`evalHot` takes the cleartext chunk value as a trailing argument: the evaluator selects the
active parent of every fold step from its own input (plan D.9 item 5). `bitKey` is the
garbler's per-bit label pair, correlated by `delta` (free XOR); the garbler folds the zero
labels, the evaluator folds the selected ones. -/
theorem evalHot_garbleHot (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (width : Nat) (delta : Block)
    (bitKey : Fin width → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (value : BitVec width) (entry : Fin (2 ^ width)) :
    evalHot oracle lane chunk width
        (garbleHot oracle lane chunk width delta (fun position => (bitKey position).1)).2
        (selectBits bitKey value) value entry
      = (garbleHot oracle lane chunk width delta (fun position => (bitKey position).1)).1 entry
        ^^^ (if binToHot width value entry then delta else 0) := by
  have hbit : ∀ step, step < width →
      labelAt (selectBits bitKey value) step
        = labelAt (fun position => (bitKey position).1) step
          ^^^ (if value.toNat.testBit step then delta else 0) := by
    intro step inRange
    have bitEq : value[(⟨step, inRange⟩ : Fin width)] = value.toNat.testBit step :=
      BitVec.getElem_eq_testBit_toNat value step inRange
    simp only [labelAt, dif_pos inRange, selectBits, ← bitEq]
    by_cases bit : value[(⟨step, inRange⟩ : Fin width)] = true
    · rw [if_pos bit, if_pos bit, correlated]
    · rw [if_neg bit, if_neg bit, xor_zero']
  have hjoin : ∀ step, step < width →
      joinAt (garbleHot oracle lane chunk width delta (fun position => (bitKey position).1)).2
          step
        = (garbleFold oracle lane chunk delta
            (labelAt fun position => (bitKey position).1) width).2 step :=
    fun step inRange =>
      joinAt_garbleHot oracle lane chunk width delta _ step inRange
  have main := evalFold_garbleFold oracle lane chunk delta
    (labelAt fun position => (bitKey position).1) (labelAt (selectBits bitKey value))
    value.toNat width
    (joinAt (garbleHot oracle lane chunk width delta (fun position => (bitKey position).1)).2)
    hbit hjoin entry
  rw [show evalHot oracle lane chunk width
        (garbleHot oracle lane chunk width delta (fun position => (bitKey position).1)).2
        (selectBits bitKey value) value
      = evalFold oracle lane chunk value.toNat (labelAt (selectBits bitKey value))
        (joinAt (garbleHot oracle lane chunk width delta
          (fun position => (bitKey position).1)).2) width from rfl]
  rw [main, Nat.mod_eq_of_lt value.isLt]
  congr 2
  simp [binToHot]

/-- The instance at the `chunkBits = 5`-bit wide chunks. -/
theorem evalHot_garbleHot_chunkBits (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (delta : Block)
    (bitKey : Fin chunkBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (value : BitVec chunkBits) (entry : Fin (2 ^ chunkBits)) :
    evalHot oracle lane chunk chunkBits
        (garbleHot oracle lane chunk chunkBits delta (fun position => (bitKey position).1)).2
        (selectBits bitKey value) value entry
      = (garbleHot oracle lane chunk chunkBits delta
          (fun position => (bitKey position).1)).1 entry
        ^^^ (if binToHot chunkBits value entry then delta else 0) :=
  evalHot_garbleHot oracle lane chunk chunkBits delta bitKey correlated value entry

/-- The instance at the `narrowChunkBits = 4`-bit narrow chunks. -/
theorem evalHot_garbleHot_narrowChunkBits (oracle : PermutationOracle FixedIndex Block)
    (lane : Lane) (chunk : Fin chunkCount) (delta : Block)
    (bitKey : Fin narrowChunkBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (value : BitVec narrowChunkBits) (entry : Fin (2 ^ narrowChunkBits)) :
    evalHot oracle lane chunk narrowChunkBits
        (garbleHot oracle lane chunk narrowChunkBits delta
          (fun position => (bitKey position).1)).2
        (selectBits bitKey value) value entry
      = (garbleHot oracle lane chunk narrowChunkBits delta
          (fun position => (bitKey position).1)).1 entry
        ^^^ (if binToHot narrowChunkBits value entry then delta else 0) :=
  evalHot_garbleHot oracle lane chunk narrowChunkBits delta bitKey correlated value entry

/-- The instance at the `firstChunkBits = 2`-bit first chunk. -/
theorem evalHot_garbleHot_firstChunkBits (oracle : PermutationOracle FixedIndex Block)
    (lane : Lane) (chunk : Fin chunkCount) (delta : Block)
    (bitKey : Fin firstChunkBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (value : BitVec firstChunkBits) (entry : Fin (2 ^ firstChunkBits)) :
    evalHot oracle lane chunk firstChunkBits
        (garbleHot oracle lane chunk firstChunkBits delta
          (fun position => (bitKey position).1)).2
        (selectBits bitKey value) value entry
      = (garbleHot oracle lane chunk firstChunkBits delta
          (fun position => (bitKey position).1)).1 entry
        ^^^ (if binToHot firstChunkBits value entry then delta else 0) :=
  evalHot_garbleHot oracle lane chunk firstChunkBits delta bitKey correlated value entry

end Kriterion.ArgoMAC.PlanB
