/-
**Phase 3, P1o — the coincidence guess, part 2: the tape families.**

Each coincidence event (`LawsGuessReach.lean`) is bounded given the stage-1 view `(P, enc)` by a
family of `swappedChallengeTape`-preserving, view-preserving maps under which the event holds for
at most `2` members out of at least `2^128` (`weighted_guess_ge`):

* **a label event at level `1`** (system B off the curve) and **a gadget event off the curve**: the
  `k₂`-family `familyKey2 0 g` moves every garbler label of system B at level `1` and every gadget
  label by `g`, and keeps the reach's (its pads are keyed by `hash(bridgeInput t_eval)`, a
  different input than `bridgeInput t`);
* **a label event at a level `m + 1 ≥ 2`**: the **transposition family** (`transAct`): the first
  half of the level-`m` fold gate at the routed parent `r' = gateEntry v m r` is precomposed with
  the involution `τ_g` that fixes the garbler's point `G` there and `G ⊕ g` and moves every other
  point by `g`. The garbler asks that gate only at `G`, so its transcript, hence the view and the
  swap kernel's points, are kept; the reach asks it at its own level-`m` label `X ≠ G`, so its
  label at level `m + 1`, entry `r` moves by `π(X) ⊕ π(τ_g X)` (`evalFold_trans`: the routed
  parent is `r`'s own parent, or `r`'s parent is the active one, whose step material XORs every
  other parent's), which hits a given value for at most two `g`;
* **a gadget collision on the curve**: the `Δ`-family moves `pad₀ ⊕ pad₁ ⊕ Δ_κ` by `g`;
* **the bridge event**: the curve family (`Hidden.CurveView`: `mask ↦ c·mask`,
  `t ↦ t − (c − 1)·mask·s`
  over the `p − 1` units `c`) keeps the view and the reach's curve value `t + mask·s`, and moves
  `bridgeInput t` onto a given key for at most two `c` (`Hidden.curve_few`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsGuessReach

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.Guess

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.Phase3.Hidden (transcriptOf QueryOnly TapeShift shiftTape)
open scoped ENNReal

noncomputable section

/-! ### 1. A view-preserving family bounds a weighted guess -/

open Classical in
/-- **The weighted symmetry bound**: if a finite family of law-preserving, view-preserving maps
moves the event onto at most `k` members from every point, the event has mass at most
`k / #G` against every weight on the view. -/
theorem weighted_guess {Ω V G : Type} [Fintype G] (μ : PMF Ω) (view : Ω → V) (w : V → ℝ≥0∞)
    (event : Ω → Prop) (act : G → Ω → Ω) (preserve : ∀ g, μ.map (act g) = μ)
    (sameView : ∀ g ω, view (act g ω) = view ω) (k : ℕ)
    (few : ∀ ω, (Finset.univ.filter fun g => event (act g ω)).card ≤ k) :
    (Fintype.card G : ℝ≥0∞) * ∑' ω, μ ω * (w (view ω) * if event ω then 1 else 0) ≤
      k * ∑' ω, μ ω * w (view ω) := by
  have moved : ∀ g, ∑' ω, μ ω * (w (view ω) * if event ω then 1 else 0) =
      ∑' ω, μ ω * (w (view ω) * if event (act g ω) then 1 else 0) := by
    intro g
    conv_lhs => rw [← preserve g]
    rw [tsum_map_mul]
    simp only [sameView]
  calc (Fintype.card G : ℝ≥0∞) * ∑' ω, μ ω * (w (view ω) * if event ω then 1 else 0)
      = ∑ g : G, ∑' ω, μ ω * (w (view ω) * if event (act g ω) then 1 else 0) := by
        rw [Finset.sum_congr rfl fun g _ => (moved g).symm, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
    _ = ∑' ω, ∑ g : G, μ ω * (w (view ω) * if event (act g ω) then 1 else 0) :=
        (Summable.tsum_finsetSum fun _ _ => ENNReal.summable).symm
    _ = ∑' ω, μ ω * w (view ω) *
          ((Finset.univ.filter fun g => event (act g ω)).card : ℝ≥0∞) := by
        refine tsum_congr fun ω => ?_
        rw [← Finset.sum_boole, Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [mul_assoc]
    _ ≤ ∑' ω, μ ω * w (view ω) * (k : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (by exact_mod_cast few ω)
    _ = k * ∑' ω, μ ω * w (view ω) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun ω => ?_
        rw [mul_comm]

open Classical in
/-- The weighted symmetry bound for a family of at least `2^128` members, divided out. -/
theorem weighted_guess_ge {Ω V G : Type} [Fintype G] (μ : PMF Ω) (view : Ω → V)
    (w : V → ℝ≥0∞) (event : Ω → Prop) (act : G → Ω → Ω) (preserve : ∀ g, μ.map (act g) = μ)
    (sameView : ∀ g ω, view (act g ω) = view ω) (k : ℕ)
    (few : ∀ ω, (Finset.univ.filter fun g => event (act g ω)).card ≤ k)
    (large : 2 ^ 128 ≤ Fintype.card G) :
    ∑' ω, μ ω * (w (view ω) * if event ω then 1 else 0) ≤
      (k / 2 ^ 128 : ℝ≥0∞) * ∑' ω, μ ω * w (view ω) := by
  have counted := weighted_guess μ view w event act preserve sameView k few
  have largeE : (2 ^ 128 : ℝ≥0∞) ≤ (Fintype.card G : ℝ≥0∞) := by exact_mod_cast large
  have pos : (Fintype.card G : ℝ≥0∞) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by positivity) largeE)
  have fin : (Fintype.card G : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc ∑' ω, μ ω * (w (view ω) * if event ω then 1 else 0)
      = (Fintype.card G : ℝ≥0∞)⁻¹ * ((Fintype.card G : ℝ≥0∞) *
          ∑' ω, μ ω * (w (view ω) * if event ω then 1 else 0)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel pos fin, one_mul]
    _ ≤ (Fintype.card G : ℝ≥0∞)⁻¹ * (k * ∑' ω, μ ω * w (view ω)) := mul_le_mul' le_rfl counted
    _ = (k / (Fintype.card G : ℝ≥0∞)) * ∑' ω, μ ω * w (view ω) := by
        rw [ENNReal.div_eq_inv_mul, mul_assoc]
    _ ≤ (k / 2 ^ 128 : ℝ≥0∞) * ∑' ω, μ ω * w (view ω) :=
        mul_le_mul' (ENNReal.div_le_div_left largeE _) le_rfl

open Classical in
/-- The weighted symmetry bound over `Block`. -/
theorem weighted_guess_block {Ω V : Type} (μ : PMF Ω) (view : Ω → V) (w : V → ℝ≥0∞)
    (event : Ω → Prop) (act : Block → Ω → Ω) (preserve : ∀ g, μ.map (act g) = μ)
    (sameView : ∀ g ω, view (act g ω) = view ω) (k : ℕ)
    (few : ∀ ω, (Finset.univ.filter fun g => event (act g ω)).card ≤ k) :
    ∑' ω, μ ω * (w (view ω) * if event ω then 1 else 0) ≤
      (k / 2 ^ 128 : ℝ≥0∞) * ∑' ω, μ ω * w (view ω) :=
  weighted_guess_ge μ view w event act preserve sameView k few
    (le_of_eq (Kriterion.ArgoMAC.Security.PGS.card_block).symm)

/-! ### 2. The fold under a changed gate -/

variable [FieldCertificate] [GroupCertificate]

/-- No gate of step `0` is asked: its only entry is the active one. -/
theorem activeAt_zero (value : Nat) (r : Fin (2 ^ 0)) : r = activeAt value 0 :=
  Fin.ext (by
    have h1 := r.isLt
    have h2 := (activeAt value 0).isLt
    simp only [pow_zero] at h1 h2
    omega)

theorem xorFoldExcept_fin1 (skip : Fin 1) (f : Fin 1 → Block) : xorFoldExcept skip f = 0 := by
  unfold xorFoldExcept
  rw [Fin.foldl_succ, Fin.foldl_zero]
  rw [if_pos (Fin.fin_one_eq_zero skip).symm]

/-- **The reach's level-1 labels are its held bit label, at both entries.** -/
theorem evalFold_level1 (O : PermutationOracle FixedIndex Block) (lane : Lane) (c : Fin chunkCount)
    (value : Nat) (bitLabel join : Nat → Block) (r : Fin (2 ^ 1)) :
    evalFold O lane c value bitLabel join 1 r = join 0 ^^^ bitLabel 0 := by
  have step : ∀ entry : Fin (2 ^ 0), evalStep O lane c 0 (bitLabel 0) (join 0) (activeAt value 0)
      (fun _ => 0) entry = join 0 ^^^ bitLabel 0 := by
    intro entry
    unfold evalStep
    split
    · rw [xorFoldExcept_fin1]
      exact bxor_zero _
    · rename_i off
      exact absurd (activeAt_zero value entry) off
  show extendLevel 0 (fun _ => 0) (evalStep O lane c 0 (bitLabel 0) (join 0) (activeAt value 0)
    (fun _ => 0)) r = _
  unfold extendLevel
  split
  · dsimp only
    rw [step]
    exact bzero_xor _
  · rw [step]

/-- The garbler's level-1 labels: `Δ ⊕ z` and `z`, with `z` the zero label of the chunk's low
bit. -/
def levelOne (delta zero : Block) (r : Fin (2 ^ 1)) : Block :=
  if r.val = 0 then delta ^^^ zero else zero

theorem garbleFold_level1 (O : PermutationOracle FixedIndex Block) (lane : Lane)
    (c : Fin chunkCount) (delta : Block) (zeroLabel : Nat → Block) (r : Fin (2 ^ 1)) :
    (garbleFold O lane c delta zeroLabel 1).1 r = levelOne delta (zeroLabel 0) r := by
  show extendLevel 0 (fun _ => delta) (garbleStep O lane c 0 (zeroLabel 0) fun _ => delta) r = _
  unfold extendLevel garbleStep levelOne
  have r0 : r.val < 2 ^ 0 ↔ r.val = 0 := by
    rw [pow_zero]
    omega
  by_cases zero : r.val = 0
  · rw [dif_pos (r0.mpr zero), if_pos zero, if_pos rfl]
  · rw [dif_neg (fun h => zero (r0.mp h)), if_neg zero, if_pos rfl]

/-- **The garbler's fold depends on each fold gate only at its own level label.** -/
theorem garbleFold_congr (O O' : PermutationOracle FixedIndex Block) (lane : Lane)
    (c : Fin chunkCount) (delta : Block) (zeroLabel : Nat → Block) : ∀ steps,
    (∀ (n : Nat) (r : Fin (2 ^ n)) (half : Bool), n < steps →
      O'.permutation (hotIndexNat lane c n r.val half)
          ((garbleFold O lane c delta zeroLabel n).1 r) =
        O.permutation (hotIndexNat lane c n r.val half)
          ((garbleFold O lane c delta zeroLabel n).1 r)) →
    garbleFold O' lane c delta zeroLabel steps = garbleFold O lane c delta zeroLabel steps
  | 0, _ => rfl
  | steps + 1, agree => by
      have previous := garbleFold_congr O O' lane c delta zeroLabel steps
        fun n r half small => agree n r half (by omega)
      have right : garbleStep O' lane c steps (zeroLabel steps)
          (garbleFold O lane c delta zeroLabel steps).1 =
          garbleStep O lane c steps (zeroLabel steps) (garbleFold O lane c delta zeroLabel steps).1 := by
        funext r
        unfold garbleStep
        split
        · rfl
        · unfold foldMask PlanB.hash daviesMeyer
          rw [agree steps r false (by omega), agree steps r true (by omega)]
      show (extendLevel steps (garbleFold O' lane c delta zeroLabel steps).1
          (garbleStep O' lane c steps (zeroLabel steps) (garbleFold O' lane c delta zeroLabel steps).1),
        fun step => if step = steps then stepJoin steps (zeroLabel steps)
          (garbleStep O' lane c steps (zeroLabel steps) (garbleFold O' lane c delta zeroLabel steps).1)
          else (garbleFold O' lane c delta zeroLabel steps).2 step) =
        (extendLevel steps (garbleFold O lane c delta zeroLabel steps).1
          (garbleStep O lane c steps (zeroLabel steps) (garbleFold O lane c delta zeroLabel steps).1),
        fun step => if step = steps then stepJoin steps (zeroLabel steps)
          (garbleStep O lane c steps (zeroLabel steps) (garbleFold O lane c delta zeroLabel steps).1)
          else (garbleFold O lane c delta zeroLabel steps).2 step)
      rw [previous, right]

/-- **The evaluator's fold below a level reads no gate of that level.** -/
theorem evalFold_congr (O O' : PermutationOracle FixedIndex Block) (lane : Lane)
    (c : Fin chunkCount) (value : Nat) (bitLabel join : Nat → Block) : ∀ steps,
    (∀ (n : Nat) (r : Nat) (half : Bool), n < steps →
      O'.permutation (hotIndexNat lane c n r half) = O.permutation (hotIndexNat lane c n r half)) →
    evalFold O' lane c value bitLabel join steps = evalFold O lane c value bitLabel join steps
  | 0, _ => rfl
  | steps + 1, agree => by
      have previous := evalFold_congr O O' lane c value bitLabel join steps
        fun n r half small => agree n r half (by omega)
      have mask : ∀ (r : Nat) (x : Block), foldMask O' lane c steps r x =
          foldMask O lane c steps r x := by
        intro r x
        unfold foldMask PlanB.hash daviesMeyer
        rw [agree steps r false (by omega), agree steps r true (by omega)]
      show extendLevel steps (evalFold O' lane c value bitLabel join steps)
          (evalStep O' lane c steps (bitLabel steps) (join steps) (activeAt value steps)
            (evalFold O' lane c value bitLabel join steps)) =
        extendLevel steps (evalFold O lane c value bitLabel join steps)
          (evalStep O lane c steps (bitLabel steps) (join steps) (activeAt value steps)
            (evalFold O lane c value bitLabel join steps))
      rw [previous]
      unfold evalStep
      simp only [mask]

/-- Two fold gates of paid levels are equal only at the same level and entry. -/
theorem hotIndexNat_inj {lane lane' : Lane} {c c' : Fin chunkCount} {n n' e e' : Nat}
    {half half' : Bool} (small : n < chunkBits) (small' : n' < chunkBits) (entry : e < 2 ^ n)
    (entry' : e' < 2 ^ n')
    (same : hotIndexNat lane c n e half = hotIndexNat lane' c' n' e' half') :
    lane = lane' ∧ c = c' ∧ n = n' ∧ e = e' ∧ half = half' := by
  have bound : ∀ k, k < chunkBits → 2 ^ k ≤ 2 ^ chunkBits :=
    fun k h => Nat.pow_le_pow_right (by omega) h.le
  rw [hotIndexNat_eq lane c n e half small (lt_of_lt_of_le entry (bound n small)),
    hotIndexNat_eq lane' c' n' e' half' small' (lt_of_lt_of_le entry' (bound n' small'))] at same
  simp only [FixedIndex.hot.injEq, Fin.mk.injEq] at same
  exact same

/-- Fold gates of different paid levels are different. -/
theorem hotIndexNat_fold_ne {lane lane' : Lane} {c c' : Fin chunkCount} {n m e e' : Nat}
    {half half' : Bool} (small : n < chunkBits) (small' : m < chunkBits) (differ : n ≠ m) :
    hotIndexNat lane c n e half ≠ hotIndexNat lane' c' m e' half' := by
  intro hit
  unfold hotIndexNat at hit
  injection hit with _ _ fold
  have level := congrArg Fin.val fold
  simp only [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt small'] at level
  exact differ level

/-- XOR-ing a shift into one entry of a family shifts its skipped fold by it. -/
theorem xorFoldExcept_shift {count : Nat} (skip k : Fin count) (off : k ≠ skip)
    (f : Fin count → Block) (d : Block) :
    xorFoldExcept skip (fun o => f o ^^^ if o = k then d else 0) = xorFoldExcept skip f ^^^ d := by
  rw [xorFoldExcept_eq, xorFoldExcept_eq, Hidden.xorFold_xor, xorFold_single, if_neg off.symm,
    bxor_zero]
  ac_rfl

/-- **One gate half changed at one point moves the fold material of its parent by the change.** -/
theorem foldMask_trans (O O' : PermutationOracle FixedIndex Block) (lane : Lane)
    (c : Fin chunkCount) (m : Nat) (small : m < chunkBits) (r' : Fin (2 ^ m))
    (same : ∀ i, i ≠ hotIndexNat lane c m r'.val false → O'.permutation i = O.permutation i)
    (e : Fin (2 ^ m)) (x : Block) :
    foldMask O' lane c m e.val x = foldMask O lane c m e.val x ^^^
      if e = r' then O.permutation (hotIndexNat lane c m r'.val false) x ^^^
        O'.permutation (hotIndexNat lane c m r'.val false) x else 0 := by
  have halfTrue : hotIndexNat lane c m e.val true ≠ hotIndexNat lane c m r'.val false :=
    fun hit => Bool.noConfusion (hotIndexNat_inj small small e.isLt r'.isLt hit).2.2.2.2
  unfold foldMask PlanB.hash daviesMeyer
  rw [same _ halfTrue]
  by_cases hit : e = r'
  · subst hit
    rw [if_pos rfl]
    generalize O.permutation (hotIndexNat lane c m e.val false) x = a
    generalize O'.permutation (hotIndexNat lane c m e.val false) x = b
    generalize O.permutation (hotIndexNat lane c m e.val true) x = t
    simp only [Cryptography.xor]
    refine BitVec.eq_of_getLsbD_eq fun position _ => ?_
    simp only [BitVec.getLsbD_xor]
    cases a.getLsbD position <;> cases b.getLsbD position <;> cases t.getLsbD position <;>
      cases x.getLsbD position <;> rfl
  · have halfFalse : hotIndexNat lane c m e.val false ≠ hotIndexNat lane c m r'.val false :=
      fun same' => hit (Fin.ext (hotIndexNat_inj small small e.isLt r'.isLt same').2.2.2.1)
    rw [if_neg hit, same _ halfFalse, bxor_zero]

/-- **The transposition lemma.** If only the first half of the level-`m` gate at the non-active
parent `r'` changes, the evaluator's label at level `m + 1`, entry `r`, moves by the change at
`r'`'s level-`m` label — when `r'` is `r`'s parent or `r`'s parent is the active one. -/
theorem evalFold_trans (O O' : PermutationOracle FixedIndex Block) (lane : Lane)
    (c : Fin chunkCount) (value : Nat) (bitLabel join : Nat → Block) (m : Nat)
    (small : m < chunkBits) (r' : Fin (2 ^ m)) (off : r' ≠ activeAt value m)
    (same : ∀ i, i ≠ hotIndexNat lane c m r'.val false → O'.permutation i = O.permutation i)
    (r : Fin (2 ^ (m + 1))) (routed : r'.val = r.val % 2 ^ m ∨ r.val % 2 ^ m = value % 2 ^ m) :
    evalFold O' lane c value bitLabel join (m + 1) r =
      evalFold O lane c value bitLabel join (m + 1) r ^^^
        (O.permutation (hotIndexNat lane c m r'.val false)
            (evalFold O lane c value bitLabel join m r') ^^^
          O'.permutation (hotIndexNat lane c m r'.val false)
            (evalFold O lane c value bitLabel join m r')) := by
  have below : evalFold O' lane c value bitLabel join m = evalFold O lane c value bitLabel join m :=
    evalFold_congr O O' lane c value bitLabel join m fun n e half level =>
      same _ (hotIndexNat_fold_ne (lt_trans level small) small (by omega))
  set prev := evalFold O lane c value bitLabel join m
  set d := O.permutation (hotIndexNat lane c m r'.val false) (prev r') ^^^
    O'.permutation (hotIndexNat lane c m r'.val false) (prev r')
  have masks : ∀ e : Fin (2 ^ m), foldMask O' lane c m e.val (prev e) =
      foldMask O lane c m e.val (prev e) ^^^ if e = r' then d else 0 := by
    intro e
    rw [foldMask_trans O O' lane c m small r' same e (prev e)]
    by_cases hit : e = r'
    · subst hit
      rfl
    · rw [if_neg hit, if_neg hit]
  have right : ∀ e : Fin (2 ^ m), (e = r' ∨ e = activeAt value m) →
      evalStep O' lane c m (bitLabel m) (join m) (activeAt value m) prev e =
        evalStep O lane c m (bitLabel m) (join m) (activeAt value m) prev e ^^^ d := by
    intro e which
    unfold evalStep
    by_cases active : e = activeAt value m
    · rw [if_pos active, if_pos active]
      have shifted : xorFoldExcept (activeAt value m)
          (fun other => foldMask O' lane c m other.val (prev other)) =
          xorFoldExcept (activeAt value m)
            (fun other => foldMask O lane c m other.val (prev other)) ^^^ d := by
        rw [show (fun other : Fin (2 ^ m) => foldMask O' lane c m other.val (prev other)) =
            fun other => foldMask O lane c m other.val (prev other) ^^^ if other = r' then d else 0
          from funext masks]
        exact xorFoldExcept_shift _ r' off _ d
      rw [shifted]
      ac_rfl
    · rw [if_neg active, if_neg active, masks e]
      rcases which with rfl | rfl
      · rw [if_pos rfl]
      · exact absurd rfl active
  show extendLevel m (evalFold O' lane c value bitLabel join m)
      (evalStep O' lane c m (bitLabel m) (join m) (activeAt value m)
        (evalFold O' lane c value bitLabel join m)) r =
    extendLevel m prev (evalStep O lane c m (bitLabel m) (join m) (activeAt value m) prev) r ^^^ d
  rw [below]
  have parent : ∀ e : Fin (2 ^ m), e.val = r.val % 2 ^ m → (e = r' ∨ e = activeAt value m) := by
    intro e eq
    rcases routed with own | act
    · exact Or.inl (Fin.ext (eq.trans own.symm))
    · exact Or.inr (Fin.ext (by simp only [activeAt]; rw [eq, act]))
  unfold extendLevel
  split
  · rename_i lower
    rw [right _ (parent _ (Nat.mod_eq_of_lt lower).symm)]
    ac_rfl
  · rename_i upper
    refine right _ (parent _ ?_)
    have bound : r.val < 2 ^ m + 2 ^ m :=
      calc r.val < 2 ^ (m + 1) := r.isLt
        _ = 2 ^ m + 2 ^ m := by ring
    dsimp only
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ### 3. The transposition family -/

/-- `τ_g`: fixes `G` and `G ⊕ g`, moves every other point by `g`. -/
def transTauFun (g G x : Block) : Block := if x = G ∨ x = G ^^^ g then x else x ^^^ g

theorem transTauFun_involutive (g G : Block) : Function.Involutive (transTauFun g G) := by
  intro x
  unfold transTauFun
  by_cases h : x = G ∨ x = G ^^^ g
  · rw [if_pos h, if_pos h]
  · rw [if_neg h]
    have h' : ¬ (x ^^^ g = G ∨ x ^^^ g = G ^^^ g) := by
      rintro (e | e)
      · apply h
        right
        rw [← e, Hidden.xor_cancel_right]
      · apply h
        left
        rw [← Hidden.xor_cancel_right x g, e, Hidden.xor_cancel_right]
    rw [if_neg h', Hidden.xor_cancel_right]

/-- `τ_g` as a permutation. -/
def transTau (g G : Block) : Equiv.Perm Block := (transTauFun_involutive g G).toPerm _

theorem transTau_apply (g G x : Block) : transTau g G x = transTauFun g G x := rfl

theorem transTau_fix (g G : Block) : transTau g G G = G := by
  rw [transTau_apply]
  unfold transTauFun
  rw [if_pos (Or.inl rfl)]

theorem transTau_transTau (g G x : Block) : transTau g G (transTau g G x) = x :=
  transTauFun_involutive g G x

/-- **Few members hit**: off the fixed point, `π ∘ τ_g` sends `X` to a given value for at most two
`g`. -/
theorem transTau_few (G X y : Block) (π : Equiv.Perm Block) (off : X ≠ G) :
    (Finset.univ.filter fun g => π (transTau g G X) = y).card ≤ 2 := by
  classical
  have sub : (Finset.univ.filter fun g => π (transTau g G X) = y) ⊆
      {G ^^^ X, X ^^^ π.symm y} := by
    intro g member
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
    rw [Finset.mem_insert, Finset.mem_singleton]
    have image : transTau g G X = π.symm y := by rw [← member, Equiv.symm_apply_apply]
    rw [transTau_apply] at image
    unfold transTauFun at image
    by_cases h : X = G ∨ X = G ^^^ g
    · left
      rcases h with h | h
      · exact absurd h off
      · rw [h, Hidden.xor_self_left]
    · right
      rw [if_neg h] at image
      rw [← image, Hidden.xor_self_left]
  calc (Finset.univ.filter fun g => π (transTau g G X) = y).card
      ≤ ({G ^^^ X, X ^^^ π.symm y} : Finset Block).card := Finset.card_le_card sub
    _ ≤ 2 := Finset.card_le_two

open Classical in
/-- Precompose one permutation of a fixed-key oracle with a permutation of `Block`. -/
def transPerm (I : FixedIndex) (τ : Equiv.Perm Block) (O : PermutationOracle FixedIndex Block) :
    PermutationOracle FixedIndex Block :=
  ⟨fun i => if i = I then τ.trans (O.permutation i) else O.permutation i⟩

theorem transPerm_at (I : FixedIndex) (τ : Equiv.Perm Block) (O : PermutationOracle FixedIndex Block)
    (x : Block) : (transPerm I τ O).permutation I x = O.permutation I (τ x) := by
  classical
  show (if I = I then τ.trans (O.permutation I) else O.permutation I) x = _
  rw [if_pos rfl]
  rfl

theorem transPerm_other (I : FixedIndex) (τ : Equiv.Perm Block)
    (O : PermutationOracle FixedIndex Block) (i : FixedIndex) (differ : i ≠ I) :
    (transPerm I τ O).permutation i = O.permutation i := by
  classical
  show (if i = I then τ.trans (O.permutation i) else O.permutation i) = _
  rw [if_neg differ]

/-- Precomposing twice with an involution undoes it. -/
theorem transPerm_transPerm (I : FixedIndex) (τ : Equiv.Perm Block)
    (involutive : ∀ x, τ (τ x) = x) (O : PermutationOracle FixedIndex Block) :
    transPerm I τ (transPerm I τ O) = O := by
  obtain ⟨permutation⟩ := O
  refine congrArg PermutationOracle.mk (funext fun i => ?_)
  by_cases hit : i = I
  · subst hit
    refine Equiv.ext fun x => ?_
    show (transPerm i τ (transPerm i τ ⟨permutation⟩)).permutation i x = permutation i x
    rw [transPerm_at, transPerm_at, involutive]
  · show (transPerm I τ (transPerm I τ ⟨permutation⟩)).permutation i = permutation i
    rw [transPerm_other _ _ _ _ hit, transPerm_other _ _ _ _ hit]

/-- The routed parent of the label event at level `m + 1`, entry `r`. -/
abbrev routedParent (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (m r : Nat) :
    Fin (2 ^ m) :=
  gateEntry (chunkNat input lane c) m r

/-- The fold gate the family of that event acts on: the routed parent's first half. -/
def transIndex (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (m r : Nat) : FixedIndex :=
  hotIndexNat lane c m (routedParent input lane c m r).val false

/-- The garbler's level-`m` label at the routed parent, from the rest of a tape. -/
def transPoint (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (m r : Nat)
    (rest : RestTape TapeRest) : Block :=
  (garbleFold rest.1.2.1 lane c ((Hidden.restKeys rest).1 lane)
    (labelAt fun p => (chunkKey ((Hidden.restKeys rest).2 lane) c p).1) m).1
      (routedParent input lane c m r)

theorem transPoint_restOf (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (m r : Nat)
    (tape : Coins × Oracle) :
    transPoint input lane c m r (Hidden.restOf tape) =
      garbFold tape lane c m (routedParent input lane c m r) := by
  unfold transPoint garbFold
  rw [restKeys_restOf]
  rfl

/-- **The transposition family on the rest of a tape.** -/
def restAct (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (m r : Nat) (g : Block)
    (rest : RestTape TapeRest) : RestTape TapeRest :=
  ((rest.1.1, transPerm (transIndex input lane c m r)
      (transTau g (transPoint input lane c m r rest)) rest.1.2.1, rest.1.2.2), rest.2)

/-- **The transposition family on a tape.** -/
def transAct (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (m r : Nat) (g : Block)
    (tape : Coins × Oracle) : Coins × Oracle :=
  (tape.1, transPerm (transIndex input lane c m r)
    (transTau g (transPoint input lane c m r (Hidden.restOf tape))) tape.2.1, tape.2.2.1,
    tape.2.2.2)

section Family

variable (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (m r : Nat)
  (mSmall : m < chunkWidth c)

include mSmall in
theorem m_lt_chunkBits : m < chunkBits := lt_of_lt_of_le mSmall (chunkWidth_le c)

include mSmall in
/-- A fold gate of a paid level of any chunk is the transposed one only as that gate. -/
theorem hotIndexNat_eq_transIndex {lane' : Lane} {c' : Fin chunkCount} {n e : Nat} {half : Bool}
    (small : n < chunkWidth c') (entry : e < 2 ^ n)
    (same : hotIndexNat lane' c' n e half = transIndex input lane c m r) :
    lane' = lane ∧ c' = c ∧ n = m ∧ e = (routedParent input lane c m r).val ∧ half = false :=
  hotIndexNat_inj (lt_of_lt_of_le small (chunkWidth_le c')) (m_lt_chunkBits c m mSmall) entry
    (routedParent input lane c m r).isLt same

include mSmall in
/-- **The garbler's fold is kept** under a precomposition at the transposed gate that fixes the
garbler's own point there. -/
theorem garbleFold_transPerm (τ : Equiv.Perm Block) (O : PermutationOracle FixedIndex Block)
    (keys : (Lane → Block) × (Lane → Fin PlanB.coordinateBits → Block × Block))
    (fixes : τ ((garbleFold O lane c (keys.1 lane)
        (labelAt fun p => (chunkKey (keys.2 lane) c p).1) m).1 (routedParent input lane c m r)) =
      (garbleFold O lane c (keys.1 lane)
        (labelAt fun p => (chunkKey (keys.2 lane) c p).1) m).1 (routedParent input lane c m r))
    (lane' : Lane) (c' : Fin chunkCount) (n : Nat) (small : n ≤ chunkWidth c') :
    garbleFold (transPerm (transIndex input lane c m r) τ O) lane' c' (keys.1 lane')
        (labelAt fun p => (chunkKey (keys.2 lane') c' p).1) n =
      garbleFold O lane' c' (keys.1 lane') (labelAt fun p => (chunkKey (keys.2 lane') c' p).1) n :=
  garbleFold_congr O _ lane' c' _ _ n fun n' e half level => by
    by_cases hit : hotIndexNat lane' c' n' e.val half = transIndex input lane c m r
    · obtain ⟨laneEq, chunkEq, levelEq, entryEq, halfEq⟩ :=
        hotIndexNat_eq_transIndex input lane c m r mSmall (by omega) e.isLt hit
      subst lane' c' n' half
      obtain rfl : e = routedParent input lane c m r := Fin.ext entryEq
      rw [hit, transPerm_at, fixes]
    · rw [transPerm_other _ _ _ _ hit]

include mSmall in
/-- The garbler's fold up to the transposed level reads no gate of that level. -/
theorem garbleFold_transPerm_below (τ : Equiv.Perm Block) (O : PermutationOracle FixedIndex Block)
    (lane' : Lane) (c' : Fin chunkCount) (delta : Block) (zeroLabel : Nat → Block) (n : Nat)
    (below : n ≤ m) :
    garbleFold (transPerm (transIndex input lane c m r) τ O) lane' c' delta zeroLabel n =
      garbleFold O lane' c' delta zeroLabel n :=
  garbleFold_congr O _ lane' c' _ _ n fun n' e half level => by
    rw [transPerm_other (transIndex input lane c m r) _ _ _ (hotIndexNat_fold_ne
      (lt_trans (lt_of_lt_of_le level below) (m_lt_chunkBits c m mSmall))
      (m_lt_chunkBits c m mSmall) (by omega))]

include mSmall in
theorem transPoint_restAct (g : Block) (rest : RestTape TapeRest) :
    transPoint input lane c m r (restAct input lane c m r g rest) =
      transPoint input lane c m r rest := by
  unfold transPoint
  show (garbleFold (transPerm (transIndex input lane c m r) _ rest.1.2.1) lane c _ _ m).1 _ = _
  rw [garbleFold_transPerm_below input lane c m r mSmall _ _ _ _ _ _ m le_rfl]
  rfl

include mSmall in
theorem restAct_involutive (g : Block) : Function.Involutive (restAct input lane c m r g) := by
  intro rest
  have point := transPoint_restAct input lane c m r mSmall g rest
  show ((rest.1.1, transPerm (transIndex input lane c m r)
      (transTau g (transPoint input lane c m r (restAct input lane c m r g rest)))
      (transPerm (transIndex input lane c m r) (transTau g (transPoint input lane c m r rest))
        rest.1.2.1), rest.1.2.2), rest.2) = rest
  rw [point, transPerm_transPerm _ _ (transTau_transTau g _)]

/-- The rest action as a permutation. -/
def restActEquiv (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (m r : Nat)
    (mSmall : m < chunkWidth c) (g : Block) : RestTape TapeRest ≃ RestTape TapeRest :=
  (restAct_involutive input lane c m r mSmall g).toPerm _

include mSmall in
/-- **The swap kernel's points are kept.** -/
theorem garblerLabels_restAct (g : Block) (rest : RestTape TapeRest) :
    garblerLabels (restAct input lane c m r g rest) = garblerLabels rest := by
  funext site
  show (garbleFold (transPerm (transIndex input lane c m r) _ rest.1.2.1) site.lane site.chunk
      ((Hidden.restKeys rest).1 site.lane)
      (labelAt fun p => (chunkKey ((Hidden.restKeys rest).2 site.lane) site.chunk p).1)
      (chunkWidth site.chunk)).1 site.switch = _
  rw [garbleFold_transPerm input lane c m r mSmall (transTau g (transPoint input lane c m r rest))
    rest.1.2.1 (Hidden.restKeys rest) (transTau_fix g _) site.lane site.chunk
    (chunkWidth site.chunk) le_rfl]
  rfl

theorem transAct_split (g : Block) (tape : RestTape TapeRest × ScaleTable) :
    transAct input lane c m r g (reassembleEquiv (assemble tape)) =
      reassembleEquiv (assemble (restAct input lane c m r g tape.1, tape.2)) := by
  obtain ⟨rest, scale⟩ := tape
  unfold transAct
  rw [restOf_assemble]
  rfl

include mSmall in
/-- **The transposition family keeps the swapped tape.** -/
theorem swapped_trans_invariant (g : Block) :
    swappedChallengeTape.map (transAct input lane c m r g) = swappedChallengeTape := by
  have law : (swapLaw (restLaw restUniform) fun rest => limbPoint (garblerLabels rest)).map
      (fun t => (restAct input lane c m r g t.1, t.2)) =
      swapLaw (restLaw restUniform) fun rest => limbPoint (garblerLabels rest) := by
    unfold swapLaw
    rw [PMF.map_bind]
    have each : ∀ rest : RestTape TapeRest,
        ((swapKernel (limbPoint (garblerLabels rest))).map (Prod.mk rest)).map
            (fun t => (restAct input lane c m r g t.1, t.2)) =
          (swapKernel (limbPoint (garblerLabels (restAct input lane c m r g rest)))).map
            (Prod.mk (restAct input lane c m r g rest)) := by
      intro rest
      rw [PMF.map_comp, garblerLabels_restAct input lane c m r mSmall]
      rfl
    simp only [each]
    have restInvariant : (restLaw restUniform).map (restActEquiv input lane c m r mSmall g) =
        restLaw restUniform := by
      rw [Hidden.restLaw_uniform]
      exact Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv _
    conv_rhs => rw [← restInvariant]
    rw [PMF.bind_map]
    rfl
  unfold swappedChallengeTape swappedTape
  rw [PMF.map_comp, PMF.map_comp, PMF.map_comp]
  have factor : ((transAct input lane c m r g ∘ reassembleEquiv) ∘ assemble) =
      (reassembleEquiv ∘ assemble) ∘ (fun t => (restAct input lane c m r g t.1, t.2)) := by
    funext tape
    exact transAct_split input lane c m r g tape
  rw [factor, ← PMF.map_comp, law]

include mSmall in
/-- The garbler's point at the transposed gate. -/
theorem garblerPointOf_transIndex (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    Hidden.garblerPointOf scalar tape (transIndex input lane c m r) =
      transPoint input lane c m r (Hidden.restOf tape) := by
  have small := m_lt_chunkBits c m mSmall
  have bound : 2 ^ m ≤ 2 ^ chunkBits := Nat.pow_le_pow_right (by omega) small.le
  unfold transIndex
  rw [hotIndexNat_eq lane c m _ false small
      (lt_of_lt_of_le (routedParent input lane c m r).isLt bound),
    garblerPointOf_hot scalar tape lane c m _ false small (routedParent input lane c m r).isLt
      bound,
    transPoint_restOf]

include mSmall in
/-- **The garbler runs identically on the transposed tape.** -/
theorem transAct_garbler (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle) :
    transcriptOf (publicAnswer (transAct input lane c m r g tape).2)
        (Programs.garbleM scalar tape.1) =
        transcriptOf (publicAnswer tape.2) (Programs.garbleM scalar tape.1) ∧
      (Programs.garbleM scalar tape.1).eval (publicAnswer (transAct input lane c m r g tape).2) =
        (Programs.garbleM scalar tape.1).eval (publicAnswer tape.2) := by
  refine Hidden.transcriptOf_of_agrees (Programs.garbleM scalar tape.1) tape.2
    (transAct input lane c m r g tape).2 fun entry member => ?_
  have good := garblerTranscript_good scalar tape entry
    (by rw [garblerTranscript_eq]; exact member)
  rw [← Hidden.transcriptOf_agrees tape.2 _ entry member]
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x =>
      have isGood : x = Hidden.garblerPointOf scalar tape index := good
      show (transPerm (transIndex input lane c m r) _ tape.2.1).permutation index x =
        tape.2.1.permutation index x
      by_cases hit : index = transIndex input lane c m r
      · subst hit
        rw [transPerm_at, isGood, garblerPointOf_transIndex input lane c m r mSmall, transTau_fix]
      · rw [transPerm_other _ _ _ _ hit]
  | fixedInverse _ _ => exact good.elim
  | encForward _ _ => rfl
  | encInverse _ _ => exact good.elim
  | hash _ => rfl

include mSmall in
theorem garble_transAct (parameter : ℕ) (scalar : NonZeroScalar) (g : Block)
    (tape : Coins × Oracle) :
    (Scheme.scheme.garble parameter scalar (transAct input lane c m r g tape)).1 =
      (Scheme.scheme.garble parameter scalar tape).1 := by
  have sameEval := (transAct_garbler input lane c m r mSmall scalar g tape).2
  rw [garble_eval parameter, garble_eval parameter] at sameEval
  exact congrArg Prod.fst sameEval

include mSmall in
/-- **The stage-1 view is kept.** -/
theorem stageOneView_transAct (parameter : ℕ) (scalar : NonZeroScalar) (g : Block)
    (tape : Coins × Oracle) :
    stageOneView parameter scalar (transAct input lane c m r g tape) =
      stageOneView parameter scalar tape := by
  have transcriptEq : garblerTranscript scalar (transAct input lane c m r g tape) =
      garblerTranscript scalar tape := by
    rw [garblerTranscript_eq, garblerTranscript_eq]
    exact (transAct_garbler input lane c m r mSmall scalar g tape).1
  show ((Scheme.scheme.garble parameter scalar (transAct input lane c m r g tape)).1,
      (garblerTranscript scalar (transAct input lane c m r g tape)).filter Entry.IsEnc) =
    ((Scheme.scheme.garble parameter scalar tape).1,
      (garblerTranscript scalar tape).filter Entry.IsEnc)
  rw [garble_transAct input lane c m r mSmall, transcriptEq]

include mSmall in
/-- **The garbler's labels are kept**, at every level of every chunk. -/
theorem garbFold_transAct (g : Block) (tape : Coins × Oracle) (lane' : Lane) (c' : Fin chunkCount)
    (n : Nat) (small : n ≤ chunkWidth c') :
    garbFold (transAct input lane c m r g tape) lane' c' n = garbFold tape lane' c' n := by
  unfold garbFold
  show (garbleFold (transPerm (transIndex input lane c m r)
      (transTau g (transPoint input lane c m r (Hidden.restOf tape))) tape.2.1) lane' c'
      ((Hidden.laneKeys tape).1 lane')
      (labelAt fun p => (chunkKey ((Hidden.laneKeys tape).2 lane') c' p).1) n).1 = _
  rw [garbleFold_transPerm input lane c m r mSmall
    (transTau g (transPoint input lane c m r (Hidden.restOf tape))) tape.2.1
    (Hidden.laneKeys tape) (by
      have key : (garbleFold tape.2.1 lane c ((Hidden.laneKeys tape).1 lane)
          (labelAt fun p => (chunkKey ((Hidden.laneKeys tape).2 lane) c p).1) m).1
            (routedParent input lane c m r) = transPoint input lane c m r (Hidden.restOf tape) := by
        rw [transPoint_restOf]
        rfl
      rw [key]
      exact transTau_fix g _) lane' c' n small]

include mSmall in
/-- **The reach's labels are kept up to the transposed level.** -/
theorem reachFold_transAct_below (parameter : ℕ) (scalar : NonZeroScalar) (g : Block)
    (tape : Coins × Oracle) (n : Nat) (below : n ≤ m) :
    reachFold parameter scalar (transAct input lane c m r g tape) input lane c n =
      reachFold parameter scalar tape input lane c n := by
  unfold reachFold
  rw [garble_transAct input lane c m r mSmall]
  exact evalFold_congr _ _ lane c _ _ _ n fun n' e half level =>
    transPerm_other (transIndex input lane c m r) _ _ _ (hotIndexNat_fold_ne
      (lt_trans (lt_of_lt_of_le level below) (m_lt_chunkBits c m mSmall))
      (m_lt_chunkBits c m mSmall) (by omega))

include mSmall in
/-- **The reach's label at level `m + 1`, entry `r`, moves by the transposed answer at the
routed parent's level-`m` label.** -/
theorem reachFold_transAct (parameter : ℕ) (scalar : NonZeroScalar) (g : Block)
    (tape : Coins × Oracle) (one : 1 ≤ m) (target : Fin (2 ^ (m + 1))) (targetEq : target.val = r) :
    reachFold parameter scalar (transAct input lane c m r g tape) input lane c (m + 1) target =
      reachFold parameter scalar tape input lane c (m + 1) target ^^^
        (tape.2.1.permutation (transIndex input lane c m r)
            (reachFold parameter scalar tape input lane c m (routedParent input lane c m r)) ^^^
          tape.2.1.permutation (transIndex input lane c m r)
            (transTau g (transPoint input lane c m r (Hidden.restOf tape))
              (reachFold parameter scalar tape input lane c m
                (routedParent input lane c m r)))) := by
  subst targetEq
  unfold reachFold
  rw [garble_transAct input lane c m target.val mSmall]
  have shift := evalFold_trans tape.2.1 (transAct input lane c m target.val g tape).2.1 lane c
    (chunkNat input lane c) (labelAt (chunkLabels (laneLabels tape input lane) c))
    (joinAt (hotSlice (lanePub (Scheme.scheme.garble parameter scalar tape).1 lane) c)) m
    (m_lt_chunkBits c m mSmall) (routedParent input lane c m target.val)
    (fun same => gateEntry_ne _ m target.val one (congrArg Fin.val same))
    (fun i differ => transPerm_other _ _ _ _ differ) target
    (gateEntry_routed _ m target.val)
  refine shift.trans ?_
  show _ ^^^ (_ ^^^ (transPerm (transIndex input lane c m target.val) _ tape.2.1).permutation
    (transIndex input lane c m target.val) _) = _
  rw [transPerm_at]
  rfl

end Family

/-! ### 4. A label event above level 1 under the transposition family -/

theorem xor_solve (a b c d : Block) (h : a ^^^ (b ^^^ c) = d) : c = a ^^^ b ^^^ d := by
  subst h
  refine BitVec.eq_of_getLsbD_eq fun i _ => ?_
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

open Classical in
/-- **A label event above level 1 holds for at most two members of the transposition family.** -/
theorem hit_few_trans (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) (m : Fin (chunkWidth c)) (one : m.val ≠ 0)
    (r : Fin (2 ^ (m.val + 1))) (tape : Coins × Oracle) :
    (Finset.univ.filter fun g => Hit parameter scalar
      (transAct input lane c m.val r.val g tape) input lane c m r).card ≤ 2 := by
  have mSmall := m.isLt
  let r' := routedParent input lane c m.val r.val
  have levelBelow : ∀ g, reachFold parameter scalar (transAct input lane c m.val r.val g tape)
      input lane c m.val r' = reachFold parameter scalar tape input lane c m.val r' := fun g =>
    congrFun (reachFold_transAct_below input lane c m.val r.val mSmall parameter scalar g tape
      m.val le_rfl) r'
  have garbBelow : ∀ g, garbFold (transAct input lane c m.val r.val g tape) lane c m.val r' =
      garbFold tape lane c m.val r' := fun g =>
    congrFun (garbFold_transAct input lane c m.val r.val mSmall g tape lane c m.val mSmall.le) r'
  by_cases coin : reachFold parameter scalar tape input lane c m.val r' =
      garbFold tape lane c m.val r'
  · have empty : (Finset.univ.filter fun g => Hit parameter scalar
        (transAct input lane c m.val r.val g tape) input lane c m r) = ∅ := by
      refine Finset.filter_false_of_mem fun g _ hit => ?_
      have parent := hit.2
      rw [if_neg one] at parent
      exact parent ((levelBelow g).trans (coin.trans (garbBelow g).symm))
    rw [empty, Finset.card_empty]
    omega
  · have off : reachFold parameter scalar tape input lane c m.val r' ≠
        transPoint input lane c m.val r.val (Hidden.restOf tape) := by
      rw [transPoint_restOf]
      exact coin
    refine le_trans (Finset.card_le_card ?_) (transTau_few
      (transPoint input lane c m.val r.val (Hidden.restOf tape))
      (reachFold parameter scalar tape input lane c m.val r')
      (reachFold parameter scalar tape input lane c (m.val + 1) r ^^^
        tape.2.1.permutation (transIndex input lane c m.val r.val)
          (reachFold parameter scalar tape input lane c m.val r') ^^^
          garbFold tape lane c (m.val + 1) r)
      (tape.2.1.permutation (transIndex input lane c m.val r.val)) off)
    intro g member
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
    have eq := member.1
    rw [reachFold_transAct input lane c m.val r.val mSmall parameter scalar g tape
      (Nat.one_le_iff_ne_zero.mpr one) r rfl,
      garbFold_transAct input lane c m.val r.val mSmall g tape lane c (m.val + 1) mSmall] at eq
    exact xor_solve _ _ _ _ eq

/-! ### 5. The `k₂`-family: label events at level 1 and gadget events off the curve -/

theorem key2Valid (g : Block) : (familyKey2 0 g).Valid := familyKey2_valid 0 g

theorem key2_tape_coins (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle) :
    (shiftTape (familyKey2 0 g) scalar tape).1 = tape.1 :=
  key2_coins 0 g tape.1

/-- Off the curve, with its bridge input not the garbler's, the reach's pads are kept. -/
theorem padsOf_key2 (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle)
    (input : AffineInput)
    (bridge : bridgeInput (evalKey tape.1 input) ≠ bridgeInput tape.1.bridgeKey) :
    padsOf (shiftTape (familyKey2 0 g) scalar tape) input = padsOf tape input := by
  unfold padsOf
  rw [key2_tape_coins]
  show Programs.realEvalPads tape.2.2.1
      ⟨(Hidden.shiftHash (familyKey2 0 g) tape.1.bridgeKey tape.2.2.2
          (bridgeInput (evalKey tape.1 input))).1,
        (Hidden.shiftHash (familyKey2 0 g) tape.1.bridgeKey tape.2.2.2
          (bridgeInput (evalKey tape.1 input))).2⟩
      (BitInput.ofAffine input) = _
  unfold Hidden.shiftHash
  rw [if_neg bridge, Hidden.relabel_of_not_lt _ _ (bridgeInput_not_lt _)]

theorem macOf_key2 (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle)
    (input : AffineInput) :
    macOf (shiftTape (familyKey2 0 g) scalar tape) input = macOf tape input := by
  unfold macOf
  rw [key2_tape_coins]

theorem laneLabels_key2 (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle)
    (input : AffineInput)
    (bridge : bridgeInput (evalKey tape.1 input) ≠ bridgeInput tape.1.bridgeKey) (lane : Lane) :
    laneLabels (shiftTape (familyKey2 0 g) scalar tape) input lane =
      laneLabels tape input lane := by
  have mac := macOf_key2 scalar g tape input
  have pads := padsOf_key2 scalar g tape input bridge
  cases lane
  · exact congrArg (fun m => Pipeline.macLabels m .x) mac
  · exact congrArg (fun m => Pipeline.macLabels m .y) mac
  · exact congrArg₂ (fun p m => Pipeline.macLabels (Programs.whitenMacOf p m) .x) pads mac
  · exact congrArg₂ (fun p m => Pipeline.macLabels (Programs.whitenMacOf p m) .y) pads mac

theorem joinAt_step0 {width : Nat} (joins : Vector Block (width - 1)) : joinAt joins 0 = 0 :=
  if_pos rfl

/-- The reach's level-1 label is its held label of the chunk's low bit. -/
theorem reachFold_one (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (r : Fin (2 ^ 1)) :
    reachFold parameter scalar tape input lane c 1 r =
      labelAt (chunkLabels (laneLabels tape input lane) c) 0 := by
  unfold reachFold
  rw [evalFold_level1, joinAt_step0]
  exact bzero_xor _

theorem labelAt_step0 {width : Nat} (labels : Fin width → Block) (pos : 0 < width) :
    labelAt labels 0 = labels ⟨0, pos⟩ := by
  unfold labelAt
  rw [dif_pos pos]

/-- The garbler's level-1 labels, from the lane keys. -/
theorem garbFold_one (tape : Coins × Oracle) (lane : Lane) (c : Fin chunkCount)
    (r : Fin (2 ^ 1)) :
    garbFold tape lane c 1 r = levelOne ((Hidden.laneKeys tape).1 lane)
      ((chunkKey ((Hidden.laneKeys tape).2 lane) c ⟨0, chunkWidth_pos c⟩).1) r := by
  unfold garbFold
  rw [garbleFold_level1, labelAt_step0 _ (chunkWidth_pos c)]

theorem levelOne_shift (delta zero g : Block) (r : Fin (2 ^ 1)) :
    levelOne (delta ^^^ 0) (zero ^^^ g) r = levelOne delta zero r ^^^ g := by
  unfold levelOne
  rw [bxor_zero]
  split
  · exact (BitVec.xor_assoc _ _ _).symm
  · rfl

/-- The lane keys of a shifted tape are the shifted rest's. -/
theorem laneKeys_shift (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    Hidden.laneKeys (shiftTape T scalar tape) =
      Hidden.restKeys (Hidden.restShift T scalar (Hidden.restOf tape)) := by
  rw [← restKeys_restOf, Hidden.restOf_shiftTape]

/-- **The `k₂`-family moves the garbler's level-1 labels of system B by `g`.** -/
theorem garbFold_one_key2 (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle)
    (lane : Lane) (point : Hidden.laneIsPoint lane = true) (c : Fin chunkCount)
    (r : Fin (2 ^ 1)) :
    garbFold (shiftTape (familyKey2 0 g) scalar tape) lane c 1 r =
      garbFold tape lane c 1 r ^^^ g := by
  have delta : ((familyKey2 0 g).lane lane).delta = 0 := rfl
  have zero : ((familyKey2 0 g).lane lane).zero (chunkBitIndex c ⟨0, chunkWidth_pos c⟩) = g := by
    simp [TapeShift.lane, familyKey2, point]
  rw [garbFold_one, garbFold_one, laneKeys_shift, ← restKeys_restOf]
  show levelOne ((Hidden.restKeys (Hidden.restShift (familyKey2 0 g) scalar
        (Hidden.restOf tape))).1 lane)
      ((Hidden.restKeys (Hidden.restShift (familyKey2 0 g) scalar (Hidden.restOf tape))).2 lane
        (chunkBitIndex c ⟨0, chunkWidth_pos c⟩)).1 r =
    levelOne ((Hidden.restKeys (Hidden.restOf tape)).1 lane)
      ((Hidden.restKeys (Hidden.restOf tape)).2 lane
        (chunkBitIndex c ⟨0, chunkWidth_pos c⟩)).1 r ^^^
        g
  rw [Hidden.garblerKeys_delta, Hidden.garblerKeys_zero, delta, zero]
  exact levelOne_shift _ _ g r

open Classical in
/-- **A label event at level 1 holds for at most one member of the `k₂`-family.** -/
theorem hit_few_key2 (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) (r : Fin (2 ^ (0 + 1))) (tape : Coins × Oracle) :
    (Finset.univ.filter fun g => Hit parameter scalar (shiftTape (familyKey2 0 g) scalar tape)
      input lane c ⟨0, chunkWidth_pos c⟩ r).card ≤ 2 := by
  refine le_trans (Finset.card_le_card (t := {garbFold tape lane c 1 r ^^^
    reachFold parameter scalar tape input lane c 1 r}) ?_) (by rw [Finset.card_singleton]; omega)
  intro g member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
  obtain ⟨eq, side⟩ := member
  rw [if_pos rfl] at side
  obtain ⟨point, _, bridge⟩ := side
  rw [key2_tape_coins] at bridge
  have reach : reachFold parameter scalar (shiftTape (familyKey2 0 g) scalar tape) input lane c 1 r
      = reachFold parameter scalar tape input lane c 1 r := by
    rw [reachFold_one, reachFold_one, laneLabels_key2 scalar g tape input bridge]
  have eq' : reachFold parameter scalar tape input lane c 1 r = garbFold tape lane c 1 r ^^^ g := by
    rw [← reach, ← garbFold_one_key2 scalar g tape lane point c r]
    exact eq
  rw [Finset.mem_singleton, eq', Hidden.xor_self_left]

/-- The EncPRF coordinate of a gadget coordinate. -/
def encCoord : Coord → EncPRF.Coordinate
  | .x => .x
  | .y => .y

/-- **The garbler's gadget label** is the pad of its bit over the Lamport label of its bit. -/
theorem glabel_eq (tape : Coins × Oracle) (κ : Coord) (position : Fin PlanB.coordinateBits)
    (bit : Bool) :
    glabel tape κ position bit =
      encrypt (Programs.realPads tape.2.2.1 (EncPRF.whiteningKeys tape.2.2.2 tape.1.bridgeKey)
        (encCoord κ) position bit)
        (BitAdaptor.encode (keyAt tape.1.inputMacKey κ position) bit) := by
  unfold glabel keyAt
  cases κ
  · simp only [EncPRF.transformKey, EncPRF.transformCoordinateKey]
    rw [vget_ofFn]
    cases bit <;> rfl
  · simp only [EncPRF.transformKey, EncPRF.transformCoordinateKey]
    rw [vget_ofFn]
    cases bit <;> rfl

theorem encrypt_shift (p l g : Block) : encrypt (p ^^^ g) l = encrypt p l ^^^ g := by
  simp only [encrypt, Cryptography.xor]
  refine BitVec.eq_of_getLsbD_eq fun i _ => ?_
  simp only [BitVec.getLsbD_xor]
  cases p.getLsbD i <;> cases l.getLsbD i <;> cases g.getLsbD i <;> rfl

/-- The whitening keys of a shifted hash: `k₂` moves by the shift. -/
theorem whiteningKeys_shift (T : TapeShift) (hash : EncPRF.HashOracle) (t : BaseField) :
    EncPRF.whiteningKeys (Hidden.shiftHash T t hash) t =
      ⟨(EncPRF.whiteningKeys hash t).first, (EncPRF.whiteningKeys hash t).second ^^^ T.key2⟩ := by
  unfold EncPRF.whiteningKeys Hidden.shiftHash
  rw [if_pos rfl]

/-- **The `k₂`-family moves the garbler's gadget labels by `g`.** -/
theorem glabel_key2 (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle) (κ : Coord)
    (position : Fin PlanB.coordinateBits) (bit : Bool) :
    glabel (shiftTape (familyKey2 0 g) scalar tape) κ position bit =
      glabel tape κ position bit ^^^ g := by
  rw [glabel_eq, glabel_eq, key2_tape_coins]
  have pads := (congrArg (fun keys => Programs.realPads tape.2.2.1 keys (encCoord κ) position bit)
    (whiteningKeys_shift (familyKey2 0 g) tape.2.2.2 tape.1.bridgeKey)).trans
    (Hidden.realPads_shift (familyKey2 0 g) tape.2.2.1
      (EncPRF.whiteningKeys tape.2.2.2 tape.1.bridgeKey) (encCoord κ) position bit)
  refine (congrArg (fun p => encrypt p (BitAdaptor.encode (keyAt tape.1.inputMacKey κ position)
    bit)) pads).trans ?_
  exact encrypt_shift _ _ g

theorem reachGadget_key2 (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle)
    (input : AffineInput)
    (bridge : bridgeInput (evalKey tape.1 input) ≠ bridgeInput tape.1.bridgeKey) (κ : Coord)
    (position : Fin PlanB.coordinateBits) :
    reachGadget (shiftTape (familyKey2 0 g) scalar tape) input κ position =
      reachGadget tape input κ position := by
  unfold reachGadget
  rw [padsOf_key2 scalar g tape input bridge, macOf_key2]

open Classical in
/-- **A gadget event off the curve holds for at most one member of the `k₂`-family.** -/
theorem gadgetOff_few (scalar : NonZeroScalar) (input : AffineInput) (κ : Coord)
    (position : Fin PlanB.coordinateBits) (bit : Bool) (tape : Coins × Oracle) :
    (Finset.univ.filter fun g =>
      GadgetOff (shiftTape (familyKey2 0 g) scalar tape) input κ position bit).card ≤ 2 := by
  refine le_trans (Finset.card_le_card
    (t := {glabel tape κ position bit ^^^ reachGadget tape input κ position}) ?_)
    (by rw [Finset.card_singleton]; omega)
  intro g member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
  obtain ⟨_, bridge, eq⟩ := member
  rw [key2_tape_coins] at bridge
  rw [reachGadget_key2 scalar g tape input bridge, glabel_key2] at eq
  rw [Finset.mem_singleton, eq, Hidden.xor_self_left]

/-! ### 6. The `Δ`-family: gadget collisions on the curve -/

theorem keyAt_inputMacKey (coins : Coins) (κ : Coord) (position : Fin PlanB.coordinateBits) :
    keyAt coins.inputMacKey κ position =
      ⟨coins.inputZero κ position, coins.inputZero κ position ^^^ coins.inputDelta κ⟩ := by
  cases κ <;> exact vget_ofFn _ position

theorem collide_xor (p0 p1 z tz d td : Block) :
    encrypt (p0 ^^^ 0) (z ^^^ tz) ^^^ encrypt (p1 ^^^ 0) (z ^^^ tz ^^^ (d ^^^ td)) =
      encrypt p0 z ^^^ encrypt p1 (z ^^^ d) ^^^ td := by
  rw [bxor_zero, bxor_zero]
  simp only [encrypt, Cryptography.xor]
  refine BitVec.eq_of_getLsbD_eq fun i _ => ?_
  simp only [BitVec.getLsbD_xor]
  cases p0.getLsbD i <;> cases p1.getLsbD i <;> cases z.getLsbD i <;> cases tz.getLsbD i <;>
    cases d.getLsbD i <;> cases td.getLsbD i <;> rfl

/-- **The `Δ`-family moves the collision difference `pad₀ ⊕ pad₁ ⊕ Δ_κ` by `g`.** -/
theorem glabel_deltaU (scalar : NonZeroScalar) (κ : Coord) (input : AffineInput) (g : Block)
    (tape : Coins × Oracle) (position : Fin PlanB.coordinateBits) :
    glabel (shiftTape (familyDeltaU κ input g) scalar tape) κ position false ^^^
        glabel (shiftTape (familyDeltaU κ input g) scalar tape) κ position true =
      glabel tape κ position false ^^^ glabel tape κ position true ^^^ g := by
  rw [glabel_eq, glabel_eq, glabel_eq, glabel_eq]
  have pads : ∀ bit, Programs.realPads tape.2.2.1
      (EncPRF.whiteningKeys (Hidden.shiftHash (familyDeltaU κ input g) tape.1.bridgeKey tape.2.2.2)
        tape.1.bridgeKey) (encCoord κ) position bit =
      Programs.realPads tape.2.2.1 (EncPRF.whiteningKeys tape.2.2.2 tape.1.bridgeKey) (encCoord κ)
        position bit ^^^ (familyDeltaU κ input g).key2 := fun bit =>
    (congrArg (fun keys => Programs.realPads tape.2.2.1 keys (encCoord κ) position bit)
      (whiteningKeys_shift (familyDeltaU κ input g) tape.2.2.2 tape.1.bridgeKey)).trans
      (Hidden.realPads_shift (familyDeltaU κ input g) tape.2.2.1
        (EncPRF.whiteningKeys tape.2.2.2 tape.1.bridgeKey) (encCoord κ) position bit)
  have key := keyAt_inputMacKey (Hidden.shiftCoins (familyDeltaU κ input g) tape.1) κ position
  have key0 := keyAt_inputMacKey tape.1 κ position
  have tDelta : (familyDeltaU κ input g).delta κ = g := if_pos rfl
  have moved := congrArg₂ (fun a b =>
    encrypt a (BitAdaptor.encode
      (keyAt (Hidden.shiftCoins (familyDeltaU κ input g) tape.1).inputMacKey κ position) false) ^^^
    encrypt b (BitAdaptor.encode
      (keyAt (Hidden.shiftCoins (familyDeltaU κ input g) tape.1).inputMacKey κ position) true))
      (pads false) (pads true)
  refine moved.trans ?_
  rw [key, key0]
  simp only [BitAdaptor.encode, Bool.false_eq_true, if_false, if_true]
  refine (collide_xor _ _ _ _ _ _).trans ?_
  rw [tDelta]

open Classical in
/-- **A gadget collision holds for at most one member of the `Δ`-family.** -/
theorem gadgetOn_few (scalar : NonZeroScalar) (input : AffineInput) (κ : Coord)
    (position : Fin PlanB.coordinateBits) (tape : Coins × Oracle) :
    (Finset.univ.filter fun g =>
      GadgetOn (shiftTape (familyDeltaU κ input g) scalar tape) κ position).card ≤ 2 := by
  refine le_trans (Finset.card_le_card
    (t := {glabel tape κ position false ^^^ glabel tape κ position true}) ?_)
    (by rw [Finset.card_singleton]; omega)
  intro g member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
  have moved := glabel_deltaU scalar κ input g tape position
  rw [member, BitVec.xor_self] at moved
  rw [Finset.mem_singleton]
  have zero : glabel tape κ position false ^^^ glabel tape κ position true ^^^ g = 0 :=
    moved.symm
  calc g = (glabel tape κ position false ^^^ glabel tape κ position true) ^^^
        ((glabel tape κ position false ^^^ glabel tape κ position true) ^^^ g) :=
        (Hidden.xor_self_left _ g).symm
    _ = (glabel tape κ position false ^^^ glabel tape κ position true) ^^^ 0 := by rw [zero]
    _ = _ := bxor_zero _

/-! ### 7. The curve family: the bridge event -/

/-- The reach's curve value on the curve coordinates. -/
def coordKey (input : AffineInput) (z : CurveCoord input) : BaseField :=
  evalKey z.1.1.1 input

/-- **The curve family keeps the reach's curve value** `t + mask·s`. -/
theorem coordKey_shift (input : AffineInput) (c : BaseFieldˣ) (z : CurveCoord input) :
    coordKey input (curveShiftCoord input c z) = coordKey input z := by
  show (curveRest input c z.1).1.1.bridgeKey +
      (curveRest input c z.1).1.1.curveMask.value * curveGap input =
    z.1.1.1.bridgeKey + z.1.1.1.curveMask.value * curveGap input
  rw [curveRest_bridgeKey]
  show z.1.1.1.bridgeKey - ((c : BaseField) - 1) * z.1.1.1.curveMask.value * curveGap input +
      (c : BaseField) * z.1.1.1.curveMask.value * curveGap input = _
  ring

theorem modulus_large : 2 ^ 128 ≤ Fintype.card BaseFieldˣ := by
  rw [card_units_base]
  have big := two_pow_150_lt_baseFieldModulus
  have le : 2 ^ 128 ≤ 2 ^ 150 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

open Classical in
set_option linter.constructorNameAsVariable false in
/-- **The bridge event's guess bound**: off the curve, given the stage-1 view, the reach's bridge
input is the garbler's with mass at most `2/(p − 1) ≤ 2/2^128`. -/
theorem bridge_bound (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
        if BridgeHit tape input then 1 else 0) ≤
      (2 / 2 ^ 128 : ℝ≥0∞) *
        ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) := by
  by_cases valid : validate input = true
  · have none' : ∀ tape : Coins × Oracle, ¬ BridgeHit tape input := fun tape hit => by
      rw [hit.1] at valid
      cases valid
    simp only [none', if_false, mul_zero, tsum_zero]
    exact zero_le
  · have invalid : validate input = false := by simpa using valid
    let Φ := curveCoord input
    have view : ∀ tape, stageOneView parameter scalar tape =
        (curveView scalar input (Φ tape)).1 := fun tape =>
      congrArg Prod.fst (view_eq parameter scalar input invalid tape)
    have event : ∀ tape, BridgeHit tape input ↔
        bridgeInput (coordKey input (Φ tape)) = bridgeInput (Φ tape).1.1.1.bridgeKey :=
      fun tape => ⟨fun hit => hit.2, fun hit => ⟨invalid, hit⟩⟩
    have transfer : ∀ F : CurveCoord input → ℝ≥0∞,
        ∑' tape, swappedChallengeTape tape * F (Φ tape) = ∑' z, curveLaw input z * F z := by
      intro F
      rw [← swapped_curveCoord input, tsum_map_mul]
    have left := transfer fun z => weight (curveView scalar input z).1 *
      if bridgeInput (coordKey input z) = bridgeInput z.1.1.1.bridgeKey then 1 else 0
    have right := transfer fun z => weight (curveView scalar input z).1
    have bound := weighted_guess_ge (curveLaw input) (fun z => (curveView scalar input z).1) weight
      (fun z => bridgeInput (coordKey input z) = bridgeInput z.1.1.1.bridgeKey)
      (fun c => curveShiftCoord input c) (fun c => curveLaw_shift input c)
      (fun c z => congrArg Prod.fst (curveView_shift scalar input c z)) 2 (fun z => by
        refine curve_few input invalid z.1 (bridgeInput (coordKey input z)) _ fun c member => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
        rw [coordKey_shift] at member
        exact member.symm) modulus_large
    calc ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
          if BridgeHit tape input then 1 else 0)
        = ∑' z, curveLaw input z * (weight (curveView scalar input z).1 *
            if bridgeInput (coordKey input z) = bridgeInput z.1.1.1.bridgeKey then 1 else 0) := by
          rw [← left]
          exact tsum_congr fun tape => by simp only [view, event]
      _ ≤ (2 / 2 ^ 128 : ℝ≥0∞) * ∑' z, curveLaw input z * weight (curveView scalar input z).1 := by
          exact_mod_cast bound
      _ = (2 / 2 ^ 128 : ℝ≥0∞) *
            ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) := by
          rw [← right]
          exact congrArg _ (tsum_congr fun tape => by simp only [view])

/-! ### 8. The guess bounds of the events -/

open Classical in
/-- **A label event's guess bound**: the `k₂`-family at level 1, the transposition family
above. -/
theorem hit_bound (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (lane : Lane)
    (c : Fin chunkCount) (m : Fin (chunkWidth c)) (r : Fin (2 ^ (m.val + 1)))
    (weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
        if Hit parameter scalar tape input lane c m r then 1 else 0) ≤
      (2 / 2 ^ 128 : ℝ≥0∞) *
        ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) := by
  by_cases zero : m.val = 0
  · obtain ⟨m, mSmall⟩ := m
    simp only at zero
    subst zero
    exact weighted_guess_block swappedChallengeTape (stageOneView parameter scalar) weight
      (fun tape => Hit parameter scalar tape input lane c ⟨0, mSmall⟩ r)
      (fun g => shiftTape (familyKey2 0 g) scalar)
      (fun g => Hidden.swapped_shift_invariant (familyKey2 0 g) (key2Valid g) scalar)
      (fun g tape => stageOneView_shift (familyKey2 0 g) (key2Valid g) parameter scalar tape) 2
      (hit_few_key2 parameter scalar input lane c r)
  · exact weighted_guess_block swappedChallengeTape (stageOneView parameter scalar) weight
      (fun tape => Hit parameter scalar tape input lane c m r)
      (fun g => transAct input lane c m.val r.val g)
      (fun g => swapped_trans_invariant input lane c m.val r.val m.isLt g)
      (fun g tape => stageOneView_transAct input lane c m.val r.val m.isLt parameter scalar g tape)
      2 (hit_few_trans parameter scalar input lane c m zero r)

open Classical in
/-- **A gadget event's guess bound off the curve.** -/
theorem gadgetOff_bound (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (κ : Coord) (position : Fin PlanB.coordinateBits) (bit : Bool)
    (weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
        if GadgetOff tape input κ position bit then 1 else 0) ≤
      (2 / 2 ^ 128 : ℝ≥0∞) *
        ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) :=
  weighted_guess_block swappedChallengeTape (stageOneView parameter scalar) weight
    (fun tape => GadgetOff tape input κ position bit) (fun g => shiftTape (familyKey2 0 g) scalar)
    (fun g => Hidden.swapped_shift_invariant (familyKey2 0 g) (key2Valid g) scalar)
    (fun g tape => stageOneView_shift (familyKey2 0 g) (key2Valid g) parameter scalar tape) 2
    (gadgetOff_few scalar input κ position bit)

open Classical in
/-- **A gadget collision's guess bound on the curve.** -/
theorem gadgetOn_bound (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (κ : Coord)
    (position : Fin PlanB.coordinateBits)
    (weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
        if GadgetOn tape κ position then 1 else 0) ≤
      (2 / 2 ^ 128 : ℝ≥0∞) *
        ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) :=
  weighted_guess_block swappedChallengeTape (stageOneView parameter scalar) weight
    (fun tape => GadgetOn tape κ position) (fun g => shiftTape (familyDeltaU κ input g) scalar)
    (fun g => Hidden.swapped_shift_invariant (familyDeltaU κ input g)
      (familyDeltaU_valid κ input g) scalar)
    (fun g tape => stageOneView_shift (familyDeltaU κ input g) (familyDeltaU_valid κ input g)
      parameter scalar tape) 2
    (gadgetOn_few scalar input κ position)

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.Guess
