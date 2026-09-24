/-
**Phase 3, P1k — (B2): the reveal mass of `planBShadow`, from the collision product and the
sharper doubling bound.**

On the curve, `M'`'s unflagged reveal bit is the generalised exceptional event `revealOnPred`: some
nonzero digit `o` whose exceptional input `exc_o` agrees with the input `u` at every position `j`
outside the collision set `S = {j | pad₀(j) ⊕ pad₁(j) = Δ}`.

* **The collision product** (`truePads_collision`, `collision_step`): after `HW`'s opening the
  EncPRF part is exactly the bit-`false` pads at the prefix's key (`opening_encExact`), so the
  shadow's bit-`true` pads are fresh answers, uniform on at least `2^128 − 1` outputs, one position
  at a time: for every `T`, `Pr[T ⊆ S] ≤ (1/(2^128 − 1))^{|T|}` (a product potential,
  `collisionPotential`, is a supermartingale along the lazy run). The rest of the shadow only grows
  the state, so it keeps the collision set (`padXor_grows`).
* **The union over `T`** (`reveal_indicator_le`): a revealing digit differs from `u` exactly on a
  set `T ⊆ S` (`DiffersOn`), so `1[reveal] ≤ Σ_T 1[T ⊆ S] · 1[∃ o, DiffersOn o T]`
  (`shadow_reveal_le`).
* **The coins** (`coins_differ_mul_le`): for a fixed `T` each digit has at most one offset whose
  exceptional input differs from `u` exactly on `T` (`differTargets_card_le`: `exc` is injective
  off `φ = 0`, the bit encoding is injective), so P1e's `goodTails_hit_mul_le` gives
  `Pr[∃ o, DiffersOn o T] · (1 − 91/#Point) ≤ 91/#Point`.
* Hence the reveal mass is at most `91 · (1 + 1/(2^128 − 1))^508 / (#Point − 91) ≤ 182/(r − 1)`,
  using only `#Point ≥ r` (`reveal_numeric`).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsRun
import Proof.Privacy.Phase3.PublicFirst.Doubling

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM interceptAnswer whitePadsM)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell consumeCell refillAnswer touch runRefill
  consumeCell_spec AllQ card_unusedOutput)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The collision potential -/

section Potential

/-- `1/(2^128 − 1)`: the collision mass of one fresh bit-`true` pad. -/
abbrev epsPad : ℝ≥0∞ := ((2 ^ 128 - 1 : ℕ) : ℝ≥0∞)⁻¹

open Classical in
/-- **The collision weight of one position**: `ε` while its bit-`true` pad is unasked (and at most
one pair is stored there), then the indicator of the collision. -/
def collisionWeight (w : Block) (delta : EncPRF.Coordinate → Block) (state : LState)
    (j : EncPRF.PermutationIndex) : ℝ≥0∞ :=
  if lk (state.enc j) (padInput true w) = none then
    (if (state.enc j).used ≤ 1 then epsPad else 1)
  else if padXor state j.1 j.2 w = some (delta j.1) then 1 else 0

/-- **The collision potential of a set of positions.** -/
def collisionPotential (w : Block) (delta : EncPRF.Coordinate → Block)
    (T : Finset EncPRF.PermutationIndex) (state : LState) : ℝ≥0∞ :=
  ∏ j ∈ T, collisionWeight w delta state j

/-- The indicator of a proposition, as a weight (one constant, so no decidability instance is ever
synthesised at a use site). -/
def ind (p : Prop) : ℝ≥0∞ := open Classical in if p then 1 else 0

theorem ind_pos {p : Prop} (h : p) : ind p = 1 := by
  unfold ind
  exact if_pos h

theorem ind_neg {p : Prop} (h : ¬ p) : ind p = 0 := by
  unfold ind
  exact if_neg h

theorem ind_mono {p q : Prop} (h : p → q) : ind p ≤ ind q := by
  by_cases hp : p
  · rw [ind_pos hp, ind_pos (h hp)]
  · rw [ind_neg hp]
    exact zero_le

theorem ite_eq_ind (p : Prop) [Decidable p] : (if p then (1 : ℝ≥0∞) else 0) = ind p := by
  by_cases hp : p
  · rw [if_pos hp, ind_pos hp]
  · rw [if_neg hp, ind_neg hp]

theorem uniform_single_le {X : Type} [Fintype X] [Nonempty X] (P : X → Prop) [DecidablePred P]
    (unique : ∀ a b, P a → P b → a = b) :
    ∑' x, PMF.uniformOfFintype X x * (if P x then 1 else 0) ≤
      (Fintype.card X : ℝ≥0∞)⁻¹ := by
  by_cases found : ∃ x, P x
  · obtain ⟨x₀, h₀⟩ := found
    rw [tsum_eq_single x₀]
    · simp [h₀, PMF.uniformOfFintype_apply]
    · intro x different
      have notP : ¬ P x := fun hx => different (unique x x₀ hx h₀)
      simp [notP]
  · simp only [not_exists] at found
    simp [found]

/-- **A fresh bit-`true` pad collides with mass at most the collision weight.** -/
theorem fresh_collision_le (w target : Block) (s : SparsePermutation (2 ^ 128))
    (fresh : ¬ s.knownInput (padInput true w)) (room : s.used < 2 ^ 128)
    [Nonempty (Unknown s)] :
    ∑' y : Unknown s, PMF.uniformOfFintype (Unknown s) y *
      (open Classical in
        if ((lk (s.extend room (s.input.symm (padInput true w)) (s.output.symm y.val))
            (padInput false w)).bind fun zero =>
          (lk (s.extend room (s.input.symm (padInput true w)) (s.output.symm y.val))
            (padInput true w)).map fun one => BitVec.ofFin zero ^^^ BitVec.ofFin one) = some target
        then 1 else 0) ≤
      (if s.used ≤ 1 then epsPad else 1) := by
  classical
  have shapeTrue : ∀ y : Unknown s,
      lk (s.extend room (s.input.symm (padInput true w)) (s.output.symm y.val)) (padInput true w)
        = some y.val := by
    intro y
    rw [lookup_extend s _ _ fresh y.2 room, if_pos rfl]
  have shapeFalse : ∀ y : Unknown s,
      lk (s.extend room (s.input.symm (padInput true w)) (s.output.symm y.val)) (padInput false w)
        = lk s (padInput false w) := by
    intro y
    rw [lookup_extend s _ _ fresh y.2 room, if_neg (padInput_true_ne w).symm]
  simp only [shapeTrue, shapeFalse]
  -- the mass of one output
  have single : ∑' y : Unknown s, PMF.uniformOfFintype (Unknown s) y *
      (if (lk s (padInput false w)).bind (fun zero =>
          (some y.val).map fun one => BitVec.ofFin zero ^^^ BitVec.ofFin one) = some target
        then 1 else 0) ≤ ((2 ^ 128 - s.used : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [← card_unusedOutput s]
    refine uniform_single_le _ fun a b ha hb => ?_
    cases found : lk s (padInput false w) with
    | none => rw [found] at ha; cases ha
    | some zero =>
      rw [found] at ha hb
      simp only [Option.bind_some, Option.map_some, Option.some.injEq] at ha hb
      apply Subtype.ext
      have same : BitVec.ofFin a.val = BitVec.ofFin b.val := by
        have := ha.trans hb.symm
        have cancel := congrArg (BitVec.ofFin zero ^^^ ·) this
        simpa [← BitVec.xor_assoc] using cancel
      exact congrArg BitVec.toFin same
  refine le_trans single ?_
  split_ifs with small
  · exact ENNReal.inv_le_inv.mpr (by exact_mod_cast (show 2 ^ 128 - 1 ≤ 2 ^ 128 - s.used by omega))
  · exact ENNReal.inv_le_one.mpr (by exact_mod_cast (show 1 ≤ 2 ^ 128 - s.used by omega))

open Classical in
/-- **One bit-`true` pad question does not raise the collision potential in expectation.** -/
theorem collision_step (w : Block) (delta : EncPRF.Coordinate → Block)
    (T : Finset EncPRF.PermutationIndex) (position : EncPRF.PermutationIndex) (state : LState) :
    ∑' answer, LazyOracle.query (.encForward position (encodeBit true ^^^ w)) state answer *
      collisionPotential w delta T answer.2 ≤ collisionPotential w delta T state := by
  obtain ⟨c, i⟩ := position
  -- the other positions keep their weight
  have frame : ∀ (next : SparsePermutation (2 ^ 128)) (j : EncPRF.PermutationIndex), j ≠ (c, i) →
      collisionWeight w delta { state with enc := Function.update state.enc (c, i) next } j =
        collisionWeight w delta state j := by
    intro next j different
    obtain ⟨c', i'⟩ := j
    simp only [collisionWeight, padXor, Function.update_of_ne different]
  have split : ∀ next : SparsePermutation (2 ^ 128),
      collisionPotential w delta T { state with enc := Function.update state.enc (c, i) next } =
        (if (c, i) ∈ T then collisionWeight w delta
            { state with enc := Function.update state.enc (c, i) next } (c, i) else 1) *
          ∏ j ∈ T.erase (c, i), collisionWeight w delta state j := by
    intro next
    unfold collisionPotential
    by_cases member : (c, i) ∈ T
    · rw [if_pos member, ← Finset.mul_prod_erase T _ member]
      congr 1
      exact Finset.prod_congr rfl fun j inside => frame next j (Finset.ne_of_mem_erase inside)
    · rw [if_neg member, one_mul, Finset.erase_eq_of_notMem member]
      exact Finset.prod_congr rfl fun j inside => frame next j (fun same => member (same ▸ inside))
  have splitState : collisionPotential w delta T state =
      (if (c, i) ∈ T then collisionWeight w delta state (c, i) else 1) *
        ∏ j ∈ T.erase (c, i), collisionWeight w delta state j := by
    have := split (state.enc (c, i))
    simp only [Function.update_eq_self] at this
    exact this
  change ∑' answer, (((state.enc (c, i)).forward (padInput true w)).distribution.map
      (fun answer => (BitVec.ofFin answer.1,
        { state with enc := Function.update state.enc (c, i) answer.2 }))) answer *
      collisionPotential w delta T answer.2 ≤ _
  rw [tsum_map_mul]
  by_cases known : (state.enc (c, i)).knownInput (padInput true w)
  · have pure : ((state.enc (c, i)).forward (padInput true w)).distribution =
        PMF.pure ((state.enc (c, i)).output ((state.enc (c, i)).input.symm (padInput true w)),
          state.enc (c, i)) := by
      unfold SparsePermutation.forward
      simp only [SparsePermutation.knownInput] at known
      rw [dif_pos known]
      rfl
    rw [pure, tsum_pure_mul]
    simp only [Function.update_eq_self]
    exact le_rfl
  · obtain ⟨room, _, law⟩ := forward_fresh_eq (state.enc (c, i)) (padInput true w) known
    rw [law, tsum_map_mul]
    simp only [split]
    rw [splitState]
    by_cases member : (c, i) ∈ T
    · simp only [if_pos member]
      simp_rw [← mul_assoc]
      rw [ENNReal.tsum_mul_right]
      refine mul_le_mul' ?_ le_rfl
      have unknownLk : lk (state.enc (c, i)) (padInput true w) = none := by
        by_contra found
        exact known ((knownInput_iff _ _).mpr found)
      have weightState : collisionWeight w delta state (c, i) =
          (if (state.enc (c, i)).used ≤ 1 then epsPad else 1) := by
        simp only [collisionWeight, unknownLk, if_true]
      rw [weightState]
      refine le_trans (le_of_eq (tsum_congr fun y => ?_))
        (fresh_collision_le w (delta c) (state.enc (c, i)) known room)
      congr 1
      have present : lk ((state.enc (c, i)).extend room ((state.enc (c, i)).input.symm
          (padInput true w)) ((state.enc (c, i)).output.symm y.val)) (padInput true w) ≠ none := by
        rw [lookup_extend _ _ _ known y.2 room, if_pos rfl]
        simp
      simp only [collisionWeight, padXor, Function.update_self]
      rw [if_neg present]
    · simp only [if_neg member, one_mul]
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The bit-`true` pads' questions are at their input. -/
theorem truePadsM_encInput (keys : WhiteningKeys) :
    AllQ (EncInputIs (encodeBit true ^^^ keys.first)) (truePadsM keys) :=
  (AllQ.vector fun _ => padM_encInput _ _ _ _).bind fun _ =>
    (AllQ.vector fun _ => padM_encInput _ _ _ _).bind fun _ => .pure _

/-- **The collision potential is a supermartingale along the bit-`true` pads.** -/
theorem truePads_collision (w w' : Block) (delta : EncPRF.Coordinate → Block)
    (T : Finset EncPRF.PermutationIndex) (state : LState) :
    ∑' outcome, runLazyQ (truePadsM ⟨w, w'⟩) state outcome * collisionPotential w delta T outcome.2
      ≤ collisionPotential w delta T state :=
  runLazyQ_potential (EncInputIs (encodeBit true ^^^ w)) _ (fun request s holds => by
      cases request with
      | encForward position input =>
        change input = encodeBit true ^^^ w at holds
        subst holds
        exact collision_step w delta T position s
      | fixedForward _ _ => exact holds.elim
      | fixedInverse _ _ => exact holds.elim
      | encInverse _ _ => exact holds.elim
      | hash _ => exact holds.elim)
    _ (truePadsM_encInput ⟨w, w'⟩) state

/-- **On an exact EncPRF part the collision potential is `ε^{|T|}`.** -/
theorem collisionPotential_exact (w : Block) (delta : EncPRF.Coordinate → Block)
    (T : Finset EncPRF.PermutationIndex) (state : LState) (exact : EncExact state w) :
    collisionPotential w delta T state = epsPad ^ T.card := by
  classical
  unfold collisionPotential
  rw [← Finset.prod_const]
  refine Finset.prod_congr rfl fun j _ => ?_
  have missing : lk (state.enc j) (padInput true w) = none := by
    by_contra found
    exact padInput_true_ne w ((exact j _).mp found)
  have small : (state.enc j).used ≤ 1 := by
    rw [← card_known]
    refine Fintype.card_le_one_iff.mpr fun a b => Subtype.ext ?_
    have ha := (exact j a.1).mp ((knownInput_iff _ _).mp a.2)
    have hb := (exact j b.1).mp ((knownInput_iff _ _).mp b.2)
    rw [ha, hb]
  simp only [collisionWeight, missing, if_true, small]

/-- **All of `T` colliding saturates the potential.** -/
theorem collisionPotential_ge (w : Block) (delta : EncPRF.Coordinate → Block)
    (T : Finset EncPRF.PermutationIndex) (state : LState)
    (collide : ∀ j ∈ T, padXor state j.1 j.2 w = some (delta j.1)) :
    1 ≤ collisionPotential w delta T state := by
  classical
  unfold collisionPotential
  rw [Finset.prod_eq_one fun j member => ?_]
  obtain ⟨c, i⟩ := j
  have hit := collide (c, i) member
  have present : lk (state.enc (c, i)) (padInput true w) ≠ none := by
    intro missing
    simp only [padXor] at hit
    rw [show (encodeBit true ^^^ w).toFin = padInput true w from rfl, missing] at hit
    simp at hit
  simp only [collisionWeight, if_neg present]
  exact if_pos hit

end Potential

/-! ### Growth keeps the collisions -/

section Grow

/-- The pads' xor survives growth. -/
theorem padXor_grows {s t : LState} (grow : Grows s t) {coordinate : EncPRF.Coordinate}
    {position : Fin coordinateBitCount} {w v : Block}
    (found : padXor s coordinate position w = some v) : padXor t coordinate position w = some v := by
  unfold padXor at found ⊢
  cases h0 : lk (s.enc (coordinate, position)) (encodeBit false ^^^ w).toFin with
  | none => rw [h0] at found; cases found
  | some a =>
    cases h1 : lk (s.enc (coordinate, position)) (encodeBit true ^^^ w).toFin with
    | none => rw [h0, h1] at found; cases found
    | some b =>
      rw [h0, h1] at found
      rw [grow.enc _ _ _ h0, grow.enc _ _ _ h1]
      exact found

/-- A bit-`true` pad's question is on the transcript of the bit-`true` pads. -/
theorem truePad_mem_transcript (answer : ∀ query : PublicQuery FixedIndex EncPRF.PermutationIndex,
    query.Answer) (keys : WhiteningKeys) (j : EncPRF.PermutationIndex) :
    ⟨.encForward j (encodeBit true ^^^ keys.first),
        answer (.encForward j (encodeBit true ^^^ keys.first))⟩ ∈
      transcript answer (truePadsM keys) := by
  obtain ⟨coordinate, index⟩ := j
  have single : ∀ c : EncPRF.Coordinate,
      (⟨.encForward (c, index) (encodeBit true ^^^ keys.first),
        answer (.encForward (c, index) (encodeBit true ^^^ keys.first))⟩ :
          Entry FixedIndex EncPRF.PermutationIndex) ∈
        transcript answer (Programs.padM keys c index true) := by
    intro c
    exact List.mem_cons_self
  cases coordinate with
  | x =>
    exact mem_transcript_left answer
      (mem_transcript_vector answer coordinateBitCount _ index (single .x))
  | y =>
    exact mem_transcript_right answer (mem_transcript_left answer
      (mem_transcript_vector answer coordinateBitCount _ index (single .y)))

end Grow

/-- An expectation is bounded by a bound on the support. -/
theorem tsum_le_of_support {X : Type} (μ : PMF X) (f : X → ℝ≥0∞) (c : ℝ≥0∞)
    (bound : ∀ x ∈ μ.support, f x ≤ c) : ∑' x, μ x * f x ≤ c := by
  calc ∑' x, μ x * f x ≤ ∑' x, μ x * c := ENNReal.tsum_le_tsum fun x => by
        by_cases member : x ∈ μ.support
        · exact mul_le_mul' le_rfl (bound x member)
        · rw [(PMF.apply_eq_zero_iff _ _).mpr member]
          simp
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ### The reveal event as a union over collision sets -/

section Union

variable [FieldCertificate] [GroupCertificate]

/-- **Digit `o`'s exceptional input differs from `bits` exactly on `T`.** -/
def DiffersOn (scalar : NonZeroScalar) (offsets : FieldMacToECMac.SuccessfulOffsets)
    (bits : BitInput) (T : Finset EncPRF.PermutationIndex) (o : Fin digitCount) : Prop :=
  ∃ phi, digitEndomorphismBase (outputKeyOf scalar offsets o).digit = some phi ∧
    ∀ j : EncPRF.PermutationIndex,
      (inputBit (BitInput.ofAffine (Exception.exceptionalInput phi
          (outputKeyOf scalar offsets o).offset.coordinates)) j.1 j.2 ≠ inputBit bits j.1 j.2 ↔
        j ∈ T)

/-- **A revealing digit differs from `u` on a set of colliding positions.** -/
theorem revealsAt_differs (scalar : NonZeroScalar) (offsets : FieldMacToECMac.SuccessfulOffsets)
    (bits : BitInput) (collide : EncPRF.Coordinate → Fin coordinateBitCount → Prop)
    (o : Fin digitCount) (reveals : RevealsAt scalar offsets bits collide o) :
    ∃ T : Finset EncPRF.PermutationIndex,
      (∀ j ∈ T, collide j.1 j.2) ∧ DiffersOn scalar offsets bits T o := by
  classical
  obtain ⟨phi, digit, agree⟩ := reveals
  refine ⟨Finset.univ.filter fun j : EncPRF.PermutationIndex =>
      inputBit (BitInput.ofAffine (Exception.exceptionalInput phi
        (outputKeyOf scalar offsets o).offset.coordinates)) j.1 j.2 ≠ inputBit bits j.1 j.2,
    ?_, phi, digit, ?_⟩
  · intro j member
    rw [Finset.mem_filter] at member
    exact (agree j.1 j.2).resolve_left member.2
  · intro j
    rw [Finset.mem_filter]
    simp

/-- **The reveal indicator is at most the sum over collision sets.** -/
theorem reveal_indicator_le (scalar : NonZeroScalar) (offsets : FieldMacToECMac.SuccessfulOffsets)
    (bits : BitInput) (collide : EncPRF.Coordinate → Fin coordinateBitCount → Prop) :
    ind (∃ o, RevealsAt scalar offsets bits collide o) ≤
      ∑ T ∈ (Finset.univ : Finset EncPRF.PermutationIndex).powerset,
        ind (∀ j ∈ T, collide j.1 j.2) * ind (∃ o, DiffersOn scalar offsets bits T o) := by
  by_cases hit : ∃ o, RevealsAt scalar offsets bits collide o
  · obtain ⟨o, reveals⟩ := hit
    obtain ⟨T, collides, differs⟩ := revealsAt_differs scalar offsets bits collide o reveals
    rw [ind_pos ⟨o, reveals⟩]
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum
      (f := fun T => ind (∀ j ∈ T, collide j.1 j.2) * ind (∃ o, DiffersOn scalar offsets bits T o))
      (fun _ _ => zero_le) (Finset.mem_powerset.mpr (Finset.subset_univ T)))
    rw [ind_pos collides, ind_pos ⟨o, differs⟩, mul_one]
  · rw [ind_neg hit]
    exact zero_le

/-- The input bits the opening reads. -/
abbrev restoredBits (source : Stage1Source) (input : AffineInput) : BitInput :=
  (Lamport.restore input (sourceLabels source input)).input

/-- The input MAC the opening reads. -/
abbrev restoredMac (source : Stage1Source) (input : AffineInput) : InputMac :=
  (Lamport.restore input (sourceLabels source input)).inputMac

open Classical in
/-- **After the bit-`true` pads, any further lazy questions reveal only on collision sets**: the
reveal indicator of every final state is at most the sum over `T` of the collision potential of the
state right after the pads. -/
theorem pads_reveal_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (coins : Coins) (delta : EncPRF.Coordinate → Block) (state padsState : LState)
    (stored : StoredPath state (curvePrefixM source.publicValue (restoredBits source input)
      (restoredMac source input)))
    (exact : EncExact state (prefixKeysOn state source.publicValue (restoredBits source input)
      (restoredMac source input)).1)
    (padsGrow : Grows state padsState)
    (padsStored : StoredPath padsState (truePadsM
      ⟨(prefixKeysOn state source.publicValue (restoredBits source input)
          (restoredMac source input)).1,
        (prefixKeysOn state source.publicValue (restoredBits source input)
          (restoredMac source input)).2⟩))
    (continuation : FreeQuery Programs.Spec Unit) :
    ∑' result, runLazyQ continuation padsState result *
        ind (revealOnPred scalar source input coins delta result.2) ≤
      ∑ T ∈ (Finset.univ : Finset EncPRF.PermutationIndex).powerset,
        collisionPotential (prefixKeysOn state source.publicValue (restoredBits source input)
            (restoredMac source input)).1 delta T padsState *
          ind (∃ o, DiffersOn scalar coins.offsets (restoredBits source input) T o) := by
  -- after the bit-`true` pads both pads are stored at every position
  have both : ∀ j : EncPRF.PermutationIndex, ∃ v, padXor padsState j.1 j.2
      (prefixKeysOn state source.publicValue (restoredBits source input)
        (restoredMac source input)).1 = some v := by
    intro j
    obtain ⟨c, i⟩ := j
    have zero := ne_none_of_grows (padsGrow.enc (c, i)) ((exact (c, i) _).mpr rfl)
    have one := enc_ne_none_of_stored (padsStored _ (truePad_mem_transcript _ _ (c, i)))
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp zero
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp one
    refine ⟨BitVec.ofFin a ^^^ BitVec.ofFin b, ?_⟩
    unfold padXor
    rw [ha, hb]
    rfl
  refine tsum_le_of_support _ _ _ fun result resultMember => ?_
  have grow := runLazyQ_grows _ padsState result resultMember
  have keysSame : prefixKeysOn result.2 source.publicValue (restoredBits source input)
      (restoredMac source input) = prefixKeysOn state source.publicValue
        (restoredBits source input) (restoredMac source input) :=
    (storedPath_grows _ (padsGrow.trans grow) stored).2
  refine le_trans ?_ (Finset.sum_le_sum fun T _ => mul_le_mul'
    (show ind (∀ j ∈ T, padXor padsState j.1 j.2 (prefixKeysOn state source.publicValue
          (restoredBits source input) (restoredMac source input)).1 = some (delta j.1)) ≤
        collisionPotential (prefixKeysOn state source.publicValue
          (restoredBits source input) (restoredMac source input)).1 delta T padsState by
      by_cases hit : ∀ j ∈ T, padXor padsState j.1 j.2 (prefixKeysOn state source.publicValue
          (restoredBits source input) (restoredMac source input)).1 = some (delta j.1)
      · rw [ind_pos hit]
        exact collisionPotential_ge _ _ _ _ hit
      · rw [ind_neg hit]
        exact zero_le) le_rfl)
  refine le_trans (ind_mono ?_) (reveal_indicator_le scalar coins.offsets (restoredBits source input)
    (fun c i => padXor padsState c i (prefixKeysOn state source.publicValue
      (restoredBits source input) (restoredMac source input)).1 = some (delta c)))
  intro reveals
  unfold revealOnPred at reveals
  dsimp only at reveals
  rw [keysSame] at reveals
  obtain ⟨o, phi, digit, agree⟩ := reveals
  refine ⟨o, phi, digit, fun c i => (agree c i).imp_right fun collide => ?_⟩
  obtain ⟨v, hv⟩ := both (c, i)
  have hv' : padXor padsState c i (prefixKeysOn state source.publicValue
      (restoredBits source input) (restoredMac source input)).1 = some v := hv
  have collide' : padXor result.2 c i (prefixKeysOn state source.publicValue
      (restoredBits source input) (restoredMac source input)).1 = some (delta c) := collide
  rw [padXor_grows grow hv'] at collide'
  show padXor padsState c i _ = some (delta c)
  rw [hv', collide']

open Classical in
/-- **The shadow's reveal mass after the opening**, for fixed coins and offsets `Δ`. -/
theorem shadow_reveal_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (coins : Coins) (delta : EncPRF.Coordinate → Block) (state : LState)
    (stored : StoredPath state (curvePrefixM source.publicValue (restoredBits source input)
      (restoredMac source input)))
    (exact : EncExact state (prefixKeysOn state source.publicValue (restoredBits source input)
      (restoredMac source input)).1) :
    ∑' result, runLazyQ (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) state result *
        ind (revealOnPred scalar source input coins delta result.2) ≤
      ∑ T ∈ (Finset.univ : Finset EncPRF.PermutationIndex).powerset,
        epsPad ^ T.card * ind (∃ o, DiffersOn scalar coins.offsets (restoredBits source input) T o) := by
  rw [shadowOnM_run _ _ _ state stored, runLazyQ_bind, tsum_bind_mul]
  calc _ ≤ ∑' padsRun, runLazyQ (truePadsM
          ⟨(prefixKeysOn state source.publicValue (restoredBits source input)
              (restoredMac source input)).1,
            (prefixKeysOn state source.publicValue (restoredBits source input)
              (restoredMac source input)).2⟩) state padsRun *
          ∑ T ∈ (Finset.univ : Finset EncPRF.PermutationIndex).powerset,
            collisionPotential (prefixKeysOn state source.publicValue (restoredBits source input)
                (restoredMac source input)).1 delta T padsRun.2 *
              ind (∃ o, DiffersOn scalar coins.offsets (restoredBits source input) T o) :=
        ENNReal.tsum_le_tsum fun padsRun => by
          by_cases member : padsRun ∈ (runLazyQ (truePadsM
              ⟨(prefixKeysOn state source.publicValue (restoredBits source input)
                  (restoredMac source input)).1,
                (prefixKeysOn state source.publicValue (restoredBits source input)
                  (restoredMac source input)).2⟩) state).support
          · obtain ⟨padsGrow, padsStored, _⟩ := runLazyQ_stores _ state padsRun member
            exact mul_le_mul' le_rfl (pads_reveal_le scalar source input coins delta state
              padsRun.2 stored exact padsGrow padsStored _)
          · rw [(PMF.apply_eq_zero_iff _ _).mpr member]
            simp
    _ = ∑ T ∈ (Finset.univ : Finset EncPRF.PermutationIndex).powerset,
          (∑' padsRun, runLazyQ (truePadsM
              ⟨(prefixKeysOn state source.publicValue (restoredBits source input)
                  (restoredMac source input)).1,
                (prefixKeysOn state source.publicValue (restoredBits source input)
                  (restoredMac source input)).2⟩) state padsRun *
            collisionPotential (prefixKeysOn state source.publicValue (restoredBits source input)
                (restoredMac source input)).1 delta T padsRun.2) *
              ind (∃ o, DiffersOn scalar coins.offsets (restoredBits source input) T o) := by
        simp_rw [Finset.mul_sum]
        rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun padsRun => ?_
        ring
    _ ≤ _ := Finset.sum_le_sum fun T _ => mul_le_mul'
          (le_trans (truePads_collision _ _ delta T state)
            (le_of_eq (collisionPotential_exact _ delta T state exact))) le_rfl

end Union

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
