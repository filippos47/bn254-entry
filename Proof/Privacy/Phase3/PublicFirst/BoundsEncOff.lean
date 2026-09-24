/-
**Phase 3, P1m — (B1): the EncPRF conjunct off the curve (`designedOff`), and the whole EncPRF
conjunct of `PerPairBound (designedShadow scalar) scalar (4/2^128)`, real.**

Off the curve the designed shadow asks the pads of every position at a uniform coin `k₁`
(`Programs.padsM ⟨k₁, 0⟩`) and system A (fold questions and hash questions at its cells), through
the fill runner `runFillFlag` from the empty oracle.

* `runFillFlag_invariant`, `runFillFlag_potential` — the fill runner's invariants and
  supermartingales (the consumed questions are hash programs at scale inputs).
* `designedOff_enc_inputs` — every stored EncPRF input is `0 ⊕ k₁` or `1 ⊕ k₁`.
* `encIn_off_le` — `Pr[x ∈ encIn_j] ≤ 2/2^128` (the coin);
  `encOut_off_le` — `Pr[y ∈ encOut_j] ≤ 2/2^128` (the exact marginal `outPotential`).
* **`designedShadow_encBound`** — the EncPRF conjunct, on and off the curve.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsEncBound
import Proof.Privacy.Phase3.PublicFirst.BoundsDesigned

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape uniformMaskTape AllQ LaneAt consumeCell
  refillAnswer consumeCell_spec evalLaneM_allQ)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The fill runner: invariants and potentials -/

section Fill

/-- **An invariant of the fill runner**, for a program all of whose questions satisfy `Q`. -/
theorem runFillFlag_invariant (planted : LState) (draw : Cell → PMF (Block × Block))
    (Q : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop) (Inv : LState → Prop)
    (lazyStep : ∀ (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState),
      Q request → Inv state → ∀ answer ∈ (LazyOracle.query request state).support, Inv answer.2)
    (programStep : ∀ (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState)
      (touched : Set Cell) (cell : Cell) (value : Block × Block) (updated : LState),
      Q request → Inv state → consumeCell touched state request = some cell →
        LazyOracle.program request (refillAnswer request value) state = some updated → Inv updated)
    {α : Type} (computation : FreeQuery Programs.Spec α) (holds : AllQ Q computation) :
    ∀ (oracle : LState) (touched : Set Cell) (outcome : α × LState), Inv oracle →
      some outcome ∈ (runFillFlag planted draw computation oracle touched).support →
        Inv outcome.2 := by
  induction computation with
  | pure value =>
    intro oracle touched outcome invariant member
    simp only [runFillFlag, PMF.mem_support_pure_iff, Option.some.injEq] at member
    subst member
    exact invariant
  | query request next ih =>
    intro oracle touched outcome invariant member
    simp only [runFillFlag] at member
    split at member
    · rename_i cell consumed
      simp only [PMF.mem_support_bind_iff] at member
      obtain ⟨value, _, rest⟩ := member
      split at rest
      · simp at rest
      · split at rest
        · simp at rest
        · rename_i updated success
          exact ih _ (AllQ.tail holds _) _ _ _
            (programStep request oracle touched cell value updated (AllQ.head holds) invariant
              consumed success) rest
    · simp only [PMF.mem_support_bind_iff] at member
      obtain ⟨answer, answerMember, rest⟩ := member
      split at rest
      · simp at rest
      · exact ih _ (AllQ.tail holds _) _ _ _
          (lazyStep request oracle (AllQ.head holds) invariant answer answerMember) rest

/-- A potential of an outcome of the fill runner (a stop weighs nothing). -/
def fillWeight {α : Type} (potential : LState → ℝ≥0∞) : Option (α × LState) → ℝ≥0∞
  | none => 0
  | some result => potential result.2

/-- **A supermartingale along the fill runner**, for a potential reading only the EncPRF part and
the off-scale hash lookups (the consumed programs are hash programs at scale inputs). -/
theorem runFillFlag_potential (planted : LState) (draw : Cell → PMF (Block × Block))
    (Q : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop) (potential : LState → ℝ≥0∞)
    (congr : ∀ s s' : LState, s.enc = s'.enc →
      (∀ k, OffScale k → s.hash.lookup k = s'.hash.lookup k) → potential s = potential s')
    (step : ∀ (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState),
      Q request →
        ∑' answer, LazyOracle.query request state answer * potential answer.2 ≤ potential state)
    {α : Type} (computation : FreeQuery Programs.Spec α) (holds : AllQ Q computation) :
    ∀ (oracle : LState) (touched : Set Cell),
      ∑' o, runFillFlag planted draw computation oracle touched o * fillWeight potential o ≤
        potential oracle := by
  induction computation with
  | pure value =>
    intro oracle touched
    simp only [runFillFlag]
    rw [tsum_pure_mul]
    rfl
  | query request next ih =>
    intro oracle touched
    simp only [runFillFlag]
    split
    · rename_i cell consumed
      obtain ⟨input, rfl, _, _, found⟩ := consumeCell_spec consumed
      rw [tsum_bind_mul]
      refine le_trans (ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (?_ :
        _ ≤ potential oracle)) (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
      split
      · rw [tsum_pure_mul]
        exact zero_le
      · split
        · rw [tsum_pure_mul]
          exact zero_le
        · rename_i updated success
          have same : potential updated = potential oracle :=
            congr _ _ (program_hash_enc input _ oracle updated success)
              (program_hash_offScale (cellOf_scale found) success)
          rw [← same]
          exact ih _ (AllQ.tail holds _) _ _
    · rw [tsum_bind_mul]
      refine le_trans (ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (?_ :
        _ ≤ potential answer.2)) (step request oracle (AllQ.head holds))
      split
      · rw [tsum_pure_mul]
        exact zero_le
      · exact ih answer.1 (AllQ.tail holds _) _ _

end Fill

/-! ### The designed off-curve questions -/

section Questions

/-- A question whose EncPRF part is a forward question at one of the two pad inputs of key `w`
(fixed-key and hash questions allowed). -/
def EncAtKey (w : Block) : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward _ _ => True
  | .fixedInverse _ _ => True
  | .encForward _ input => input = encodeBit false ^^^ w ∨ input = encodeBit true ^^^ w
  | .encInverse _ _ => False
  | .hash _ => True

theorem padM_encAtKey (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    AllQ (EncAtKey keys.first) (Programs.padM keys coordinate index bit) := by
  refine AllQ.bind (.query _ _ ?_ fun _ => .pure _) fun _ => .pure _
  cases bit
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem padsM_encAtKey (keys : WhiteningKeys) : AllQ (EncAtKey keys.first) (Programs.padsM keys) := by
  unfold Programs.padsM
  exact (AllQ.vector fun _ => (padM_encAtKey _ _ _ _).bind fun _ =>
    (padM_encAtKey _ _ _ _).bind fun _ => .pure _).bind fun _ =>
      (AllQ.vector fun _ => (padM_encAtKey _ _ _ _).bind fun _ =>
        (padM_encAtKey _ _ _ _).bind fun _ => .pure _).bind fun _ => .pure _

theorem encAtKey_of_laneAt {lane : Lane} (w : Block)
    {request : PublicQuery FixedIndex EncPRF.PermutationIndex} (inside : ∃ c, LaneAt lane c request) :
    EncAtKey w request := by
  obtain ⟨_, inside⟩ := inside
  cases request with
  | fixedForward _ _ => trivial
  | fixedInverse _ _ => exact inside.elim (fun h => h.elim) (fun h => h.elim)
  | encForward _ _ => exact inside.elim (fun h => h.elim) (fun h => h.elim)
  | encInverse _ _ => exact inside.elim (fun h => h.elim) (fun h => h.elim)
  | hash _ => trivial

theorem padsM_forwardOnly (keys : WhiteningKeys) : AllQ ForwardOnly (Programs.padsM keys) := by
  unfold Programs.padsM
  exact (AllQ.vector fun _ => (padM_forwardOnly _ _ _ _).bind fun _ =>
    (padM_forwardOnly _ _ _ _).bind fun _ => .pure _).bind fun _ =>
      (AllQ.vector fun _ => (padM_forwardOnly _ _ _ _).bind fun _ =>
        (padM_forwardOnly _ _ _ _).bind fun _ => .pure _).bind fun _ => .pure _

variable [FieldCertificate]

theorem designedOffM_encAtKey (table : Public) (bits : BitInput) (mac : InputMac) (first : Block) :
    AllQ (EncAtKey first) (designedOffM table bits mac first) := by
  unfold designedOffM systemAM
  refine (padsM_encAtKey ⟨first, 0⟩).bind fun _ => ?_
  refine ((evalLaneM_allQ _ _ _ _ _).mono fun _ inside => encAtKey_of_laneAt first inside).bind
    fun _ => ?_
  exact ((evalLaneM_allQ _ _ _ _ _).mono fun _ inside => encAtKey_of_laneAt first inside).bind
    fun _ => .pure _

theorem designedOffM_forwardOnly (table : Public) (bits : BitInput) (mac : InputMac)
    (first : Block) : AllQ ForwardOnly (designedOffM table bits mac first) := by
  unfold designedOffM systemAM
  refine (padsM_forwardOnly ⟨first, 0⟩).bind fun _ => ?_
  exact (evalLaneM_forwardOnly _ _ _ _ _).bind fun _ =>
    (evalLaneM_forwardOnly _ _ _ _ _).bind fun _ => .pure _

end Questions

/-! ### The EncPRF part off the curve -/

section Off

variable [FieldCertificate] [GroupCertificate]

/-- The two pad inputs of key `w`. -/
def PadInputs (w : Block) (state : LState) : Prop :=
  ∀ j z, lk (state.enc j) z ≠ none → z = padInput false w ∨ z = padInput true w

/-- **After the designed off-curve fill, every stored EncPRF input is a pad input of `k₁`.** -/
theorem designedOff_enc_inputs (table : Public) (bits : BitInput) (mac : InputMac) (first : Block)
    (tape : Tape) (outcome : Unit × LState)
    (member : some outcome ∈ (runFillFlag LazyOracle.empty (fun cell => PMF.pure (tape cell))
      (designedOffM table bits mac first) LazyOracle.empty ∅).support) :
    PadInputs first outcome.2 :=
  runFillFlag_invariant LazyOracle.empty _ (EncAtKey first) (PadInputs first)
    (fun request state holds invariant answer answerMember => by
      cases request with
      | encForward index input =>
        obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        intro j z found
        by_cases same : j = index
        · subst same
          simp only [Function.update_self] at found
          rcases forward_new _ _ drawn drawnMember z found with old | new
          · exact invariant j z old
          · subst new
            rcases holds with h | h
            · exact Or.inl (by rw [h])
            · exact Or.inr (by rw [h])
        · simp only [Function.update_of_ne same] at found
          exact invariant j z found
      | fixedForward _ _ =>
        obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        exact invariant
      | fixedInverse _ _ =>
        obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        exact invariant
      | encInverse _ _ => exact holds.elim
      | hash _ =>
        obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        exact invariant)
    (fun request state _ cell value updated _ invariant consumed success => by
      obtain ⟨input, rfl, _⟩ := consumeCell_spec consumed
      rw [PadInputs, program_hash_enc input _ state updated success]
      exact invariant)
    _ (designedOffM_encAtKey table bits mac first) _ _ outcome
    (fun j z found => absurd rfl found) member

theorem designedOff_offCurve (source : Stage1Source) (input : AffineInput)
    (first : designedOff.Coin) :
    designedOff.offCurve source input first =
      designedOffM source.publicValue (Lamport.restore input (sourceLabels source input)).input
        (Lamport.restore input (sourceLabels source input)).inputMac first := rfl

/-- **Off the curve, an event's mass factors through the coin, the tape and the fill.** -/
theorem off_event_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (G : Block → Tape → ℝ≥0∞)
    (perRun : ∀ first tape, ∑' o, runFillFlag LazyOracle.empty (fun cell => PMF.pure (tape cell))
        (designedOffM source.publicValue (restoredBits source input) (restoredMac source input)
          first) LazyOracle.empty ∅ o *
        fillWeight (fun state => ind (event (pointsOf state))) o ≤ G first tape) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind (event (outcomePoints o)) ≤
      ∑' first, PMF.uniformOfFintype Block first *
        ∑' tape, uniformMaskTape tape * G first tape := by
  unfold designedShadow
  rw [privateStage2U_off]
  unfold offOutcome
  rw [tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun first => mul_le_mul' (le_of_eq rfl) ?_
  rw [tsum_map_mul, tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
  have bound := perRun first tape
  rw [designedOff_offCurve,
    show (Lamport.restore input (sourceLabels source input)).input = restoredBits source input
      from rfl,
    show (Lamport.restore input (sourceLabels source input)).inputMac = restoredMac source input
      from rfl]
  refine le_trans (tsum_mul_le_of_support _ _ _ fun o member => ?_) bound
  rcases o with _ | result
  · exact absurd member (runFillFlag_empty_ne_none _ _ _ _)
  · exact le_rfl

/-- `Pr[k ∈ keysOf x] ≤ 2/2^128` for a uniform key. -/
theorem uniform_keysOf_le (x : Block) :
    ∑' first, PMF.uniformOfFintype Block first * ind (first ∈ keysOf x) ≤
      2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  have single : ∀ a : Block, ∑' first, PMF.uniformOfFintype Block first * ind (first = a) ≤
      ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro a
    have bound := uniform_single_le (X := Block) (fun first => first = a)
      (fun _ _ ha hb => ha.trans hb.symm)
    rw [Kriterion.ArgoMAC.Phase3.Lazy.card_block] at bound
    refine le_trans (le_of_eq (tsum_congr fun first => ?_)) bound
    rw [ite_eq_ind]
  calc ∑' first, PMF.uniformOfFintype Block first * ind (first ∈ keysOf x)
      ≤ ∑' first, (PMF.uniformOfFintype Block first * ind (first = x ^^^ encodeBit false) +
          PMF.uniformOfFintype Block first * ind (first = x ^^^ encodeBit true)) :=
        ENNReal.tsum_le_tsum fun first => by
          rw [← mul_add]
          refine mul_le_mul' le_rfl ?_
          by_cases h : first ∈ keysOf x
          · rw [ind_pos h]
            rcases Finset.mem_insert.mp h with h | h
            · rw [ind_pos h]
              exact le_self_add
            · rw [ind_pos (Finset.mem_singleton.mp h)]
              exact le_add_self
          · rw [ind_neg h]
            exact zero_le
    _ = ∑' first, PMF.uniformOfFintype Block first * ind (first = x ^^^ encodeBit false) +
          ∑' first, PMF.uniformOfFintype Block first * ind (first = x ^^^ encodeBit true) :=
        ENNReal.tsum_add
    _ ≤ ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ + ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := add_le_add (single _) (single _)
    _ = 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by rw [two_mul]

/-- **The EncPRF input mass off the curve.** -/
theorem encIn_off_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (j : EncPRF.PermutationIndex) (x : Block) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind ((outcomePoints o).encIn j x) ≤ 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  refine le_trans (off_event_le scalar source input (fun p => p.encIn j x)
    (fun first _ => ind (first ∈ keysOf x)) fun first tape => ?_) ?_
  · refine le_trans (tsum_mul_le_of_support _ _ (fun _ => ind (first ∈ keysOf x))
      fun o member => ?_) (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
    rcases o with _ | outcome
    · exact zero_le
    · simp only [fillWeight]
      refine ind_mono fun hit => ?_
      rcases designedOff_enc_inputs _ _ _ first tape outcome member j x.toFin hit with same | same
      · exact mem_keysOf_of_pad false (BitVec.toFin_inj.mp same)
      · exact mem_keysOf_of_pad true (BitVec.toFin_inj.mp same)
  · refine le_trans (le_of_eq (tsum_congr fun first => ?_)) (uniform_keysOf_le x)
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **The EncPRF output mass off the curve** (the exact marginal). -/
theorem encOut_off_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (j : EncPRF.PermutationIndex) (y : Block) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind ((outcomePoints o).encOut j y) ≤ 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  refine le_trans (off_event_le scalar source input (fun p => p.encOut j y)
    (fun _ _ => 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹) fun first tape => ?_) ?_
  · refine le_trans (tsum_mul_le_of_support _ _ (fillWeight (outPotential j y.toFin))
      fun o member => ?_) ?_
    · rcases o with _ | outcome
      · exact zero_le
      · simp only [fillWeight]
        have inputs := designedOff_enc_inputs _ _ _ first tape outcome member j
        exact encOut_ind_le j y outcome.2 (used_le_two _ _ _ inputs)
    · refine le_trans (runFillFlag_potential LazyOracle.empty _ ForwardOnly (outPotential j y.toFin)
        (fun s s' same _ => outPotential_congr j y.toFin s s' same)
        (fun request state forward => outPotential_step j y.toFin request forward state) _
        (designedOffM_forwardOnly source.publicValue (restoredBits source input)
          (restoredMac source input) first) LazyOracle.empty ∅) (le_of_eq ?_)
      exact outPotential_empty j y.toFin
  · rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, PMF.tsum_coe, PMF.tsum_coe, one_mul,
      one_mul]

end Off

/-! ### The EncPRF conjunct -/

section Conjunct

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
  [Fintype EncPRF.PermutationIndex]

theorem two_inv_add_two_inv :
    2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ + 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ = 4 / 2 ^ 128 := by
  have cast : ((2 ^ 128 : ℕ) : ℝ≥0∞) = 2 ^ 128 := by rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [cast, ← add_mul, div_eq_mul_inv]
  congr 1
  norm_num

/-- **The EncPRF conjunct of `PerPairBound (designedShadow scalar) scalar (4/2^128)`.** -/
theorem designedShadow_encBound (scalar : NonZeroScalar) (pub : PubPart) (input : AffineInput)
    (i : EncPRF.PermutationIndex) (x y : Block) :
    (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.encIn i x} +
      (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.encOut i y} ≤
        4 / 2 ^ 128 := by
  rw [← two_inv_add_two_inv]
  refine add_le_add (keyedPoints_le_of_source _ _ _ _ _ _ fun source => ?_)
    (keyedPoints_le_of_source _ _ _ _ _ _ fun source => ?_)
  · cases output : Scheme.scheme.function scalar input with
    | none => exact encIn_off_le scalar source input i x
    | some target => exact encIn_onCurve_le scalar designedOff source input target i x
  · cases output : Scheme.scheme.function scalar input with
    | none => exact encOut_off_le scalar source input i y
    | some target => exact encOut_onCurve_le scalar designedOff source input target i y

end Conjunct

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
