/-
**Phase 3, P1l — the two laws, part 5: the designed shadow's off-curve private run, eager.**

`designedOff_eager`: averaged against any lookup-invariant weight of its final state, the designed
shadow's off-curve private run (the pads at a uniform coin `k₁`, then system A filled from the mask
tape) is

```
E_{k₁} E_{T ~ uniformMaskTape} E_{O ~ uniform oracle} E_{v uniform}
  Φ (plantAll (transcript (fixedAnswer v T) systemA) (plantAll (transcript O (padsM k₁)) ∅)),
```

i.e. the pads read a uniform oracle and system A a uniform table of fixed-key answers and the mask
tape (`runLazyQ_eager`, `runFill_once`, `once_systemAM`): the fill run of a sequence whose first stage
asks only EncPRF questions is the lazy first stage then the fill of the second (`runFill_encBind`),
and an EncPRF-only stage leaves the fixed-key and hash parts of the state as they were
(`runLazyQ_enc_fixed`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnce

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape AllQ EncAt consumeCell touch)
open scoped ENNReal

noncomputable section

section Enc

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

theorem touch_enc (index : EncPRF.PermutationIndex) (input : Block) (τ : Set Cell) :
    touch (.encForward index input) τ = τ := by
  ext cell
  simp only [touch, Set.mem_ofPred_eq, Kriterion.ArgoMAC.Phase3.Lazy.touchedCell, reduceCtorEq,
    or_false]

/-- **A fill run whose first stage asks only EncPRF questions is the lazy first stage, then the
fill of the rest.** -/
theorem runFill_encBind (draw : Cell → PMF (Block × Block)) {α β : Type}
    {c : FreeQuery Programs.Spec α} (enc : AllQ EncAt c) (f : α → FreeQuery Programs.Spec β) :
    ∀ (s : LState) (τ : Set Cell),
      runFillFlag LazyOracle.empty draw (c >>= f) s τ =
        (runLazyQ c s).bind fun r => runFillFlag LazyOracle.empty draw (f r.1) r.2 τ := by
  induction enc with
  | pure value =>
      intro s τ
      show runFillFlag LazyOracle.empty draw (f value) s τ = (PMF.pure (value, s)).bind _
      rw [PMF.pure_bind]
  | query request next isEnc rest ih =>
      intro s τ
      cases request with
      | encForward index input =>
          show runFillFlag LazyOracle.empty draw
              (FreeQuery.query (.encForward index input) fun answer => next answer >>= f) s τ = _
          simp only [runFillFlag, runLazyQ, consumeCell, PMF.bind_bind]
          refine congrArg _ (funext fun answer => ?_)
          rw [if_neg (not_fullTouch_empty _ _), touch_enc, ih answer.1 answer.2 τ]
      | fixedForward _ _ => exact isEnc.elim
      | fixedInverse _ _ => exact isEnc.elim
      | encInverse _ _ => exact isEnc.elim
      | hash _ => exact isEnc.elim

/-- An EncPRF-only lazy run leaves the fixed-key and hash parts of the state as they were. -/
theorem runLazyQ_enc_fixed {α : Type} {c : FreeQuery Programs.Spec α} (enc : AllQ EncAt c) :
    ∀ (s : LState) (r : α × LState), r ∈ (runLazyQ c s).support →
      r.2.fixed = s.fixed ∧ r.2.hash = s.hash := by
  induction enc with
  | pure value =>
      intro s r member
      simp only [runLazyQ, PMF.support_pure, Set.mem_singleton_iff] at member
      rw [member]
      exact ⟨rfl, rfl⟩
  | query request next isEnc rest ih =>
      intro s r member
      cases request with
      | encForward index input =>
          simp only [runLazyQ] at member
          obtain ⟨answer, answerMember, inner⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          rw [(ih answer.1 answer.2 r inner).1, (ih answer.1 answer.2 r inner).2]
          simp only [LazyOracle.query, PMF.support_map] at answerMember
          obtain ⟨_, _, rfl⟩ := answerMember
          exact ⟨rfl, rfl⟩
      | fixedForward _ _ => exact isEnc.elim
      | fixedInverse _ _ => exact isEnc.elim
      | encInverse _ _ => exact isEnc.elim
      | hash _ => exact isEnc.elim

end Enc

section Private

/- The uniform laws below are read at the derived `Fintype` instances (those `runFill_once` uses);
only the runner's `DecidableEq` instances are parameters. -/
variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **The designed shadow's off-curve run from the empty oracle, eager.** -/
theorem designedOff_eager (table : Public) (bits : BitInput) (mac : InputMac) (first : Block)
    (T : Tape) (Φ : LState → ℝ≥0∞) (invariant : ∀ s t, SameLookups s t → Φ s = Φ t) :
    ∑' r, runFillFlag LazyOracle.empty (fun cell => PMF.pure (T cell))
        (designedOffM table bits mac first) LazyOracle.empty ∅ r *
          (match r with
            | none => 0
            | some x => Φ x.2)
      = ∑' O, publicCompletion LazyOracle.empty O *
          ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
            Φ (plantAll (transcript (fixedAnswer v T) (systemAM table bits mac))
              (plantAll (transcript (publicAnswer O) (Programs.padsM ⟨first, 0⟩)) LazyOracle.empty)) := by
  let F : Option (Unit × LState) → ℝ≥0∞ := fun r => match r with
    | none => 0
    | some x => Φ x.2
  have pads : AllQ EncAt (Programs.padsM ⟨first, 0⟩) := padsM_allQ _
  unfold designedOffM
  rw [runFill_encBind _ pads, tsum_bind_mul]
  have inner : ∀ r ∈ (runLazyQ (Programs.padsM ⟨first, 0⟩) LazyOracle.empty).support,
      ∑' o, runFillFlag LazyOracle.empty (fun cell => PMF.pure (T cell)) (systemAM table bits mac)
          r.2 ∅ o * F o =
        ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
          F (some ((systemAM table bits mac).eval (fixedAnswer v T),
            plantAll (transcript (fixedAnswer v T) (systemAM table bits mac)) r.2)) := by
    intro r member
    have same := runLazyQ_enc_fixed pads LazyOracle.empty r member
    have fresh : ∀ i ∈ onceLaneSet Lane.curveX ∪ onceLaneSet Lane.curveY,
        r.2.fixed i = (LazyOracle.empty : LState).fixed i := fun i _ => congrFun same.1 i
    have unstored : ∀ cell ∈ onceCellSet Lane.curveX ∪ onceCellSet Lane.curveY, ∀ label,
        r.2.hash.lookup (Kriterion.ArgoMAC.Phase3.Lazy.cellInput cell label) = none := by
      intro cell _ label
      rw [same.2]
      rfl
    have untouched : ∀ cell ∈ onceCellSet Lane.curveX ∪ onceCellSet Lane.curveY,
        cell ∉ (∅ : Set Cell) := fun _ _ member => member.elim
    have invariantF : ∀ (a : Unit) (t t' : LState), SameLookups t t' → F (some (a, t)) = F (some (a, t')) :=
      fun a t t' same => invariant t t' same
    exact runFill_once T (once_systemAM table bits mac) r.2 ∅ fresh unstored untouched F invariantF
  have step : ∑' r, runLazyQ (Programs.padsM ⟨first, 0⟩) LazyOracle.empty r *
      ∑' o, runFillFlag LazyOracle.empty (fun cell => PMF.pure (T cell)) (systemAM table bits mac)
        r.2 ∅ o * F o =
      ∑' r, runLazyQ (Programs.padsM ⟨first, 0⟩) LazyOracle.empty r *
        (fun (_ : Programs.Pads) (s : LState) => ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
          Φ (plantAll (transcript (fixedAnswer v T) (systemAM table bits mac)) s)) r.1 r.2 := by
    refine tsum_congr fun r => ?_
    by_cases member : r ∈ (runLazyQ (Programs.padsM ⟨first, 0⟩) LazyOracle.empty).support
    · rw [inner r member]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]
  rw [step]
  exact runLazyQ_eager (Programs.padsM ⟨first, 0⟩) LazyOracle.empty
    (fun (_ : Programs.Pads) (s : LState) => ∑' v, PMF.uniformOfFintype (FixedIndex → Block) v *
      Φ (plantAll (transcript (fixedAnswer v T) (systemAM table bits mac)) s))
    (fun _ t t' same => tsum_congr fun v => congrArg _ (invariant _ _ (plantAll_congr _ same)))

end Private

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
