/-
**The replay's hash inputs and the designated site.**

* `not_isDesignated_scaleInput`: a scale input of any other (lane, chunk, switch) than
  `(pointX, 0, j*)` is not designated (`PlanB.scaleInput_injective`), and neither is the bridge
  input (`not_isDesignated_bridgeInput`: `bridgeInput t ≥ 2^150` lies above every scale input);
* `clean_askHash`: such a question is asked of the lazy oracle, the record unchanged;
* `interceptT_designatedMask`: the evaluator's `452` limb questions of the designated vector are
  all intercepted (`isDesignated_designatedInput`), answered by `(0, 0)`, and leave the record
  `fun _ => some E*`; the vector they give is `sampleLane` of zeros, i.e. `0`.
-/

import Proof.Simulator.ReplayElement

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### Which hash inputs are designated -/

/-- **A scale input off the designated site is not designated.** -/
theorem not_isDesignated_scaleInput (bits : BitInput) (lane : Lane) (chunk : Fin chunkCount)
    (switch limb : Nat) (label : Block) (switchSmall : switch < 2 ^ chunkBits)
    (limbSmall : limb < 512)
    (away : lane ≠ .pointX ∨ chunk ≠ chunkZero ∨ switch ≠ (designatedSwitch bits).val) :
    ¬ IsDesignated bits (scaleInput lane chunk switch limb label) := by
  rintro ⟨designated, same⟩
  have jSmall : (designatedSwitch bits).val < 2 ^ chunkBits :=
    lt_of_lt_of_le (designatedSwitch bits).isLt
      (Nat.pow_le_pow_right (by norm_num) (chunkWidth_le chunkZero))
  obtain ⟨sameLane, sameChunk, sameSwitch, -, -⟩ := scaleInput_injective jSmall switchSmall
    (lt_trans designated.isLt (limbCount_lt _)) limbSmall same
  rcases away with other | other | other
  · exact other sameLane.symm
  · exact other sameChunk.symm
  · exact other sameSwitch.symm

/-- **The bridge input is not designated**: it lies above every scale input. -/
theorem not_isDesignated_bridgeInput (bits : BitInput) (t : BaseField) :
    ¬ IsDesignated bits (bridgeInput t) := by
  rintro ⟨designated, same⟩
  exact bridgeInput_ne_scaleInput t _ _ _ _ _ same.symm

/-- A non-designated hash question is not intercepted. -/
theorem interceptAnswer_hash (bits : BitInput) (input : BaseField)
    (clean : ¬ IsDesignated bits input) : interceptAnswer bits (.hash input) = none := by
  simp only [interceptAnswer, if_neg clean]

/-- A clean hash question. -/
theorem clean_askHash (bits : BitInput) (input : BaseField) (clean : ¬ IsDesignated bits input) :
    Clean bits (Programs.askHash input) :=
  Clean.ask _ (interceptAnswer_hash bits input clean)

/-! ### The designated vector -/

/-- A designated hash question is answered by `(0, 0)`. -/
theorem interceptAnswer_designated (bits : BitInput) (limb : Fin (limbCount .pointX))
    (label : Block) :
    interceptAnswer bits (.hash (designatedInput bits limb label)) = some ((0, 0) : Block × Block) := by
  unfold interceptAnswer
  exact if_pos (isDesignated_designatedInput bits limb label)

/-- A designated hash question, intercepted: answered by `(0, 0)`, its label recorded. -/
theorem interceptT_askHash_designated (bits : BitInput) (limb : Fin (limbCount .pointX))
    (label : Block) (record : DesignatedRecord) :
    interceptT bits (Programs.askHash (designatedInput bits limb label)) record =
      .pure ((0, 0), Function.update record limb (some label)) := by
  rw [← recordAfter_designatedInput]
  exact interceptT_query_some bits (.hash (designatedInput bits limb label)) FreeQuery.pure record
    ((0, 0) : Block × Block) (interceptAnswer_designated bits limb label)

/-- **The designated questions, intercepted**: a vector of designated limb questions at one label
is answered by `(0, 0)` throughout and records the label at every asked limb. -/
theorem interceptT_vector_designated (bits : BitInput) (label : Block) :
    ∀ (count : Nat) (limbOf : Fin count → Fin (limbCount .pointX)) (record : DesignatedRecord),
      interceptT bits (FreeQuery.vector count fun index =>
          Programs.askHash (designatedInput bits (limbOf index) label)) record =
        .pure (Vector.replicate count (0, 0), fun limb =>
          if ∃ index, limbOf index = limb then some label else record limb)
  | 0, limbOf, record => by
      simp only [FreeQuery.vector, TreeLaws.monad_pure, interceptT]
      refine congrArg FreeQuery.pure (Prod.ext (Vector.ext fun index bound =>
        absurd bound (Nat.not_lt_zero _)) ?_)
      funext limb
      have none : ¬ ∃ index : Fin 0, limbOf index = limb := fun ⟨index, _⟩ => index.elim0
      show record limb = if ∃ index, limbOf index = limb then some label else record limb
      rw [if_neg none]
  | count + 1, limbOf, record => by
      simp only [FreeQuery.vector, TreeLaws.monad_bind, TreeLaws.monad_pure, interceptT_bind]
      rw [interceptT_vector_designated bits label count (fun index => limbOf index.castSucc) record,
        TreeLaws.bind_pure_left, interceptT_askHash_designated, TreeLaws.bind_pure_left]
      show FreeQuery.pure _ = FreeQuery.pure _
      dsimp only
      congr 2
      · exact Vector.ext fun index bound => by
          simp only [Vector.getElem_push, Vector.getElem_replicate]
          split <;> rfl
      · funext limb
        by_cases last : limb = limbOf (Fin.last count)
        · subst last
          rw [Function.update_self, if_pos ⟨Fin.last count, rfl⟩]
        · rw [Function.update_of_ne last]
          by_cases earlier : ∃ index : Fin count, limbOf index.castSucc = limb
          · rw [if_pos earlier, if_pos (by
              obtain ⟨index, hit⟩ := earlier
              exact ⟨index.castSucc, hit⟩)]
          · rw [if_neg earlier, if_neg]
            rintro ⟨index, hit⟩
            induction index using Fin.lastCases with
            | last => exact last hit.symm
            | cast index => exact earlier ⟨index, hit⟩

/-- **The evaluator's designated vector, intercepted**: `sampleLane` of `452` zero answers, the
record `fun _ => some E*`. -/
theorem interceptT_designatedMask (bits : BitInput) (label : Block) (record : DesignatedRecord) :
    interceptT bits (Programs.switchMaskM .pointX chunkZero (designatedSwitch bits).val label)
        record =
      .pure (Vector.ofFn (sampleLane pointElementCountX (limbCount .pointX) fun _ => (0, 0)),
        fun _ => some label) := by
  unfold Programs.switchMaskM
  rw [TreeLaws.monad_bind, interceptT_bind]
  have asks : (fun limb : Fin (limbCount .pointX) =>
      Programs.askHash (scaleInput .pointX chunkZero (designatedSwitch bits).val limb.val label)) =
      fun limb => Programs.askHash (designatedInput bits (id limb) label) := rfl
  have getReplicate : (Vector.replicate (limbCount .pointX) ((0, 0) : Block × Block)).get =
      fun _ => (0, 0) := funext fun limb => Vector.getElem_replicate limb.isLt
  have recordAll : (fun limb : Fin (limbCount .pointX) =>
      if ∃ index, id index = limb then some label else record limb) = fun _ => some label :=
    funext fun limb => if_pos ⟨limb, rfl⟩
  rw [asks, interceptT_vector_designated bits label (limbCount .pointX) id record,
    TreeLaws.bind_pure_left, TreeLaws.monad_pure, getReplicate, recordAll]
  rfl

/-- `sampleLane` of zero answers is the zero vector. -/
theorem sampleLane_zero (n k : Nat) :
    sampleLane n k (fun _ => ((0 : Block), (0 : Block))) = fun _ => 0 := by
  funext element
  simp [sampleLane, limbsToNat, limbValue]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
