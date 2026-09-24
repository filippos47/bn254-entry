/-
**The label response.** `words_labelRuns`: the protocol's `words 128 508` parse of `508` emitted
`128`-bit runs is the vector of the emitted words, read modulo `2^128`.
-/

import Proof.Simulator.Stage2Prefix

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine GarbledCircuit

/-- Dropping whole chunks of a flattened list of equal-length chunks. -/
theorem drop_flatten_chunks {α : Type} (width : Nat) :
    ∀ (chunks : List (List α)), (∀ chunk ∈ chunks, chunk.length = width) →
      ∀ count, chunks.flatten.drop (width * count) = (chunks.drop count).flatten
  | [], _, count => by simp
  | chunk :: rest, sized, count => by
      cases count with
      | zero => simp
      | succ count =>
          rw [List.flatten_cons, Nat.mul_succ, Nat.add_comm, ← List.drop_drop,
            List.drop_left' (sized chunk (by simp)), List.drop_succ_cons]
          exact drop_flatten_chunks width rest (fun chunk member => sized chunk (by simp [member]))
            count

theorem length_flatten_chunks {α : Type} (width : Nat) :
    ∀ (chunks : List (List α)), (∀ chunk ∈ chunks, chunk.length = width) →
      chunks.flatten.length = width * chunks.length
  | [], _ => by simp
  | chunk :: rest, sized => by
      rw [List.flatten_cons, List.length_append, sized chunk (by simp),
        length_flatten_chunks width rest (fun chunk member => sized chunk (by simp [member])),
        List.length_cons]
      ring

theorem bitRun_length (value : Word) (offset count : Nat) :
    (bitRun value offset count).length = count := by
  simp [bitRun]

/-- **The label response parses to the emitted words.** -/
theorem words_labelRuns (count : Nat) (words : Fin count → Word) :
    SimulatorProtocol.words 128 count
        (List.ofFn fun index : Fin count => bitRun (words index) 0 128).flatten =
      some (Vector.ofFn fun index : Fin count => BitVec.ofNat 128 (words index).toNat) := by
  have sized : ∀ chunk ∈ List.ofFn (fun index : Fin count => bitRun (words index) 0 128),
      chunk.length = 128 := by
    intro chunk member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact bitRun_length _ _ _
  unfold SimulatorProtocol.words
  rw [if_pos (by rw [length_flatten_chunks 128 _ sized, List.length_ofFn])]
  congr 1
  refine congrArg Vector.ofFn (funext fun index => ?_)
  rw [show index.val * 128 = 128 * index.val by ring, drop_flatten_chunks 128 _ sized,
    List.drop_eq_getElem_cons (by simp), List.flatten_cons,
    List.take_left' (by simp [bitRun_length]), List.getElem_ofFn, bitRun_decode]
  apply BitVec.eq_of_toNat_eq
  simp

end Kriterion.ArgoMAC.PlanB.SimMachine
