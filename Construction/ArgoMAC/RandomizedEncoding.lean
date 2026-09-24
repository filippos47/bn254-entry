/-
This file defines the ArgoMAC randomized encoding.
-/

import Construction.ArgoMAC.Offsets
import RandomizedEncoding

namespace Kriterion.ArgoMAC

open BN254

def Construction.outputs [FieldCertificate] [GroupCertificate]
    (construction : Construction) (scalar : ScalarField)
    (randomness : OffsetRandomness) (point : Point) : List Point :=
  encodeDigits point ((construction.digits scalar).map digitScalar)
    (construction.offsets randomness)

theorem Construction.correct [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    (construction : Construction) (scalar : ScalarField)
    (randomness : OffsetRandomness) (point : Point) :
    pointHorner radix (construction.outputs scalar randomness point) =
      scalarMultiplication scalar point := by
  rw [Construction.outputs]
  rw [pointHornerEncodeDigits radix point
    ((construction.digits scalar).map digitScalar) (construction.offsets randomness)
    (by rw [List.length_map, construction.digitCount scalar,
      construction.offsetsLength randomness])]
  rw [construction.scalarReconstruction scalar, construction.offsetsCancel randomness]
  simp [scalarMultiplication]

theorem Construction.outputCount [FieldCertificate] [GroupCertificate]
    (construction : Construction) (scalar : ScalarField)
    (randomness : OffsetRandomness) (point : Point) :
    (construction.outputs scalar randomness point).length = 91 := by
  rw [Construction.outputs, encodeDigitsLength point]
  · simp [construction.digitCount scalar]
  · rw [List.length_map, construction.digitCount scalar,
      construction.offsetsLength randomness]

def Construction.randomizedEncoding [FieldCertificate] [GroupCertificate]
    (construction : Construction) :
    Kriterion.RandomizedEncoding (ScalarField × Point) Point OffsetRandomness (List Point) := {
  function := fun input => scalarMultiplication input.1 input.2
  encode := fun input randomness => construction.outputs input.1 randomness input.2
  decode := fun encoded => some (pointHorner radix encoded)
}

theorem Construction.randomizedEncodingCorrect [FieldCertificate] [GroupCertificate]
    [TerminationCertificate]
    (construction : Construction) :
    Kriterion.RandomizedEncoding.Correctness construction.randomizedEncoding := by
  intro input randomness
  exact congrArg some (construction.correct input.1 randomness input.2)

def Construction.simulatedOutputs [FieldCertificate] [GroupCertificate]
    (_construction : Construction) (output : Point) (randomness : OffsetRandomness) :
    List Point :=
  (output - radix • pointHorner radix randomness.freeOffsets) :: randomness.freeOffsets

theorem Construction.simulatedOutputsCorrect [FieldCertificate] [GroupCertificate]
    (construction : Construction) (output : Point) (randomness : OffsetRandomness) :
    pointHorner radix (construction.simulatedOutputs output randomness) = output := by
  simp [simulatedOutputs, pointHorner, sub_eq_add_neg, add_assoc]

def Construction.randomizedEncodingSimulator [FieldCertificate] [GroupCertificate]
    (construction : Construction) :
    Kriterion.RandomizedEncoding.Simulator Point OffsetRandomness (List Point) := {
  simulate := construction.simulatedOutputs
}

def Construction.tailShifts [FieldCertificate] [GroupCertificate]
    (construction : Construction) (scalar : ScalarField) (point : Point) : List Point :=
  ((construction.digits scalar).map digitScalar).tail.map (fun digit => digit • point)

theorem Construction.tailShiftsLength [FieldCertificate] [GroupCertificate]
    (construction : Construction) (scalar : ScalarField) (point : Point) :
    (construction.tailShifts scalar point).length = 90 := by
  simp [tailShifts, construction.digitCount scalar]

def Construction.offsetEquiv [FieldCertificate] [GroupCertificate]
    (construction : Construction) (scalar : ScalarField) (point : Point) :
    OffsetRandomness ≃ OffsetRandomness where
  toFun randomness := {
    freeOffsets := translatePoints (construction.tailShifts scalar point) randomness.freeOffsets
    freeOffsetCount := by
      rw [translateLength _ _]
      · exact randomness.freeOffsetCount
      · rw [construction.tailShiftsLength scalar point, randomness.freeOffsetCount]
  }
  invFun randomness := {
    freeOffsets := untranslatePoints (construction.tailShifts scalar point) randomness.freeOffsets
    freeOffsetCount := by
      rw [untranslateLength _ _]
      · exact randomness.freeOffsetCount
      · rw [construction.tailShiftsLength scalar point, randomness.freeOffsetCount]
  }
  left_inv randomness := by
    cases randomness with
    | mk freeOffsets freeOffsetCount =>
        rw [OffsetRandomness.mk.injEq]
        exact untranslateTranslate _ _ (by
          rw [construction.tailShiftsLength scalar point, freeOffsetCount])
  right_inv randomness := by
    cases randomness with
    | mk freeOffsets freeOffsetCount =>
        rw [OffsetRandomness.mk.injEq]
        exact translateUntranslate _ _ (by
          rw [construction.tailShiftsLength scalar point, freeOffsetCount])

theorem Construction.outputs_eq_simulatedOutputs_reindex
    [FieldCertificate] [GroupCertificate] [TerminationCertificate] (construction : Construction)
    (scalar : ScalarField) (point : Point) (randomness : OffsetRandomness) :
    construction.outputs scalar randomness point =
      construction.simulatedOutputs (scalarMultiplication scalar point)
        (construction.offsetEquiv scalar point randomness) := by
  set digits := (construction.digits scalar).map digitScalar with digitsDefinition
  have digitCount : digits.length = 91 := by
    simp [digits, construction.digitCount scalar]
  have digitsNotEmpty : digits ≠ [] := by
    intro empty
    simp [empty] at digitCount
  obtain ⟨digit, tail, digitsShape⟩ := List.exists_cons_of_ne_nil digitsNotEmpty
  have tailCount : tail.length = 90 := by
    rw [digitsShape] at digitCount
    simpa using digitCount
  have reindexed : (construction.offsetEquiv scalar point randomness).freeOffsets =
      translatePoints (tail.map (fun value => value • point)) randomness.freeOffsets := by
    change translatePoints (construction.tailShifts scalar point) randomness.freeOffsets = _
    rw [tailShifts, ← digitsDefinition, digitsShape]
    rfl
  have realShape : construction.outputs scalar randomness point =
      (digit • point - radix • pointHorner radix randomness.freeOffsets) ::
        translatePoints (tail.map (fun value => value • point)) randomness.freeOffsets := by
    rw [Construction.outputs, Construction.offsets, clampOffsets, ← digitsDefinition,
      digitsShape]
    simp [encodeDigits]
    constructor
    · simp [sub_eq_add_neg]
    · exact encodeDigits_eq_translatePoints point tail randomness.freeOffsets
  have reconstructed := construction.correct scalar randomness point
  rw [realShape] at reconstructed
  simp only [pointHorner] at reconstructed
  rw [realShape]
  simp only [simulatedOutputs, reindexed]
  congr 1
  rw [← reconstructed]
  abel

theorem Construction.randomizedEncodingPrivate [FieldCertificate] [GroupCertificate]
    [TerminationCertificate]
    (construction : Construction) :
    Kriterion.RandomizedEncoding.Privacy construction.randomizedEncoding
      construction.randomizedEncodingSimulator := by
  intro input
  exact ⟨construction.offsetEquiv input.1 input.2,
    construction.outputs_eq_simulatedOutputs_reindex input.1 input.2⟩

end Kriterion.ArgoMAC
