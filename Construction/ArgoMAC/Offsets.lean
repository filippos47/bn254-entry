/-
This file defines the constrained ArgoMAC offsets.
-/

import Construction.ArgoMAC.Base7

namespace Kriterion.ArgoMAC

open BN254

def clampOffsets [FieldCertificate] [GroupCertificate]
    (beta : ScalarField) (freeOffsets : List Point) : List Point :=
  -(beta • pointHorner beta freeOffsets) :: freeOffsets

theorem pointHornerClampOffsets [FieldCertificate] [GroupCertificate]
    (beta : ScalarField) (freeOffsets : List Point) :
    pointHorner beta (clampOffsets beta freeOffsets) = 0 := by
  simp [clampOffsets, pointHorner]

structure OffsetRandomness [FieldCertificate] where
  freeOffsets : List Point
  freeOffsetCount : freeOffsets.length = 90

def Construction.offsets [FieldCertificate] [GroupCertificate]
    (_construction : Construction) (randomness : OffsetRandomness) : List Point :=
  clampOffsets radix randomness.freeOffsets

theorem Construction.offsetsLength [FieldCertificate] [GroupCertificate]
    (construction : Construction) (randomness : OffsetRandomness) :
    (construction.offsets randomness).length = 91 := by
  simp [Construction.offsets, clampOffsets, randomness.freeOffsetCount]

theorem Construction.offsetsCancel [FieldCertificate] [GroupCertificate]
    (construction : Construction) (randomness : OffsetRandomness) :
    pointHorner radix (construction.offsets randomness) = 0 :=
  pointHornerClampOffsets radix randomness.freeOffsets

end Kriterion.ArgoMAC
