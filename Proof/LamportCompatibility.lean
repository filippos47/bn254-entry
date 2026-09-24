import Proof.LamportCompatibility.Labels

namespace Kriterion.ArgoMAC.Lamport

open BN254

/-- The encoded labels select the required Lamport key branches. -/
theorem encodeSelectsLabels [FieldCertificate] [GroupCertificate]
    (key : Garbling.EncodingKey) (input : AffineInput) :
    selectedLabels ((Garbling.garbledCircuit construction).encode key input).inputMac =
      GarbledCircuit.selectLamportLabels (keyPairs key.randomness.inputMacKey)
        (affineLamportBits input) :=
  selectedLabels_eq key.randomness.inputMacKey input

def compatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility
      wireCircuit affineLamportBits := {
  keyPairs := fun key => keyPairs key.randomness.inputMacKey
  encodeSelectsLabels := by
    intro key input
    exact encodeSelectsLabels key input
}


end Kriterion.ArgoMAC.Lamport
