import Proof.Correctness
import Proof.LamportCompatibility
import Construction.ArgoMAC.Seed

open Kriterion Kriterion.BN254

theorem argoMACRandomizedEncodingCorrect [FieldCertificate] [GroupCertificate] :
    RandomizedEncoding.Correctness ArgoMAC.construction.randomizedEncoding :=
  ArgoMAC.construction.randomizedEncodingCorrect

theorem argoMACRandomizedEncodingPrivate [FieldCertificate] [GroupCertificate] :
    RandomizedEncoding.Privacy ArgoMAC.construction.randomizedEncoding
      ArgoMAC.construction.randomizedEncodingSimulator :=
  ArgoMAC.construction.randomizedEncodingPrivate

theorem argoMACOutputCount [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField)
    (randomness : ArgoMAC.OffsetRandomness) (point : Point) :
    (ArgoMAC.construction.outputs scalar randomness point).length = 91 :=
  ArgoMAC.construction.outputCount scalar randomness point

theorem argoMACPerfectCorrectness [FieldCertificate] [GroupCertificate]
    [ArgoMAC.TerminationCertificate] :
    GarbledCircuit.PerfectCorrectness
      (ArgoMAC.Garbling.garbledCircuit ArgoMAC.construction)
      (fun randomness =>
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)) :=
  ArgoMAC.JacobianMixed.perfectCorrectness

def argoMACLamportCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility
      ArgoMAC.Lamport.wireCircuit affineLamportBits :=
  ArgoMAC.Lamport.compatible

theorem seedOffsetsClamped [FieldCertificate] [GroupCertificate] :
    ArgoMAC.Seed.offsets.IsClamped :=
  ArgoMAC.Seed.offsets_clamped
