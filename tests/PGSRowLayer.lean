import Construction.Garbling
import Proof.CiphertextSize
import Proof.Correctness.CanonicalBits

open Kriterion.ArgoMAC

#print axioms Biquadratic.evaluateEncodedX
#print axioms Biquadratic.evaluateEncodedY
#print axioms Biquadratic.evaluateEncodedY_raw
#print axioms Biquadratic.evaluateEncodedZ
#print axioms CurveMembership.evaluateEncoded
#print axioms CurveMembership.evaluateEncodedOnCurve
#print axioms FieldMacToECMac.evaluateHomogeneousEncoded
#print axioms FieldMacToECMac.evaluateEncoded
#print axioms FieldMacToECMac.unlockExceptional
#print axioms Pipeline.evaluateEncoded
#print axioms Pipeline.hotIndexNat_injective
#print axioms Garbling.evaluateEncodeRows
#print axioms Garbling.Randomness.correlated
#print axioms PlanB.lamportBits_high
#print axioms PlanB.Wire.garbledCircuit_length
