import Proof.Correctness
import Proof.LamportCompatibility
import Proof.CiphertextSize

open Kriterion Kriterion.ArgoMAC

#print axioms Kriterion.ArgoMAC.JacobianMixed.perfectCorrectness
#print axioms Kriterion.ArgoMAC.perfectCorrectness
#print axioms Kriterion.ArgoMAC.functionCorrect
#print axioms Kriterion.ArgoMAC.JacobianMixed.evaluateCorrect
#print axioms Kriterion.ArgoMAC.JacobianMixed.evaluateCorrectValid
#print axioms Kriterion.ArgoMAC.JacobianMixed.evaluateCorrectInvalid
#print axioms Kriterion.ArgoMAC.JacobianMixed.decodeExpectedResult
#print axioms Kriterion.ArgoMAC.JacobianMixed.exceptionDigitCorrect
#print axioms Kriterion.ArgoMAC.PlanB.delivers
#print axioms Kriterion.ArgoMAC.PlanB.Wire.garbledCircuit_length
#print axioms Kriterion.ArgoMAC.PlanB.Wire.ciphertextSize
#print axioms Kriterion.ArgoMAC.evaluateCorrect
#print axioms Kriterion.ArgoMAC.Lamport.compatible
#print axioms Kriterion.ArgoMAC.Lamport.encodeSelectsLabels
#print axioms Kriterion.ArgoMAC.Lamport.selectedLabels_eq
#print axioms Kriterion.ArgoMAC.PlanB.Wire.ciphertextBytesConstant_eq
#print axioms Kriterion.ArgoMAC.PlanB.three_not_square
#print axioms Kriterion.ArgoMAC.PlanB.sq_sub_three_ne_zero
#print axioms Kriterion.ArgoMAC.PlanB.onCurve_x_ne_zero
