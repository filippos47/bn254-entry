/-
This file defines the ArgoMAC weighted sums.
-/

import ScalarMultiplication

namespace Kriterion.ArgoMAC

open BN254

def scalarHorner (beta : ScalarField) : List ScalarField → ScalarField
  | [] => 0
  | digit :: digits => digit + beta * scalarHorner beta digits

def pointHorner [FieldCertificate] [GroupCertificate]
    (beta : ScalarField) : List Point → Point
  | [] => 0
  | point :: points => point + beta • pointHorner beta points

def encodeDigits [FieldCertificate] [GroupCertificate] (point : Point) :
    List ScalarField → List Point → List Point
  | digit :: digits, offset :: offsets =>
      (digit • point + offset) :: encodeDigits point digits offsets
  | _, _ => []

theorem encodeDigitsLength [FieldCertificate] [GroupCertificate]
    (point : Point) (digits : List ScalarField) (offsets : List Point)
    (sameLength : digits.length = offsets.length) :
    (encodeDigits point digits offsets).length = digits.length := by
  induction digits generalizing offsets with
  | nil => cases offsets <;> simp [encodeDigits]
  | cons digit digits inductionHypothesis =>
      cases offsets with
      | nil => simp at sameLength
      | cons offset offsets =>
          simp only [List.length_cons, Nat.succ.injEq] at sameLength
          simp [encodeDigits, inductionHypothesis offsets sameLength]

theorem pointHornerEncodeDigits [FieldCertificate] [GroupCertificate]
    (beta : ScalarField) (point : Point) (digits : List ScalarField)
    (offsets : List Point) (sameLength : digits.length = offsets.length) :
    pointHorner beta (encodeDigits point digits offsets) =
      scalarHorner beta digits • point + pointHorner beta offsets := by
  induction digits generalizing offsets with
  | nil =>
      cases offsets with
      | nil =>
          change (0 : Point) = (0 : ScalarField) • point + 0
          rw [add_zero]
          exact (Module.zero_smul point).symm
      | cons offset offsets => simp at sameLength
  | cons digit digits inductionHypothesis =>
      cases offsets with
      | nil => simp at sameLength
      | cons offset offsets =>
          simp only [List.length_cons, Nat.succ.injEq] at sameLength
          simp only [encodeDigits, pointHorner, scalarHorner]
          rw [inductionHypothesis offsets sameLength]
          simp only [smul_add, mul_smul, add_smul]
          abel

def translatePoints [FieldCertificate] : List Point → List Point → List Point
  | shift :: shifts, point :: points => (shift + point) :: translatePoints shifts points
  | _, _ => []

def untranslatePoints [FieldCertificate] : List Point → List Point → List Point
  | shift :: shifts, point :: points => (-shift + point) :: untranslatePoints shifts points
  | _, _ => []

theorem encodeDigits_eq_translatePoints [FieldCertificate] [GroupCertificate]
    (point : Point) (digits : List ScalarField) (offsets : List Point) :
    encodeDigits point digits offsets =
      translatePoints (digits.map (fun digit => digit • point)) offsets := by
  induction digits generalizing offsets with
  | nil => simp [encodeDigits, translatePoints]
  | cons digit digits inductionHypothesis =>
      cases offsets <;> simp [encodeDigits, translatePoints, inductionHypothesis]

theorem translateLength [FieldCertificate] (shifts points : List Point)
    (sameLength : shifts.length = points.length) :
    (translatePoints shifts points).length = points.length := by
  induction shifts generalizing points with
  | nil => cases points <;> simp_all [translatePoints]
  | cons shift shifts inductionHypothesis =>
      cases points with
      | nil => simp at sameLength
      | cons point points =>
          simp only [List.length_cons, Nat.succ.injEq] at sameLength
          simp [translatePoints, inductionHypothesis points sameLength]

theorem untranslateLength [FieldCertificate] (shifts points : List Point)
    (sameLength : shifts.length = points.length) :
    (untranslatePoints shifts points).length = points.length := by
  induction shifts generalizing points with
  | nil => cases points <;> simp_all [untranslatePoints]
  | cons shift shifts inductionHypothesis =>
      cases points with
      | nil => simp at sameLength
      | cons point points =>
          simp only [List.length_cons, Nat.succ.injEq] at sameLength
          simp [untranslatePoints, inductionHypothesis points sameLength]

theorem untranslateTranslate [FieldCertificate] (shifts points : List Point)
    (sameLength : shifts.length = points.length) :
    untranslatePoints shifts (translatePoints shifts points) = points := by
  induction shifts generalizing points with
  | nil => cases points <;> simp_all [untranslatePoints]
  | cons shift shifts inductionHypothesis =>
      cases points with
      | nil => simp at sameLength
      | cons point points =>
          simp only [List.length_cons, Nat.succ.injEq] at sameLength
          simp [translatePoints, untranslatePoints, inductionHypothesis points sameLength]

theorem translateUntranslate [FieldCertificate] (shifts points : List Point)
    (sameLength : shifts.length = points.length) :
    translatePoints shifts (untranslatePoints shifts points) = points := by
  induction shifts generalizing points with
  | nil => cases points <;> simp_all [translatePoints]
  | cons shift shifts inductionHypothesis =>
      cases points with
      | nil => simp at sameLength
      | cons point points =>
          simp only [List.length_cons, Nat.succ.injEq] at sameLength
          simp [translatePoints, untranslatePoints, inductionHypothesis points sameLength]

end Kriterion.ArgoMAC
