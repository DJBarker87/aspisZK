import AspisV8R19.R166CircleExecution

set_option autoImplicit false
namespace AspisV8R19.R730CircleConversionSuccess
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R15.ExactTowerBase
open R164ProductExecution
open R165QuarticExecution
open R166CircleExecution
noncomputable section

theorem encoded_success_outside (t : QM31Exact) (p : circle.SecureCirclePoint)
    (hs : circle.secure_ood_circle_point_from_parameter (encode t) = .ok (.Ok p)) :
    t.im ≠ 0 := by
  intro ht
  by_cases hd : 1 + t * t = 0
  · have hsing := ood_singular t hd
    rw [hs] at hsing
    simp at hsing
  · have hsub := ood_subfield t hd ht
    rw [hs] at hsub
    simp at hsub

theorem source_success_outside (t : field.QM31) (hc : Canonical t)
    (p : circle.SecureCirclePoint)
    (hs : circle.secure_ood_circle_point_from_parameter t = .ok (.Ok p)) :
    (decode t).im ≠ 0 := by
  rw [← encode_decode t hc] at hs
  exact encoded_success_outside (decode t) p hs

#print axioms encoded_success_outside
#print axioms source_success_outside
end
end AspisV8R19.R730CircleConversionSuccess
