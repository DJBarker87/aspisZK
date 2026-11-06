import NKM_Roots
import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualPolicyUnconditionalV1
set_option autoImplicit false
noncomputable section
namespace NKM_Domains
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase AspisV8R19
open NKM_FieldLaws NKM_circle

def arguments (t : QM31Exact) : List (QM31Exact × QM31Exact) :=
 [(t,t),(1,t*t),(1+t*t,0)] ++
 if 1+t*t=0 then [] else [(1,t*t),(1-t*t,(1+t*t)⁻¹),(t,t),(t+t,(1+t*t)⁻¹)]

/-- Every reached field argument is encoded canonically, including the inverse domain. -/
theorem all_arguments (t : QM31Exact) (a : QM31Exact × QM31Exact) (_ : a ∈ arguments t) :
 Canon (encode a.1) ∧ Canon (encode a.2) := ⟨canonical _,canonical _⟩

theorem inverse_return (d : QM31Exact) :
 NKM_circle.field.QM31.try_inv (encode d) =
 ok (if d=0 then none else some (encode d⁻¹)) := by
 by_cases h:d=0
 · subst d;rw [inverse_zero];rfl
 · rw [inverse_nonzero d h,if_neg h]

/-- None rejects immediately; the successful inverse is canonical before both products. -/
theorem inverse_output_canonical (d : QM31Exact) : Canon (encode d⁻¹) := canonical _

def fromWrapper (q : AspisR1CircleSampleWrapper.field.QM31) : NKM_circle.field.QM31 :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem caller_sample (block : Array U8 32#usize) :
 ∃ q, _root_.sampler.qm31_sample block=ok q ∧ Canon (fromWrapper q) := by
 obtain ⟨q,hq,hc⟩ := AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyUnconditionalV1.sampler_total_canonical block
 exact ⟨q,hq,hc⟩

theorem ood_to_circle (q : NKM_circle.field.QM31) (hc : Canon q) : Canon q := hc

theorem fallback_domains : Canon NKM_FallbackModel.parameter0 ∧ Canon NKM_FallbackModel.parameter1 := by
 rw [NKM_FallbackModel.parameter0_encode,NKM_FallbackModel.parameter1_encode]
 exact ⟨canonical _,canonical _⟩

#print axioms all_arguments
#print axioms inverse_return
#print axioms inverse_output_canonical
#print axioms caller_sample
#print axioms ood_to_circle
#print axioms fallback_domains
end NKM_Domains
end
