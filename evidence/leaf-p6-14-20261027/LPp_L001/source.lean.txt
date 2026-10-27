import AspisV8R19.SamplerClosureCircleSourceExecution

set_option autoImplicit false
noncomputable section
namespace LPp
open Aeneas Aeneas.Std Result AspisR72Sampler
open AspisV8R15.ExactTowerBase
open AspisV8R19
open SamplerClosureProductExecution (encode)
open SamplerClosureProductCorrectness (Canonical encode_canonical)

-- Symbolic addition-chain correctness, for every canonical input value.
theorem inverse_nonzero (x : QM31Exact) (hx : x ≠ 0) :
    field.QM31.try_inv (encode x) = .ok (some (encode x⁻¹)) :=
  SamplerClosureCircleFieldExecution.try_inverse_nonzero x hx

theorem inverse_zero : field.QM31.try_inv (encode 0) = .ok none :=
  SamplerClosureCircleFieldExecution.try_inverse_zero

theorem mapper_all_canonical (q : field.QM31) (hq : Canonical q) :
    circle.secure_ood_circle_point_from_parameter q =
      .ok (SamplerClosureCircleSourceExecution.encodeResult
        (SamplerCirclePolicy.pureMap (SamplerClosureProductCorrectness.decode q))) :=
  SamplerClosureCircleSourceExecution.source_execution q hq

theorem singular_arm (t : QM31Exact) (hd : 1+t*t = 0) :
    circle.secure_ood_circle_point_from_parameter (encode t) =
      .ok (.Err .SingularParameter) :=
  SamplerClosureCircleSourceExecution.ood_singular t hd

theorem subfield_arm (t : QM31Exact) (hd : 1+t*t ≠ 0) (ht : t.im = 0) :
    circle.secure_ood_circle_point_from_parameter (encode t) =
      .ok (.Err .ParameterInCm31Subfield) :=
  SamplerClosureCircleSourceExecution.ood_subfield t hd ht

theorem zero_reaches_subfield :
    circle.secure_ood_circle_point_from_parameter (encode 0) =
      .ok (.Err .ParameterInCm31Subfield) := by
  apply subfield_arm
  · simp
  · rfl

-- No inverse hypothesis and no exclusion of the reachable subfield errors.
theorem encoded_domain (t : QM31Exact) : Canonical (encode t) :=
  encode_canonical t

#print axioms inverse_nonzero
#print axioms inverse_zero
#print axioms mapper_all_canonical
#print axioms singular_arm
#print axioms subfield_arm
#print axioms zero_reaches_subfield
#print axioms encoded_domain
end LPp
