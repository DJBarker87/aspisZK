import XRk_CircleModel
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
set_option autoImplicit false
namespace LPa.Circle
-- Anonymous source closure has no loop; native K018 reaches its rejected-zero
-- branch through the public circle_sample library, without closure stubbing.
def reference (row : sampler.circle_sample.closure) : Result aspis_core.circle.SecureCirclePoint := do
  let t : aspis_core.field.QM31 := match row with
    | .First => ⟨⟨0#u32,0#u32⟩,⟨1#u32,0#u32⟩⟩
    | .Second => ⟨⟨1#u32,0#u32⟩,⟨1#u32,0#u32⟩⟩
  let point ← aspis_core.circle.secure_ood_circle_point_from_parameter t
  match point with
  | .Ok p => ok p
  | .Err _ => ok ⟨qone,qzero⟩

theorem leaf_eq_reference (row : sampler.circle_sample.closure)
    (err : aspis_core.circle.CirclePointError) :
    sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once row err =
      reference row := by rfl

theorem error_independent (row : sampler.circle_sample.closure)
    (a b : aspis_core.circle.CirclePointError) :
    sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once row a =
    sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once row b := by rfl
#print axioms leaf_eq_reference
#print axioms error_independent
end LPa.Circle
