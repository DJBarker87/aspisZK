import AspisV8R19.SamplerClosureCircleFieldExecution

set_option autoImplicit false
noncomputable section
namespace CDX
open Aeneas Aeneas.Std Result AspisR72Sampler
open AspisV8R15.ExactTowerBase
open AspisV8R19
open SamplerClosureProductExecution (encode encodeCM)
open ComplexBaseExecution (encodeBase)

private theorem base_two_ne : (2 : M31Exact) ≠ 0 := by decide
private theorem complex_two_ne : (2 : CM31Exact) ≠ 0 := by
  intro h
  exact base_two_ne (congrArg (fun z : CM31Exact => z.re) h)
private theorem quartic_two_ne : (2 : QM31Exact) ≠ 0 := by
  intro h
  exact complex_two_ne (congrArg (fun z : QM31Exact => z.re) h)

-- One squaring is exponent two; the count is not a predecessor exponent.
theorem square_two :
    field.QM31.square (encode (2 : QM31Exact)) = .ok (encode (4 : QM31Exact)) := by
  have h : (2 : QM31Exact) * 2 = 4 := by ring
  simpa only [h] using SamplerClosureCircleFieldExecution.square (2 : QM31Exact)

theorem base_inverse_two :
    field.M31.inv (encodeBase (2 : M31Exact)) =
      .ok (encodeBase ((2 : M31Exact)⁻¹)) := by
  exact SamplerClosureCircleScalarTransport.inv_encode 2 base_two_ne

theorem complex_inverse_two :
    field.CM31.inv (encodeCM (2 : CM31Exact)) =
      .ok (encodeCM ((2 : CM31Exact)⁻¹)) := by
  exact SamplerClosureCircleFieldExecution.cm_inv 2 complex_two_ne

theorem quartic_inverse_two :
    field.QM31.try_inv (encode (2 : QM31Exact)) =
      .ok (some (encode ((2 : QM31Exact)⁻¹))) := by
  exact SamplerClosureCircleFieldExecution.try_inverse_nonzero 2 quartic_two_ne

theorem inverse_cancel (x : QM31Exact) (hx : x ≠ 0) : x * x⁻¹ = 1 :=
  mul_inv_cancel₀ hx

theorem zero_inverse : field.QM31.try_inv (encode 0) = .ok none :=
  SamplerClosureCircleFieldExecution.try_inverse_zero

#print axioms square_two
#print axioms base_inverse_two
#print axioms complex_inverse_two
#print axioms quartic_inverse_two
#print axioms inverse_cancel
#print axioms zero_inverse
end CDX
