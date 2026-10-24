import Mathlib.Algebra.QuadraticAlgebra.Basic
set_option autoImplicit false
namespace AspisR1S9QuadraticFieldMulProjectionV1
noncomputable def projectedMul {R : Type} [Field R] (x y : R) : R := x*y
/-- Opaque base field, parameters, and operands. Only the inherited
multiplication projection of the quadratic Field instance is reduced. -/
theorem quadratic_field_mul {K : Type} [Field K] (a b : K)
    [Fact (∀ r : K, r^2≠a+b*r)] (x y : QuadraticAlgebra K a b) :
    projectedMul x y=x*y := by rfl
#print axioms quadratic_field_mul
end AspisR1S9QuadraticFieldMulProjectionV1
