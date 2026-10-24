import S9ScalarConstructorModelV1
set_option autoImplicit false
namespace AspisR1S9WideMulOperatorBridgeV1
abbrev E := AspisWideTower.WideExact
noncomputable def concreteMul (x y : E) : E := x*y
noncomputable def fieldMul {K : Type} [Field K] (x y : K) : K := x*y
/-- Compare the direct concrete quadratic multiplication instance with the
multiplication projected through its existing Field instance, on opaque operands.
No concrete field value, source vector or recurrence is reduced. -/
theorem mul_operator_eq (x y : E) : concreteMul x y=fieldMul x y := by rfl
#print axioms mul_operator_eq
end AspisR1S9WideMulOperatorBridgeV1
