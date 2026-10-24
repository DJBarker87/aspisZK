import S9WideMulOperatorBridgeV1
set_option autoImplicit false
namespace AspisR1S9WideFieldOperatorBridgesV1
abbrev E := AspisWideTower.WideExact
noncomputable def fieldAdd {K : Type} [Field K] (x y : K) : K := x+y
noncomputable def fieldZero {K : Type} [Field K] : K := 0
noncomputable def fieldPow {K : Type} [Field K] (x : K) (n : Nat) : K := x^n
noncomputable def fieldInv {K : Type} [Field K] (x : K) : K := x⁻¹
noncomputable def fieldFour {K : Type} [Field K] : K := 4
/-- One symbolic operator at a time; no field values or recurrences unfold. -/
theorem add_operator_eq (x y : E) : x+y=fieldAdd x y := by rfl
theorem zero_operator_eq : (0 : E)=fieldZero := by rfl
theorem pow_operator_eq (x : E) (n : Nat) : x^n=fieldPow x n := by rfl
theorem inv_operator_eq (x : E) : x⁻¹=fieldInv x := by rfl
theorem four_operator_eq : (4 : E)=fieldFour := by rfl
#print axioms add_operator_eq
#print axioms zero_operator_eq
#print axioms pow_operator_eq
#print axioms inv_operator_eq
#print axioms four_operator_eq
end AspisR1S9WideFieldOperatorBridgesV1
