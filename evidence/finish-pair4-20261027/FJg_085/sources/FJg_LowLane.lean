import FJg_Quarter
import FJg_DualTensor
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_LowLane
open scoped BigOperators

def nativeMul {R : Type} [CommRing R] (x y : R) : R := x*y
def fieldMul {R : Type} [Field R] (x y : R) : R := x*y

theorem mul {K : Type} [Field K] (r u : K)
    [Fact (∀ x : K,x^2≠r+u*x)] (x y : QuadraticAlgebra K r u) :
    fieldMul x y=nativeMul x y := rfl
theorem semiring {K : Type} [Field K] (r u : K)
    [Fact (∀ x : K,x^2≠r+u*x)] :
    (inferInstance : Field (QuadraticAlgebra K r u)).toSemifield.toDivisionSemiring.toSemiring=
      (inferInstance : CommRing (QuadraticAlgebra K r u)).toSemiring := rfl
#print axioms mul
#print axioms semiring
end AspisR1.FJg_LowLane
end
