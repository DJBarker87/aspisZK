import FIo_CMValues
set_option autoImplicit false
namespace AspisR1.FJm_SquareAlgebra

theorem real {R : Type} [CommRing R] (a b : R) :
    (a+b)*(a-b)=a*a+(-1)*b*b := by ring

theorem imag {R : Type} [CommRing R] (a b : R) : a*b+a*b=a*b+b*a := by
  rw [mul_comm b a]
#print axioms real
#print axioms imag
end AspisR1.FJm_SquareAlgebra
