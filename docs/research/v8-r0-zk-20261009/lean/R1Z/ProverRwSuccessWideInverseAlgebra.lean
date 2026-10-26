import R1Z.ProverCommitWideOps48
set_option autoImplicit false
namespace R1Z.ProverRwSuccessWideInverseAlgebra
open ProverCommitWideOps48

theorem norm_value (x : Exact) :
    QuadraticAlgebra.norm x=x.re*x.re-AspisWideTower.wideU*x.im*x.im := by
  simp only [QuadraticAlgebra.norm_def]
  ring

theorem inverse_coordinates (x : Exact) :
    (⟨x.re*(QuadraticAlgebra.norm x)⁻¹,-x.im*(QuadraticAlgebra.norm x)⁻¹⟩ : Exact)=x⁻¹ := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_inv,zero_mul,add_zero]
    ring
  · simp only [QuadraticAlgebra.im_inv]
    ring
#print axioms norm_value
#print axioms inverse_coordinates
end R1Z.ProverRwSuccessWideInverseAlgebra
