import FIp_CircleValue
import FoldRuntimeAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_CircleAlgebra
open SAQ_LineSource
abbrev FE := AspisWideTower.WideExact

theorem quarter : algebraMap FP FE R1ZCircleFoldMathV1.rustQuarter=(4:FE)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have h := congrArg (algebraMap FP FE) R1ZCircleFoldMathV1.four_mul_rustQuarter
  rwa [map_mul,map_one,map_ofNat] at h

theorem formula (alpha a b c d : FE) (ix iy : FP) :
    FIp_CircleValue.formula alpha a b c d ix iy =
      FoldRuntimeAlgebra.circleWithInverses alpha (algebraMap FP FE ix)
        (algebraMap FP FE iy) (values4 a b c d) := by
  have h0 : values4 a b c d 0=a := rfl
  have h1 : values4 a b c d 1=b := rfl
  have h2 : values4 a b c d 2=c := rfl
  have h3 : values4 a b c d 3=d := rfl
  simp only [FIp_CircleValue.formula,FoldRuntimeAlgebra.circleWithInverses,
    h0,h1,h2,h3,map_mul,quarter]

#print axioms quarter
#print axioms formula
end AspisR1.FIp_CircleAlgebra
end
