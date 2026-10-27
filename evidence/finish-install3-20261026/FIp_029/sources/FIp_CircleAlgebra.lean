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
  simp only [FIp_CircleValue.formula,FoldRuntimeAlgebra.circleWithInverses,
    values4,Fin.val_natCast,Nat.reduceMod,map_mul,quarter]

#print axioms quarter
#print axioms formula
end AspisR1.FIp_CircleAlgebra
end
