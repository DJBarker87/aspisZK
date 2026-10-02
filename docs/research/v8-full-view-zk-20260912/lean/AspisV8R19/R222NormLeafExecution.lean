import AspisR221NormExecutionRaw
import AspisV8R19.R164ProductExecution
import AspisV8R19.R218CircleNormAlgebra

/-! Actual selected norm/polar leaves, bound to current word arithmetic.
This does not identify the vector/coefficient/line/batch inverse algorithm. -/
set_option autoImplicit false
namespace AspisV8R19.R222NormLeafExecution
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R15.ExactTowerBase
open AspisR221NormExecutionRaw
noncomputable section

 theorem times_r_current (z : field.CM31) :
    circle_norm.times_r z = field.mul_by_r z := by
  simp only [circle_norm.times_r,field.mul_by_r,field.CM31.new]

 theorem times_r_exact (z : CM31Exact) :
    circle_norm.times_r (R163ComplexExecution.encode z) =
      .ok (R163ComplexExecution.encode (qm31R*z)) := by
  rw [times_r_current,R163ComplexExecution.cm_mul_r]

 theorem norm_exact (v : QM31Exact) :
    circle_norm.norm (R164ProductExecution.encode v) =
      .ok (R163ComplexExecution.encode (NormInverse.quarticNorm v)) := by
  simp only [circle_norm.norm,R164ProductExecution.encode,
    R163ComplexExecution.cm_square,times_r_exact,R163ComplexExecution.cm_sub,
    bind_tc_ok,NormInverse.quarticNorm]

 theorem polar_exact (v w : QM31Exact) :
    circle_norm.polar (R164ProductExecution.encode v) (R164ProductExecution.encode w) =
      .ok (R163ComplexExecution.encode (R218CircleNormAlgebra.polar v w)) := by
  simp only [circle_norm.polar,R164ProductExecution.encode,
    R163ComplexExecution.cm_mul,times_r_exact,R163ComplexExecution.cm_sub,
    R163ComplexExecution.cm_double,bind_tc_ok,R218CircleNormAlgebra.polar,mul_two]

 theorem norm_affine_exact (a b c : QM31Exact) (x y : CM31Exact) :
    circle_norm.norm (R164ProductExecution.encode (R218CircleNormAlgebra.affine a b c x y)) =
      .ok (R163ComplexExecution.encode (
        NormInverse.quarticNorm a+NormInverse.quarticNorm b*x^2+
        NormInverse.quarticNorm c*y^2+R218CircleNormAlgebra.polar a b*x+
        R218CircleNormAlgebra.polar a c*y+R218CircleNormAlgebra.polar b c*(x*y))) := by
  rw [norm_exact,R218CircleNormAlgebra.norm_affine]

#print axioms times_r_current
#print axioms times_r_exact
#print axioms norm_exact
#print axioms polar_exact
#print axioms norm_affine_exact
end
end AspisV8R19.R222NormLeafExecution
