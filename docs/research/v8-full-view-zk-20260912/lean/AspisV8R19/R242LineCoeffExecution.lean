import AspisR239CoeffExecutionRaw
import AspisV8R19.R222NormLeafExecution
import AspisV8R19.R240HalfExecution
import AspisV8R19.R241CoeffExecution
import AspisV8R19.R225LineNormAlgebra

/-! Exact execution of the selected joined-inverse line coefficient leaves.
These identities concern the raw constructor and evaluator only. -/
set_option autoImplicit false
namespace AspisV8R19.R242LineCoeffExecution
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisR239CoeffExecutionRaw
open AspisV8R19.R240HalfExecution (mapBase)

noncomputable section

theorem line_coeff_new_exact (a b c : QM31Exact) :
    circle_norm.joined_inverse.line_norm.LineCoeff.new
      (Array.make 3#usize [R164ProductExecution.encode a,
        R164ProductExecution.encode b, R164ProductExecution.encode c]) =
    .ok (Array.make 5#usize [
      R163ComplexExecution.encode
        (NormInverse.quarticNorm a + NormInverse.quarticNorm c +
          (NormInverse.quarticNorm b - NormInverse.quarticNorm c)/2),
      R163ComplexExecution.encode
        ((NormInverse.quarticNorm b - NormInverse.quarticNorm c)/2),
      R163ComplexExecution.encode (R218CircleNormAlgebra.polar a b),
      R163ComplexExecution.encode (R218CircleNormAlgebra.polar a c),
      R163ComplexExecution.encode (R218CircleNormAlgebra.polar b c)]) := by
  simp [circle_norm.joined_inverse.line_norm.LineCoeff.new,
    circle_norm.Coeff.new, Array.index_usize, Array.make,
    R222NormLeafExecution.norm_exact, R222NormLeafExecution.polar_exact,
    R163ComplexExecution.cm_add, R163ComplexExecution.cm_sub,
    R240HalfExecution.cm_half_exact, bind_tc_ok]

theorem line_coeff_four_exact (a b c : QM31Exact) (x y t : M31Exact) :
    circle_norm.joined_inverse.line_norm.LineCoeff.four
      (Array.make 5#usize [
        R163ComplexExecution.encode
          (NormInverse.quarticNorm a + NormInverse.quarticNorm c +
            (NormInverse.quarticNorm b - NormInverse.quarticNorm c)/2),
        R163ComplexExecution.encode
          ((NormInverse.quarticNorm b - NormInverse.quarticNorm c)/2),
        R163ComplexExecution.encode (R218CircleNormAlgebra.polar a b),
        R163ComplexExecution.encode (R218CircleNormAlgebra.polar a c),
        R163ComplexExecution.encode (R218CircleNormAlgebra.polar b c)])
      (ComplexBaseExecution.encodeBase x)
      (ComplexBaseExecution.encodeBase y)
      (ComplexBaseExecution.encodeBase t) =
    .ok (Array.make 4#usize [
      R163ComplexExecution.encode
        ((R225LineNormAlgebra.lineFour a b c (mapBase x) (mapBase y) (mapBase t)).1),
      R163ComplexExecution.encode
        ((R225LineNormAlgebra.lineFour a b c (mapBase x) (mapBase y) (mapBase t)).2.1),
      R163ComplexExecution.encode
        ((R225LineNormAlgebra.lineFour a b c (mapBase x) (mapBase y) (mapBase t)).2.2.1),
      R163ComplexExecution.encode
        ((R225LineNormAlgebra.lineFour a b c (mapBase x) (mapBase y) (mapBase t)).2.2.2)]) := by
  simp [circle_norm.joined_inverse.line_norm.LineCoeff.four,
    Array.index_usize, Array.make, R161WrappedMulExecution.mul_encode,
    R240HalfExecution.cm_mul_m31_exact,
    R163ComplexExecution.cm_add, R163ComplexExecution.cm_sub, bind_tc_ok,
    R225LineNormAlgebra.lineFour,
    AspisV8R19.R241CoeffExecution.mapBase_mul]

#print axioms line_coeff_new_exact
#print axioms line_coeff_four_exact
end
end AspisV8R19.R242LineCoeffExecution
