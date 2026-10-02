import AspisV8R19.R265PrivateNormClosures
import AspisV8R19.R260PrivateInputExecution
import AspisV8R19.R242LineCoeffExecution

/-! Actual private coefficient constructor/evaluator on canonical encodings.
The constructor's Option input calls and exact two closure executions remain
in the raw definition. This does not prove its vector consumers or inversion. -/
set_option autoImplicit false
namespace AspisV8R19.R270PrivateCoefficientExecution
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisR264PrivateCoefficientRaw.circle_norm.joined_inverse.line_norm.r110_norm (Coeff110)
open R250PrivateBaseExecution (encodeC)
open R240HalfExecution (mapBase)
noncomputable section

def coefficients (a b c : QM31Exact) : Coeff110 :=
  Array.make 5#usize [
    encodeC (NormInverse.quarticNorm a+NormInverse.quarticNorm c+
      (NormInverse.quarticNorm b-NormInverse.quarticNorm c)/2),
    encodeC ((NormInverse.quarticNorm b-NormInverse.quarticNorm c)/2),
    encodeC (R218CircleNormAlgebra.polar a b),
    encodeC (R218CircleNormAlgebra.polar a c),
    encodeC (R218CircleNormAlgebra.polar b c)]

theorem coeff_new_exact (a b c : QM31Exact) :
    Coeff110.new (Array.make 3#usize [R164ProductExecution.encode a,
      R164ProductExecution.encode b,R164ProductExecution.encode c]) =
        .ok (some (coefficients a b c)) := by
  simp [Coeff110.new,Array.index_usize,Array.make,R164ProductExecution.encode,
    R260PrivateInputExecution.input_encoded,R260PrivateInputExecution.branch_some,
    R265PrivateNormClosures.norm_exact,R265PrivateNormClosures.polar_exact,
    R252PrivateComplexLinear.c_sub,R252PrivateComplexLinear.c_add,
    R252PrivateComplexLinear.c_half,coefficients,bind_tc_ok]

theorem coeff_four_exact (a b c : QM31Exact) (x y t : M31Exact) :
    Coeff110.four (coefficients a b c)
      (ComplexBaseExecution.encodeBase x) (ComplexBaseExecution.encodeBase y)
      (ComplexBaseExecution.encodeBase t) =
        .ok (Array.make 4#usize [
          encodeC ((R225LineNormAlgebra.lineFour a b c (mapBase x) (mapBase y) (mapBase t)).1),
          encodeC ((R225LineNormAlgebra.lineFour a b c (mapBase x) (mapBase y) (mapBase t)).2.1),
          encodeC ((R225LineNormAlgebra.lineFour a b c (mapBase x) (mapBase y) (mapBase t)).2.2.1),
          encodeC ((R225LineNormAlgebra.lineFour a b c (mapBase x) (mapBase y) (mapBase t)).2.2.2)]) := by
  simp [Coeff110.four,coefficients,Array.index_usize,Array.make,
    R250PrivateBaseExecution.mul_encoded,R252PrivateComplexLinear.c_mul_m,
    R252PrivateComplexLinear.c_add,R252PrivateComplexLinear.c_sub,
    R225LineNormAlgebra.lineFour,R241CoeffExecution.mapBase_mul,bind_tc_ok]

#print axioms coeff_new_exact
#print axioms coeff_four_exact
end
end AspisV8R19.R270PrivateCoefficientExecution
