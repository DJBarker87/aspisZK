import AspisR239CoeffExecutionRaw
import AspisV8R19.R222NormLeafExecution
import AspisV8R19.R240HalfExecution

/-! Exact execution of the selected coefficient constructor and four-value
coefficient evaluator.  These theorems describe only the raw leaves. -/
set_option autoImplicit false
namespace AspisV8R19.R241CoeffExecution
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisR239CoeffExecutionRaw
open AspisV8R19.R240HalfExecution (mapBase)
noncomputable section

theorem coeff_new_exact (a b c : QM31Exact) :
    circle_norm.Coeff.new
      (Array.make 3#usize [R164ProductExecution.encode a,
        R164ProductExecution.encode b, R164ProductExecution.encode c]) =
    .ok (Array.make 5#usize [
      R163ComplexExecution.encode (NormInverse.quarticNorm a + NormInverse.quarticNorm c),
      R163ComplexExecution.encode (NormInverse.quarticNorm b - NormInverse.quarticNorm c),
      R163ComplexExecution.encode (R218CircleNormAlgebra.polar a b),
      R163ComplexExecution.encode (R218CircleNormAlgebra.polar a c),
      R163ComplexExecution.encode (R218CircleNormAlgebra.polar b c)]) := by
  simp only [circle_norm.Coeff.new, Array.index_usize, Array.make,
    R222NormLeafExecution.norm_exact, R222NormLeafExecution.polar_exact,
    R163ComplexExecution.cm_add, R163ComplexExecution.cm_sub, bind_tc_ok]

private theorem mul_mapBase (z : CM31Exact) (u v : M31Exact) :
    z * mapBase (u*v) = (z * mapBase u) * mapBase v := by
  apply QuadraticAlgebra.ext <;>
    simp [mapBase, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring

theorem coeff_four_exact (a b c : QM31Exact) (x y : M31Exact) :
    circle_norm.Coeff.four
      (Array.make 5#usize [
        R163ComplexExecution.encode (NormInverse.quarticNorm a + NormInverse.quarticNorm c),
        R163ComplexExecution.encode (NormInverse.quarticNorm b - NormInverse.quarticNorm c),
        R163ComplexExecution.encode (R218CircleNormAlgebra.polar a b),
        R163ComplexExecution.encode (R218CircleNormAlgebra.polar a c),
        R163ComplexExecution.encode (R218CircleNormAlgebra.polar b c)])
      (ComplexBaseExecution.encodeBase x) (ComplexBaseExecution.encodeBase y) =
    .ok (Array.make 4#usize [
      R163ComplexExecution.encode ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).1),
      R163ComplexExecution.encode ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.1),
      R163ComplexExecution.encode ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.2.1),
      R163ComplexExecution.encode ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.2.2)]) := by
  simp only [circle_norm.Coeff.four, Array.index_usize, Array.make,
    R161WrappedMulExecution.mul_encode, R240HalfExecution.cm_mul_m31_exact,
    R163ComplexExecution.cm_add, R163ComplexExecution.cm_sub, bind_tc_ok]
  simp only [R218CircleNormAlgebra.four, mapBase]
  congr 1 <;> congr 1 <;> congr 1 <;> ring

#print axioms coeff_new_exact
#print axioms mul_mapBase
#print axioms coeff_four_exact
end
end AspisV8R19.R241CoeffExecution
