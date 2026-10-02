import AspisV8R19.R242LineCoeffExecution

/-! A composed arithmetic fragment matching the source point-derived line
coordinate and retained coefficient leaves. No pointer, vector, private R110
fast-path or whole callback correspondence is asserted. -/
set_option autoImplicit false
namespace AspisV8R19.R243LineNormBridge
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase)
open R240HalfExecution (mapBase)
noncomputable section

def rawLineCoordinate (x : U32) : Result U32 := do
  let xx ← AspisR156FullFreeze.aspis_core.field.M31.mul x x
  let twice ← AspisR156FullFreeze.aspis_core.field.M31.double xx
  AspisR156FullFreeze.aspis_core.field.M31.sub twice
    1#u32

theorem line_coordinate_exact (x : M31Exact) :
    rawLineCoordinate (encodeBase x) = .ok (encodeBase (2*x^2-1)) := by
  have hone : 1#u32 = encodeBase 1 := rfl
  simp only [rawLineCoordinate,R161WrappedMulExecution.mul_encode,
    R159WideBaseExecution.double_encode,R159WideBaseExecution.sub_encode,
    hone,bind_tc_ok]
  congr 2
  ring

theorem mapBase_line (x : M31Exact) :
    mapBase (2*x^2-1) = 2*(mapBase x)^2-1 := by
  have hr1 : (1 : CM31Exact).re = (1 : M31Exact) := rfl
  have hi1 : (1 : CM31Exact).im = 0 := rfl
  have hr2 : (2 : CM31Exact).re = (2 : M31Exact) := rfl
  have hi2 : (2 : CM31Exact).im = 0 := rfl
  apply QuadraticAlgebra.ext <;>
    simp [mapBase,pow_two,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,hr1,hi1,hr2,hi2] <;> ring

def retainedLineFragment (abc : Aeneas.Std.Array AspisR156FullFreeze.aspis_core.field.QM31 3#usize)
    (x y : U32) : Result (Aeneas.Std.Array AspisR156FullFreeze.aspis_core.field.CM31 4#usize) := do
  let t ← rawLineCoordinate x
  let coeff ← AspisR239CoeffExecutionRaw.circle_norm.joined_inverse.line_norm.LineCoeff.new abc
  AspisR239CoeffExecutionRaw.circle_norm.joined_inverse.line_norm.LineCoeff.four coeff x y t

theorem retained_line_four (a b c : QM31Exact) (x y : M31Exact) :
    retainedLineFragment (Array.make 3#usize [R164ProductExecution.encode a,
      R164ProductExecution.encode b,R164ProductExecution.encode c])
      (encodeBase x) (encodeBase y) =
    .ok (Array.make 4#usize [
      R163ComplexExecution.encode ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).1),
      R163ComplexExecution.encode ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.1),
      R163ComplexExecution.encode ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.2.1),
      R163ComplexExecution.encode ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.2.2)]) := by
  simp only [retainedLineFragment,line_coordinate_exact,
    R242LineCoeffExecution.line_coeff_new_exact,bind_tc_ok,
    R242LineCoeffExecution.line_coeff_four_exact,mapBase_line,
    R225LineNormAlgebra.lineFour_eq]

theorem retained_line_norms (a b c : QM31Exact) (x y : M31Exact)
    (hcircle : x^2+y^2=1) :
    retainedLineFragment (Array.make 3#usize [R164ProductExecution.encode a,
      R164ProductExecution.encode b,R164ProductExecution.encode c])
      (encodeBase x) (encodeBase y) =
    .ok (Array.make 4#usize [
      R163ComplexExecution.encode (NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (mapBase x) (mapBase y))),
      R163ComplexExecution.encode (NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (mapBase x) (-(mapBase y)))),
      R163ComplexExecution.encode (NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (-(mapBase x)) (-(mapBase y)))),
      R163ComplexExecution.encode (NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (-(mapBase x)) (mapBase y)))]) := by
  have hc : (mapBase x)^2+(mapBase y)^2=1 := by
    have hr1 : (1 : CM31Exact).re = (1 : M31Exact) := rfl
    have hi1 : (1 : CM31Exact).im = 0 := rfl
    apply QuadraticAlgebra.ext
    · simpa [mapBase,pow_two,QuadraticAlgebra.re_mul,hr1] using hcircle
    · simp [mapBase,pow_two,QuadraticAlgebra.im_mul,hi1]
  rw [retained_line_four,R218CircleNormAlgebra.four_exact a b c (mapBase x) (mapBase y) hc]

#print axioms line_coordinate_exact
#print axioms mapBase_line
#print axioms retained_line_four
#print axioms retained_line_norms
end
end AspisV8R19.R243LineNormBridge
