import AspisR264PrivateCoefficientRaw
import AspisV8R19.R257PrivateSquare
import AspisV8R19.R258PrivateProduct
import AspisV8R19.R252PrivateComplexLinear
import AspisV8R19.R218CircleNormAlgebra

/-! The two actual private coefficient closures, with their indexed arrays
and selected private arithmetic. No coefficient constructor or batch proof. -/
set_option autoImplicit false
namespace AspisV8R19.R265PrivateNormClosures
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisR264PrivateCoefficientRaw.circle_norm.joined_inverse.line_norm.r110_norm (Coeff110)
open AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm (C)
open R250PrivateBaseExecution (encodeC)
noncomputable section

def privateParts (v : QM31Exact) : Array C 2#usize :=
  Array.make 2#usize [encodeC v.re,encodeC v.im]

theorem norm_exact (v : QM31Exact) :
    Coeff110.new.closure.Insts.CoreOpsFunctionFnTupleArrayC2C.call () (privateParts v) =
      .ok (encodeC (NormInverse.quarticNorm v)) := by
  simp [Coeff110.new.closure.Insts.CoreOpsFunctionFnTupleArrayC2C.call,
    privateParts,Array.make,Array.index_usize,R257PrivateSquare.c_square,
    R252PrivateComplexLinear.c_times_r,R252PrivateComplexLinear.c_sub,
    NormInverse.quarticNorm,bind_tc_ok]

theorem polar_exact (v w : QM31Exact) :
    Coeff110.new.closure_1.Insts.CoreOpsFunctionFnPairArrayC2ArrayC2C.call ()
      (privateParts v,privateParts w) =
        .ok (encodeC (R218CircleNormAlgebra.polar v w)) := by
  simp [Coeff110.new.closure_1.Insts.CoreOpsFunctionFnPairArrayC2ArrayC2C.call,
    privateParts,Array.make,Array.index_usize,R258PrivateProduct.c_mul,
    R252PrivateComplexLinear.c_times_r,R252PrivateComplexLinear.c_sub,
    R252PrivateComplexLinear.c_double,R218CircleNormAlgebra.polar,
    mul_two,bind_tc_ok]

#print axioms norm_exact
#print axioms polar_exact
end
end AspisV8R19.R265PrivateNormClosures
