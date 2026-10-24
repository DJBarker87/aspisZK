import S9SharedHighConstructorModelV1
import S9TwoFoldProductModelV1
import S9SymbolicRowTransportV1
import S9SourceFactorShapeTransportV1
import S9SourceQuarterModelBridgeV1
import S9OpaqueQEmbedTripleV1
import S9QuadraticFieldMulProjectionV1
set_option autoImplicit false
namespace AspisR1S9PointNativeMulProjectionV1
open AspisR1S9QuadraticFieldMulProjectionV1
abbrev E := AspisWideTower.WideExact
/-- The actual consumer import context; operands remain opaque. -/
theorem native_mul_projected (x y : E) : x*y=projectedMul x y := by
  exact (quadratic_field_mul AspisWideTower.wideU 0 x y).symm
#print axioms native_mul_projected
end AspisR1S9PointNativeMulProjectionV1
