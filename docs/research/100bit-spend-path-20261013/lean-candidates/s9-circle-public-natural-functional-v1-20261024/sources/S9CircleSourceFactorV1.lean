import S9CircleTensorGenericV1
import S9CirclePointscanModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisR1S9CircleSourceFactorV1
open AspisR1S9FactorTableSemanticsV1 (ExactQM)
abbrev Point := AspisR1S9CirclePointscanModelV1.Point
open AspisR1S9ConstructorV3QMMulSemanticsV1 (decode)

/-- One opaque source factor matches the generic natural-circle table.
The arbitrary dimension/index are not evaluated and no recurrence unfolds. -/
theorem source_circle_factor (point : Point) (d i : Nat) :
    AspisR1S9CirclePointscanModelV1.circleRow point d i=
      AspisR1S9CircleTensorGenericV1.circleTable (decode point.x) (decode point.y) d i := by
  unfold AspisR1S9CirclePointscanModelV1.circleRow
    AspisR1S9CirclePointscanModelV1.rowZero AspisR1S9CircleFactorModelV1.coefficient
    AspisR1S9CircleFactorModelV1.base AspisR1S9CircleTensorGenericV1.circleTable
    AspisR1S9CircleTensorGenericV1.firstCoefficient AspisR1S9CircleTensorGenericV1.lineCoefficient
    AspisR1S9CircleTensorGenericV1.base
  rfl

#print axioms source_circle_factor
end AspisR1S9CircleSourceFactorV1
