import AspisR1S9SquareMulQMCutV1.Funs
import S9ActualCMSquareOperandMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualCMSquareGraphV1

abbrev ActualCM := AspisR1S9SquareMulQMCutV1.field.CM31

/-- The extracted source square body, split at its wrapping product. This
preserves the source call order: product, reduction, coordinate multiply,
double, then construction. -/
theorem actual_cm_square_graph (x : ActualCM) :
    AspisR1S9SquareMulQMCutV1.field.CM31.square x = (do
      let product ← AspisR1S9ActualCMSquareOperandMapV1.actualSquareOperand x.a x.b
      let real ← AspisR1S9SquareMulQMCutV1.field.M31.reduce_u64 product
      let ab ← AspisR1S9SquareMulQMCutV1.field.M31.mul x.a x.b
      let imag ← AspisR1S9SquareMulQMCutV1.field.M31.double ab
      Result.ok ⟨real, imag⟩) := by
  simp only [AspisR1S9SquareMulQMCutV1.field.CM31.square,
    AspisR1S9ActualCMSquareOperandMapV1.actualSquareOperand,
    Aeneas.Std.lift, bind_tc_ok, bind_assoc_eq]

#print axioms actual_cm_square_graph

end AspisR1S9ActualCMSquareGraphV1
