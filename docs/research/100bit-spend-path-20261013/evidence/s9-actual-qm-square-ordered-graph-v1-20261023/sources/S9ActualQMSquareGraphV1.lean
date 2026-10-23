import AspisR1S9SquareMulQMCutV1.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualQMSquareGraphV1

theorem actual_qm_square_graph (x : AspisR1S9SquareMulQMCutV1.field.QM31) :
    AspisR1S9SquareMulQMCutV1.field.QM31.square x = (do
      let c0Square ← AspisR1S9SquareMulQMCutV1.field.CM31.square x.c0
      let c1Square ← AspisR1S9SquareMulQMCutV1.field.CM31.square x.c1
      let rotated ← AspisR1S9SquareMulQMCutV1.field.mul_by_r c1Square
      let c0 ← AspisR1S9SquareMulQMCutV1.field.CM31.add c0Square rotated
      let cross ← AspisR1S9SquareMulQMCutV1.field.CM31.mul x.c0 x.c1
      let c1 ← AspisR1S9SquareMulQMCutV1.field.CM31.double cross
      Result.ok { c0 := c0, c1 := c1 }) := by
  rfl

#print axioms actual_qm_square_graph

end AspisR1S9ActualQMSquareGraphV1
