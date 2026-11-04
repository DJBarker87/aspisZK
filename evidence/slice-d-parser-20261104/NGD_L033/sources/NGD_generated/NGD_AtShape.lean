import NGD_AtG.Funs
import NFQ_RowShape
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_AtShape
theorem reference (row : U8) :
    NGD_AtG.shape row = AspisR1PrefixAggregateParser.r1_wire.row_shape row := by
  rw [← NFQ_RowShape.prefix_reference]
  rfl
#print axioms reference
end NGD_AtShape
