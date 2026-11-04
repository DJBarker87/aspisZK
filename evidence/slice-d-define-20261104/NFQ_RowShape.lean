import NFQ_Reference.Funs
import NCO_ScalarBridge
import NCO_ParserShape
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NFQ_RowShape
theorem reference (row : U8) :
    NFQ_Reference.row_shape_ref row = AspisS1NativeCompact.r1_wire.row_shape row := by
  change NCO_Reference.row_shape_ref row = _
  exact NCO_ScalarBridge.row_shape row
theorem prefix_reference (row : U8) :
    NFQ_Reference.row_shape_ref row = AspisR1PrefixAggregateParser.r1_wire.row_shape row := by
  change NCO_Reference.row_shape_ref row = _
  exact NCO_ParserShape.prefix_shape row
theorem compact_reference (row : U8) :
    NFQ_Reference.compact_row_ref row = AspisS1NativeCompact.compact.compact_row row := by
  change NCO_Reference.compact_row_ref row = _
  exact NCO_ScalarBridge.compact_row row
#print axioms reference
#print axioms prefix_reference
#print axioms compact_reference
end NFQ_RowShape
