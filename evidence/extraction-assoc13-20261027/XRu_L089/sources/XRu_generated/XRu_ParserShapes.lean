import XRr_RecordAssociation
import ExtractedPrefixParseCore
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers
set_option autoImplicit false
namespace XRu_ParserShapes
abbrev OldError := AspisR1PrefixAggregateParser.r1_wire.Error
def error : r1_wire.Error → OldError
 | .Allocation => .Allocation | .RowOrder a b => .RowOrder a b
 | .InvalidRow => .InvalidRow | .Tag a => .Tag a | .Length a => .Length a
 | .NonCanonical a b => .NonCanonical a b | .Boundary a => .Boundary a
 | .Terminal => .Terminal | .EqualCirclePoints => .EqualCirclePoints
 | .TrailingBytes => .TrailingBytes | .Public => .Public
theorem error_composition (e : r1_wire.Error) :
 AspisR1PublicPreparation.PrefixAdapter.errorFromOld (error e)=XRr_SemanticCarriers.wire e := by
 cases e <;> rfl
/-- Complete row geometry equality, before either parser accesses bytes. -/
theorem source (row : U8) : r1_wire.row_shape row=
 AspisR1PrefixAggregateParser.r1_wire.row_shape row := by
 rfl
#print axioms error_composition
#print axioms source
end XRu_ParserShapes
