import XRu_ParserShapes
import XRo_Join_ResultTransport
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XRu_ParserHeader
open XRu_ParserShapes
/-- Exact frame checks for the unvalidated header rows; validation rows14..26
remain a separate whole-parser obligation. -/
theorem source (row : U8) (bytes : Slice U8) (early : row.val<14) :
 mapR (inner id error) (r1_wire.parse_record row bytes)=
 AspisR1PrefixAggregateParser.r1_wire.parse_record row bytes := by
 have h : ¬row≥14#u8 := by scalar_tac
 unfold r1_wire.parse_record AspisR1PrefixAggregateParser.r1_wire.parse_record
 rw [XRu_ParserShapes.source row]
 simp only [if_neg h,mapR_bind]
 repeat' first | rfl | (congr 1) | (funext x) | (split)
#print axioms source
end XRu_ParserHeader
