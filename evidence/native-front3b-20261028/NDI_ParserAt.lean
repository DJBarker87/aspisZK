import NDI_ParserTotal
import NDF_AtCompose
set_option autoImplicit false
namespace NDI_ParserAt
open Aeneas Aeneas.Std Result

theorem reference (bytes : Slice U8) (row tag : U8) (offset size len finish : Usize)
    (shape : NCO_ParserRef.row_shape_ref row=ok (some (tag,size)))
    (sum : 5#usize+size=ok len) (add : offset+len=ok finish) :
    (do let r ← NCO_ParserRef.parse_at_ref bytes row offset; ok (NCO_Framing.result r)) =
      AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes row offset :=
  NDF_AtCompose.reference bytes row tag offset size len finish shape sum add
    (NDI_ParserTotal.reference row)

#print axioms reference
end NDI_ParserAt
