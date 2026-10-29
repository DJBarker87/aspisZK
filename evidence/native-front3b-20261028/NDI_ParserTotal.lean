import NDI_ParserBody
import NDI_ParserInvalid
import ExtractedRowShape
set_option autoImplicit false
namespace NDI_ParserTotal
open Aeneas Aeneas.Std Result

theorem reference (row : U8) (frame : Slice U8) :
    (do let r ← NCO_ParserRef.parse_record_ref row frame; ok (NCO_Framing.result r)) =
      AspisR1PrefixAggregateParser.r1_wire.parse_record row frame := by
  have shape : NCO_ParserRef.row_shape_ref row=ok (AspisR1.ExtractedRowShape.table row) := by
    rw [NCO_ParserShape.parser_shape,NDF_ParserDomain.shape_source,
      AspisR1.ExtractedRowShape.row_shape_eq_table]
  cases tableCall : AspisR1.ExtractedRowShape.table row with
  | none =>
    rw [tableCall] at shape
    exact NDI_ParserInvalid.reference row frame shape
  | some pair =>
    rcases pair with ⟨tag,size⟩
    rw [tableCall] at shape
    have sourceShape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok (some (tag,size)) := by
      simpa only [NCO_ParserShape.parser_shape] using shape
    have cap := (NDF_ParserDomain.shape_bound row tag size sourceShape).1
    obtain ⟨total,sum,_⟩ := WP.spec_imp_exists (Usize.add_spec (x:=5#usize) (y:=size) (by scalar_tac))
    exact NDI_ParserBody.reference row tag size total frame shape sum

#print axioms reference
end NDI_ParserTotal
