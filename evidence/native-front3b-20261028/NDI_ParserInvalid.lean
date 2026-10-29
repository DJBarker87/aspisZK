import NCO_Framing
set_option autoImplicit false
namespace NDI_ParserInvalid
open Aeneas Aeneas.Std Result

theorem reference (row : U8) (frame : Slice U8)
    (shape : NCO_ParserRef.row_shape_ref row=ok none) :
    (do let r ← NCO_ParserRef.parse_record_ref row frame; ok (NCO_Framing.result r)) =
      AspisR1PrefixAggregateParser.r1_wire.parse_record row frame := by
  have sourceShape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok none := by
    simpa only [NCO_ParserShape.parser_shape] using shape
  simp only [NCO_ParserRef.parse_record_ref,AspisR1PrefixAggregateParser.r1_wire.parse_record,
    shape,sourceShape,NCO_ParserRef.core.option.Option.ok_or,
    AspisR1PrefixAggregateParser.core.option.Option.ok_or,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from,NCO_Framing.result,NCO_Framing.error]

#print axioms reference
end NDI_ParserInvalid
