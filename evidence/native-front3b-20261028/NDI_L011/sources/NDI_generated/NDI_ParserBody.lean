import NDI_ParserPayload
import NDI_ParserHeader
import NCO_Framing
import NDI_HeaderShifts
set_option autoImplicit false
namespace NDI_ParserBody
open Aeneas Aeneas.Std Result

theorem reference (row tag : U8) (size total : Usize) (frame : Slice U8)
    (shape : NCO_ParserRef.row_shape_ref row=ok (some (tag,size)))
    (sum : 5#usize+size=ok total) :
    (do let r ← NCO_ParserRef.parse_record_ref row frame; ok (NCO_Framing.result r)) =
      AspisR1PrefixAggregateParser.r1_wire.parse_record row frame := by
  have sourceShape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok (some (tag,size)) := by
    simpa only [NCO_ParserShape.parser_shape] using shape
  by_cases wrongLength : Slice.len frame ≠ total
  · exact NCO_Framing.length_bridge row tag size total frame shape sum wrongLength
  have length : Slice.len frame=total := not_ne_iff.mp wrongLength
  have totalVal : total.val=5+size.val := by
    have bound := (NDF_ParserDomain.shape_bound row tag size sourceShape).1
    obtain ⟨z,call,value⟩ := WP.spec_imp_exists (Usize.add_spec (x:=5#usize) (y:=size) (by scalar_tac))
    have same : z=total := Result.ok.inj (call.symm.trans sum)
    simpa only [same,show (5#usize).val=5 by scalar_tac] using value
  have frameVal : frame.val.length=5+size.val := by
    have h := congrArg UScalar.val length
    change frame.val.length=total.val at h
    omega
  have five : 5≤frame.val.length := by omega
  have bound := NDF_ParserDomain.framed_cap row tag size frame sourceShape frameVal
  obtain ⟨a,ha,_⟩ := WP.spec_imp_exists (Slice.index_usize_spec frame 0#usize (by scalar_tac))
  obtain ⟨b,hb,_⟩ := WP.spec_imp_exists (Slice.index_usize_spec frame 1#usize (by scalar_tac))
  obtain ⟨c,hc,_⟩ := WP.spec_imp_exists (Slice.index_usize_spec frame 2#usize (by scalar_tac))
  obtain ⟨d,hd,_⟩ := WP.spec_imp_exists (Slice.index_usize_spec frame 3#usize (by scalar_tac))
  obtain ⟨e,he,_⟩ := WP.spec_imp_exists (Slice.index_usize_spec frame 4#usize (by scalar_tac))
  have word := NDF_ParserWord.little_endian b c d e
  simp only [NDF_ParserWord.word,NDI_HeaderShifts.byte8,NDI_HeaderShifts.byte16,NDI_HeaderShifts.byte24,bind_tc_ok] at word
  have wordVal := Result.ok.inj word
  unfold NCO_ParserRef.parse_record_ref AspisR1PrefixAggregateParser.r1_wire.parse_record
  simp only [shape,sourceShape,NCO_ParserRef.core.option.Option.ok_or,
    AspisR1PrefixAggregateParser.core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    bind_tc_ok,sum,length,ne_self,if_false,ha,hb,hc,hd,he,lift,
    NDI_HeaderShifts.byte8,NDI_HeaderShifts.byte16,NDI_HeaderShifts.byte24,wordVal,
    NDI_ParserPayload.range frame five]
  split
  · rfl
  · split
    · rfl
    · split
      · rw [← NDI_ParserPayload.validator row frame bound]
        generalize NCO_ParserRef.validate_ref row (Slice.drop frame 5#usize)=reply
        cases reply with
        | fail error => rfl
        | div => rfl
        | ok reply => cases reply <;> rfl
      · rfl

#print axioms reference
end NDI_ParserBody
