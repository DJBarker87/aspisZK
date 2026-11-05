import NGO_CanonicalPort
import NGO_ParseDomain
import NGV_ParsePacket
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_DecodeAfterParse
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter
/-- The decoder is reached only after the SAME record parsed. Derive its
framing from that producer, then reuse the CLOSED NGO packet verbatim. -/
theorem result (N off : Usize) (record : MainRecord) (payload : Slice U8)
 (call : NGO_CallerDomains.Call record.row.val N.val off.val)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.parse_record record.row record.framed=ok (.Ok payload)) :
    ∃ (start : Usize) (d : NGD_DecodeTrace.Domain N (recordToDecoder record) off start)
      (window : Slice U8) (ce : core.slice.iter.ChunksExact U8) (final : NGD_DecodeTrace.Final N),
      window.val=((record.framed.val.drop 5).drop (32*off.val)).take (32*N.val) ∧
      core.slice.Slice.chunks_exact window 32#usize=ok ce ∧
      NGO_NativeTrace.Run d (NGO_ScheduleState.state ce 0#usize)
        (Array.repeat N AspisR1DecodeKFullV10.aspis_core.field.QM31.ZERO) final ∧
      decodeMain N record off=decoderResultToMain N
        (ok (match final.2 with | none=>.Ok final.1 | some reply=>reply)) ∧
      ∃ halt, halt≤N.val ∧ NGO_FirstError.Terminal d halt final ∧
        ∀ j (inside : j<N.val), halt≤j →
          final.1.val[j]'(by rw [final.1.property];exact inside) =
            (Array.repeat N AspisR1DecodeKFullV10.aspis_core.field.QM31.ZERO).val[j]'(by simp [Array.repeat];exact inside) := by
 have valid : record.row.val<27 := (NGO_CallerDomains.numeric record.row.val N.val off.val call).2.1
 obtain ⟨tag,size,shape⟩:=NGD_RowPayload.present record.row valid
 have sourceShape : AspisR1PrefixAggregateParser.r1_wire.row_shape record.row=ok (some (tag,size)) := by
   rw [←NGD_AtShape.reference];exact shape
 have bounds:=NFU_RowDomains.parser_shape record.row tag size sourceShape
 obtain ⟨total,addition,value⟩:=WP.spec_imp_exists
   (UScalar.add_spec (x:=5#usize) (y:=size) (by scalar_tac))
 have framed:=NGO_ParseDomain.header_size AspisR1PrefixAggregateParser.r1_wire.validate_record_fields
   record.row tag size total record.framed payload sourceShape addition (by
     rw [←NGD_ParseCut.emitted];exact parsed)
 rw [NGD_RowPayload.exact_size record.row tag size valid shape] at framed
 exact NGO_DecodeComposed.result N off record call framed
#print axioms result
end NGV_DecodeAfterParse
