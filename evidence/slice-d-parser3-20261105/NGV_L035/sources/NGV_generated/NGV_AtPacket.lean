import NGV_AtSubstitution
import NGO_AtDomain
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_AtPacket
open AspisR1PrefixAggregateParser
/-- Complete borrowed parser-at packet at every deployed original row cursor.
The callee reply is constructed on that exact original window before the full
error/borrowed carrier is transported. There is no parser success premise. -/
theorem result (bytes : Slice U8) (row : U8) (offset : Usize)
 (valid : row.val<27) (cursor : offset.val=NGD_SemanticSchedule.dst row.val) :
 ∃ (tag : U8) (size length finish : Usize) (framed : Slice U8)
   (reply : core.result.Result Unit NGD_AtG.Error),
 NGD_AtG.shape row=ok (some (tag,size)) ∧
 5#usize+size=ok length ∧ offset+length=ok finish ∧
 finish.val=NGD_SemanticSchedule.dst (row.val+1) ∧
 framed.val=(bytes.val.drop offset.val).take (5+size.val) ∧
 NGD_ParseReference.mapResult NGO_ValidatorErrors.mapError
  (NFU_Retarget.r1_wire.validate_record_fields row (NGV_Payload.original framed))=
  ok (NGD_ErrorPort.mapError reply) ∧
 r1_wire.parse_record_at bytes row offset=
 NGD_ParseReference.mapResult NGD_ErrorPort.mapError (NGD_AtG.parse_at_g bytes row offset reply) := by
 obtain ⟨tag,size,length,finish,shape,lengthAdd,endAdd,finishValue,finishBound⟩:=
   NGD_AtDomains.from_cursor row offset valid cursor
 have sourceShape : r1_wire.row_shape row=ok (some (tag,size)) := by rw [←NGD_AtShape.reference];exact shape
 have sizeBounds:=NFU_RowDomains.parser_shape row tag size sourceShape
 have lengthValue : length.val=5+size.val := by
   have h:=UScalar.add_equiv 5#usize size;rw [lengthAdd] at h;simpa using h.2.1
 have endValue : finish.val=offset.val+5+size.val := by
   have h:=UScalar.add_equiv offset length;rw [endAdd] at h;rw [h.2.1,lengthValue];omega
 let framed : Slice U8:=⟨(bytes.val.drop offset.val).take (5+size.val),by
   have h:=bytes.property;simp only [List.length_take,List.length_drop];omega⟩
 have frameBound : framed.val.length≤3717 := by
   simp only [framed,List.length_take];omega
 obtain ⟨reply,validator,parser⟩:=NGV_ParsePacket.result row framed frameBound
 refine ⟨tag,size,length,finish,framed,reply,shape,lengthAdd,endAdd,finishValue,rfl,validator,?_⟩
 rw [NGD_AtCut.emitted]
 rw [NGV_AtSubstitution.congr bytes row tag offset size length finish r1_wire.parse_record
   (NGD_AtReference.parser reply) sourceShape lengthAdd endAdd (by
     intro actual original
     have actualWindow: actual=framed := by
       apply Subtype.ext
       exact (NGO_AtDomain.from_source_window bytes actual offset finish size original endValue).2
     rw [actualWindow,parser]
     exact NGD_ParseReference.all_inputs row framed reply)]
 exact (NGD_AtReference.forward row tag size length finish offset bytes reply shape lengthAdd endAdd).symm
#print axioms result
end NGV_AtPacket
