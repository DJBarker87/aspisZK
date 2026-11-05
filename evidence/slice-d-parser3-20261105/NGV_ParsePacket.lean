import NGV_ParseSubstitution
import NGV_Payload
import NGV_ValidatorTotal
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_ParsePacket
open AspisR1PrefixAggregateParser
/-- Construct the complete parser packet from the original input, including
all rejection branches and borrowed payload provenance. The native reply is
computed by the CLOSED validator, never supplied as a success premise. -/
theorem result (row : U8) (record : Slice U8) (bound : record.val.length≤3717) :
 ∃ reply : core.result.Result Unit NGD_AtG.Error,
 NGD_ParseReference.mapResult NGO_ValidatorErrors.mapError
   (NFU_Retarget.r1_wire.validate_record_fields row (NGV_Payload.original record))=
   ok (NGD_ErrorPort.mapError reply) ∧
 r1_wire.parse_record row record=
   NGD_ParseReference.mapResult NGD_ErrorPort.mapError (NGD_AtG.parse_g row record reply) := by
 have payloadBound : (NGV_Payload.original record).val.length≤3712 := by
   simp only [NGV_Payload.original,List.length_drop];omega
 obtain ⟨reply,validator,model⟩:=NGV_ValidatorTotal.result row (NGV_Payload.original record) payloadBound
 let nativeReply:=NGD_ErrorPort.unmapError reply
 have same: NGD_ErrorPort.mapError nativeReply=reply := NGD_ErrorPort.result_roundtrip reply
 refine ⟨nativeReply,by simpa only [same] using model,?_⟩
 rw [NGD_ParseCut.emitted]
 rw [NGV_ParseSubstitution.congr row record r1_wire.validate_record_fields
   (fun _ _=>ok (NGD_ErrorPort.mapError nativeReply)) (by
     intro payload original
     rw [NGV_Payload.selected record payload original,validator,same])]
 exact (NGD_ParseReference.all_inputs row record nativeReply).symm
#print axioms result
end NGV_ParsePacket
