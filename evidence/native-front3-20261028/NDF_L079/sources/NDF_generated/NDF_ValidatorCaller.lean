import NDF_ValidatorBridge
import NDF_AcceptedFrame
set_option autoImplicit false
namespace NDF_ValidatorCaller
open Aeneas Aeneas.Std Result

theorem payload_bound (row tag : U8) (size : Usize) (frame payload acceptedPayload : Slice U8)
    (shape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok (some (tag,size)))
    (parsed : AspisR1PrefixAggregateParser.r1_wire.parse_record row frame=ok (.Ok acceptedPayload))
    (range : payload.val=frame.val.drop 5) : payload.val.length≤3712 := by
  have cap := NDF_AcceptedFrame.accepted row tag size frame acceptedPayload shape parsed
  rw [range,List.length_drop]
  omega

theorem validator (row tag : U8) (size : Usize) (frame payload acceptedPayload : Slice U8)
    (shape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok (some (tag,size)))
    (parsed : AspisR1PrefixAggregateParser.r1_wire.parse_record row frame=ok (.Ok acceptedPayload))
    (range : payload.val=frame.val.drop 5) :
    (do let status ← NCO_ParserRef.validate_ref row payload; ok (NCO_Framing.result status)) =
      AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row payload := by
  exact NDF_ValidatorBridge.reference row payload
    (payload_bound row tag size frame payload acceptedPayload shape parsed range)

#print axioms payload_bound
#print axioms validator
end NDF_ValidatorCaller
