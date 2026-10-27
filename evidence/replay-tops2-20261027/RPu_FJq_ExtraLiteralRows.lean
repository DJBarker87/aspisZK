import RPu_FJq_CircleArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_ExtraLiteralRows
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIz_ConcretePack (embed)
/-- The full actual extra subarray, including lane28, is decoded from the
SAME row25 strict payload after the 87 point-claim entries. -/
theorem value (record : r1_wire.ValidatedRecord) (payload : CircleRecordCodec.Payload 0)
    (parsed : CircleRecordCodec.decode 0 (record.framed.val.map ExtractedRecordByteValue.rawByte)=some payload)
    (out : Array aspis_core.field.QM31 29#usize)
    (run : AspisS1ExtractedRoundChildren.decodeMain 29#usize record 87#usize=ok (.Ok out))
    (l : Fin 29) :
    embed (FIp_SemanticValues.decode (FJq_MainCells.cell out l))=(CircleRecordCodec.extra payload l).val :=
  FJq_CircleArray.value 0 record payload parsed 29#usize 87#usize out run (by decide) l
#print axioms value
end AspisR1.FJq_ExtraLiteralRows
end
