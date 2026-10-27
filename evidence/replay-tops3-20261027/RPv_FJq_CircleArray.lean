import RPv_FJq_CirclePayload
import RPv_FJq_DecodeSequence
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_CircleArray
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIz_ConcretePack (embed)
theorem value (row : Fin 2) (record : r1_wire.ValidatedRecord)
    (payload : CircleRecordCodec.Payload row)
    (parsed : CircleRecordCodec.decode row (record.framed.val.map ExtractedRecordByteValue.rawByte)=some payload)
    (n : Usize) (offset : Usize) (out : Array aspis_core.field.QM31 n)
    (run : RawActualDecodeKMainAdapter.decodeMain n record offset=ok (.Ok out))
    (bound : offset.val+n.val≤CircleRecordCodec.count row) (j : Fin n.val) :
    embed (FIp_SemanticValues.decode (FJq_MainCells.cell out j))=
      (payload ⟨offset.val+j.val,by omega⟩).val :=
  FJq_DecodeSequence.value n record offset out run _ payload
    (FJq_CirclePayload.value row record payload parsed) bound j
#print axioms value
end AspisR1.FJq_CircleArray
end
