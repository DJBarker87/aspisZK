import RPv_FJq_DecodeChunk
import R1SelectedFieldSequenceCodec
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_DecodeSequence
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIz_ConcretePack (embed)
/-- Any installed source subarray is exactly the selected interval of the
SAME strict low-wide sequence; arbitrary offsets remain checked. -/
theorem value (n : Usize) (record : r1_wire.ValidatedRecord) (offset : Usize)
    (out : Array aspis_core.field.QM31 n)
    (run : RawActualDecodeKMainAdapter.decodeMain n record offset=ok (.Ok out))
    (N : Nat) (payload : Fin N → SemanticCoefficientCodec.LowWide)
    (parsed : SelectedFieldSequenceCodec.decodeLow N
      ((record.framed.val.drop 5).map ExtractedRecordByteValue.rawByte)=some payload)
    (bound : offset.val+n.val≤N) (j : Fin n.val) :
    embed (FIp_SemanticValues.decode (FJq_MainCells.cell out j))=
      (payload ⟨offset.val+j.val,by omega⟩).val := by
  have slot:=((SelectedFieldSequenceCodec.decodeLow_eq_some_iff _ payload).mp parsed).2
    ⟨offset.val+j.val,by omega⟩
  apply FJq_DecodeChunk.value n record offset out run j
  simpa only [List.map_drop,List.map_take] using slot
#print axioms value
end AspisR1.FJq_DecodeSequence
end
