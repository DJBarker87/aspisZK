import RPv_FJq_CheckedOffset
import RPv_FJq_MainCells
import RPu_FIq_S_RawSemanticTypedPolynomialLift
import RPu_FIq_S_StrictLowChunkFromTypedDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_DecodeChunk
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open RawActualDecodeKMainAdapter RawActualDecodeKMainReadback RawActualDecodeKPayloadBytes
open RawActualDecodeKStrictChunkBridge
open FIz_ConcretePack (embed)
/-- Any actual installed decode_k slot agrees with strict decoding of the SAME
32-byte original record chunk, at its checked offset. No chosen field output. -/
theorem value (n : Usize) (record : r1_wire.ValidatedRecord) (offset : Usize)
    (out : Array aspis_core.field.QM31 n) (run : decodeMain n record offset=ok (.Ok out))
    (j : Fin n.val) (x : SemanticCoefficientCodec.LowWide)
    (literal : SemanticCoefficientCodec.decodeLow
      ((((record.framed.val.drop 5).drop (32*(offset.val+j.val))).take 32).map
        ExtractedRecordByteValue.rawByte)=some x) :
    embed (FIp_SemanticValues.decode (FJq_MainCells.cell out j))=x.val := by
  obtain ⟨byteOffset,hOffset,hvalues⟩:=decodeMain_success_indexed_parser n record offset out run
  obtain ⟨q,call,source,⟨trace⟩,canonical⟩:=hvalues j
  have byteValue:=FJq_CheckedOffset.value offset byteOffset hOffset
  have start : (AspisR1DecodeKFullValueTrace.ParserTrace.payloadStart trace).val=32*(offset.val+j.val) := by
    rw [payloadStart_eq trace,byteValue]
    change offset.val*32+j.val*32=_
    omega
  have raw : (((AspisR1DecodeKFullValueTrace.ParserTrace.payloadData trace).val.drop
      (AspisR1DecodeKFullValueTrace.ParserTrace.payloadStart trace).val).take 32)=
      (((record.framed.val.drop 5).drop (32*(offset.val+j.val))).take 32) := by
    rw [payloadData_eq_drop trace,start]
    rfl
  have strict:=StrictLowChunkFromTypedDecode.strictLowChunk_of_decodeLow _ x literal
  rw [←raw] at strict
  obtain ⟨limbs,decoded,same,field,encoded⟩:=trace_strict_chunk_decodes_same_value trace strict
  rw [raw,literal] at decoded
  have chosen:=Option.some.inj decoded
  have field' : FIp_SemanticValues.decode (FJq_MainCells.cell out j)=x.val.re := by
    unfold FJq_MainCells.cell
    rw [source]
    change ExtractedMaskQM31Exact.decode (RawSemanticFieldOwnerAdapter.mainToProbe (decoderQMToMain q))=_
    rw [chosen]
    exact field
  rw [field']
  exact RawSemanticTypedPolynomialLift.lowWide_eq_embedding x
#print axioms value
end AspisR1.FJq_DecodeChunk
end
