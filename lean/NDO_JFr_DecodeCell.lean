import NDO_JFv_DecodeCanonical
import RPu_FIq_S_RawActualDecodeKPayloadBytes
import RPu_FIq_S_RawActualDecodeKInitialLowClaim
set_option autoImplicit false
namespace AspisR1.JFr_DecodeCell
open Aeneas Aeneas.Std Result
open AspisS1ExtractedRoundChildren
open AspisR1PublicPreparation
open AspisR1PublicPreparation.RawActualDecodeKMainStrictReadback
open AspisR1PublicPreparation.RawActualDecodeKPayloadBytes
open AspisR1DecodeKFullValueTrace (ParserTrace)

theorem source {N : Usize} (record : r1_wire.ValidatedRecord) (out : Array MainQM N)
    (call : decodeMain N record 0#usize=ok (.Ok out)) (j : Fin N.val)
    (arr : Array U8 16#usize) (expected : DecodeQM)
    (bytes : ((record.framed.val.drop 5).drop (32*j.val)).take 16=arr.val)
    (parser : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice arr)=ok (some expected)) :
    out.val[j.val]'(by simpa only [out.property] using j.isLt)=decoderQMToMain expected := by
  obtain ⟨decoded,run,same⟩ := F3P_DecodeCells.source record 0#usize out call
  obtain ⟨byteOffset,offset,values⟩ := AspisR1DecodeKFullSuccessIndexedParser.decode_k_success_indexed_parser
    N (recordToDecoder record) 0#usize decoded run
  have hzero : byteOffset=0#usize := by
    rw [RawActualDecodeKInitialLowClaim.checked_mul_zero_32] at offset
    change ok (some 0#usize)=ok (some byteOffset) at offset
    exact (Option.some.inj (Result.ok.inj offset)).symm
  obtain ⟨q,qcall,qcell,⟨trace⟩⟩ := values j j.isLt
  have start : (ParserTrace.payloadStart trace).val=32*j.val := by
    have h := payloadStart_eq trace
    have hz : byteOffset.val=0 := by rw [hzero];rfl
    change (ParserTrace.payloadStart trace).val=byteOffset.val+j.val*32 at h
    omega
  have input : (inputArray trace).val=arr.val := by
    rw [inputArray_payload_slice,payloadData_eq_drop,start]
    exact bytes
  have arraySame : inputArray trace=arr := Subtype.ext input
  have read := ParserTrace.hparse trace
  rw [trace_input_eq,arraySame,parser] at read
  have expectedSame : q=expected := (Option.some.inj (Result.ok.inj read)).symm
  rw [←same]
  simp only [decoderArrayToMain,List.getElem_map,qcell,expectedSame]

#print axioms source
end AspisR1.JFr_DecodeCell
