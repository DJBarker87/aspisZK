import NDO_JFv_DecodeCanonical
import RPu_FIq_S_RawActualDecodeKPayloadBytes
import RPu_FIq_S_RawActualDecodeKInitialLowClaim
set_option autoImplicit false
namespace AspisR1.JFu_DecodeAt
open Aeneas Aeneas.Std Result
open AspisS1ExtractedRoundChildren
open AspisR1PublicPreparation
open AspisR1PublicPreparation.RawActualDecodeKMainStrictReadback
open AspisR1PublicPreparation.RawActualDecodeKPayloadBytes
open AspisR1DecodeKFullValueTrace (ParserTrace)

theorem source {N : Usize} (record : r1_wire.ValidatedRecord) (out : Array MainQM N)
    (offset : Usize) (smallOffset : offset.val ≤ 116)
    (call : decodeMain N record offset=ok (.Ok out)) (j : Fin N.val)
    (arr : Array U8 16#usize) (expected : DecodeQM)
    (bytes : ((record.framed.val.drop 5).drop (32*(offset.val+j.val))).take 16=arr.val)
    (parser : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice arr)=ok (some expected)) :
    out.val[j.val]'(by simpa only [out.property] using j.isLt)=decoderQMToMain expected := by
  obtain ⟨decoded,run,same⟩ := F3P_DecodeCells.source record offset out call
  obtain ⟨byteOffset,offsetCall,values⟩ := AspisR1DecodeKFullSuccessIndexedParser.decode_k_success_indexed_parser
    N (recordToDecoder record) offset decoded run
  obtain ⟨actual,multiplied,actualVal⟩ := JFv_Checked.multiply offset 32#usize (by scalar_tac)
  rw [multiplied] at offsetCall
  have hsame : byteOffset=actual := (Option.some.inj (Result.ok.inj offsetCall)).symm
  obtain ⟨q,qcall,qcell,⟨trace⟩⟩ := values j j.isLt
  have start : (ParserTrace.payloadStart trace).val=32*(offset.val+j.val) := by
    have h := payloadStart_eq trace
    have hz : byteOffset.val=offset.val*32 := by
      rw [hsame]
      simpa only [show (32#usize).val=32 from rfl] using actualVal
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
end AspisR1.JFu_DecodeAt
