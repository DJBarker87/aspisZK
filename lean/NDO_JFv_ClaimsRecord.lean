import NDO_JFv_PrefixRecord
set_option autoImplicit false
namespace AspisR1.JFv_ClaimsRecord
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open OraclePortCompactDraft MultiproofConeCanonical

theorem fields (bytes : Slice U8) (pre : r1_wire.Prefix)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) :
    ∃ vr,r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok vr) ∧
      vr.row=25#u8 ∧ vr.framed.val.length=3717 ∧ canonical (bytesOf (vr.framed.val.drop 5)) := by
  obtain ⟨vr,call⟩ := JFv_PrefixRecord.validated pre 25#u8 (by decide)
  have hp := PrefixAdapter.parse_success bytes pre parsed
  obtain ⟨sameRow,slot⟩ := SourceFull25.validated_record_bytes pre 25#u8 vr call
  have member : (25#u8,vr.framed) ∈ ExtractedPrefixTrace.rowOrder.zip (PrefixAdapter.toOld pre).records.val := by
    apply List.mem_of_getElem? (i:=25)
    exact List.getElem?_zip_eq_some.mpr ⟨rfl,slot⟩
  obtain ⟨payload,accepted⟩ := ExtractedPrefixParse.parse_record_of_success bytes
    (PrefixAdapter.toOld pre) hp 25#u8 vr.framed member
  have canon := PSem_FieldCanonical.source_payload 25#u8 vr.framed payload (by decide) accepted
  have framing := ExtractedRecordFraming.parse_record_success 25#u8 vr.framed payload
    (ExtractedPrefixParserAgreement.parse_record_success 25#u8 vr.framed payload accepted)
  rcases framing with ⟨tag,size,b1,b2,b3,b4,shape,length,rest⟩
  refine ⟨vr,call,sameRow,NP6_RecordShape.on_parsed_prefix bytes pre vr parsed call,?_⟩
  rcases rest with ⟨h0,h1,h2,h3,h4,header,selected,payloadLength,validator⟩
  rw [selected] at canon
  exact canon

#print axioms fields
end AspisR1.JFv_ClaimsRecord
