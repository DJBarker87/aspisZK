import NDO_JFv_RowOrder
import RPz7_PSem_SourceRows
set_option autoImplicit false
namespace AspisR1.JFv_FieldRecord
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open OraclePortCompactDraft MultiproofConeCanonical

theorem fields (bytes : Slice U8) (pre : r1_wire.Prefix)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) (row : U8)
    (valid : row.val<27) (field : 14 ≤ row.val) :
    ∃ vr,r1_wire.Prefix.validated_record pre row=ok (.Ok vr) ∧
      vr.row=row ∧ vr.framed.val.length=5+(rowShape row.val).2 ∧ canonical (bytesOf (vr.framed.val.drop 5)) := by
  obtain ⟨vr,call⟩ := JFv_PrefixRecord.validated pre row valid
  have hp := PrefixAdapter.parse_success bytes pre parsed
  obtain ⟨sameRow,slot⟩ := SourceFull25.validated_record_bytes pre row vr call
  have member : (row,vr.framed) ∈ ExtractedPrefixTrace.rowOrder.zip (PrefixAdapter.toOld pre).records.val := by
    apply List.mem_of_getElem? (i:=row.val)
    exact List.getElem?_zip_eq_some.mpr ⟨JFv_RowOrder.get row valid,slot⟩
  obtain ⟨payload,accepted⟩ := ExtractedPrefixParse.parse_record_of_success bytes
    (PrefixAdapter.toOld pre) hp row vr.framed member
  have canon := PSem_FieldCanonical.source_payload row vr.framed payload field accepted
  have framing := ExtractedRecordFraming.parse_record_success row vr.framed payload
    (ExtractedPrefixParserAgreement.parse_record_success row vr.framed payload accepted)
  rcases framing with ⟨tag,size,b1,b2,b3,b4,shape,length,h0,h1,h2,h3,h4,header,selected,payloadLength,validator⟩
  refine ⟨vr,call,sameRow,PSem_SourceRows.record_length row vr.framed payload accepted,?_⟩
  rw [selected] at canon
  exact canon

#print axioms fields
end AspisR1.JFv_FieldRecord
