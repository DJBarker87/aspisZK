import NKQ_StrictDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_RecordDomains
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open RawActualDecodeKMainAdapter ExtractedPrefixStrictPayload

def Ready (record : MainRecord) (N off : Usize) : Prop :=
 NGO_CallerDomains.Call record.row.val N.val off.val ∧
 record.framed.val.length=5+NFU_PacketDomains.payloadSize record.row.val ∧
 (∀ chunk∈(List.toChunksExact 32 (by decide) (record.framed.val.drop 5)).1,StrictLowChunk chunk)

/-- The SAME native parser/getter record supplies every byte, not an address
selected after execution. This constructor is independent of terminal256. -/
theorem entered (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (row : U8) (N off : Usize) (live : row.val<27) (fields : 14≤row.val)
 (call : NGO_CallerDomains.Call row.val N.val off.val) :
 ∃ record,r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) row=ok (.Ok record) ∧
 record.row=row ∧ Ready record N off := by
 let idx : Fin 27:=⟨row.val,live⟩
 let frame:=FJb_TailCell.cell pre.records idx
 have recordLength : pre.records.val.length=27:=pre.records.property
 have rowLength : ExtractedPrefixTrace.rowOrder.length=27:=rfl
 have pairMember : (row,frame)∈ExtractedPrefixTrace.rowOrder.zip pre.records.val := by
  have bound : row.val<(ExtractedPrefixTrace.rowOrder.zip pre.records.val).length := by
   simp only [List.length_zip,recordLength,rowLength];exact live
  have mem:=List.mem_of_getElem (List.getElem_zip (h:=bound))
  have selected : ExtractedPrefixTrace.rowOrder[row.val]'(by omega)=row := by
   apply UScalar.eq_of_val_eq
   have mapped : (ExtractedPrefixTrace.rowOrder.map UScalar.val)[row.val]'(by simp only [List.length_map,rowLength];exact live)=row.val := by
    simp only [ExtractedPrefixTypedFull.rowOrder_values,List.getElem_range]
   simpa only [List.getElem_map] using mapped
  simpa only [frame,FJb_TailCell.cell,selected] using mem
 obtain ⟨payload,recordParsed⟩:=ExtractedPrefixParse.parse_record_of_success bytes pre parsed row frame pairMember
 have strict:=NJT_QClaimsCanonical.strict_frame row frame payload fields recordParsed
 obtain ⟨record,getter,tag,same⟩:=NIX_ProducerInstall.lookup pre row live
 have geometry : record.framed.val.length=5+NFU_PacketDomains.payloadSize record.row.val := by
  rw [tag,same]
  exact NIX_PredecessorFrames.aggregate bytes pre parsed idx
 refine ⟨record,getter,tag,?_,geometry,?_⟩
 · rw [tag];exact call
 · simpa only [same,frame,idx] using strict

#print axioms entered
end AspisR1.NKQ_RecordDomains
end
