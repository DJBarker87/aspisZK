import NJT_QClaimsLow
import NIX_ProducerInstall
import ExtractedPrefixTypedFull
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_QClaimsCanonical
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter
open ExtractedPrefixStrictPayload

/-- A successful field-bearing record parser validates every actual payload
chunk, and identifies that payload with the SAME frame after its5-byte header. -/
theorem strict_frame (row : U8) (frame payload : Slice U8)
 (live : 14≤row.val)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.parse_record row frame=ok (.Ok payload)) :
 ∀ chunk∈(List.toChunksExact 32 (by decide) (frame.val.drop 5)).1,StrictLowChunk chunk := by
 obtain ⟨_,_,strict⟩:=ExtractedPrefixStrictPayload.parse_record_strict_payload row frame payload live parsed
 have old:=ExtractedPrefixParserAgreement.parse_record_success row frame payload parsed
 obtain ⟨tag,size,b1,b2,b3,b4,shape,length,h0,h1,h2,h3,h4,declared,drop,plen,validate⟩:=
  ExtractedRecordFraming.parse_record_success row frame payload old
 simpa only [drop,Slice.drop] using strict

/-- Complete29-value decoder success follows from predecessor byte validity;
all first-error, failure and divergence cases are excluded, not assumed away. -/
theorem decode (record : MainRecord) (p off : Usize)
 (row : record.row.val=25) (live : p.val<3) (offset : off.val=p.val*29)
 (framed : record.framed.val.length=3717)
 (strict : ∀ chunk∈(List.toChunksExact 32 (by decide) (record.framed.val.drop 5)).1,StrictLowChunk chunk) :
 ∃ out,decodeMain 29#usize record off=ok (.Ok out) := by
 have call : NGO_CallerDomains.Call record.row.val (29#usize).val off.val := by
  rw [row,offset]
  exact NGO_CallerDomains.Call.claims p.val live
 have geometry : record.framed.val.length=5+NFU_PacketDomains.payloadSize record.row.val := by
  rw [row]
  exact framed
 obtain ⟨start,d,window,ce,final,same,chunks,native,run,halt,bound,terminal,rest⟩:=
  NGO_DecodeComposed.result 29#usize off record call geometry
 rcases terminal with ⟨finished,_⟩ | ⟨index,active,error,_,failed,reply⟩
 · refine ⟨decoderArrayToMain final.1,?_⟩
   simpa only [finished,decoderResultToMain] using run
 · obtain ⟨q,good⟩:=NJT_QClaimsLow.answer d strict index active
   rw [good] at reply
   cases reply

/-- The actual aggregate parser supplies the row25 token and every one of its
three successful decodes. No decoded-row or canonicality premise is added. -/
theorem claims (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre)) :
 ∃ record,r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) 25#u8=ok (.Ok record) ∧
 record.row=25#u8 ∧
 ∀ (p off : Usize),p.val<3 → off.val=p.val*29 → ∃ out,decodeMain 29#usize record off=ok (.Ok out) := by
 let idx : Fin 27:=⟨25,by decide⟩
 let frame:=FJb_TailCell.cell pre.records idx
 have recordLength : pre.records.val.length=27:=pre.records.property
 have rowLength : ExtractedPrefixTrace.rowOrder.length=27:=rfl
 have pairMember : (25#u8,frame)∈ExtractedPrefixTrace.rowOrder.zip pre.records.val := by
  have bound : 25<(ExtractedPrefixTrace.rowOrder.zip pre.records.val).length := by
   simp only [List.length_zip,recordLength,rowLength]
   decide
  have mem:=List.mem_of_getElem (List.getElem_zip (h:=bound))
  simpa only [frame,FJb_TailCell.cell,show ExtractedPrefixTrace.rowOrder[25]'(by omega)=25#u8 by rfl] using mem
 obtain ⟨payload,recordParsed⟩:=ExtractedPrefixParse.parse_record_of_success bytes pre parsed 25#u8 frame pairMember
 have strict:=strict_frame 25#u8 frame payload (by decide) recordParsed
 obtain ⟨record,getter,tag,same⟩:=NIX_ProducerInstall.lookup pre 25#u8 (by decide)
 have equalFrame : record.framed=frame:=same
 have framed : record.framed.val.length=3717 := by
  rw [same]
  exact NIX_PredecessorFrames.aggregate bytes pre parsed idx
 refine ⟨record,getter,tag,?_⟩
 intro p off live offset
 apply decode record p off (congrArg UScalar.val tag) live offset framed
 simpa only [equalFrame] using strict

#print axioms strict_frame
#print axioms decode
#print axioms claims
#check @claims
end AspisR1.NJT_QClaimsCanonical
end
