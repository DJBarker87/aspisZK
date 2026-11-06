import NKQ_DecodeCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_StrictDecode
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open RawActualDecodeKMainAdapter ExtractedPrefixStrictPayload

/-- All CLOSED147 call shapes, including extra87 and before_z1. The native
one-step/error/frame packet is reused; strict predecessor bytes exclude its
first-error alternative rather than assuming a decoded reply. -/
theorem total (N off : Usize) (record : MainRecord)
 (call : NGO_CallerDomains.Call record.row.val N.val off.val)
 (geometry : record.framed.val.length=5+NFU_PacketDomains.payloadSize record.row.val)
 (strict : ∀ chunk∈(List.toChunksExact 32 (by decide) (record.framed.val.drop 5)).1,StrictLowChunk chunk) :
 ∃ out,decodeMain N record off=ok (.Ok out) ∧ NKQ_DecodeCanonical.MainRowCanon out := by
 obtain ⟨start,d,window,ce,final,same,chunks,native,run,halt,bound,terminal,rest⟩:=
  NGO_DecodeComposed.result N off record call geometry
 rcases terminal with ⟨finished,_⟩ | ⟨index,active,error,_,failed,reply⟩
 · have decoded : decodeMain N record off=ok (.Ok (decoderArrayToMain final.1)) := by
    simpa only [finished,decoderResultToMain] using run
   exact ⟨_,decoded,NKQ_DecodeCanonical.main record off _ decoded⟩
 · obtain ⟨q,good⟩:=NJT_QClaimsLow.answer d strict index active
   rw [good] at reply
   cases reply
#print axioms total
end AspisR1.NKQ_StrictDecode
end
