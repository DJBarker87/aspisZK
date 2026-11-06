import NGO_CanonicalPort
import ExtractedPrefixStrictPayload
import ExtractedPrefixChunkOrder
import RPu_FIq_S_RawActualDecodeKStrictChunkBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_QClaimsLow
open Aeneas Aeneas.Std Result
open ExtractedPrefixStrictPayload RetainedFieldByteCodec StrictWideByteCodec
open ExtractedRecordByteValue
open AspisR1PublicPreparation.RawActualDecodeKStrictChunkBridge

/-- Strict Prefix chunks imply successful decoding of their actual low16
bytes. No successful decoder output is a hypothesis. -/
theorem low (raw : List U8) (arr : Array U8 16#usize)
 (strict : StrictLowChunk raw) (same : arr.val=raw.take 16) :
 ∃ limbs,decodeQM31LE (CandidateParserByteOrder.arrayBytes16 arr)=some limbs := by
 obtain ⟨bytes,hbytes,lo,hdecode,hencode⟩:=strict
 have input : CandidateParserByteOrder.arrayBytes16 arr=lowBytes bytes := by
  apply List.ofFn_injective
  rw [arrayBytes16_list,lowBytes_list,hbytes,same,List.map_take]
 obtain ⟨hlow,_⟩:=successful_halves bytes _ hdecode
 exact ⟨lo,input ▸ hlow⟩

/-- Every requested value in a framed strict payload has an Ok answer in the
CLOSED decoder's own exact natural-byte model. -/
theorem answer {N : Usize} {r : NGD_DecodeTrace.Record} {off start : Usize}
 (d : NGD_DecodeTrace.Domain N r off start)
 (strict : ∀ chunk∈(List.toChunksExact 32 (by decide) (r.framed.val.drop 5)).1,StrictLowChunk chunk)
 (i : Usize) (live : i.val<N.val) :
 ∃ q,NGD_DecodeTrace.answer d i live=.Ok q := by
 let raw:=((r.framed.val.drop 5).drop (32*(off.val+i.val))).take 32
 have bound : 32*(off.val+i.val+1)≤(r.framed.val.drop 5).length := by
  have range:=d.range
  simp only [List.length_drop]
  omega
 have hs : StrictLowChunk raw:=strict raw (ExtractedPrefixChunkOrder.slice_mem 32 (by decide) _ (off.val+i.val) bound)
 let arr:=NGD_DecodeValueLaw.input r off N i d.minlen d.cap d.positive live d.range
 have same : arr.val=raw.take 16 := by
  simp only [arr,NGD_DecodeValueLaw.input,raw,List.take_take]
  rfl
 obtain ⟨limbs,parsed⟩:=low raw arr hs same
 refine ⟨ActualDecodeKStrictQM31Parser.limbsToActual limbs,?_⟩
 simp only [NGD_DecodeTrace.answer,NGD_DecodeValueLaw.expected,←show arr=NGD_DecodeValueLaw.input r off N i d.minlen d.cap d.positive live d.range from rfl,parsed,Option.map_some]

#print axioms low
#print axioms answer
end AspisR1.NJT_QClaimsLow
end
