import PSem_Canonical
import ExtractedPrefixStrictPayload
import ExtractedRecordStrictCodec
set_option autoImplicit false
namespace AspisR1.PSem_FieldCanonical
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft MultiproofConeCanonical
open ExtractedRecordByteCanonicality ExtractedRecordStrictCodec

theorem word_slice (arr : Array U8 32#usize) (j : Fin 8) :
    slice (bytesOf arr.val) (4*j.val) 4=List.ofFn (wordBytesAt arr j) := by
  have length : arr.val.length=32 := arr.property
  apply List.ext_getElem
  · simp only [slice,bytesOf,List.length_take,List.length_drop,List.length_map,List.length_ofFn,length]
    omega
  · intro i hi hj
    simp only [slice,bytesOf,List.getElem_take,List.getElem_map,List.getElem_drop,
      List.getElem_ofFn,wordBytesAt,byteAt]
    congr 2
    omega

theorem canonical_chunk (raw : List U8) (h : ExtractedRecordValidator.CanonicalChunk raw) :
    canonical (bytesOf raw) := by
  obtain ⟨arr,rfl,bounds,_⟩ := h
  have length : arr.val.length=32 := arr.property
  refine ⟨by simp only [bytesOf,List.length_map,length];decide,?_⟩
  intro j hj
  have bound : j<8 := by simpa only [List.mem_range,bytesOf,List.length_map,length] using hj
  rw [word_slice arr ⟨j,bound⟩,MultiproofConeEndian.little_four,decodeWord_at]
  exact bounds ⟨j,bound⟩

theorem canonical_flatten (chunks : List (List U8))
    (valid : ∀ c ∈ chunks,ExtractedRecordValidator.CanonicalChunk c) :
    canonical (bytesOf chunks.flatten) := by
  induction chunks with
  | nil => simp [bytesOf,canonical]
  | cons c cs ih =>
    have hc := canonical_chunk c (valid c (List.mem_cons_self ..))
    have tail := ih (fun x hx => valid x (List.mem_cons_of_mem _ hx))
    simp only [List.flatten_cons,MultiproofConeExpandModel.bytes_append]
    rw [MultiproofConeCanonicalAppend.canonical_append _ _ hc.1]
    exact ⟨hc,tail⟩

theorem source_payload (row : U8) (frame payload : Slice U8) (fieldRow : 14 ≤ row.val)
    (h : AspisR1PrefixAggregateParser.r1_wire.parse_record row frame=ok (.Ok payload)) :
    canonical (bytesOf payload.val) := by
  have actual := ExtractedPrefixParserAgreement.parse_record_success row frame payload h
  obtain ⟨_,cover,valid⟩ := ExtractedRecordPayloadSoundness.parse_record_full_payload row frame payload fieldRow actual
  rw [←cover]
  exact canonical_flatten _ valid

#print axioms word_slice
#print axioms canonical_chunk
#print axioms canonical_flatten
#print axioms source_payload
end AspisR1.PSem_FieldCanonical
