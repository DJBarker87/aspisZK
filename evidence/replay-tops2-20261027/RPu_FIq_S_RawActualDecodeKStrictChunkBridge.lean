import RPu_FIq_S_RawActualDecodeKPayloadBytes
import RPu_FIq_S_RawActualDecodeKRetainedFieldInterpretation
import StrictLowChunkCodec

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawActualDecodeKStrictChunkBridge
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter
open AspisR1PublicPreparation.RawActualDecodeKMainStrictReadback
open AspisR1PublicPreparation.RawActualDecodeKPayloadBytes
open AspisR1PublicPreparation.RawActualDecodeKRetainedFieldInterpretation
open AspisR1.ActualDecodeKStrictQM31Parser
open AspisR1.RetainedFieldByteCodec
open AspisR1.StrictWideByteCodec
open AspisR1.ExtractedRecordByteValue
open AspisR1.ExtractedPrefixStrictPayload
open AspisR1.ExtractedPrefixSemanticLow
open AspisR1.SemanticCoefficientCodec
open AspisR1DecodeKFullValueTrace (ParserTrace)

theorem arrayBytes16_list (arr : Array U8 16#usize) :
    List.ofFn (AspisR1.CandidateParserByteOrder.arrayBytes16 arr) = arr.val.map rawByte := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map]
    exact arr.property.symm
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_map,
      AspisR1.CandidateParserByteOrder.arrayBytes16]
    rfl

theorem lowBytes_list (bytes : WideBytes) :
    List.ofFn (lowBytes bytes) = (List.ofFn bytes).take 16 := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_take]
    decide
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_take,lowBytes]
    apply congrArg bytes
    exact Fin.ext rfl

/-- The actual decoder's low-half value and the retained semantic low-wide
value agree on the very same original 32-byte payload chunk. The only strict
parse input is the existing Prefix strict-chunk predicate. -/
theorem trace_strict_chunk_decodes_same_value
    {r : DecodeRecord} {byteOffset value offset : Usize} {q : DecodeQM}
    (trace : Trace r byteOffset value offset q)
    (hstrict : StrictLowChunk
      (((ParserTrace.payloadData trace).val.drop (ParserTrace.payloadStart trace).val).take 32)) :
    ∃ limbs : QM31Limbs,
      decodeLow ((((ParserTrace.payloadData trace).val.drop
        (ParserTrace.payloadStart trace).val).take 32).map rawByte) = some (lowValue limbs) ∧
      q = limbsToActual limbs ∧
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe (decoderQMToMain q)) =
        (lowValue limbs).val.re ∧
      encodeLow (lowValue limbs) =
        (((ParserTrace.payloadData trace).val.drop (ParserTrace.payloadStart trace).val).take 32).map rawByte := by
  let raw := ((ParserTrace.payloadData trace).val.drop (ParserTrace.payloadStart trace).val).take 32
  obtain ⟨limbs,hdecode,hencode⟩ := strict_chunk_decodeLow raw hstrict
  let bytes : WideBytes := encodeWideLE (limbs,fun _ => AspisR1.ExtractedRecordStrictLow.zeroLimb)
  have hbytes : List.ofFn bytes = raw.map rawByte := by
    change List.ofFn (encodeWideLE
      (AspisR1.WideExactLimbCodec.pairExactEquiv.symm
        (AspisR1.WideExactLimbCodec.pairExactEquiv
          (limbs,fun _ => AspisR1.ExtractedRecordStrictLow.zeroLimb)))) = _ at hencode
    rw [Equiv.symm_apply_apply] at hencode
    exact hencode
  have hinput : AspisR1.CandidateParserByteOrder.arrayBytes16 (inputArray trace) = lowBytes bytes := by
    apply List.ofFn_injective
    rw [arrayBytes16_list,lowBytes_list,hbytes,inputArray_payload_slice]
    simp only [raw,List.map_take,List.take_take]
    rfl
  have hlow : lowBytes bytes = encodeQM31LE limbs := by
    funext i
    exact Fin.append_left _ _ _
  have hp := ParserTrace.hparse trace
  rw [trace_input_eq trace,source_refines,hinput,hlow,decodeQM31LE_encodeQM31LE] at hp
  have hq : limbsToActual limbs = q := by simpa only [Option.map_some,Result.ok.injEq,Option.some.injEq] using hp
  refine ⟨limbs,hdecode,hq.symm,?_,hencode⟩
  rw [← hq]
  exact limbsToActual_field limbs

#print axioms arrayBytes16_list
#print axioms lowBytes_list
#print axioms trace_strict_chunk_decodes_same_value
end AspisR1PublicPreparation.RawActualDecodeKStrictChunkBridge
