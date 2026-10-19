import RawActualDecodeKStrictChunkBridge

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualDecodeKTypedCoefficients
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter
open AspisR1PublicPreparation.RawActualDecodeKMainReadback
open AspisR1PublicPreparation.RawActualDecodeKMainStrictReadback
open AspisR1PublicPreparation.RawActualDecodeKPayloadBytes
open AspisR1PublicPreparation.RawActualDecodeKStrictChunkBridge
open AspisR1.ExtractedRecordByteValue
open AspisR1.ExtractedPrefixStrictPayload
open AspisR1.ExtractedPrefixSemanticLow
open AspisR1.SemanticCoefficientCodec
open AspisR1DecodeKFullValueTrace (ParserTrace)

def payload (r : MainRecord) : List U8 := r.framed.val.drop 5

/-- Successful actual decoding of the 28 source coefficients agrees with the
retained typed coefficient decoder on the same complete original payload.
Length and strictness are precisely the existing Prefix parse obligations;
no field-value or polynomial-correspondence premise is supplied. -/
theorem decodeMain_coefficients_same_typed_payload
    (r : MainRecord) (out : Array MainQM 28#usize)
    (h : decodeMain 28#usize r 0#usize = .ok (.Ok out))
    (hlen : (payload r).length = 896)
    (hstrict : ∀ j : Fin 28, StrictLowChunk (((payload r).drop (32*j.val)).take 32)) :
    ∃ typed : Coefficients,
      decodeCoefficients ((payload r).map rawByte) = some typed ∧
      ∀ j : Fin 28,
        AspisR1.ExtractedMaskQM31Exact.decode
          (mainToProbe (out.val[j.val]'(by simpa [out.property] using j.isLt))) =
            (typed j).val.re := by
  obtain ⟨byteOffset,hOffset,hvalues⟩ := decodeMain_success_indexed_parser
    28#usize r 0#usize out h
  have hzero : byteOffset = 0#usize := by
    have hz : Usize.checked_mul 0#usize 32#usize = some (0#usize) := by
      have hm := UScalar.mul_equiv (0#usize) (32#usize)
      cases hr : UScalar.mul (0#usize) (32#usize) with
      | ok z =>
        rw [hr] at hm
        have hz0 : z = 0#usize := by
          apply UScalar.eq_of_val_eq
          simpa using hm.2.1
        simp [Usize.checked_mul,core.num.checked_mul_UScalar,hr,hz0,Option.ofResult]
      | fail e =>
        rw [hr] at hm
        simp at hm
      | div =>
        rw [hr] at hm
        exact False.elim hm
    rw [hz] at hOffset
    change Result.ok (some (0#usize)) = Result.ok (some byteOffset) at hOffset
    exact (Option.some.inj (Result.ok.inj hOffset)).symm
  have hslot : ∀ j : Fin 28, ∃ x : LowWide,
      decodeLow ((((payload r).drop (32*j.val)).take 32).map rawByte) = some x ∧
      AspisR1.ExtractedMaskQM31Exact.decode
        (mainToProbe (out.val[j.val]'(by simpa [out.property] using j.isLt))) = x.val.re := by
    intro j
    obtain ⟨q,_hcall,hcell,⟨trace⟩,_hcanonical⟩ := hvalues j
    have hstart : (ParserTrace.payloadStart trace).val = 32*j.val := by
      have hs := payloadStart_eq trace
      simpa [hzero,Nat.mul_comm] using hs
    have hraw :
        (((ParserTrace.payloadData trace).val.drop (ParserTrace.payloadStart trace).val).take 32) =
          (((payload r).drop (32*j.val)).take 32) := by
      rw [payloadData_eq_drop trace,hstart]
      rfl
    have hstrictActual : StrictLowChunk
        (((ParserTrace.payloadData trace).val.drop (ParserTrace.payloadStart trace).val).take 32) := by
      rw [hraw]
      exact hstrict j
    obtain ⟨limbs,hdecode,_hq,hfield,_hencode⟩ :=
      trace_strict_chunk_decodes_same_value trace hstrictActual
    refine ⟨lowValue limbs,?_,?_⟩
    · simpa only [hraw] using hdecode
    · rw [hcell]
      exact hfield
  classical
  choose typed hd hf using hslot
  refine ⟨typed,?_,hf⟩
  apply (decodeCoefficients_eq_some_iff _ _).2
  refine ⟨by simpa only [List.length_map] using hlen,?_⟩
  intro j
  simpa only [List.map_drop,List.map_take] using hd j

#print axioms decodeMain_coefficients_same_typed_payload
end AspisR1PublicPreparation.RawActualDecodeKTypedCoefficients
end
