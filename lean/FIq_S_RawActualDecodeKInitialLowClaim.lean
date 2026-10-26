import ExtractedMaskHornerStep
import FIq_S_RawActualDecodeKTypedCoefficients
import FIq_S_StrictLowChunkFromTypedDecode
import FIq_S_RawSemanticTypedPolynomialLift

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualDecodeKInitialLowClaim
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter
open AspisR1PublicPreparation.RawActualDecodeKMainReadback
open AspisR1PublicPreparation.RawActualDecodeKMainStrictReadback
open AspisR1PublicPreparation.RawActualDecodeKPayloadBytes
open AspisR1PublicPreparation.RawActualDecodeKStrictChunkBridge
open AspisR1PublicPreparation.RawActualDecodeKTypedCoefficients
open AspisR1.ExtractedRecordByteValue
open AspisR1.SemanticCoefficientCodec
open AspisR1DecodeKFullValueTrace (ParserTrace)

theorem checked_mul_zero_32 : Usize.checked_mul 0#usize 32#usize = some 0#usize := by
  have hm := UScalar.mul_equiv (0#usize) (32#usize)
  cases hr : UScalar.mul (0#usize) (32#usize) with
  | ok z =>
    rw [hr] at hm
    have hz : z = 0#usize := by
      apply UScalar.eq_of_val_eq
      simpa using hm.2.1
    simp [Usize.checked_mul, core.num.checked_mul_UScalar, hr, hz, Option.ofResult]
  | fail e => rw [hr] at hm; simp at hm
  | div => rw [hr] at hm; exact False.elim hm

/-- The actual row-14 decoder and retained typed low-value decoder agree on
the same complete payload. Strictness and payload length are derived from
typed decoding, not separately assumed. -/
theorem decodeMain_one_same_low_value
    (record : MainRecord) (out : Array MainQM 1#usize) (value : LowWide)
    (hactual : decodeMain 1#usize record 0#usize = .ok (.Ok out))
    (htyped : decodeLow ((payload record).map rawByte) = some value) :
    AspisR1.ExtractedMaskQM31Exact.decode
      (mainToProbe (out.val[0]'(by simpa [out.property]))) = value.val.re := by
  obtain ⟨byteOffset, hoffset, hvalues⟩ :=
    decodeMain_success_indexed_parser 1#usize record 0#usize out hactual
  have hzero : byteOffset = 0#usize := by
    rw [checked_mul_zero_32] at hoffset
    change Result.ok (some 0#usize) = Result.ok (some byteOffset) at hoffset
    exact (Option.some.inj (Result.ok.inj hoffset)).symm
  obtain ⟨q, _hcall, hcell, ⟨trace⟩, _hcanonical⟩ := hvalues (0 : Fin 1)
  have hstart : (ParserTrace.payloadStart trace).val = 0 := by
    have hs := payloadStart_eq trace
    simpa [hzero] using hs
  have hlen : (payload record).length = 32 := by
    have he := encodeLow_of_decode _ value htyped
    have hl := congrArg List.length he
    simpa only [encodeLow_length, List.length_map] using hl.symm
  have hraw :
      (((ParserTrace.payloadData trace).val.drop (ParserTrace.payloadStart trace).val).take 32) =
        payload record := by
    rw [payloadData_eq_drop trace, hstart, List.drop_zero]
    exact List.take_of_length_le hlen.le
  have hstrict : AspisR1.ExtractedPrefixStrictPayload.StrictLowChunk
      (((ParserTrace.payloadData trace).val.drop (ParserTrace.payloadStart trace).val).take 32) := by
    rw [hraw]
    exact AspisR1.StrictLowChunkFromTypedDecode.strictLowChunk_of_decodeLow _ value htyped
  obtain ⟨limbs, hd, _hq, hf, _he⟩ := trace_strict_chunk_decodes_same_value trace hstrict
  have hd' : decodeLow ((payload record).map rawByte) =
      some (AspisR1.ExtractedPrefixSemanticLow.lowValue limbs) := by
    simpa only [hraw] using hd
  have hv : AspisR1.ExtractedPrefixSemanticLow.lowValue limbs = value :=
    Option.some.inj (hd'.symm.trans htyped)
  have hcell0 : out.val[0]'(by simpa [out.property]) = decoderQMToMain q := by
    simpa only [Fin.val_zero] using hcell
  exact (congrArg (fun x : MainQM =>
    AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe x)) hcell0).trans
      (hf.trans (congrArg (fun x : LowWide => x.val.re) hv))

theorem decodeMain_one_indexed_wide_value
    (record : MainRecord) (out : Array MainQM 1#usize) (initial : MainQM) (value : LowWide)
    (hactual : decodeMain 1#usize record 0#usize = .ok (.Ok out))
    (hindex : Array.index_usize out 0#usize = .ok initial)
    (htyped : decodeLow ((payload record).map rawByte) = some value) :
    algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact
      (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe initial)) = value.val := by
  have hb : 0 < out.val.length := by simpa [out.property]
  have hindex0 : Array.index_usize out 0#usize = .ok (out.val[0]'hb) := by
    exact AspisR1.ExtractedMaskHornerStep.array_index_usize_ok out 0#usize (by scalar_tac)
  have hi : initial = out.val[0]'hb := Result.ok.inj (hindex.symm.trans hindex0)
  have hf : AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe initial) = value.val.re :=
    (congrArg (fun x : MainQM =>
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe x)) hi).trans
        (decodeMain_one_same_low_value record out value hactual htyped)
  exact (congrArg
    (algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact) hf).trans
      (RawSemanticTypedPolynomialLift.lowWide_eq_embedding value)

#print axioms checked_mul_zero_32
#print axioms decodeMain_one_same_low_value
#print axioms decodeMain_one_indexed_wide_value
end AspisR1PublicPreparation.RawActualDecodeKInitialLowClaim
end
