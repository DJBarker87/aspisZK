import ActualDecodeKStrictQM31Parser
import RawActualDecodeKMainReadback

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawActualDecodeKMainStrictReadback
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter
open AspisR1.ActualDecodeKStrictQM31Parser
open AspisR1.RetainedFieldByteCodec

abbrev Trace := AspisR1DecodeKFullValueTrace.ParserTrace

def inputArray {r : DecodeRecord} {byteOffset value offset : Usize} {q : DecodeQM}
    (trace : Trace r byteOffset value offset q) : Array U8 16#usize :=
  Array.make 16#usize [(AspisR1DecodeKFullValueTrace.ParserTrace.b0 trace),(AspisR1DecodeKFullValueTrace.ParserTrace.b1 trace),(AspisR1DecodeKFullValueTrace.ParserTrace.b2 trace),(AspisR1DecodeKFullValueTrace.ParserTrace.b3 trace),
    (AspisR1DecodeKFullValueTrace.ParserTrace.b4 trace),(AspisR1DecodeKFullValueTrace.ParserTrace.b5 trace),(AspisR1DecodeKFullValueTrace.ParserTrace.b6 trace),(AspisR1DecodeKFullValueTrace.ParserTrace.b7 trace),(AspisR1DecodeKFullValueTrace.ParserTrace.b8 trace),(AspisR1DecodeKFullValueTrace.ParserTrace.b9 trace),(AspisR1DecodeKFullValueTrace.ParserTrace.b10 trace),
    (AspisR1DecodeKFullValueTrace.ParserTrace.b11 trace),(AspisR1DecodeKFullValueTrace.ParserTrace.b12 trace),(AspisR1DecodeKFullValueTrace.ParserTrace.b13 trace),(AspisR1DecodeKFullValueTrace.ParserTrace.b14 trace),(AspisR1DecodeKFullValueTrace.ParserTrace.b15 trace)]

theorem trace_input_eq {r : DecodeRecord} {byteOffset value offset : Usize} {q : DecodeQM}
    (trace : Trace r byteOffset value offset q) :
    (AspisR1DecodeKFullValueTrace.ParserTrace.inputBytes trace) = Array.to_slice (inputArray trace) := by
  have h := (AspisR1DecodeKFullValueTrace.ParserTrace.hinput trace)
  change Result.ok (Array.to_slice (inputArray trace)) = Result.ok (AspisR1DecodeKFullValueTrace.ParserTrace.inputBytes trace) at h
  exact (Result.ok.inj h).symm

/-- The sixteen bytes read by the actual generated decoder determine its
canonical retained field limbs and are recovered by the retained encoder. -/
theorem trace_strict_limbs {r : DecodeRecord} {byteOffset value offset : Usize} {q : DecodeQM}
    (trace : Trace r byteOffset value offset q) :
    ∃ limbs : QM31Limbs,
      decodeQM31LE (AspisR1.CandidateParserByteOrder.arrayBytes16 (inputArray trace)) = some limbs ∧
      q = limbsToActual limbs ∧
      encodeQM31LE limbs = AspisR1.CandidateParserByteOrder.arrayBytes16 (inputArray trace) := by
  have hp := (AspisR1DecodeKFullValueTrace.ParserTrace.hparse trace)
  rw [trace_input_eq trace] at hp
  exact success_has_strict_limbs (inputArray trace) q hp

/-- Every Main coefficient is the retained canonical decode of the actual
byte reads on that same input record. No coefficient/limb identity premise
is supplied by the caller. -/
theorem decodeMain_success_strict_readback
    (n : Usize) (r : MainRecord) (offset : Usize) (out : Array MainQM n)
    (h : decodeMain n r offset = .ok (.Ok out)) :
    ∃ byteOffset : Usize,
      lift (Usize.checked_mul offset 32#usize) = .ok (some byteOffset) ∧
      ∀ j : Fin n, ∃ q : DecodeQM,
        ∃ trace : Trace (recordToDecoder r) byteOffset
          (UScalar.ofNatCore j.val (by have := j.isLt; scalar_tac)) offset q,
        ∃ limbs : QM31Limbs,
          AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value
            (recordToDecoder r) byteOffset
            (UScalar.ofNatCore j.val (by have := j.isLt; scalar_tac)) offset = .ok (.Ok q) ∧
          out.val[j.val]'(by simpa [out.property] using j.isLt) =
            decoderQMToMain (limbsToActual limbs) ∧
          decodeQM31LE (AspisR1.CandidateParserByteOrder.arrayBytes16 (inputArray trace)) = some limbs ∧
          encodeQM31LE limbs = AspisR1.CandidateParserByteOrder.arrayBytes16 (inputArray trace) := by
  obtain ⟨byteOffset,hOffset,hvalues⟩ :=
    AspisR1PublicPreparation.RawActualDecodeKMainReadback.decodeMain_success_indexed_parser
      n r offset out h
  refine ⟨byteOffset,hOffset,?_⟩
  intro j
  obtain ⟨q,hcall,hcell,⟨trace⟩,_⟩ := hvalues j
  obtain ⟨limbs,hdecode,hq,hencode⟩ := trace_strict_limbs trace
  refine ⟨q,trace,limbs,hcall,?_,hdecode,hencode⟩
  exact hcell.trans (congrArg decoderQMToMain hq)

#print axioms trace_input_eq
#print axioms trace_strict_limbs
#print axioms decodeMain_success_strict_readback
end AspisR1PublicPreparation.RawActualDecodeKMainStrictReadback
