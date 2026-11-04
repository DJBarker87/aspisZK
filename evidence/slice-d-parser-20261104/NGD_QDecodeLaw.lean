import ActualDecodeKStrictQM31Parser
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_QDecodeLaw
/-- Exact emitted result on every sixteen-byte input, including noncanonical
rejection; no caller canonicality or successful decoder hypothesis. -/
theorem stub_law (bytes : Array U8 16#usize) :
    AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice bytes) =
      ok ((AspisR1.RetainedFieldByteCodec.decodeQM31LE
        (AspisR1.CandidateParserByteOrder.arrayBytes16 bytes)).map
          AspisR1.ActualDecodeKStrictQM31Parser.limbsToActual) :=
  AspisR1.ActualDecodeKStrictQM31Parser.source_refines bytes
#print axioms stub_law
end NGD_QDecodeLaw
