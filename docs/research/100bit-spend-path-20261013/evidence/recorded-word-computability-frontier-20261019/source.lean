import RawCutWordsFromView

set_option autoImplicit false
namespace AspisR1.RecordedWordsComputabilityProbe

/-- Probe that the fixed recorded-log word constructor has executable code.
No concrete received word or random tape is evaluated. -/
def recover (decoder : LiteralByteProtocol.Decoder)
    (run : RawCutProverCompiler.RunView) : CanonicalCutEnrichedTranscript.Words :=
  RawCutWordsFromView.buildWords decoder run

#print axioms recover
end AspisR1.RecordedWordsComputabilityProbe
