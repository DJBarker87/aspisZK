import FIr_PhysicalInitial
set_option autoImplicit false
namespace AspisR1.FJq_ParsedRows
open MultiproofConeCanonical OraclePortCompactDraft
/-- The actual physical parser supplies its own complete semantic row table. -/
theorem value (stored : Bytes) (tr : RawCutTranscriptRun.ErasedPrefix) (p : Parsed)
    (parsed : OraclePortStoredParserC4.parseReached stored tr=some p) :
    semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic := by
  have raw:=(OraclePortStoredParserC4.parsed _ _ _ parsed).1
  unfold parse at raw
  split at raw
  · cases raw
  · split at raw
    · cases raw
    · cases rows : semanticRows 27 0 (slice stored 48 6983) with
      | none=>rw [rows] at raw;cases raw
      | some entries=>
        rw [rows] at raw
        simp only [Option.bind_some,Option.pure_def,Option.some.injEq] at raw
        cases raw
        exact rows
#print axioms value
end AspisR1.FJq_ParsedRows
