import PreparedParsedInactiveV1
import R1SourceWideExactCodec
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PreparedInactiveCodecV1
open AspisR1PreparedParsedInactiveV1 AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim.Concrete

theorem parser_carrier_decode_same (value : ParserWide) :
    decode (toClaimE (fromParser value))=
      AspisR1.SourceWideExactCodec.candidateWideToExact value := rfl

/-- The same successful byte parse has the exact tower interpretation used
by current claim arithmetic, reusing the existing strict codec theorem. -/
theorem parsed_inactive_decodes (bytes : Array U8 32#usize) (value : PE)
    (h : parseInactive (Array.to_slice bytes)=ok (some value)) :
    AspisR1.FoldedLeafCodec.decodeWide
      (List.ofFn (AspisR1.WideParserArrayHalves.arrayBytes32 bytes))=
        some (decode (toClaimE value)) := by
  unfold parseInactive at h
  cases hp : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
      (Array.to_slice bytes) with
  | fail e => simp only [hp,bind_tc_fail] at h; cases h
  | div => simp only [hp,bind_tc_div] at h; cases h
  | ok out =>
    simp only [hp,bind_tc_ok] at h
    cases out with
    | none => cases h
    | some x =>
      have hv : fromParser x=value := Option.some.inj (Result.ok.inj h)
      rw [← hv,parser_carrier_decode_same]
      exact AspisR1.SourceWideExactCodec.successful_parse_decodes bytes x hp

#print axioms parser_carrier_decode_same
#print axioms parsed_inactive_decodes
end AspisR1PreparedInactiveCodecV1
