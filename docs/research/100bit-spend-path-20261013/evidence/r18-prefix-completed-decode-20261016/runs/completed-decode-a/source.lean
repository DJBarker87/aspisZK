import ExtractedPrefixTypedFull

/-! Supply the exact completed-record decoding premise from actual Prefix
success and explicit byte equality. Message projection is a parameter; the
source-side bytes remain the fixed first25/rawByte map. -/
set_option autoImplicit false
namespace AspisR1.ExtractedPrefixCompletedDecode
open Aeneas Aeneas.Std Result
open FS2.Duplex SemanticPrefixCodec ExtractedPrefixTypedFull

/-- With M = SelectedTranscriptParams.Message and messageBytes = Subtype.val,
the first conclusion is the unchanged completed_read_of_decode hypothesis.
This theorem does not establish hbytes, any record states, or challenges. -/
theorem completed_decode {M : Type} (messageBytes : M → Bytes)
    (bytes : Slice U8) (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix)
    (hparse : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes =
      ok (core.result.Result.Ok parsed))
    (rs : List (Rec M))
    (hbytes : rs.map (fun r => messageBytes r.2.2.1) = completedRecords parsed) :
    ∃ values : Full,
      decodeFrom 0 (rs.map (fun r => messageBytes r.2.2.1)) = some (entriesOf values) ∧
      decodeFull (rs.map (fun r => messageBytes r.2.2.1)) = some values ∧
      encodeFull values = rs.map (fun r => messageBytes r.2.2.1) := by
  obtain ⟨values, hfull, hencode, hdecode⟩ := parse_decodeFull bytes parsed hparse
  exact ⟨values, by simpa only [hbytes] using hdecode,
    by simpa only [hbytes] using hfull, by simpa only [hbytes] using hencode⟩

#print axioms completed_decode
end AspisR1.ExtractedPrefixCompletedDecode
