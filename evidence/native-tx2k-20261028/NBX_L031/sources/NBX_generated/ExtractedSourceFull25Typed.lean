import ExtractedSourceFull25Frames
import ExtractedPrefixTypedFullCurrent
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SourceFull25
open r1_wire BeginCalls

def rawFrames {H : Type} {D : aspis_core.Digest32 H} {pre : Prefix}
    (cs : List (Call D pre)) : List AspisR1.SemanticRecordCodec.Bytes :=
  cs.map (fun c => c.record.framed.val.map AspisR1.ExtractedRecordByteValue.rawByte)

/-- No hbytes or decode premise: actual ordered calls plus actual strict parser
success supply byte identity, full typed decoding and the source message bound.
Actual verifier-tail reachability and selected oracle/context remain separate. -/
theorem run_typedFull {H : Type} (D : aspis_core.Digest32 H)
    (bytes : Slice U8) (pre : Prefix)
    (hparse : PrefixAdapter.parseAccepted bytes = ok (.Ok pre))
    {rows before after qs} (run : SemanticRun D pre rows before after qs)
    (hrows : rows.map (fun row => row.val) = List.range 25) :
    ∃ cs : List (Call D pre), ∃ values : AspisR1.SemanticPrefixCodec.Full,
      Trace D pre before after cs ∧ cs.map Call.row = rows ∧ cs.map Call.q = qs ∧
      rawFrames cs = PrefixAdapter.completedRecords pre ∧
      AspisR1.SemanticPrefixCodec.decodeFrom 0 (rawFrames cs) =
        some (AspisR1.SemanticPrefixCodec.entriesOf values) ∧
      (∀ c ∈ cs, (c.record.framed.val.map AspisR1.ExtractedRecordByteValue.rawByte).length ≤ 901) := by
  obtain ⟨cs, ht, hr, hq, hf⟩ := run_full25_frames D pre run hrows
  have hb : rawFrames cs = PrefixAdapter.completedRecords pre := by
    simpa only [rawFrames, PrefixAdapter.completedRecords, List.map_map, Function.comp_def]
      using congrArg (List.map (fun frame : Slice U8 =>
        frame.val.map AspisR1.ExtractedRecordByteValue.rawByte)) hf
  obtain ⟨values, _, _, hd⟩ := PrefixAdapter.parse_typedFull bytes pre hparse
  refine ⟨cs, values, ht, hr, hq, hb, ?_, ?_⟩
  · rw [hb]; exact hd
  · intro c hc
    apply PrefixAdapter.parsed_record_bound bytes pre hparse
    rw [← hb]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩

#print axioms run_typedFull
end AspisR1PublicPreparation.SourceFull25
