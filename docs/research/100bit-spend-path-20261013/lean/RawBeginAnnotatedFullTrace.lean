import RawActualViewSourceChallenges
import ExtractedSourceFull25Typed

/-! Join actual begin to the very same annotated arithmetic rounds, retaining
one complete source call log and the semantic view's own strict decoding. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawBeginAnnotatedFullTrace
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun

 theorem semantic_run_append {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) {rows rows' : List U8}
    {before mid after : r1_wire.SemanticTranscript H}
    {qs qs' : List aspis_core.field.QM31}
    (left : BeginCalls.SemanticRun D pre rows before mid qs)
    (right : BeginCalls.SemanticRun D pre rows' mid after qs') :
    BeginCalls.SemanticRun D pre (rows ++ rows') before after (qs ++ qs') := by
  induction left with
  | nil => exact right
  | cons hr hs tail ih => exact .cons hr hs (ih right)

 theorem begin_annotated_full_trace {H : Type} (D : aspis_core.Digest32 H)
    (bytes : Slice U8) (pre : r1_wire.Prefix)
    (hparse : PrefixAdapter.parseAccepted bytes = .ok (.Ok pre))
    (beforeBegin before : r1_wire.SemanticTranscript H)
    (challenges : r1_wire.Challenges)
    (hbegin : r1_wire.begin D pre beforeBegin = .ok (.Ok challenges, before))
    (initial : MainQM) (initialAlpha : Array MainQM 10#usize)
    (final : Outcome H) (entries : List (RoundEvidence D pre))
    (run : AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule
      (initial, initialAlpha, before) final entries)
    (values : AspisR1.SemanticPrefixCodec.Full)
    (hfull : AspisR1.SemanticPrefixCodec.encodeFull values =
      PrefixAdapter.completedRecords pre) :
    ∃ cs : List (SourceFull25.Call D pre),
      SourceFull25.Trace D pre beforeBegin final.2.2 cs ∧
      (cs.map (fun c => c.row.val)) = List.range 25 ∧
      cs.map SourceFull25.Call.q =
        BeginCalls.challengeList challenges ++ entries.map RoundEvidence.q ∧
      SourceFull25.rawFrames cs = PrefixAdapter.completedRecords pre ∧
      AspisR1.SemanticPrefixCodec.decodeFrom 0 (SourceFull25.rawFrames cs) =
        some (AspisR1.SemanticPrefixCodec.entriesOf values) ∧
      (∀ c ∈ cs, (SourceDigestAddresses.rawBytes c.record.framed).length ≤ 901) := by
  obtain ⟨qs, hbeginRun, hbeginQs⟩ :=
    BeginCalls.begin_success D pre beforeBegin before challenges hbegin
  have hroundRun := RawAnnotatedSourceTrace.annotated_semantic_run D pre
    SemanticRoundsCheckedTrace.schedule (initial, initialAlpha, before) final entries run
  have hrun := semantic_run_append D pre hbeginRun hroundRun
  have hrows : (BeginCalls.rows ++ SemanticRoundsCheckedTrace.schedule.map Prod.snd).map
      (fun row => row.val) = List.range 25 := by rfl
  obtain ⟨cs, htrace, hcallrows, hqs, hframes⟩ :=
    SourceFull25.run_full25_frames D pre hrun hrows
  have hb : SourceFull25.rawFrames cs = PrefixAdapter.completedRecords pre := by
    simpa only [SourceFull25.rawFrames, PrefixAdapter.completedRecords,
      List.map_map, Function.comp_def] using
      congrArg (List.map (fun frame : Slice U8 =>
        frame.val.map AspisR1.ExtractedRecordByteValue.rawByte)) hframes
  refine ⟨cs, htrace, ?_, ?_, hb, ?_, ?_⟩
  · simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun row : U8 => row.val)) hcallrows).trans hrows
  · exact hqs.trans (congrArg (fun qs0 => qs0 ++ entries.map RoundEvidence.q) hbeginQs)
  · rw [hb, ← hfull]
    exact AspisR1.SemanticPrefixCodec.decode_encodeFull values
  · intro c hc
    apply PrefixAdapter.parsed_record_bound bytes pre hparse
    rw [← hb]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩

#print axioms semantic_run_append
#print axioms begin_annotated_full_trace
end AspisR1PublicPreparation.RawBeginAnnotatedFullTrace
end
