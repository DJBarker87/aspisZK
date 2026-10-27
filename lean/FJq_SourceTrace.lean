import PSem_SemanticTrace
import FIq_TypedData
import FJq_ChallengeSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_SourceTrace
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open RawActualAnnotatedPolynomialRun
/-- The actual begin and annotated arithmetic rounds supply ONE full source
trace and its ordered values. No independent successful transcript is assumed. -/
theorem value {H : Type} (D : aspis_core.Digest32 H)
    (bytes : Slice U8) (pre : r1_wire.Prefix)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre))
    (t0 t15 : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges)
    (begin : r1_wire.begin D pre t0=ok (.Ok c,t15))
    (initial : MainQM) (initialAlpha : Array MainQM 10#usize)
    (final : Outcome H) (entries : List (RoundEvidence D pre))
    (rounds : AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule
      (initial,initialAlpha,t15) final entries)
    (values : SemanticPrefixCodec.Full)
    (full : SemanticPrefixCodec.encodeFull values=PrefixAdapter.completedRecords pre)
    (alpha : Array MainQM 10#usize) (same : entries.map RoundEvidence.q=alpha.val) :
    ∃ cs : List (SourceFull25.Call D pre),
      SourceFull25.Trace D pre t0 final.2.2 cs ∧ cs.length=25 ∧
      cs.map SourceFull25.Call.q=BeginCalls.challengeList c++alpha.val ∧
      SourceFull25.rawFrames cs=PrefixAdapter.completedRecords pre := by
  obtain ⟨qs,beginRun,beginQs⟩:=BeginCalls.begin_success D pre t0 t15 c begin
  have roundRun:=RawActualAnnotatedChallengeSequence.annotatedRun_semantic D pre _ _ _ entries rounds
  have total:=PSem_SemanticTrace.semantic_append D pre beginRun roundRun
  have schedule : (BeginCalls.rows++SemanticRoundsCheckedTrace.schedule.map Prod.snd).map UScalar.val=List.range 25 := rfl
  obtain ⟨cs,trace,rows,qsSame,frames⟩:=SourceFull25.run_full25_frames D pre total schedule
  have count:=congrArg List.length rows
  simp only [List.length_map,List.length_range] at count
  refine ⟨cs,trace,count,?_,?_⟩
  · rw [qsSame,beginQs,same]
  · simpa only [SourceFull25.rawFrames,PrefixAdapter.completedRecords,List.map_map,Function.comp_def] using
      congrArg (List.map (fun frame : Slice U8=>frame.val.map ExtractedRecordByteValue.rawByte)) frames
#print axioms value
end AspisR1.FJq_SourceTrace
end
