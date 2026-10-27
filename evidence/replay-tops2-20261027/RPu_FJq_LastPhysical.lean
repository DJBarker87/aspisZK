import RPu_FJq_LastSource
import RPu_FJq_ParsedFrames
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_LastPhysical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open FIz_ConcretePack (embed)
/-- Final-polynomial/source-running equality with all frame associations
proved from the SAME actual source and physical parser results. -/
theorem value {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8) (pre : r1_wire.Prefix)
    (sourceParsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre))
    (before after : r1_wire.SemanticTranscript H) (running : aspis_core.field.QM31)
    (alpha : Array aspis_core.field.QM31 10#usize)
    (rounds : RoundModel.rounds AspisS1ExtractedRoundChildren.children D pre before=ok (.Ok (running,alpha,after)))
    (stored : Bytes) (p : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (parsed : OraclePortStoredParserC4.parseReached stored tr=some p)
    (records : p.semantic=pre.records.val.map (fun s=>bytesOf s.val))
    (v : LiteralOpeningView.View) (read : LiteralOpeningView.read (typedRows p q tr)=some v)
    (c : r1_wire.Challenges) (same : v.semantic.map Prod.snd=FJq_ChallengeSlots.values c alpha)
    (polys : Fin 10 → Polynomial AspisWideTower.WideExact)
    (polyRead : R0P.Mask.semPolysZ (SelectedSemanticPrefixFacts.lift v.semantic)=some polys) :
    (polys 9).eval ((v.semantic.map Prod.snd).getD 24 0)=embed (FIp_SemanticValues.decode running) := by
  obtain ⟨values,typed,full,decode⟩:=PrefixAdapter.parse_typedFull bytes pre sourceParsed
  have frames:=FJq_ParsedFrames.value stored tr p parsed q pre values full records
  exact FJq_LastSource.value D pre before after running alpha rounds values full _ v read frames c same polys polyRead
#print axioms value
end AspisR1.FJq_LastPhysical
end
