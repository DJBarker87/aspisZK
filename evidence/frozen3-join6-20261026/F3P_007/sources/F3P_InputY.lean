import F3P_MatchingY
import OraclePortStoredDecisionDraftC4
import F3P_AlignedRow
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_InputY
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4

theorem rows (p : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (aligned : Aligned p tr) (i : RecordedBinaryExperimentBin.SourceInputs)
    (found : input p q tr=some i) :
    ∃ (r25 : CircleRecordCodec.Payload 0) (r26 : CircleRecordCodec.Payload 1)
      (r27 : OpeningRecordCodec.Payload .gamma),
      CircleRecordCodec.decode 0 (rowBytes p 25)=some r25 ∧
      CircleRecordCodec.decode 1 (rowBytes p 26)=some r26 ∧
      OpeningRecordCodec.decode .gamma (rowBytes p 27)=some r27 ∧
      i.data.Y=SelectedOpeningClaims.Y r25 r26 r27 := by
  obtain ⟨r25,r26,r27,h25,h26,h27,same⟩ := F3P_MatchingY.read _ i.data (input_fields p q tr i found).2
  refine ⟨r25,r26,r27,?_,?_,?_,same⟩
  · exact (F3P_AlignedRow.read_iff p q tr aligned 25 (by decide) (by decide) _ r25).mp h25
  · exact (F3P_AlignedRow.read_iff p q tr aligned 26 (by decide) (by decide) _ r26).mp h26
  · exact (F3P_AlignedRow.read_iff p q tr aligned 27 (by decide) (by decide) _ r27).mp h27

#print axioms rows
end AspisR1.F3P_InputY
end
