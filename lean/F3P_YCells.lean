import F3P_InputY
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_YCells
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4

theorem identified (p : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (aligned : Aligned p tr) (i : RecordedBinaryExperimentBin.SourceInputs) (found : input p q tr=some i)
    (r25 : CircleRecordCodec.Payload 0) (r26 : CircleRecordCodec.Payload 1)
    (r27 : OpeningRecordCodec.Payload .gamma)
    (h25 : CircleRecordCodec.decode 0 (rowBytes p 25)=some r25)
    (h26 : CircleRecordCodec.decode 1 (rowBytes p 26)=some r26)
    (h27 : OpeningRecordCodec.decode .gamma (rowBytes p 27)=some r27) :
    i.data.Y=SelectedOpeningClaims.Y r25 r26 r27 := by
  obtain ⟨s25,s26,s27,g25,g26,g27,same⟩ := F3P_InputY.rows p q tr aligned i found
  have e25 := Option.some.inj (g25.symm.trans h25)
  have e26 := Option.some.inj (g26.symm.trans h26)
  have e27 := Option.some.inj (g27.symm.trans h27)
  subst s25;subst s26;subst s27
  exact same

#print axioms identified
end AspisR1.F3P_YCells
end
