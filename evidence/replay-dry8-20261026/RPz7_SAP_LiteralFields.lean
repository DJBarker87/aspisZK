import RPz7_SAP_NumericTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_LiteralFields
open OraclePortCheckpointResumeC5

/-- The data fields actually stored in the current TX1 Prepared. Opening
values remain in SourceInputs; they are not claimed to be Prepared fields. -/
structure Fields (p : AspisR1CurrentCaller.verifier.Prepared)
    (i : RecordedBinaryExperimentBin.SourceInputs) (q : Fin 22 → Fin 262144) (c : Context) : Prop where
  gamma : CheckpointBytes5Output.ofE (Tx1Q_Carriers.e p.gamma)=i.data.gamma
  kappa : CheckpointBytes5Output.ofE (Tx1Q_Carriers.e p.kappa)=i.data.kappa
  alpha0 : CheckpointBytes5Output.ofE (Tx1Q_Carriers.e (SAP_CurrentNumeric.alpha p 0))=i.data.alpha0
  alpha1 : CheckpointBytes5Output.ofE (Tx1Q_Carriers.e (SAP_CurrentNumeric.alpha p 1))=i.data.alpha1
  rho : CheckpointBytes5Output.ofK (Tx1Q_Carriers.k p.rho)=SelectedChallengeMap.rhoOf i.rho
  queries : CheckpointBytes5Output.queries (Tx1Q_Carriers.prepared p)=q
  state : (SAP_CurrentNumeric.numeric p).state=c.state
  roots : (SAP_CurrentNumeric.numeric p).roots=c.roots
  semanticAlpha : (SAP_CurrentNumeric.numeric p).semanticAlpha=c.semanticAlpha
  coordinates : (SAP_CurrentNumeric.numeric p).coordinates=c.coordinates
  claim : CheckpointBytes5Output.ofE (Tx1Q_Carriers.e p.claim)=c.claim

theorem of_numeric (p : AspisR1CurrentCaller.verifier.Prepared)
    (i : RecordedBinaryExperimentBin.SourceInputs) (q : Fin 22 → Fin 262144) (c : Context)
    (h : SAP_CurrentNumeric.numeric p=prepared c i.data (SelectedChallengeMap.rhoOf i.rho) q) :
    Fields p i q c := by
  refine ⟨congrArg OraclePortCheckpointAbiC5.Prepared.gamma h,
    congrArg OraclePortCheckpointAbiC5.Prepared.kappa h,?_,?_,
    congrArg OraclePortCheckpointAbiC5.Prepared.rho h,
    congrArg OraclePortCheckpointAbiC5.Prepared.queries h,
    congrArg OraclePortCheckpointAbiC5.Prepared.state h,
    congrArg OraclePortCheckpointAbiC5.Prepared.roots h,
    congrArg OraclePortCheckpointAbiC5.Prepared.semanticAlpha h,
    congrArg OraclePortCheckpointAbiC5.Prepared.coordinates h,
    congrArg OraclePortCheckpointAbiC5.Prepared.claim h⟩
  · exact congrArg (fun p : OraclePortCheckpointAbiC5.Prepared=>p.alpha 0) h
  · exact congrArg (fun p : OraclePortCheckpointAbiC5.Prepared=>p.alpha 1) h

#print axioms of_numeric
end AspisR1.SAP_LiteralFields
end
