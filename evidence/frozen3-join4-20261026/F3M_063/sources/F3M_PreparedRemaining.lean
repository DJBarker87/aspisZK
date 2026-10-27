import F3L_PreparedRemaining
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_PreparedRemaining

theorem remaining (out : AspisR1PublicPreparation.verifier.Prepared)
    (p : OraclePortCompactDraft.Parsed) (i : RecordedBinaryExperimentBin.SourceInputs)
    (v : LiteralOpeningView.View) (q : Fin 22 → Fin 262144)
    (six : F3L_PreparedModelSix.Fields out i q)
    (roots : (F3L_SourcePrepared.numeric out).roots=(fun j=>OraclePortBatchDraft.committedRoot p j.val))
    (alpha : (F3L_SourcePrepared.numeric out).semanticAlpha=(OraclePortAcceptedContextC6.context p i v).semanticAlpha) :
    let source := F3L_SourcePrepared.numeric out
    let target := OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p i v)
      i.data (SelectedChallengeMap.rhoOf i.rho) q
    source=target ↔ source.coordinates=target.coordinates ∧ source.claim=target.claim := by
  have prior := F3L_PreparedRemaining.remaining out p i v q six roots
  constructor
  · intro h
    exact ⟨((prior.mp h).2.1),((prior.mp h).2.2)⟩
  · intro h
    exact prior.mpr ⟨alpha,h⟩

#print axioms remaining
end AspisR1.F3M_PreparedRemaining
end
