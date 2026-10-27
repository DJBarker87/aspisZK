import RPz7_F3L_PreparedModelSix
import F3L_PreparedExt
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_PreparedRemaining

/-- Exact residual obligation after the six groups and stored roots proved in
NativePreparedModel. This equivalence does not discharge any of the three. -/
theorem remaining (out : AspisR1PublicPreparation.verifier.Prepared)
    (p : OraclePortCompactDraft.Parsed) (i : RecordedBinaryExperimentBin.SourceInputs)
    (v : LiteralOpeningView.View) (q : Fin 22 → Fin 262144)
    (six : F3L_PreparedModelSix.Fields out i q)
    (roots : (F3L_SourcePrepared.numeric out).roots=(fun j=>OraclePortBatchDraft.committedRoot p j.val)) :
    let source := F3L_SourcePrepared.numeric out
    let target := OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p i v)
      i.data (SelectedChallengeMap.rhoOf i.rho) q
    source=target ↔ source.semanticAlpha=target.semanticAlpha ∧
      source.coordinates=target.coordinates ∧ source.claim=target.claim := by
  constructor
  · intro same
    exact ⟨congrArg (fun x=>x.semanticAlpha) same,congrArg (fun x=>x.coordinates) same,
      congrArg (fun x=>x.claim) same⟩
  · rintro ⟨alpha,coordinates,claim⟩
    exact F3L_PreparedExt.fields _ _ six.2.2.2.2.2 roots six.1 six.2.1 six.2.2.1 six.2.2.2.1
      six.2.2.2.2.1 alpha coordinates claim

#print axioms remaining
end AspisR1.F3L_PreparedRemaining
end
