import SAP_LiteralFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_BindingUnique
open OraclePortCheckpointResumeC5

theorem queries (p : AspisR1CurrentCaller.verifier.Prepared)
    (i j : RecordedBinaryExperimentBin.SourceInputs)
    (q q' : Fin 22 → Fin 262144) (c c' : Context)
    (h : SAP_LiteralFields.Fields p i q c) (h' : SAP_LiteralFields.Fields p j q' c') : q=q' :=
  h.queries.symm.trans h'.queries

theorem data_fields (p : AspisR1CurrentCaller.verifier.Prepared)
    (i j : RecordedBinaryExperimentBin.SourceInputs)
    (q q' : Fin 22 → Fin 262144) (c c' : Context)
    (h : SAP_LiteralFields.Fields p i q c) (h' : SAP_LiteralFields.Fields p j q' c') :
    i.data.gamma=j.data.gamma ∧ i.data.kappa=j.data.kappa ∧
    i.data.alpha0=j.data.alpha0 ∧ i.data.alpha1=j.data.alpha1 ∧
    SelectedChallengeMap.rhoOf i.rho=SelectedChallengeMap.rhoOf j.rho :=
  ⟨h.gamma.symm.trans h'.gamma,h.kappa.symm.trans h'.kappa,
    h.alpha0.symm.trans h'.alpha0,h.alpha1.symm.trans h'.alpha1,h.rho.symm.trans h'.rho⟩

theorem context (p : AspisR1CurrentCaller.verifier.Prepared)
    (i j : RecordedBinaryExperimentBin.SourceInputs)
    (q q' : Fin 22 → Fin 262144) (c c' : Context)
    (h : SAP_LiteralFields.Fields p i q c) (h' : SAP_LiteralFields.Fields p j q' c') : c=c' := by
  have state := h.state.symm.trans h'.state
  have roots := h.roots.symm.trans h'.roots
  have semanticAlpha := h.semanticAlpha.symm.trans h'.semanticAlpha
  have coordinates := h.coordinates.symm.trans h'.coordinates
  have claim := h.claim.symm.trans h'.claim
  cases c
  cases c'
  cases state
  cases roots
  cases semanticAlpha
  cases coordinates
  cases claim
  rfl

#print axioms queries
#print axioms data_fields
#print axioms context
end AspisR1.SAP_BindingUnique
end
