import SAP_LiteralFields
import F3L_PreparedExt
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_FieldsExact
open OraclePortCheckpointResumeC5

theorem numeric (p : AspisR1CurrentCaller.verifier.Prepared)
    (i : RecordedBinaryExperimentBin.SourceInputs) (q : Fin 22 → Fin 262144) (c : Context)
    (h : SAP_LiteralFields.Fields p i q c) :
    SAP_CurrentNumeric.numeric p=prepared c i.data (SelectedChallengeMap.rhoOf i.rho) q := by
  apply F3L_PreparedExt.fields
  · exact h.state
  · exact h.roots
  · exact h.gamma
  · exact h.kappa
  · funext j
    fin_cases j
    · exact h.alpha0
    · exact h.alpha1
  · exact h.rho
  · exact h.queries
  · exact h.semanticAlpha
  · exact h.coordinates
  · exact h.claim

theorem iff_numeric (p : AspisR1CurrentCaller.verifier.Prepared)
    (i : RecordedBinaryExperimentBin.SourceInputs) (q : Fin 22 → Fin 262144) (c : Context) :
    SAP_LiteralFields.Fields p i q c ↔
      SAP_CurrentNumeric.numeric p=prepared c i.data (SelectedChallengeMap.rhoOf i.rho) q :=
  ⟨numeric p i q c,SAP_LiteralFields.of_numeric p i q c⟩

#print axioms numeric
#print axioms iff_numeric
end AspisR1.SAP_FieldsExact
end
