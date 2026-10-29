import PV_RJ4ID_Axioms
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4ID_Replay
open ProverRwFull
/-- Combined model equalities. The incoming records are explicit models,
not a hidden proposition identifying them with the deployed native execution. -/
theorem model_installations [ExternalTypes] (ops : ExternalFuns) :
    PV_RJ4ID_Op79.native ops = PV_DL_EncoderSelected.selected ops ∧
    PV_RJ4ID_Op254.incoming ops =
      {ops with op254 := ProverRwP6PowersInstall.powers ops} :=
  ⟨PV_RJ4ID_Op79.installation ops,PV_RJ4ID_Op254.installation ops⟩
#print axioms model_installations
#print axioms PV_RJ4ID_Statement.consume
#print axioms PV_RJDec_CommonCases.complete_pair
#print axioms PV_RJDec_ResultCases.fibres_iff
end R1Z.PV_RJ4ID_Replay
