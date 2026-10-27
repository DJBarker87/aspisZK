import FJt_GlobalOwners
set_option autoImplicit false
namespace AspisR1.FJt_OwnerEquivalence
theorem equivalent {C : Type} (m : IDa_Deployed.Uninstalled C) (err : C) (r : NP6_StdModel.Reservation)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) :
    FIp_GlobalOwners.Owners (FJt_GlobalTerminal.configuration m err r) B ↔
      FJt_GlobalOwners.Owners (FJt_GlobalTerminal.configuration m err r) B :=
  ⟨FJt_GlobalOwners.project _ B,FJt_GlobalOwners.complete m err r B⟩
#print axioms equivalent
end AspisR1.FJt_OwnerEquivalence
