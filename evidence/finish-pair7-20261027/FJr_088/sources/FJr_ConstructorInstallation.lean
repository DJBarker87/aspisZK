import FJr_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_ConstructorInstallation

theorem weights {C : Type} (err : C)
    (c : DrvC_Installation.Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err c r).finish.newWeights=FIn_WeightsInstall.newWeights := rfl

#print axioms weights
end AspisR1.FJr_ConstructorInstallation
end
