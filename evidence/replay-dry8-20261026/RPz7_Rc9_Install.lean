import RPz7_FIp_Install
import RPz7_FGm_Owners
import RPz7_FIp_GlobalOwners
import RPz7_S6N_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc9_Install

theorem compatible {C : Type} (err : C)
    (c : DrvC_Installation.Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) :
    FIo_Install.configuration err (FIp_Install.select r c) r = FIp_Install.configuration err c r := rfl

theorem finish_preserved {C : Type} (err : C)
    (c : DrvC_Installation.Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err c r).finish = (FIo_Install.configuration err c r).finish := rfl

/-- Old owners imply new owners with the additional internally-derived Shape guard.
This does not discharge any of the five remaining law families. -/
theorem owners {F C : Type} (c : DrvC_Installation.Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (old : FGm_Owners.Owners c B) : FIp_GlobalOwners.Owners c B := by
  intro s H e i p q data t atPrepared calls shape x
  exact old s H e i p q data t atPrepared calls x

#print axioms compatible
#print axioms finish_preserved
#print axioms owners
end AspisR1.Rc9_Install
end
