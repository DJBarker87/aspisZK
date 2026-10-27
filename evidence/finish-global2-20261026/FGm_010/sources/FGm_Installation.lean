import FIo_Install
import Hist_Authority
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_Installation
open Aeneas Aeneas.Std Result

theorem key {C : Type} (err : C) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    (DrvC_Installation.sdk (FIo_Install.configuration err c r)).op36=Hist_Authority.keyEq := rfl

#print axioms key
end AspisR1.FGm_Installation
end
