import FIp_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_Installation

theorem pair {C : Type} (err : C)
    (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err c r).finish.pair = FIo_Install.pair r := rfl

#print axioms pair
end AspisR1.FJr_Installation
end
