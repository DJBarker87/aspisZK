import FIp_Top
import FIp_Nonvacuity
import FIp_InstalledLaws
import FIp_FinalPolynomial
import FIp_PairAdapterTrace
import FIp_MaskNativeValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_FinalClosure
open Aeneas Aeneas.Std Result DrvC_Installation

theorem installed_pair {C : Type} (err : C) (c : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err c r).finish.pair=FIo_Install.pair r := rfl

theorem installed_dot {C : Type} (err : C) (c : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) :
    (FIp_Install.configuration err c r).finish.dot=SAG_DotClosed.source := rfl

#print axioms installed_pair
#print axioms installed_dot
#print axioms FIp_Top.deployed
#print axioms FIp_Nonvacuity.composed
#print axioms FIp_InstalledLaws.dots
#print axioms FIp_FinalPolynomial.seven
#print axioms FIp_PairAdapterTrace.reached
#print axioms FIp_MaskNativeValue.source
end AspisR1.FIp_FinalClosure
end
