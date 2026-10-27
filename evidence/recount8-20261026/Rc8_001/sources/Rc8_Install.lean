import FGm_Headline
import FIo_Nonvacuity
import S6N_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc8_Install
open AspisR1Stage2.Stage2Finish

theorem native_headline {C : Type} (err : C)
    (c : DrvC_Installation.Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) :
    FIo_Install.configuration err c r = Rc5_Install.configuration err (FIo_Install.select r c) r := rfl

theorem arithmetic (r : NP6_StdModel.Reservation) (seed : FinishOps FIo_Install.W) :
    FIn_Install.finishOps (FIo_Install.finishOps r seed) = FIo_Install.finishOps r seed := rfl

theorem complete_pair {C : Type} (err : C)
    (c : DrvC_Installation.Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) :
    (FIo_Install.configuration err c r).finish.pair = FIo_Install.pair r := rfl

theorem native_public {C : Type} (err : C)
    (c : DrvC_Installation.Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) :
    S6N_Installation.Facts (DrvC_Installation.sdk (FIo_Install.configuration err c r)) :=
  S6N_Installation.facts _

#print axioms native_headline
#print axioms arithmetic
#print axioms complete_pair
#print axioms native_public
end AspisR1.Rc8_Install
end
