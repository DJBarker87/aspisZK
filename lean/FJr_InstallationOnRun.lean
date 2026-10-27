import FJr_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_InstallationOnRun
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish

theorem pair {C : Type} (err : C) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (w : FIo_Install.W) (alpha : Slice E) (f : Slice U8) (kappa out : E)
    (run : (FIp_Install.configuration err c r).finish.pair w alpha f kappa=ok (.Ok out)) :
    FIo_Install.pair r w alpha f kappa=ok (.Ok out) := by
  rw [FJr_Installation.pair] at run
  exact run

#print axioms pair
end AspisR1.FJr_InstallationOnRun
end
