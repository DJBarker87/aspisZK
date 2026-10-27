import IDb_Deployed
set_option autoImplicit false
noncomputable section
namespace AspisR1.IDb_Residual
open Aeneas Aeneas.Std Result
variable {C : Type} (adapter : AdapterRw.Ops) (currentBase : AspisR1CurrentCaller.Ops)
  (stageBase : VTop_Stages.Ops) (reserved : Bool) (err : C) (r : NP6_StdModel.Reservation)

/-- The original caller's generic filled-vector callback is still supplied by
its seed, even after all the adopted current/Claims/buffer installers. -/
theorem current_allocation :
    @(DrvC_Installation.currentInstalled
      (IDb_Deployed.deployedConfigurationFull adapter currentBase stageBase reserved err r)).op1 =
      @currentBase.op1 := rfl

#print axioms current_allocation
end AspisR1.IDb_Residual
end
