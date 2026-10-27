import IDb_Deployed
set_option autoImplicit false
noncomputable section
namespace AspisR1.IDb_Residual
open Aeneas Aeneas.Std Result
variable {C : Type} (adapter : AdapterRw.Ops) (currentBase : AspisR1CurrentCaller.Ops)
  (stageBase : VTop_Stages.Ops) (reserved : Bool) (err : C) (r : NP6_StdModel.Reservation)

theorem row_allocation (ops : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) :
    @(RowShape_InstalledSlots.verifierOps ops B std).op1 = @ops.op1 := rfl

theorem uni_allocation (ops : AspisR1CurrentCaller.Ops) (flag : Bool)
    (q : Port3_NativeQueryBody.Ops) (g : Port3_NativeGeometryBody.Ops C) :
    @(Uni_Install.current ops flag q g).op1 = @ops.op1 := rfl

/-- Split projections prevent normalization of unrelated source callbacks. -/
theorem current_allocation :
    @(DrvC_Installation.currentInstalled
      (IDb_Deployed.deployedConfigurationFull adapter currentBase stageBase reserved err r)).op1 =
      @currentBase.op1 := by
  rw [DrvC_Installation.currentInstalled, row_allocation]
  exact uni_allocation currentBase reserved _ _

#print axioms row_allocation
#print axioms uni_allocation
#print axioms current_allocation
end AspisR1.IDb_Residual
end
