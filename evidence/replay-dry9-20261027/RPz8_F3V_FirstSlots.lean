import RPz8_F3V_AllWorldPair
import RPz7_SdkD_Tx1Run
import RPz7_SdkD_FoldedCut
set_option autoImplicit false
namespace AspisR1.F3V_FirstSlots

theorem same {C : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    GExp_FirstCode.installed (GExp_FirstPair.base ops reserved query geo) B std=
      Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std := by
  rw [GExp_FirstPair.installed,Uni_Install.compose_tx1]
  rfl

#print axioms same
end AspisR1.F3V_FirstSlots
