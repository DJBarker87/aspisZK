import RPz7_Tx1Q_Execution
import RPz7_WAdm_Execution
import NDO_JFz_ScanAccepted
set_option autoImplicit false
namespace AspisR1.JGi_TX1Prefix
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem tx1 {C : Type} (ops : Ops) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    (Tx1Q_Execution.actual ops true query geo B std).op3 JFx_NativeBytes.proof=ok (.Ok .S2) ∧
    (Tx1Q_Execution.actual ops true query geo B std).op4 JFx_NativeBytes.proof=ok (.Ok ()) := by
  change Op3I_Install.sourceBody JFx_NativeBytes.proof=ok (.Ok .S2) ∧
    Op4P_Install.sourceBody JFx_NativeBytes.proof=ok (.Ok ())
  exact JFz_ScanAccepted.shape_and_scan
#print axioms tx1

theorem writer {C : Type} (ops : Ops) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    (WAdm_Execution.actual ops true query geo B std).op3 JFx_NativeBytes.proof=ok (.Ok .S2) ∧
    (WAdm_Execution.actual ops true query geo B std).op4 JFx_NativeBytes.proof=ok (.Ok ()) := by
  change Op3I_Install.sourceBody JFx_NativeBytes.proof=ok (.Ok .S2) ∧
    Op4P_Install.sourceBody JFx_NativeBytes.proof=ok (.Ok ())
  exact JFz_ScanAccepted.shape_and_scan
#print axioms writer
end AspisR1.JGi_TX1Prefix
