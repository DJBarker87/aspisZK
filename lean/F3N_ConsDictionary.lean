import Cons_Pair
import F3N_PreparedClaimSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_ConsDictionary
open Aeneas Aeneas.Std Result

def adapter {F C : Type} (a : AdapterRw.Ops) (stage : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C) :=
  Tx2I_Install.install a (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stage) reserved query geo)) finish

theorem dictionary {F C : Type} (a : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std=
      ClaimsUnrolledSdk.sdkOps (adapter a stage finish reserved query geo)
        (Tx1Q_SameCut.dictionary (Op5T_Concrete.current ops) reserved query geo) B std := by
  rw [AuS1_Install.dictionary]
  simp only [Uni_Install.compose_tx1]
  rfl

theorem digest {F C : Type} (a : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    SdkD_PairBatches.current a ops stage finish reserved query geo B std=
      Tx1Q_SameCut.callerDigest (adapter a stage finish reserved query geo)
        (Op5T_Concrete.current ops) reserved query geo B std := by
  unfold SdkD_PairBatches.current Tx1Q_SameCut.callerDigest
  rw [dictionary]

#print axioms dictionary
#print axioms digest
end AspisR1.F3N_ConsDictionary
end
