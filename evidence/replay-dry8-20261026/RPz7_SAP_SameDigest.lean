import RPz7_AuS1_Install
import RPz7_Tx1Q_SameCut
import RPz7_Uni_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_SameDigest

theorem digest {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    SdkD_PairBatches.current adapter ops stage finish reserved query geo B std =
    Tx1Q_SameCut.callerDigest
      (Tx2I_Install.install adapter
        (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stage) reserved query geo)) finish)
      (Op5T_Concrete.current ops) reserved query geo B std := by
  unfold SdkD_PairBatches.current Tx1Q_SameCut.callerDigest
  rw [AuS1_Install.dictionary,Uni_Install.compose_tx1]

#print axioms digest
end AspisR1.SAP_SameDigest
end
