import AuS1_OnRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Install
open Aeneas Aeneas.Std Result

def base (stage : VTop_Stages.Ops) : VTop_Stages.Ops :=
  {stage with op14 := ok 7783#usize,op15 := ok 7751#usize,unwrap32 := Port4B_FoldedCut.unwrap32}

 theorem dictionary {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std =
      ClaimsUnrolledSdk.sdkOps
        (Tx2I_Install.install adapter (Op5T_Concrete.stage (Tx2N_Execution.control (base stage) reserved query geo)) finish)
        (Uni_Install.current ops reserved query geo) B std := by
  unfold SdkD_PairBatches.dictionary
  rw [SdkD_Install.inner]
  rfl

#print axioms dictionary
end AspisR1.AuS1_Install
end
