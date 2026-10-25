import Cons_Ten
import Cons_Finish
import Cons_Native
import AuS1_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.Cons_CallType
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open S2W_NativeConsolidation MultiproofConeCanonical

def check {F C : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (claimsStd : ClaimsUnrolledFinish.StdCalls)
    (s : SecondCut) (tx2 : Cons_Native.Witness) : Prop :=
  Cons_Native.Calls (AuS1_Install.base stageBase) finishOps reserved queryOps geoOps
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
      (ClaimsUnrolledSdk.sdkOps (Tx2I_Install.install adapterOps
        (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps)
        (Uni_Install.current ops reserved queryOps geoOps) B claimsStd)) () s.pub s.proof s.checkpoint tx2
end AspisR1.Cons_CallType
end
