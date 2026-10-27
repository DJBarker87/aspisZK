import RPz8_F3S_MapLog
import RPz8_RawK_EventHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_ChildLogs
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 theorem first {Hash : Type} (D : AdapterRw.aspis_core.digest.Digest32 Hash)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : Hash)
    (obs : Option (AdapterRw.aspis_r1_cost_probe.verifier.Phase → Result Unit))
    (answer : SdkD_FirstChild.Reply) :
    RawK_TraceLogs.eventLog hashv (GExq_Caller.child adapter ops stage finish reserved query geo B std hashv)
      (.returned (.op10 D semantic pub proof split hash obs) answer)=
    SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_FirstCode.code (GExp_FirstPair.base ops reserved query geo) B std hashv
        (AspisS6CurrentFirstInstallation.toDigest D) (AspisS6CurrentVerifierCarrier.toPublic semantic)
        pub proof split hash) []).2 := by
  exact congrArg SdkC_Source.readLog (F3S_MapLog.run_map hashv _ SdkD_FirstChild.answer [])
#print axioms first
end AspisR1.F3S_ChildLogs
end
