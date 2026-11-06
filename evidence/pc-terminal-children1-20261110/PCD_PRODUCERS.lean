import NIB_ReadToSettlement
set_option autoImplicit false
noncomputable section
namespace PCD_PRODUCERS
open Aeneas Aeneas.Std Result
/-- OPEN target NIB-P1, not a producer theorem. POOL:350/347/348 and PCB344/345
must prove same invocation/program and native chronology; the far-side emitter
producer remains independently required. No equality is obtained from a summary. -/
def P1 {Invocation Context Key RuntimeState : Type}
    (runtime : NGK_NFO_PoolReturnData.Runtime Context Key RuntimeState)
    (context : Invocation → Context) (program : Invocation → Key)
    (emitInvocation poolInvocation : Invocation) (selected : Key)
    (readState : RuntimeState) (s : NFY_NEU_EmitModel.Statement) : Prop :=
  poolInvocation = emitInvocation ∧ program emitInvocation = selected ∧
  readState = runtime.write (context emitInvocation) (program emitInvocation)
    (AspisR1.S2K.ResultPayload.bytes s).val

/-- OPEN exact `checked` target. A native dictionary is still required from
POOL:311/312/313/314/339 at SAME caller input arguments. This def is not a proof,
and is never used as a row-root hypothesis or promoted to closure. -/
def P2 (validate : NGK_NFR_CSettlement.Output →
    Result (core.result.Result Unit NGK_NFR_CSettlement.Error))
    (authenticated : NGK_NFO_ReadModel.Accepted) : Prop :=
  validate authenticated.value = ok (.Ok ())

/-- OPEN exact `advanced` target. POOL:319/320 must identify the native lane
callback at the SAME pre-lane/result, complete Result and actual allocated image. -/
def P3 {LaneImage : Type} (lane : NGK_NFR_CSettlement.Output →
    Result (core.result.Result LaneImage NGK_NFR_CSettlement.Error))
    (authenticated : NGK_NFO_ReadModel.Accepted) (image : LaneImage) : Prop :=
  lane authenticated.value = ok (.Ok image)
end PCD_PRODUCERS
