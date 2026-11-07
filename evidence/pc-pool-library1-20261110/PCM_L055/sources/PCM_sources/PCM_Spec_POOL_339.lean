import PCM_ErrorMap
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_339
open RSL PCM PCM.Computation
abbrev CommonArgs := B32 × B32 × B32 × Master × Checkpoint × LaneState × UInt8 × TerminalResult
abbrev Args := B32 × B32 × B32 × Master × Checkpoint × LaneState × UInt8 × Request × TerminalResult
structure Children where
  common : Child CommonArgs Common
  transfer : Child (Common × TransferPublic) Statement
  withdrawal : Child (Common × WithdrawalPublic) Statement
  validate : Child (Statement × TerminalResult) Unit
/-- Both Box allocations belong to the named children; they happen before
the final validator may return InvalidVerifierReturnData (0x4153202d). -/
def Ref (C : Children) (a : Args) : Computation Unit := do
  let (masterKey,checkpointKey,laneKey,master,checkpoint,lane,output,request,result) := a
  let common ← C.common.call (masterKey,checkpointKey,laneKey,master,checkpoint,lane,output,result)
  let statement ← match request.pub with
    | .transfer p => C.transfer.call (common,p)
    | .withdrawal p => C.withdrawal.call (common,p)
  mapError (fun _ => .custom 0x4153202d) (C.validate.call (statement,result))
def RowSpec (C : Children) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl
end PCM_POOL_339
