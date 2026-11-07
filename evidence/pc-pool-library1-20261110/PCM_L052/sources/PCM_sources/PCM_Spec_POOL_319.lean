import PCM_ErrorMap
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_319
open RSL PCM PCM.Computation
abbrev Args := LaneState × TerminalResult
structure Children where
  nextLane : Child Args LaneState
  encodeLane : Child LaneState Bytes
/-- Deployed source-result-invariant-audit ON: a next-lane Box allocation
precedes the encoder, so even a later encoder Err has a real earlier abort arm. -/
def Ref (C : Children) (a : Args) : Computation Bytes := do
  let lane ← C.nextLane.call a
  alloc
  let image ← C.encodeLane.call lane
  alloc
  Computation.pure image

def RowSpec (C : Children) (impl : Args → State → Env → Observation Bytes) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl
end PCM_POOL_319
