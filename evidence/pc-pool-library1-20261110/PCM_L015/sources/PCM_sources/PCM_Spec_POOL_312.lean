import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_312
open RSL PCM PCM.Computation
abbrev Args := B32 × B32 × UInt8 × AccountInfo
/-- Frozen real callee: decode_lane_account_from_program_invariant_v1 (writable=true). Its graph and domain must be installed
at the SAME arguments; this module is supporting work until that installation. -/
abbrev Decoder := Child ((B32 × B32 × UInt8 × AccountInfo) × Bool) LaneState
def Ref (decoder : Decoder) (a : Args) : Computation LaneState := do
  let value ← decoder.call (a,true)
  alloc
  Computation.pure value
def RowSpec (decoder : Decoder)
    (impl : Args → State → Env → Observation LaneState) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref decoder) impl
end PCM_POOL_312
