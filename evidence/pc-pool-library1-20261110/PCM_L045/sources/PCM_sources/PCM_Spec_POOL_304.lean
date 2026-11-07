import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_304
open RSL PCM PCM.Computation
abbrev Args := B32 × B32 × UInt8 × AccountInfo
/-- Unlike terminal row312, the deployed deposit body calls decode_lane_account,
since pair-forest-deposit-invariant-audit is OFF. -/
abbrev Decoder := Child (Args × Bool) LaneState
def Ref (decoder : Decoder) (a : Args) : Computation LaneState := do
  let value ← decoder.call (a,true)
  alloc
  Computation.pure value
def RowSpec (decoder : Decoder) (impl : Args → State → Env → Observation LaneState) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref decoder) impl
end PCM_POOL_304
