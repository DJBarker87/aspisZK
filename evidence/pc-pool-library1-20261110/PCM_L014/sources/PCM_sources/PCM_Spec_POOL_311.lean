import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_311
open RSL PCM PCM.Computation
abbrev Args := B32 × B32 × AccountInfo
/-- Frozen real callee: decode_retained_pair_forest_checkpoint_account_v1. Its graph and domain must be installed
at the SAME arguments; this module is supporting work until that installation. -/
abbrev Decoder := Child (B32 × B32 × AccountInfo) Checkpoint
def Ref (decoder : Decoder) (a : Args) : Computation Checkpoint := do
  let value ← decoder.call a
  alloc
  Computation.pure value
def RowSpec (decoder : Decoder)
    (impl : Args → State → Env → Observation Checkpoint) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref decoder) impl
end PCM_POOL_311
