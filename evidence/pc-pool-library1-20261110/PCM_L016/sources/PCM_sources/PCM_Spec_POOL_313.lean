import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_313
open RSL PCM PCM.Computation
abbrev Args := B32 × AccountInfo
/-- Frozen real callee: decode_master_account (writable=false). Its graph and domain must be installed
at the SAME arguments; this module is supporting work until that installation. -/
abbrev Decoder := Child ((B32 × AccountInfo) × Bool) Master
def Ref (decoder : Decoder) (a : Args) : Computation Master := do
  let value ← decoder.call (a,false)
  alloc
  Computation.pure value
def RowSpec (decoder : Decoder)
    (impl : Args → State → Env → Observation Master) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref decoder) impl
end PCM_POOL_313
