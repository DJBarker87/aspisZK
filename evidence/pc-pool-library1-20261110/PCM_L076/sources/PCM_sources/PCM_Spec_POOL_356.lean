import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_356
open RSL PCM
abbrev Args := Instruction × List AccountInfo
/-- Exact SolanaPoolCpiRuntimeV1 wrapper. The program::invoke implementation
is a separate OPEN SDK slot; this is not a CPI-success or readonly premise. -/
def Ref (sdkInvoke : Child Args Unit) (a : Args) : Computation Unit := sdkInvoke.call a
def RowSpec (sdkInvoke : Child Args Unit) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref sdkInvoke) impl
end PCM_POOL_356
