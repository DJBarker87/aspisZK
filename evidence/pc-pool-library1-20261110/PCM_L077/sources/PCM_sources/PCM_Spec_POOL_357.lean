import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_357
open RSL PCM
abbrev Args := Instruction × List AccountInfo × List (List Bytes)
def Ref (sdkInvokeSigned : Child Args Unit) (a : Args) : Computation Unit := sdkInvokeSigned.call a
def RowSpec (sdkInvokeSigned : Child Args Unit) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref sdkInvokeSigned) impl
end PCM_POOL_357
