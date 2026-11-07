import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_338
open RSL PCM PCM.Computation
abbrev Args := Common × TransferPublic
def Ref (a : Args) : Computation Statement := do
  alloc
  Computation.pure (.transfer a.1 a.2)
def RowSpec (impl : Args → State → Env → Observation Statement) : Prop :=
  PCM.RowSpec (fun _ => True) Ref impl
end PCM_POOL_338
