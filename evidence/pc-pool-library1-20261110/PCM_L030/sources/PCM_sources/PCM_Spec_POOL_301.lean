import PCM_Carriers
import PCM_SdkOps
set_option autoImplicit false
namespace PCM_POOL_301
open RSL PCM PCM.Computation
abbrev Args := AccountInfo × B32
def Ref (a : Args) : Computation Bool := do
  let s ← get
  if s.owners a.1.cell != a.2 then Computation.pure false
  else
    let n ← dataLen a.1
    if n != PAGE_BYTES then Computation.pure false
    else guardScope a.1 .shared fun _ => do
      let current ← get
      Computation.pure ((current.bytes a.1).all (· == 0))
def RowSpec (impl : Args → State → Env → Observation Bool) : Prop :=
  PCM.RowSpec (fun _ => True) Ref impl
end PCM_POOL_301
