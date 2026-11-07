import PCM_Witness
import PCM_StepLaws
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

theorem rejects_wrong_error :
    ¬ RowSpec (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  intro h
  have hr := h (PCM.account0,B32.ofFill 1) trivial PCM.state0 env0
  unfold Ref at hr
  change PCM.Computation.bind PCM.Computation.get _ PCM.state0 env0 _ at hr
  rw [PCM.Computation.bind_get] at hr
  change (⟨.ret (.error .invalidArgument,PCM.state0),[]⟩ : Observation Bool) =
    ⟨.ret (.ok false,PCM.state0),[]⟩ at hr
  cases hr
#print axioms rejects_wrong_error
end PCM_POOL_301
