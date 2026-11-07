import PCM_AvoidRejection
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_342
open RSL PCM PCM.Computation
abbrev Args := Common × WithdrawalPublic
def Ref (a : Args) : Computation Statement := do
  alloc
  Computation.pure (.withdrawal a.1 a.2)
def RowSpec (impl : Args → State → Env → Observation Statement) : Prop :=
  PCM.RowSpec (fun _ => True) Ref impl

theorem rejects_wrong_error (a : Args) :
    ¬ RowSpec (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_avoided_error (fun _ : Args => True) Ref a trivial .invalidArgument
  unfold Ref
  apply PCM.Computation.bind_avoid
  · exact PCM.Computation.alloc_avoid _
  · intro u
    exact PCM.Computation.pure_avoid _ _
#print axioms rejects_wrong_error
end PCM_POOL_342
