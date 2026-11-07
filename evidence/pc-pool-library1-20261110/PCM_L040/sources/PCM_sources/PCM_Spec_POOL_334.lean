import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_334
open RSL PCM
abbrev Args := Bytes
def model (a : Args) : Except ProgramError (Bytes × Hints) :=
  if a.length < 4 then .error .invalidInstructionData else
    let i := a.length - 4
    .ok (a.take i, ⟨a[i]!,a[i+1]!,a[i+2]!,a[i+3]!⟩)
def Ref (a : Args) : Computation (Bytes × Hints) := Computation.ofExcept (model a)
def RowSpec (impl : Args → State → Env → Observation (Bytes × Hints)) : Prop :=
  PCM.RowSpec (fun _ => True) Ref impl
end PCM_POOL_334
