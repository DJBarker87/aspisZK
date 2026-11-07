import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_308
open RSL PCM
abbrev Args := Bytes
def model (a : Args) : Except ProgramError (Unit) :=
  if a == [65,83,56,67,1,8,1,0] then .ok () else .error .invalidInstructionData
def Ref (a : Args) : Computation (Unit) := Computation.ofExcept (model a)
def RowSpec (impl : Args → State → Env → Observation (Unit)) : Prop :=
  PCM.RowSpec (fun _ => True) Ref impl
end PCM_POOL_308
