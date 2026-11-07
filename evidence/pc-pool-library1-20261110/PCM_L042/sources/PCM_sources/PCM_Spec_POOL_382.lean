import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_382
open RSL PCM
abbrev Args := List AccountInfo
def model (a : Args) : Except ProgramError (List AccountInfo) :=
  match a with
  | [mint,source,authority,vault,token] => .ok [source,mint,vault,authority,token]
  | _ => .error (if a.length < 5 then .notEnoughAccountKeys else .invalidArgument)
def Ref (a : Args) : Computation (List AccountInfo) := Computation.ofExcept (model a)
def RowSpec (impl : Args → State → Env → Observation (List AccountInfo)) : Prop :=
  PCM.RowSpec (fun _ => True) Ref impl
end PCM_POOL_382
