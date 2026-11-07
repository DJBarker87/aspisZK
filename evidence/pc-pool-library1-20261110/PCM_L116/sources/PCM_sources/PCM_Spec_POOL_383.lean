import PCM_Clone
import PCM_Witness
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_383
open RSL PCM
abbrev Args := List AccountInfo
def model (a : Args) : Except ProgramError (List AccountInfo) :=
  match a with
  | [mint,vault,destination,authority,token] => .ok [vault,mint,destination,authority,token]
  | _ => .error (if a.length < 5 then .notEnoughAccountKeys else .invalidArgument)
def Ref (a : Args) : Computation (List AccountInfo) :=
  match model a with
  | .error e => PCM.Computation.throw e
  | .ok infos => PCM.Computation.cloneHandles infos
def RowSpec (impl : Args → State → Env → Observation (List AccountInfo)) : Prop :=
  PCM.RowSpec (fun _ => True) Ref impl

theorem rejects_wrong_error :
    ¬ RowSpec (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ : Args => True) Ref ([]) .notEnoughAccountKeys .invalidArgument trivial
  · rfl
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_383
