import PCM_Witness
import PCM_Carriers
import PCM_Spec_POOL_350
set_option autoImplicit false
namespace PCM_POOL_367
open RSL PCM
abbrev Args := List AccountInfo
def model (a : Args) : Except ProgramError (Unit) :=
  if PCM_POOL_350.duplicateKeys (a.map AccountInfo.key) then .error .invalidArgument else .ok ()
def Ref (a : Args) : Computation (Unit) := Computation.ofExcept (model a)
def RowSpec (impl : Args → State → Env → Observation (Unit)) : Prop :=
  PCM.RowSpec (fun _ => True) Ref impl

theorem rejects_wrong_error :
    ¬ RowSpec (fun _ s _ => ⟨.ret (.error .invalidInstructionData,s),[]⟩) := by
  apply PCM.rejects_error (fun _ : Args => True) Ref ([PCM.account0,PCM.account0]) .invalidArgument .invalidInstructionData trivial
  · rfl
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_367
