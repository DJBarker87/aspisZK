import PCM_Witness
import PCM_StepLaws
import PCM_Carriers
import PCM_SdkOps
set_option autoImplicit false
namespace PCM_POOL_362
open RSL PCM PCM.Computation
abbrev Args := AccountInfo × B32 × B32 × Nat
def Ref (a : Args) : Computation Preparation := do
  let (account,program,expected,n) := a
  check (account.key != expected || account.executable || account.is_signer || !account.is_writable) (.custom 0x41532035)
  let s ← get
  if s.owners account.cell == program then
    guardScope account .shared fun _ => do
      let current ← get
      let data := current.bytes account
      check (data.length != n || data.any (· != 0)) (.custom 0x41532035)
      Computation.pure .programOwnedZeroed
  else if s.owners account.cell == SYSTEM_PROGRAM then
    let empty ← dataIsEmpty account
    if empty then Computation.pure .createOrAllocateSystemOwned
    else Computation.throw (.custom 0x41532035)
  else Computation.throw (.custom 0x41532035)
def RowSpec (impl : Args → State → Env → Observation Preparation) : Prop :=
  PCM.RowSpec (fun _ => True) Ref impl

theorem rejects_wrong_error :
    ¬ RowSpec (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  let a : Args := ⟨PCM.account0,zero32,B32.ofFill 1,0⟩
  apply PCM.rejects_error (fun _ : Args => True) Ref a (.custom 0x41532035) .invalidArgument trivial
  · unfold Ref
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_362
