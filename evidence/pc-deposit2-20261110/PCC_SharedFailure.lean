import PCC_Shared
set_option autoImplicit false
namespace PCC
open PCA
/-- Acquisition failure emits no deref and no release, even with a parent's
other live guards. Cleanup of those guards belongs to the parent. -/
theorem shared_acquire_error {α : Type} (a : Nat)
    (body : NLF_SdkModel.Payload → Reference α) (s : PCA_State)
    (e : NLF_SdkModel.ProgramError)
    (h : (NLF_ParentModel.acquire s.loans a .shared).2 = .error e) :
    withShared a body s =
      ⟨{s with loans := (NLF_ParentModel.acquire s.loans a .shared).1},
        [.token (.acquire a s.loans.next .shared (.error e))],.error (.program borrowFailed)⟩ := by
  simp only [withShared,h]
#print axioms shared_acquire_error
end PCC
