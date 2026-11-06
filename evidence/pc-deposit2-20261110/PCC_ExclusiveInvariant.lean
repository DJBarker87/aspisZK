import PCC_ExclusiveReference
import PCC_ReferenceInvariant
set_option autoImplicit false
namespace PCC
open PCA

theorem exclusive_invariant (site account : Nat) : Preserves (acquireExclusive site account) := by
  intro s hs
  have h := NLF_ParentModel.acquire_preserves s.loans account .exclusive hs
  cases hr : (NLF_ParentModel.acquire s.loans account .exclusive).2 <;>
    simpa only [acquireExclusive,hr,Invariant] using h

/-- No newly acquired guard is pushed when page acquisition returns Err. -/
theorem exclusive_error_guards (site account : Nat) (s : PCA_State)
    (e : NLF_SdkModel.ProgramError)
    (hr : (NLF_ParentModel.acquire s.loans account .exclusive).2 = .error e) :
    (acquireExclusive site account s).state.liveGuards = s.liveGuards := by
  simp only [acquireExclusive,hr]
#print axioms exclusive_invariant
#print axioms exclusive_error_guards
end PCC
