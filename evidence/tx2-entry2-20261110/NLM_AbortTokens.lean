import NLM_TokenEvents
set_option autoImplicit false
noncomputable section
namespace NLM_AbortTokens
open Aeneas Aeneas.Std NLM_Snapshot
/-- No release may be manufactured after the allocation abort prefix. -/
theorem no_release (s : NLM_Snapshot.State) (a : Nat) (allocation : Result Unit)
 (g : NLF_RefCell.Guard) (reply : Except NLF_RefCell.Error Unit) :
 NLF_ParentModel.Event.release g reply ∉ (allocationPrefix s a allocation).filterMap NLM_TokenEvents.sdk := by
 rw [NLM_TokenEvents.abort_prefix]
 simp
#print no_release
#print axioms no_release
end NLM_AbortTokens
