import R1Z.PV_CBL_CoreNewCases
import R1Z.PV_CBL_ShaCore
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_CoreNewCounter
set_option autoImplicit false
/-- Field identity transport, not the op217 generic default wrapper. -/
def transport (c : PV_CBL_CoreNewOwned.ShaCoreOwned) : PV_CBL_ShaCore.Core := ⟨c.state,c.block_len⟩
theorem count_zero (n : Usize) (c : PV_CBL_CoreNewOwned.ShaCoreOwned)
    (h : PV_CBL_CoreNewOwned.sha_core_new_owned n=ok (.Ok c)) : c.block_len=0#u64 := by
  unfold PV_CBL_CoreNewOwned.sha_core_new_owned at h
  split at h <;> cases h <;> rfl
theorem transport_state (c : PV_CBL_CoreNewOwned.ShaCoreOwned) : (transport c).state=c.state := rfl
theorem transport_count (c : PV_CBL_CoreNewOwned.ShaCoreOwned) : (transport c).block_len=c.block_len := rfl
#print axioms transport
#print axioms count_zero
#print axioms transport_state
#print axioms transport_count
end R1Z.PV_CBL_CoreNewCounter
