import PoolM_CancelControl
set_option autoImplicit false
namespace PoolM_CancelReach
open Aeneas Aeneas.Std Result PoolM_Owned

def payer : Account := ⟨false,true,false,true,true,0#usize⟩
def core : Account := ⟨true,false,false,false,true,10000#usize⟩
def shard : Account := ⟨true,false,false,false,true,8504#usize⟩
def occupied (size : Usize) : Account := ⟨true,false,false,false,true,size⟩

/-- The role-control prefix has accepted paths for both source layouts. -/
theorem admitted (hasShard : Bool) : cancel_roles payer core shard hasShard = ok 0#u32 := by
  cases hasShard <;> rfl

/-- Rejection at the first role check occurs even with otherwise valid plans. -/
theorem authority_reachable (size : Usize) :
    cancel_roles (occupied size) core shard true = ok 2#u32 := by rfl

/-- Reach the core guard, rather than an earlier parser/metadata error, in the
owned source prefix. Actual native covers are separately recorded in Kani. -/
theorem core_reachable_192 :
    cancel_roles payer (occupied 192#usize) shard true = ok 1#u32 := by rfl

theorem core_reachable_1768 :
    cancel_roles payer (occupied 1768#usize) shard true = ok 1#u32 := by rfl

theorem shard_reachable_192 :
    cancel_roles payer core (occupied 192#usize) true = ok 1#u32 := by rfl

theorem shard_reachable_1768 :
    cancel_roles payer core (occupied 1768#usize) true = ok 1#u32 := by rfl

/-- The absent shard is not read: arbitrary metadata remains irrelevant. -/
theorem absent_shard (arbitrary : Account) :
    cancel_roles payer core arbitrary false = ok 0#u32 := by rfl

#print axioms admitted
#print axioms authority_reachable
#print axioms core_reachable_192
#print axioms core_reachable_1768
#print axioms shard_reachable_192
#print axioms shard_reachable_1768
#print axioms absent_shard
end PoolM_CancelReach
