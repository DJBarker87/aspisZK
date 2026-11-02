import PV_EVH_EntropySourceSlot
import PV_EVH_EntropyPhysicalCopy
set_option autoImplicit false
namespace PV_EVH_EntropyInnerFrame
open PV_EVH_StackZero (Slot State)
open PV_EVH_EntropySourceSlot (frontier)

/-- Source lifetime for an inner32 array. Numeric address is supplied by the
actual frame; the key tracks ownership independently of its byte contents. -/
def inner (owner address : Nat) (w : State) : Slot :=
  ⟨⟨frontier (w.frame.live ++ w.frame.retired),owner⟩,address,32⟩

def fieldSlot (owner address : Nat) (w : State) : Slot := inner owner address w

/-- The second initializer happens after the first lifetime is admitted. -/
def seedSlot (owner fieldAddress seedAddress : Nat) (w : State) : Slot :=
  inner owner seedAddress
    (PV_EVH_StackAdmission.enter (fieldSlot owner fieldAddress w) (List.replicate 32 0) w)

theorem fresh_live_and_retired (owner address : Nat) (w : State)
    (old : Slot) (ho : old ∈ w.frame.live ++ w.frame.retired) :
    old.key ≠ (inner owner address w).key := by
  intro he
  have hi := PV_EVH_EntropySourceSlot.identity_lt _ old ho
  have hk := congrArg PV_EVH_HeapOwnership.Key.identity he
  change old.key.identity = frontier (w.frame.live ++ w.frame.retired) at hk
  omega

theorem field_seed_distinct (owner fieldAddress seedAddress : Nat) (w : State) :
    (fieldSlot owner fieldAddress w).key ≠ (seedSlot owner fieldAddress seedAddress w).key := by
  exact fresh_live_and_retired owner seedAddress
    (PV_EVH_StackAdmission.enter (fieldSlot owner fieldAddress w) (List.replicate 32 0) w)
    (fieldSlot owner fieldAddress w) (by simp [PV_EVH_StackAdmission.enter])

theorem old_distinct (owner fieldAddress seedAddress : Nat) (w : State)
    (old : Slot) (ho : old ∈ w.frame.live) :
    old.key ≠ (fieldSlot owner fieldAddress w).key ∧
    old.key ≠ (seedSlot owner fieldAddress seedAddress w).key := by
  constructor
  · exact fresh_live_and_retired owner fieldAddress w old (List.mem_append_left _ ho)
  · exact fresh_live_and_retired owner seedAddress
      (PV_EVH_StackAdmission.enter (fieldSlot owner fieldAddress w) (List.replicate 32 0) w)
      old (by
        change old ∈ (fieldSlot owner fieldAddress w :: w.frame.live) ++ w.frame.retired
        exact List.mem_append_left _ (List.mem_cons_of_mem _ ho))

theorem live_order (owner fieldAddress seedAddress : Nat) (w : State) :
    (PV_EVH_EntropyPhysicalCopy.admit_pair (fieldSlot owner fieldAddress w)
      (seedSlot owner fieldAddress seedAddress w) w).frame.live =
      seedSlot owner fieldAddress seedAddress w :: fieldSlot owner fieldAddress w :: w.frame.live := rfl

/-- Both extents are derived; numeric separation and initialized-byte
interpretation are intentionally not inferred from these ghost facts. -/
theorem extents (owner fieldAddress seedAddress : Nat) (w : State) :
    (fieldSlot owner fieldAddress w).initialized = 32 ∧
    (seedSlot owner fieldAddress seedAddress w).initialized = 32 := ⟨rfl,rfl⟩

#print axioms fresh_live_and_retired
#print axioms field_seed_distinct
#print axioms old_distinct
#print axioms live_order
#print axioms extents
end PV_EVH_EntropyInnerFrame
