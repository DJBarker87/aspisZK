import PV_EVH_HeapOwnership
set_option autoImplicit false
namespace PV_EVH_AllocationOwnership
open PV_EVH_Runtime PV_EVH_AllocatorWorld PV_EVH_HeapOwnership
open PV_RJ4IDB (Bytes)

/-- Allocation initializes NO source elements, regardless of backing bytes. -/
def emptyView (w : State) (layout : Layout) (owner : Nat) : View :=
  ⟨⟨w.nextIdentity,owner⟩,[],layout.size⟩

theorem allocated_empty_owner (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner address : Nat) (backing : Bytes) (w : State)
    (ha : (allocator w layout).answer = .allocated address backing)
    (hv : ValidAnswer w layout (allocator w layout)) :
    let b : Block := ⟨w.nextIdentity,address,layout,backing,owner⟩
    Owns (tryAllocate allocator encode layout owner w).state.heap
      (emptyView w layout owner) b := by
  have hlen : backing.length = layout.size := by
    rw [ValidAnswer,ha] at hv
    exact hv.2.2.2.1
  change Owns (tryAllocate allocator encode layout owner w).state.heap
    (emptyView w layout owner) _
  simp only [tryAllocate,ha]
  exact ⟨List.mem_cons_self, rfl, rfl, rfl, hlen, Nat.zero_le _, rfl⟩

theorem allocated_unique_heap (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner address : Nat) (backing : Bytes) (w : State)
    (ha : (allocator w layout).answer = .allocated address backing)
    (hv : ValidAnswer w layout (allocator w layout)) (hu : UniqueHeap w.heap) :
    UniqueHeap (tryAllocate allocator encode layout owner w).state.heap := by
  rw [ValidAnswer,ha] at hv
  simp only [tryAllocate,ha]
  exact fresh_allocation_unique w.heap _ hu (fun b hb => (hv.2.2.2.2 b hb).1)

theorem old_owner_survives_allocation (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner address : Nat) (backing : Bytes) (w : State)
    (ha : (allocator w layout).answer = .allocated address backing)
    (v : View) (b : Block) (hv : Owns w.heap v b) :
    Owns (tryAllocate allocator encode layout owner w).state.heap v b := by
  simp only [tryAllocate,ha]
  exact allocation_preserves_ownership w.heap v b _ hv

/-- The stateful allocator's denial cannot create an initialized source region. -/
theorem denied_preserves_owner (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner : Nat) (w : State)
    (ha : (allocator w layout).answer = .denied)
    (v : View) (b : Block) (hv : Owns w.heap v b) :
    Owns (tryAllocate allocator encode layout owner w).state.heap v b := by
  simp only [tryAllocate,ha]
  exact hv

#print axioms allocated_empty_owner
#print axioms allocated_unique_heap
#print axioms old_owner_survives_allocation
#print axioms denied_preserves_owner
end PV_EVH_AllocationOwnership
