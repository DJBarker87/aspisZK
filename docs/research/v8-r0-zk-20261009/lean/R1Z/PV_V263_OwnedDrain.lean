import R1Z.PV_V263_AppendBinding
/-! Typed initialized memory and owned RawVec allocation metadata. Reservations
are lower bounds on the capacity derived from the allocation, not equalities.
The pointer token is retained through drain and used by deallocation. A native
heap interpretation and disjointness of simultaneous owners remain required. -/
set_option autoImplicit false
namespace R1Z.PV_V263_OwnedDrain
open Aeneas Aeneas.Std PV_V263_VectorDrain
abbrev Layout := PV_V263_PublicRequests.Layout

structure Allocation where
  pointer : Nat
  rawCapacity : Nat
  layout : Layout
  bounded : rawCapacity ≤ Usize.max

def capacity (allocation : Allocation) : Nat :=
  if allocation.layout.size=0 then Usize.max else allocation.rawCapacity

theorem capacity_bound (allocation : Allocation) : capacity allocation ≤ Usize.max := by
  unfold capacity
  split
  · exact Nat.le_refl _
  · exact allocation.bounded

structure Owner (A : Type) where
  initialized : Buffer A
  allocation : Allocation
  reserved : initialized.capacity ≤ capacity allocation

/-- The underlying allocation, not the initialized length, determines drop's
layout. In particular, draining to zero does not free or shrink the donor. -/
def release (allocation : Allocation) : Option (Nat × Nat × Nat) :=
  if allocation.layout.size=0 ∨ allocation.rawCapacity=0 then none
  else some (allocation.pointer,allocation.layout.size*allocation.rawCapacity,
    allocation.layout.align)

def drain {A : Type} (out source : Owner A)
    (room : out.initialized.values.length+source.initialized.values.length ≤ out.initialized.capacity) :
    Owner A × Owner A :=
  let stored := PV_V263_VectorDrain.drain out.initialized source.initialized room
  (⟨stored.1,out.allocation,out.reserved⟩,
   ⟨stored.2,source.allocation,source.reserved⟩)

theorem ownership {A : Type} (out source : Owner A)
    (room : out.initialized.values.length+source.initialized.values.length ≤ out.initialized.capacity) :
    (drain out source room).1.allocation=out.allocation ∧
    (drain out source room).2.allocation=source.allocation ∧
    (drain out source room).2.initialized.values.length=0 ∧
    release (drain out source room).2.allocation=release source.allocation :=
  ⟨rfl,rfl,rfl,rfl⟩

/-- Even if the physical allocation exceeds the retained lower bound, native
reserve's wrapping subtraction is ordinary subtraction and cannot grow. -/
theorem no_physical_growth {A : Type} (out source : Owner A)
    (room : out.initialized.values.length+source.initialized.values.length ≤ out.initialized.capacity) :
    ¬ source.initialized.values.length >
      PV_V263_AppendBinding.wrappedRemaining (capacity out.allocation) out.initialized.values.length := by
  let physical : Buffer A := ⟨out.initialized.values,capacity out.allocation,
    out.initialized.fits.trans out.reserved,capacity_bound out.allocation⟩
  exact PV_V263_AppendBinding.reserve_no_growth physical source.initialized (room.trans out.reserved)

theorem empty_donor_release {A : Type} (out source : Owner A)
    (room : out.initialized.values.length+source.initialized.values.length ≤ out.initialized.capacity)
    (sized : source.allocation.layout.size≠0) (allocated : source.allocation.rawCapacity≠0) :
    release (drain out source room).2.allocation=
      some (source.allocation.pointer,
        source.allocation.layout.size*source.allocation.rawCapacity,source.allocation.layout.align) := by
  simp only [drain,release,sized,allocated,or_self,if_false]

#print axioms Allocation
#print axioms capacity
#print axioms capacity_bound
#print axioms Owner
#print axioms release
#print axioms drain
#print axioms ownership
#print axioms no_physical_growth
#print axioms empty_donor_release
end R1Z.PV_V263_OwnedDrain
