import PV_STX2_OwnerAllocationWellFormed
set_option autoImplicit false
/-! All statements are conditional on owner acceptance of the translator patch. -/
noncomputable section
namespace PV_STX2_OwnerAllocationReferenceValid
open PV_EVHB_OWNER PV_EVHB_RawVecOwner
/-- LOG D918: allocation bases in the ghost heap are non-null as well as
aligned. A null native answer never executes allocation registration. -/
def AllocationNonnull (s : OWNER) : Prop :=
  ∀ pointer allocation, s.world.allocator.metadata pointer = some allocation → pointer ≠ 0
structure OwnerWellFormed (s : OWNER) (counter : Nat) : Prop where
  previous : PV_STX2_OwnerAllocationWellFormed.OwnerWellFormed s counter
  nonnull : AllocationNonnull s

theorem initial (s : OWNER) (counter : Nat)
    (aligned : PV_STX2_OwnerAllocationWellFormed.AllocationAligned s)
    (nonnull : AllocationNonnull s) :
    OwnerWellFormed (PV_EVHB_SourceLifetimes.start s.world) counter :=
  ⟨PV_STX2_OwnerAllocationWellFormed.initial s counter aligned,nonnull⟩
theorem empty (s : OWNER) (absent : ∀ p, s.world.allocator.metadata p = none) :
    AllocationNonnull s := by
  intro p allocation selected
  rw [absent p] at selected
  cases selected
theorem preserved {A : Type} (action : PV_EVHB_OwnerMachine.Request A)
    (s : OWNER) (counter : Nat) (wf : OwnerWellFormed s counter)
    (allocated : PV_STX2_OwnerActivationWellFormed.AllocatedTarget counter action) :
    OwnerWellFormed (PV_EVHB_OwnerMachine.handler action s).world counter := by
  refine ⟨PV_STX2_OwnerAllocationWellFormed.preserved action s counter wf.previous allocated,?_⟩
  cases action <;> exact wf.nonnull
theorem mono {s : OWNER} {before after : Nat} (wf : OwnerWellFormed s before)
    (le : before ≤ after) : OwnerWellFormed s after :=
  ⟨PV_STX2_OwnerAllocationWellFormed.mono wf.previous le,wf.nonnull⟩
theorem withWorld (s : OWNER) (counter : Nat) (wf : OwnerWellFormed s counter)
    (backend : PV_STX_World.World) :
    OwnerWellFormed (PV_EVHB_OwnerMachine.withWorld s backend) counter :=
  ⟨PV_STX2_OwnerAllocationWellFormed.withWorld s counter wf.previous backend,wf.nonnull⟩
theorem copied (s : OWNER) (counter : Nat) (wf : OwnerWellFormed s counter)
    (source target bytes : Nat) :
    OwnerWellFormed (PV_EVHB_OwnerHeap.copied s source target bytes) counter :=
  ⟨PV_STX2_OwnerAllocationWellFormed.copied s counter wf.previous source target bytes,wf.nonnull⟩
theorem addAllocation (s : OWNER) (counter owner pointer bytes : Nat) (h : Header)
    (zeroed : Bool) (wf : OwnerWellFormed s counter) (nonnull : pointer ≠ 0)
    (aligned : pointer % PV_EVHB_OwnerReserve.alignment h.shape.align = 0) :
    OwnerWellFormed (PV_EVHB_OwnerHeap.addAllocation s owner pointer bytes h zeroed) counter := by
  refine ⟨PV_STX2_OwnerAllocationWellFormed.addAllocation s counter owner pointer bytes h zeroed wf.previous aligned,?_⟩
  intro p allocation selected
  change (if p = pointer then some ⟨bytes,h.shape.align⟩ else
    s.world.allocator.metadata p) = some allocation at selected
  split at selected
  · next same => subst p; exact nonnull
  · exact wf.nonnull p allocation selected
theorem freeAllocation (s : OWNER) (counter pointer : Nat) (wf : OwnerWellFormed s counter) :
    OwnerWellFormed (PV_EVHB_OwnerHeap.freeAllocation s pointer) counter := by
  refine ⟨PV_STX2_OwnerAllocationWellFormed.freeAllocation s counter pointer wf.previous,?_⟩
  intro p allocation selected
  change (if p = pointer then none else s.world.allocator.metadata p) = some allocation at selected
  split at selected
  · cases selected
  · exact wf.nonnull p allocation selected
theorem owned_valid {s : OWNER} {counter : Nat} (wf : OwnerWellFormed s counter)
    (h : Header) (metadata : s.world.allocator.metadata h.pointer = some (layout h h.cap)) :
    h.pointer ≠ 0 ∧ h.pointer % PV_EVHB_OwnerReserve.alignment h.shape.align = 0 :=
  ⟨wf.nonnull _ _ metadata,PV_STX2_OwnerAllocationWellFormed.owned_alignment wf.previous h metadata⟩
#print axioms AllocationNonnull
#print axioms OwnerWellFormed
#print axioms initial
#print axioms empty
#print axioms preserved
#print axioms mono
#print axioms withWorld
#print axioms copied
#print axioms addAllocation
#print axioms freeAllocation
#print axioms owned_valid
end PV_STX2_OwnerAllocationReferenceValid
