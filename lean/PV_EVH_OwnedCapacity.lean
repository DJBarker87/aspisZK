import PV_EVH_ClientRuntimeFault
import PV_EVH_LayoutRepeat
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OwnedCapacity
open Aeneas Aeneas.Std ProverRwFull PV_EVH_Runtime PV_EVH_AllocatorWorld
open PV_EVH_HeapOwnership
open PV_RJ4IDB (Bytes NativeEvent)

/-- Preserve storage identity alongside the extensional source Vec. None means
no allocation (including ZST); no dangling native pointer is fabricated here. -/
structure OwnedVec (T : Type) where
  source : alloc.vec.Vec T
  storage : Option View

def withCapacity (system : Allocator) (encode : AllocationEvent → Bytes)
    (writer : PV_EVH_LiteralDiagnostics.Writer) (abortEvents : List NativeEvent)
    (size align usizeMax isizeMax owner : Nat) (T : Type) (capacity : Usize) : Q (OwnedVec T) :=
  match PV_EVH_LayoutRepeat.layoutArray size align usizeMax isizeMax capacity.val with
  | .error _ => PV_EVH_ClientRuntimeFault.capacityOverflow writer abortEvents
  | .ok layout =>
    if layout.size = 0 then
      PV_EVH_Runtime.lift (.ok ⟨alloc.vec.Vec.with_capacity T capacity,none⟩)
    else do
      let block ← PV_EVH_ClientAllocator.allocate system encode layout owner abortEvents
      pure ⟨alloc.vec.Vec.with_capacity T capacity,
        some ⟨⟨block.identity,block.owner⟩,[],layout.size⟩⟩

theorem empty_initialization_with_identity (system : Allocator) (encode : AllocationEvent → Bytes)
    (writer : PV_EVH_LiteralDiagnostics.Writer) (abortEvents : List NativeEvent)
    (size align usizeMax isizeMax owner : Nat) (T : Type) (capacity : Usize)
    (layout : Layout) (address : Nat) (backing : Bytes) (w : State)
    (hl : PV_EVH_LayoutRepeat.layoutArray size align usizeMax isizeMax capacity.val = .ok layout)
    (hz : layout.size ≠ 0) (ha : (system w layout).answer = .allocated address backing)
    (hv : ValidAnswer w layout (system w layout)) :
    let view := PV_EVH_AllocationOwnership.emptyView w layout owner
    let block : Block := ⟨w.nextIdentity,address,layout,backing,owner⟩
    let run := withCapacity system encode writer abortEvents size align usizeMax isizeMax owner T capacity w
    run.outcome = .returned (.ok ⟨alloc.vec.Vec.with_capacity T capacity,some view⟩) ∧
    Owns run.state.heap view block := by
  have hown := PV_EVH_AllocationOwnership.allocated_empty_owner system encode layout owner address backing w ha hv
  simp only [withCapacity,hl,hz,if_false,PV_EVH_ClientAllocator.allocate,
    Bind.bind,PV_EVH_Runtime.bind,tryAllocate,ha,Pure.pure,PV_EVH_Runtime.lift,
    PV_EVH_AllocationOwnership.emptyView] at hown ⊢
  exact ⟨True.intro,hown⟩

theorem zero_size_no_allocator (system : Allocator) (encode : AllocationEvent → Bytes)
    (writer : PV_EVH_LiteralDiagnostics.Writer) (abortEvents : List NativeEvent)
    (size align usizeMax isizeMax owner : Nat) (T : Type) (capacity : Usize)
    (layout : Layout) (w : State)
    (hl : PV_EVH_LayoutRepeat.layoutArray size align usizeMax isizeMax capacity.val = .ok layout)
    (hz : layout.size = 0) :
    withCapacity system encode writer abortEvents size align usizeMax isizeMax owner T capacity w =
      ⟨.returned (.ok ⟨alloc.vec.Vec.with_capacity T capacity,none⟩),w,[]⟩ := by
  simp only [withCapacity,hl,hz,if_true,PV_EVH_Runtime.lift]

#print axioms empty_initialization_with_identity
#print axioms zero_size_no_allocator
end PV_EVH_OwnedCapacity
