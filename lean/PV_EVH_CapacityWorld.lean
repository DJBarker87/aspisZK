import PV_EVH_AllocatorWorld
import PV_EVH_RuntimePublishCompact
set_option autoImplicit false
noncomputable section
namespace PV_EVH_CapacityWorld
open Aeneas Aeneas.Std ProverRwFull PV_EVH_Runtime PV_EVH_AllocatorWorld
open PV_RJ4IDB (Bytes NativeEvent)

/-- Natural arithmetic for the checked allocation-size branch. Binding
maxBytes/element size/alignment to Rust Layout::repeat/isize::MAX, including
valid layout padding, remains explicit source-binding work. -/
def layoutFor (elementSize alignment maxBytes : Nat) (capacity : Usize) : Except Unit Layout :=
  if elementSize * capacity.val ≤ maxBytes then
    .ok ⟨elementSize * capacity.val,alignment⟩
  else .error ()

def overflow {A : Type} (diagnostics : List NativeEvent) : Q A := fun w =>
  ⟨.fault (.panic [99,97,112,97,99,105,116,121]),w,diagnostics⟩

/-- The source vector is an extensional projection produced AFTER allocation.
Its backing identity/address/ownership survives in State.heap. This model does
not establish native vector ownership/initialization, drop or pointer fidelity.
The runtime failure branches are included, never excluded by a pure-value view. -/
def withCapacity (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (elementSize alignment maxBytes owner : Nat)
    (overflowDiagnostics oomDiagnostics : List NativeEvent)
    (T : Type) (capacity : Usize) : Q (alloc.vec.Vec T) :=
  match layoutFor elementSize alignment maxBytes capacity with
  | .error _ => overflow overflowDiagnostics
  | .ok layout =>
    if layout.size = 0 then lift (.ok (alloc.vec.Vec.with_capacity T capacity))
    else do
      let _ ← allocateOrFault allocator encode layout owner oomDiagnostics
      pure (alloc.vec.Vec.with_capacity T capacity)

theorem zero_layout (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (elementSize alignment maxBytes owner : Nat) (overflowDiagnostics oomDiagnostics : List NativeEvent)
    (T : Type) (capacity : Usize) (layout : Layout)
    (hl : layoutFor elementSize alignment maxBytes capacity = .ok layout)
    (hz : layout.size = 0) (w : State) :
    withCapacity allocator encode elementSize alignment maxBytes owner
      overflowDiagnostics oomDiagnostics T capacity w =
      ⟨.returned (.ok (alloc.vec.Vec.with_capacity T capacity)),w,[]⟩ := by
  simp only [withCapacity,hl,hz,if_true]
  rfl

theorem capacity_view (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (elementSize alignment maxBytes owner : Nat) (overflowDiagnostics oomDiagnostics : List NativeEvent)
    (T : Type) (capacity : Usize) :
    PartialView (withCapacity allocator encode elementSize alignment maxBytes owner
      overflowDiagnostics oomDiagnostics T capacity) (.ok (alloc.vec.Vec.with_capacity T capacity)) := by
  intro w r hs
  unfold withCapacity at hs
  cases hl : layoutFor elementSize alignment maxBytes capacity with
  | error e =>
    simp only [hl,overflow,sourceProjection] at hs
    cases hs
  | ok layout =>
    by_cases hz : layout.size = 0
    · simp only [hl,hz,if_true,PV_EVH_Runtime.lift,sourceProjection] at hs
      exact Option.some.inj hs
    · simp only [hl,hz,if_false,allocateOrFault,Bind.bind,PV_EVH_Runtime.bind,tryAllocate] at hs
      cases ha : (allocator w layout).answer with
      | denied =>
        simp only [ha,allocationFault,sourceProjection] at hs
        cases hs
      | allocated address backing =>
        simp only [ha,Pure.pure,PV_EVH_Runtime.lift,sourceProjection] at hs
        exact Option.some.inj hs

theorem allocator_failure (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (elementSize alignment maxBytes owner : Nat) (overflowDiagnostics oomDiagnostics : List NativeEvent)
    (T : Type) (capacity : Usize) (layout : Layout) (w : State)
    (hl : layoutFor elementSize alignment maxBytes capacity = .ok layout)
    (hz : layout.size ≠ 0) (ha : (allocator w layout).answer = .denied) :
    let run := withCapacity allocator encode elementSize alignment maxBytes owner
      overflowDiagnostics oomDiagnostics T capacity w
    run.outcome = .fault (.allocationDenied layout) ∧
    run.state.heap = w.heap ∧ run.state.errno = (allocator w layout).errno ∧
    run.events = [event encode (.request layout),
      event encode (.denied layout (allocator w layout).errno)] ++ oomDiagnostics ∧
    sourceProjection run.outcome = none := by
  simp only [withCapacity,hl,hz,if_false,allocateOrFault,Bind.bind,PV_EVH_Runtime.bind,
    tryAllocate,ha,allocationFault,sourceProjection,and_self]

#print axioms zero_layout
#print axioms capacity_view
#print axioms allocator_failure
end PV_EVH_CapacityWorld
