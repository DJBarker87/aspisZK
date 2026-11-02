import PV_EVH_OwnedCapacity
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OwnedCapacityFaults
open Aeneas Aeneas.Std ProverRwFull PV_EVH_Runtime PV_EVH_AllocatorWorld
open PV_RJ4IDB (Bytes NativeEvent)

theorem denied_no_source_vector (system : Allocator) (encode : AllocationEvent → Bytes)
    (writer : PV_EVH_LiteralDiagnostics.Writer) (abortEvents : List NativeEvent)
    (size align usizeMax isizeMax owner : Nat) (T : Type) (capacity : Usize)
    (layout : Layout) (w : State)
    (hl : PV_EVH_LayoutRepeat.layoutArray size align usizeMax isizeMax capacity.val = .ok layout)
    (hz : layout.size ≠ 0) (ha : (system w layout).answer = .denied) :
    let run := PV_EVH_OwnedCapacity.withCapacity system encode writer abortEvents
      size align usizeMax isizeMax owner T capacity w
    run.outcome = .fault (.abort []) ∧ run.state.heap = w.heap ∧
    run.state.errno = (system w layout).errno ∧
    run.events = [event encode (.request layout),
      event encode (.denied layout (system w layout).errno)] ++ abortEvents ∧
    sourceProjection run.outcome = none := by
  simp only [PV_EVH_OwnedCapacity.withCapacity,hl,hz,if_false,
    PV_EVH_ClientAllocator.allocate,Bind.bind,PV_EVH_Runtime.bind,tryAllocate,ha,
    PV_EVH_ClientAllocator.abortNull,sourceProjection,and_self]

theorem overflow_hook_fault (system : Allocator) (encode : AllocationEvent → Bytes)
    (writer : PV_EVH_LiteralDiagnostics.Writer) (abortEvents : List NativeEvent)
    (size align usizeMax isizeMax owner : Nat) (T : Type) (capacity : Usize)
    (w : State) (fault : Fault)
    (hl : PV_EVH_LayoutRepeat.layoutArray size align usizeMax isizeMax capacity.val = .error ())
    (hh : (PV_EVH_LiteralDiagnostics.panicHook writer w).outcome = .fault fault) :
    PV_EVH_OwnedCapacity.withCapacity system encode writer abortEvents
      size align usizeMax isizeMax owner T capacity w =
      ⟨.fault fault,(PV_EVH_LiteralDiagnostics.panicHook writer w).state,
        (PV_EVH_LiteralDiagnostics.panicHook writer w).events⟩ := by
  simp only [PV_EVH_OwnedCapacity.withCapacity,hl]
  exact PV_EVH_ClientRuntimeFault.hook_fault_prefix writer abortEvents w fault hh

#print axioms denied_no_source_vector
#print axioms overflow_hook_fault
end PV_EVH_OwnedCapacityFaults
