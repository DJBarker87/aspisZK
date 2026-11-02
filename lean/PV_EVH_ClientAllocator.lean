import PV_EVH_AllocationOwnership
set_option autoImplicit false
namespace PV_EVH_ClientAllocator
open Aeneas Aeneas.Std PV_EVH_Runtime PV_EVH_AllocatorWorld
open PV_RJ4IDB (Bytes NativeEvent)

/-- D474(C) diagnostics.rs aborts inside the global allocator on System null,
before the pointer can reach std's size-formatting alloc_error_handler.
External abort/crash observations are a retained event input, never silence. -/
def abortNull {A : Type} (abortEvents : List NativeEvent) : Q A := fun w =>
  ⟨.fault (.abort []),w,abortEvents⟩

def allocate (system : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner : Nat) (abortEvents : List NativeEvent) : Q Block := do
  let result ← tryAllocate system encode layout owner
  match result with
  | some block => pure block
  | none => abortNull abortEvents

theorem null_aborts_before_return (system : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner : Nat) (abortEvents : List NativeEvent) (w : State)
    (h : (system w layout).answer = .denied) :
    let run := allocate system encode layout owner abortEvents w
    run.outcome = .fault (.abort []) ∧
    run.state.heap = w.heap ∧ run.state.allocator = (system w layout).allocator ∧
    run.state.errno = (system w layout).errno ∧
    run.events = [event encode (.request layout),
      event encode (.denied layout (system w layout).errno)] ++ abortEvents ∧
    sourceProjection run.outcome = none := by
  simp only [allocate,Bind.bind,PV_EVH_Runtime.bind,tryAllocate,h,abortNull,
    sourceProjection,and_self]

theorem success_returns_system_block (system : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner address : Nat) (backing : Bytes)
    (abortEvents : List NativeEvent) (w : State)
    (h : (system w layout).answer = .allocated address backing) :
    let block : Block := ⟨w.nextIdentity,address,layout,backing,owner⟩
    (allocate system encode layout owner abortEvents w).outcome = .returned (.ok block) ∧
    (allocate system encode layout owner abortEvents w).state.heap = block :: w.heap ∧
    (allocate system encode layout owner abortEvents w).events =
      [event encode (.request layout),
        event encode (.allocated layout w.nextIdentity address (system w layout).errno)] := by
  simp only [allocate,Bind.bind,PV_EVH_Runtime.bind,tryAllocate,h,Pure.pure,
    PV_EVH_Runtime.lift,List.append_nil,and_self]

#print axioms null_aborts_before_return
#print axioms success_returns_system_block
end PV_EVH_ClientAllocator
