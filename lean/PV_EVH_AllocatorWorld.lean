import PV_EVH_Runtime
set_option autoImplicit false
namespace PV_EVH_AllocatorWorld
open Aeneas Aeneas.Std PV_EVH_Runtime
open PV_RJ4IDB (Bytes NativeEvent)

/-- Physical backing bytes, not evidence of Rust initialization. Safe reads,
initialized regions, borrow restoration and zeroization need separate laws. -/
inductive Answer where
  | denied
  | allocated (address : Nat) (backing : Bytes)

structure Reply where
  answer : Answer
  allocator : Bytes
  errno : Int

/-- The allocator sees the entire WORLD, including its retained allocator,
heap, address, ownership and errno state. No pure-value answer is used. -/
abbrev Allocator := State → Layout → Reply

inductive AllocationEvent where
  | request (layout : Layout)
  | denied (layout : Layout) (errno : Int)
  | allocated (layout : Layout) (identity address : Nat) (errno : Int)

def event (encode : AllocationEvent → Bytes) (e : AllocationEvent) : NativeEvent :=
  .side [97,108,108,111,99] (encode e)

/-- Injectivity prevents a codec from hiding the modeled metadata. Native
observation/source association is still a separate, unproved P obligation. -/
def FaithfulEncoding (encode : AllocationEvent → Bytes) : Prop := Function.Injective encode

def tryAllocate (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner : Nat) : Q (Option Block) := fun w =>
  let reply := allocator w layout
  let post : State := {w with
    allocator := reply.allocator
    errno := reply.errno
    base := {w.base with allocations := w.base.allocations + 1}}
  match reply.answer with
  | .denied => ⟨.returned (.ok none),post,
      [event encode (.request layout),event encode (.denied layout reply.errno)]⟩
  | .allocated address backing =>
    let block : Block := ⟨w.nextIdentity,address,layout,backing,owner⟩
    ⟨.returned (.ok (some block)),
      {post with heap := block :: w.heap, nextIdentity := w.nextIdentity + 1},
      [event encode (.request layout),
        event encode (.allocated layout w.nextIdentity address reply.errno)]⟩

/-- Heap layout and allocator properties are stated on the stateful answer.
They have not been established for the deployed allocator. -/
def ValidAnswer (w : State) (layout : Layout) (reply : Reply) : Prop :=
  match reply.answer with
  | .denied => True
  | .allocated address backing =>
    0 < layout.align ∧ address % layout.align = 0 ∧ address ≠ 0 ∧
    backing.length = layout.size ∧
    (∀ b ∈ w.heap, b.identity ≠ w.nextIdentity ∧
      (address + layout.size ≤ b.address ∨ b.address + b.layout.size ≤ address))

theorem denied_retains_heap (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner : Nat) (w : State)
    (h : (allocator w layout).answer = .denied) :
    (tryAllocate allocator encode layout owner w).outcome = .returned (.ok none) ∧
    (tryAllocate allocator encode layout owner w).state.heap = w.heap ∧
    (tryAllocate allocator encode layout owner w).state.errno = (allocator w layout).errno ∧
    (tryAllocate allocator encode layout owner w).state.allocator = (allocator w layout).allocator ∧
    (tryAllocate allocator encode layout owner w).events =
      [event encode (.request layout),event encode (.denied layout (allocator w layout).errno)] := by
  simp only [tryAllocate,h]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem allocated_installs_block (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner address : Nat) (backing : Bytes) (w : State)
    (h : (allocator w layout).answer = .allocated address backing) :
    let block : Block := ⟨w.nextIdentity,address,layout,backing,owner⟩
    (tryAllocate allocator encode layout owner w).outcome = .returned (.ok (some block)) ∧
    (tryAllocate allocator encode layout owner w).state.heap = block :: w.heap ∧
    (tryAllocate allocator encode layout owner w).state.nextIdentity = w.nextIdentity + 1 := by
  simp only [tryAllocate,h]
  exact ⟨rfl,rfl,rfl⟩

/-- Unchecked allocation failure handling is a runtime fault in the world,
with an explicitly supplied diagnostic prefix. Formatting/source binding OPEN. -/
def allocationFault {A : Type} (layout : Layout) (diagnostics : List NativeEvent) : Q A :=
  fun w => ⟨.fault (.allocationDenied layout),w,diagnostics⟩

def allocateOrFault (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner : Nat) (diagnostics : List NativeEvent) : Q Block := do
  let result ← tryAllocate allocator encode layout owner
  match result with
  | some block => pure block
  | none => allocationFault layout diagnostics

theorem failure_world_prefix (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner : Nat) (diagnostics : List NativeEvent) (w : State)
    (h : (allocator w layout).answer = .denied) :
    let run := allocateOrFault allocator encode layout owner diagnostics w
    run.outcome = .fault (.allocationDenied layout) ∧
    run.state.heap = w.heap ∧ run.state.errno = (allocator w layout).errno ∧
    run.state.allocator = (allocator w layout).allocator ∧
    run.events = [event encode (.request layout),
      event encode (.denied layout (allocator w layout).errno)] ++ diagnostics ∧
    sourceProjection run.outcome = none := by
  simp only [allocateOrFault,Bind.bind,PV_EVH_Runtime.bind,tryAllocate,h,allocationFault,sourceProjection]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms denied_retains_heap
#print axioms allocated_installs_block
#print axioms failure_world_prefix
end PV_EVH_AllocatorWorld
