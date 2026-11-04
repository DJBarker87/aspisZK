import PV_STX_World
set_option autoImplicit false
namespace PV_STX_AllocatorWorld
open Aeneas Aeneas.Std PV_STX_Code PV_STX_Machine PV_STX_World
open PV_RJ4IDB (Bytes NativeEvent)
inductive AllocationAnswer where
  | denied
  | allocated (address : Nat) (backing : Bytes)
structure AllocationReply where
  answer : AllocationAnswer
  allocator : Bytes
  errno : Int
abbrev Allocator := World → Layout → AllocationReply
inductive AllocationEvent where
  | request (layout : Layout)
  | denied (layout : Layout) (errno : Int)
  | allocated (layout : Layout) (identity address : Nat) (errno : Int)
def event (encode : AllocationEvent → Bytes) (e : AllocationEvent) : NativeEvent :=
  side "alloc" (encode e)

/-- Port from evhB's PV_EVH_AllocatorWorld: same post-allocator state on
success AND denial. No adequacy promise; no arbitrary effect suffix. -/
def tryAllocate (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner : Nat) (w : World) : Reply World NativeEvent (Option Block) :=
  let reply := allocator w layout
  let post : World := {w with allocator := reply.allocator
    errno := reply.errno
    base := {w.base with allocations := w.base.allocations+1}}
  match reply.answer with
  | .denied => ⟨.returned (.ok none),post,
      [event encode (.request layout),event encode (.denied layout reply.errno)]⟩
  | .allocated address backing =>
    let block : Block := ⟨w.nextIdentity,address,layout,backing,owner⟩
    ⟨.returned (.ok (some block)),
      {post with heap := block::w.heap,nextIdentity := w.nextIdentity+1},
      [event encode (.request layout),
       event encode (.allocated layout w.nextIdentity address reply.errno)]⟩

inductive Request : Type → Type 1 where
  | allocate (layout : Layout) (owner : Nat) : Request (Option Block)
  | abort : Request Block

def handler (allocator : Allocator) (encode : AllocationEvent → Bytes) :
    Handler Request World NativeEvent := fun op w => match op with
  | .allocate layout owner => tryAllocate allocator encode layout owner w
  | .abort => ⟨.fault .abort,w,[side "allocator-abort" []]⟩

/-- Reached null handling is a continuation in the same machine. Its exact
native diagnostic association is not inferred from allocation success laws. -/
def allocate (layout : Layout) (owner : Nat) : Code Request Block := do
  let out ← Code.call (.allocate layout owner)
  match out with | some block => pure block | none => Code.call .abort

theorem denied_prefix (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner : Nat) (w : World)
    (h : (allocator w layout).answer = .denied) :
    run (handler allocator encode) 3 (allocate layout owner) w =
      ⟨.fault .abort,
       {w with allocator := (allocator w layout).allocator
        errno := (allocator w layout).errno
        base := {w.base with allocations := w.base.allocations+1}},
       [event encode (.request layout),event encode (.denied layout (allocator w layout).errno),
        side "allocator-abort" []]⟩ := by
  simp only [allocate,run,advance,start,step,handler,tryAllocate,h,resumed,continueWith,
    List.nil_append,List.append_nil,List.cons_append,List.nil_append]

theorem allocated_frame (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (layout : Layout) (owner : Nat) (w : World) :
    (tryAllocate allocator encode layout owner w).world.base.files = w.base.files ∧
    (tryAllocate allocator encode layout owner w).world.base.entropyCursor = w.base.entropyCursor ∧
    (tryAllocate allocator encode layout owner w).world.handles = w.handles := by
  unfold tryAllocate
  cases (allocator w layout).answer <;> exact ⟨rfl,rfl,rfl⟩

#print axioms denied_prefix
#print axioms allocated_frame
end PV_STX_AllocatorWorld
