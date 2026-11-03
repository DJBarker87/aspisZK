import PV_EVH_Runtime
import R1Z.PV_RunJoin_AllocatorWorld63
set_option autoImplicit false
noncomputable section
namespace PV_EVHB_ReserveWorld
open Aeneas Aeneas.Std ProverRwFull PV_EVH_Runtime
open PV_RJ4IDB (Bytes NativeEvent)
open R1Z.PV_FXM_ReserveWorld
variable [ExternalTypes]

inductive Observation where
  | allocator (event : R1Z.PV_FXM_ReserveWorld.Event)
  | completed (result : Except R1Z.PV_FXM_ReserveWorld.Error Unit)

abbrev Runtime (S : Type) := R1Z.PV_RunJoin_AllocatorWorld63.Runtime S State

def events {T S : Type} (encode : Observation → Bytes)
    (before : World S State) (e : Execution T S State) : List NativeEvent :=
  ((e.world.history.drop before.history.length).map
    (fun h => NativeEvent.side [114,101,115,101,114,118,101] (encode (.allocator h)))) ++
  [.side [114,101,115,101,114,118,101] (encode (.completed e.returned))]

/-- The V183 world is returned to the continuation on BOTH Ok and Err. Its
frame is the current event-world state, not a reset snapshot. Metadata, allocator
private state and logical physical memory are retained separately. Their native
same-memory association and encoding fidelity remain runtime P obligations. -/
def reserve {T S : Type} (runtime : Runtime S) (encode : Observation → Bytes)
    (world : World S State) (v : alloc.vec.Vec T) (n : Usize) :
    Q ((core.result.Result Unit alloc.collections.TryReserveError × alloc.vec.Vec T) ×
      World S State) := fun state =>
  let before := {world with frame := state}
  let e := R1Z.PV_RunJoin_AllocatorWorld63.execute runtime before v n
  ⟨.returned (.ok ((R1Z.PV_FXM_ReserveSelected.returned runtime.encode e.returned,v),e.world)),
    e.world.frame,events encode before e⟩

/-- Exact source Result at the same world-indexed selected dictionary; neither
allocation success nor a pure callback result is an input. -/
theorem selected_result {T S : Type} (runtime : Runtime S) (encode : Observation → Bytes)
    (ops : ExternalFuns) (world : World S State) (v : alloc.vec.Vec T) (n : Usize)
    (Allocator : Type) (state : State) :
    let before := {world with frame := state}
    let e := R1Z.PV_RunJoin_AllocatorWorld63.execute runtime before v n
    @alloc.vec.Vec.try_reserve_exact _
      (R1Z.PV_RunJoin_AllocatorWorld63.selectedAt runtime ops before) T Allocator v n =
      .ok (R1Z.PV_FXM_ReserveSelected.returned runtime.encode e.returned,v) ∧
    (reserve runtime encode world v n state).outcome =
      .returned (.ok ((R1Z.PV_FXM_ReserveSelected.returned runtime.encode e.returned,v),e.world)) := by
  exact ⟨R1Z.PV_RunJoin_AllocatorWorld63.complete runtime ops _ Allocator v n,rfl⟩

/-- All continuation outcomes propagate under the original Runtime.bind;
this includes fail/div, faults and exhausted, with the exact reserve prefix. -/
theorem continuation {T S A : Type} (runtime : Runtime S) (encode : Observation → Bytes)
    (world : World S State) (v : alloc.vec.Vec T) (n : Usize)
    (caller : (core.result.Result Unit alloc.collections.TryReserveError × alloc.vec.Vec T) →
      World S State → Q A) (state : State) :
    let before := {world with frame := state}
    let e := R1Z.PV_RunJoin_AllocatorWorld63.execute runtime before v n
    let r := caller (R1Z.PV_FXM_ReserveSelected.returned runtime.encode e.returned,v) e.world e.world.frame
    PV_EVH_Runtime.bind (reserve runtime encode world v n)
      (fun p => caller p.1 p.2) state =
      ⟨r.outcome,r.state,events encode before e ++ r.events⟩ := rfl

/-- Public metadata equality suffices for identical request, denial/overflow,
address, memory and allocator histories. Secret ELEMENT VALUES are not read by
V183. Equal public metadata/initial world and a shared allocator are required;
this does not infer witness-independence of those premises or of later calls. -/
theorem public_metadata {T U S F : Type}
    (step : Request → S → Option Nat × S) (wordMax byteMax : Nat) (shape : Shape)
    (b : Buffer T) (c : Buffer U) (n : Nat) (w : World S F)
    (address : b.address = c.address) (capacity : b.capacity = c.capacity)
    (length : b.values.length = c.values.length) :
    (native step wordMax byteMax shape b n w).returned =
      (native step wordMax byteMax shape c n w).returned ∧
    (native step wordMax byteMax shape b n w).world =
      (native step wordMax byteMax shape c n w).world := by
  unfold native growExact finish
  simp only [address,capacity,length]
  split <;> try exact ⟨rfl,rfl⟩
  split <;> try exact ⟨rfl,rfl⟩
  split <;> try exact ⟨rfl,rfl⟩
  split <;> try exact ⟨rfl,rfl⟩
  try dsimp only
  cases step ⟨c.address,c.capacity,c.values.length+n,shape⟩ w.allocator with
  | mk p s => cases p <;> exact ⟨rfl,rfl⟩

/-- Failed allocation retains the allocator's NEW private state, while keeping
old logical memory and live allocation map. This is not an adequacy assumption. -/
theorem denied_effects {T S F : Type}
    (step : Request → S → Option Nat × S) (shape : Shape) (b : Buffer T)
    (n : Nat) (w : World S F) (s : S)
    (denied : step ⟨b.address,b.capacity,b.values.length+n,shape⟩ w.allocator = (none,s)) :
    (finish step shape b n w).returned =
        .error (.allocError ⟨usize ((b.values.length+n)*shape.width),shape.align⟩) ∧
    (finish step shape b n w).world.allocator = s ∧
    (finish step shape b n w).world.memory = w.memory ∧
    (finish step shape b n w).world.live = w.live := by
  have h := allocation_error step shape b n w s denied
  exact ⟨h.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩

#print axioms selected_result
#print axioms continuation
#print axioms public_metadata
#print axioms denied_effects
end PV_EVHB_ReserveWorld
