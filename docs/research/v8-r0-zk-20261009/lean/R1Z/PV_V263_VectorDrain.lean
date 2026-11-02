import R1Z.PV_V263_VectorLoop
/-! Explicit owned Vec stores for worker appends. Capacity is a lower bound,
not an invented exact physical allocation. Native heap/allocator lowering is
still required; the source vector is emptied before its destructor runs. -/
set_option autoImplicit false
namespace R1Z.PV_V263_VectorDrain
open Aeneas Aeneas.Std PV_V263_World

structure Buffer (A : Type) where
  values : alloc.vec.Vec A
  capacity : Nat
  fits : values.length ≤ capacity
  bounded : capacity ≤ Usize.max

def empty {A : Type} (capacity : Nat) (bound : capacity ≤ Usize.max) : Buffer A :=
  ⟨alloc.vec.Vec.new A,capacity,Nat.zero_le _,bound⟩

/-- An append with an adequate existing reservation does not allocate. Both
owned vectors are returned: the donor keeps its reservation and has length 0.
This is a source store model, not an Aeneas extraction of Vec::append. -/
def drain {A : Type} (out source : Buffer A)
    (room : out.values.length + source.values.length ≤ out.capacity) : Buffer A × Buffer A :=
  (⟨⟨out.values.val ++ source.values.val,by
      simpa only [List.length_append] using room.trans out.bounded⟩,
      out.capacity,by simpa only [alloc.vec.Vec.length,List.length_append] using room,out.bounded⟩,
   empty source.capacity source.bounded)

theorem drain_values {A : Type} (out source : Buffer A)
    (room : out.values.length + source.values.length ≤ out.capacity) :
    (drain out source room).1.values.val = out.values.val ++ source.values.val := rfl

theorem drain_length {A : Type} (out source : Buffer A)
    (room : out.values.length + source.values.length ≤ out.capacity) :
    (drain out source room).1.values.length = out.values.length + source.values.length := by
  exact List.length_append _ _

theorem drain_source {A : Type} (out source : Buffer A)
    (room : out.values.length + source.values.length ≤ out.capacity) :
    (drain out source room).2.values.val = [] ∧
    (drain out source room).2.capacity = source.capacity ∧
    (drain out source room).1.capacity = out.capacity := ⟨rfl,rfl,rfl⟩

/-- Runtime append at the current world, then stores, then donor destructor.
A method fault leaves the earlier world/events; it is not a source Result. -/
def appendDrop {S A : Type} (runtime : PV_V263_MapSpine.Runtime S)
    (layouts : PV_V263_MapSpine.Layouts) (site donorSite thread : Nat)
    (out source : Buffer A)
    (room : out.values.length + source.values.length ≤ out.capacity) : Q S (Buffer A) :=
  PV_V263_World.bind
    (runtime.vector (.append site thread out.values.length source.values.length layouts.item)) fun _ =>
    let stored := drain out source room
    PV_V263_World.bind (runtime.vector (.drop donorSite thread layouts.item)) fun _ =>
    lift (.ok stored.1)

/-- A successful method world constructs the drained output. No output vector
or callback success is supplied by the resource oracle. -/
theorem granting_appendDrop {S A : Type}
    (osCodec : {B : Type} → PV_V263_WorkerRequests.Request B → PV_RJ4IDB.Bytes)
    (vecCodec : PV_V263_MapSpine.VecCall → PV_RJ4IDB.Bytes)
    (layouts : PV_V263_MapSpine.Layouts) (site donorSite thread : Nat)
    (out source : Buffer A)
    (room : out.values.length + source.values.length ≤ out.capacity) (w : State S) :
    (appendDrop (PV_V263_GrantControl.resourceWorld osCodec vecCodec) layouts
      site donorSite thread out source room w).outcome = .returned (.ok (drain out source room).1) := rfl

#print axioms Buffer
#print axioms empty
#print axioms drain
#print axioms drain_values
#print axioms drain_length
#print axioms drain_source
#print axioms appendDrop
#print axioms granting_appendDrop
end R1Z.PV_V263_VectorDrain
