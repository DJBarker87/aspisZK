import R1Z.PV_V263_BufferFamily
/-! Reservation-preserving methods for the outer worker stores. These are
source-store refinements, not a native allocator interpretation. A successful
reserve establishes a LOWER bound, never an invented exact physical capacity.
The old Vec-only view is recovered with every outcome/world/event unchanged. -/
set_option autoImplicit false
namespace R1Z.PV_V263_RetainedMethods
open Aeneas Aeneas.Std PV_V263_World PV_V263_VectorDrain PV_V263_BufferLoop
abbrev Runtime := PV_V263_VecSpine.Runtime
abbrev Layouts := PV_V263_MapSpine.Layouts

def push {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (site thread : Nat) (out : Buffer A) (a : A) : Q S (Buffer A) :=
  PV_V263_World.bind
    (runtime.methods.vector (.push site thread out.values.length layouts.item)) fun _ =>
    if bound : out.values.length+1 ≤ Usize.max then
      let next : Buffer A := ⟨⟨out.values.val++[a],by
        simpa only [List.length_append,List.length_singleton] using bound⟩,
        max out.capacity (out.values.length+1),by
          simp only [alloc.vec.Vec.length,List.length_append,List.length_singleton]
          exact Nat.le_max_right _ _,max_le out.bounded bound⟩
      lift (.ok next)
    else runtime.capacityOverflow

def append {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (site thread : Nat) (out source : Buffer A) : Q S (Buffer A × Buffer A) :=
  PV_V263_World.bind
    (runtime.methods.vector (.append site thread out.values.length source.values.length layouts.item)) fun _ =>
    if bound : out.values.length+source.values.length ≤ Usize.max then
      let next : Buffer A := ⟨⟨out.values.val++source.values.val,by
        simpa only [List.length_append] using bound⟩,
        max out.capacity (out.values.length+source.values.length),by
          simp only [alloc.vec.Vec.length,List.length_append]
          exact Nat.le_max_right _ _,max_le out.bounded bound⟩
      lift (.ok (next,empty source.capacity source.bounded))
    else runtime.capacityOverflow

/-- Neither the successful reserve nor erasure destroys the donor reservation. -/
theorem append_stores {A : Type} (out source : Buffer A)
    (bound : out.values.length+source.values.length ≤ Usize.max) :
    let next : Buffer A := ⟨⟨out.values.val++source.values.val,by
      simpa only [List.length_append] using bound⟩,
      max out.capacity (out.values.length+source.values.length),by
        simp only [alloc.vec.Vec.length,List.length_append]
        exact Nat.le_max_right _ _,max_le out.bounded bound⟩
    next.values.val=out.values.val++source.values.val ∧
    (empty (A := A) source.capacity source.bounded).capacity=source.capacity := ⟨rfl,rfl⟩

def erasePair {A : Type} (p : Buffer A × Buffer A) : alloc.vec.Vec A × alloc.vec.Vec A :=
  (p.1.values,p.2.values)

theorem append_erasure {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (site thread : Nat) (out source : Buffer A)
    (bound : out.values.length+source.values.length ≤ Usize.max) :
    mapAction erasePair (append runtime layouts site thread out source) =
      PV_V263_VecSpine.append runtime layouts site thread out.values source.values := by
  unfold append PV_V263_VecSpine.append
  rw [map_bind]
  congr 1
  funext unit
  simp only [dif_pos bound]
  funext w
  rfl

#print axioms push
#print axioms append
#print axioms append_stores
#print axioms erasePair
#print axioms append_erasure
end R1Z.PV_V263_RetainedMethods
