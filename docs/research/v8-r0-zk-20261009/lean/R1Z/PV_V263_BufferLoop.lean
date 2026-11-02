import R1Z.PV_V263_CollectBinding
/-! Capacity-carrying inner source loop. This constructs Buffer stores and
proves complete-run erasure to the existing Vec loop. Capacity is a retained
reservation lower bound; physical allocator metadata is still not supplied. -/
set_option autoImplicit false
namespace R1Z.PV_V263_BufferLoop
open Aeneas Aeneas.Std PV_V263_World PV_V263_VectorDrain

def stored {A : Type} (out : Buffer A) (a : A)
    (room : out.values.length+1 ≤ out.capacity) : Buffer A :=
  ⟨⟨out.values.val++[a],by
      simpa only [List.length_append,List.length_singleton] using room.trans out.bounded⟩,
    out.capacity,by simpa only [alloc.vec.Vec.length,List.length_append,List.length_singleton] using room,out.bounded⟩

theorem stored_length {A : Type} (out : Buffer A) (a : A)
    (room : out.values.length+1 ≤ out.capacity) :
    (stored out a room).values.length=out.values.length+1 := by
  exact List.length_append.trans (congrArg (out.values.length+·) (List.length_singleton))

theorem stored_push {A : Type} (out : Buffer A) (a : A)
    (room : out.values.length+1 ≤ out.capacity) :
    alloc.vec.Vec.push out.values a = .ok (stored out a room).values := by
  obtain ⟨next,hpush,hval⟩ := PV_RunJoin_Vector44.push out.values a (room.trans out.bounded)
  have same : next=(stored out a room).values := Subtype.ext hval
  rw [same] at hpush
  exact hpush

def loop {S A : Type} (runtime : PV_V263_MapSpine.Runtime S)
    (layouts : PV_V263_MapSpine.Layouts) (thread : Nat) (callback : Nat → Q S A) :
    (ids : List Nat) → (out : Buffer A) → (completed : Nat) →
    (room : out.values.length+ids.length ≤ out.capacity) → Q S (Buffer A × Nat)
  | [],out,completed,_ => lift (.ok (out,completed))
  | i::ids,out,completed,room =>
      PV_V263_World.bind (callback i) fun a =>
      PV_V263_World.bind (runtime.vector (.push 0 thread out.values.length layouts.item)) fun _ =>
      let next := stored out a (by simp only [List.length_cons] at room; omega)
      loop runtime layouts thread callback ids next (completed+1) (by
        change next.values.length+ids.length ≤ next.capacity
        dsimp only [next]
        rw [stored_length]
        simp only [stored]
        simp only [List.length_cons] at room
        omega)

def erase {A : Type} (p : Buffer A × Nat) : alloc.vec.Vec A × Nat := (p.1.values,p.2)

def mapAction {S A B : Type} (f : A → B) (action : Q S A) : Q S B :=
  PV_V263_World.bind action (fun a => lift (.ok (f a)))

theorem mapAction_run {S A B : Type} (f : A → B) (action : Q S A) (w : State S) :
    mapAction f action w = PV_V263_CollectBinding.mapRun f (action w) :=
  PV_V263_CollectBinding.pure_bind f action w

theorem map_bind {S A B C : Type} (f : B → C) (action : Q S A) (next : A → Q S B) :
    mapAction f (PV_V263_World.bind action next) =
      PV_V263_World.bind action (fun a => mapAction f (next a)) :=
  PV_V263_World.bind_assoc action next (fun b => lift (.ok (f b)))

/-- Complete operational equality after erasing only reservation metadata.
No callback law or successful run is supplied as a premise. -/
theorem erasure {S A : Type} (runtime : PV_V263_MapSpine.Runtime S)
    (layouts : PV_V263_MapSpine.Layouts) (thread : Nat) (callback : Nat → Q S A)
    (ids : List Nat) (out : Buffer A) (completed : Nat)
    (room : out.values.length+ids.length ≤ out.capacity) :
    mapAction erase (loop runtime layouts thread callback ids out completed room) =
      PV_V263_VectorLoop.loop runtime layouts thread callback ids out.values completed := by
  induction ids generalizing out completed with
  | nil => funext w; rfl
  | cons i ids ih =>
    simp only [loop,map_bind]
    congr 1
    funext a
    congr 1
    funext unit
    let next := stored out a (by simp only [List.length_cons] at room; omega)
    have remaining : next.values.length+ids.length ≤ next.capacity := by
      dsimp only [next]
      rw [stored_length]
      simp only [stored]
      simp only [List.length_cons] at room
      omega
    rw [ih next (completed+1) remaining]
    have hp := stored_push out a (by simp only [List.length_cons] at room; omega)
    rw [hp]
    funext w
    rfl

#print axioms stored
#print axioms stored_length
#print axioms stored_push
#print axioms loop
#print axioms erase
#print axioms mapAction
#print axioms mapAction_run
#print axioms map_bind
#print axioms erasure
end R1Z.PV_V263_BufferLoop
