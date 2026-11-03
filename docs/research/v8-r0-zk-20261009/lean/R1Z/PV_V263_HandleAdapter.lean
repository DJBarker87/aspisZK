import R1Z.PV_V263_GrowingPush
import R1Z.PV_V263_RetainedSpine
/-! Step 1 helper: a descriptor-reading handle method adapter. This is NOT
native association: the descriptor view and allocator still require a native
heap interpretation and a reached-state preservation proof. In particular this
module must not be installed at opsNative or cited as the D579 target. -/
set_option autoImplicit false
namespace R1Z.PV_V263_HandleAdapter
open Aeneas Aeneas.Std PV_V263_World PV_V263_OwnedDrain
open PV_V263_BufferLoop (mapAction)

/-- Capacity failure has no successful value at any result type. Its native
post-world and diagnostics may be arbitrary; none are erased. -/
def stopAs {S A : Type} (stop : Q S Empty) : Q S A :=
  mapAction Empty.elim stop

def growth {S : Type} (resize : PV_V263_RawGrowth.Resize → Q S Nat)
    (stop : Q S Empty) : PV_V263_RawGrowth.Runtime S :=
  ⟨resize,stopAs stop⟩

/-- Read the descriptor at the invocation world, not from a captured owner.
Only grow_one has a resource effect; a reserved push has none. -/
def method {S : Type} (resize : PV_V263_RawGrowth.Resize → Q S Nat)
    (stop : Q S Empty) (allocation : Allocation) (length : Nat) : Q S Unit :=
  if length=capacity allocation then
    mapAction (fun _ => ()) (PV_V263_RawGrowth.grow (growth resize stop) allocation)
  else lift (.ok ())

def runtime {S : Type} (base : PV_V263_RetainedMethods.Runtime S)
    (resize : PV_V263_RawGrowth.Resize → Q S Nat) (stop : Q S Empty)
    (descriptor : State S → Allocation) : PV_V263_RetainedMethods.Runtime S :=
  {base with methods := {base.methods with vector := fun call =>
    match call with
    | .push 2 0 length _ => fun w => method resize stop (descriptor w) length w
    | _ => base.methods.vector call},capacityOverflow := stopAs stop}

/-- Empty has no successful inhabitant; mapping its stopped execution cannot
introduce success, alter faults or shorten the event prefix. -/
theorem stop_map {S A B : Type} (stop : Q S Empty) (f : A → B) (w : State S) :
    mapAction f (stopAs stop) w = stopAs stop w := by
  cases h : (stop w).outcome with
  | fault e => simp only [mapAction,stopAs,PV_V263_World.bind,h]
  | exhausted => simp only [mapAction,stopAs,PV_V263_World.bind,h]
  | returned r =>
    cases r with
    | fail e => simp only [mapAction,stopAs,PV_V263_World.bind,h]
    | div => simp only [mapAction,stopAs,PV_V263_World.bind,h]
    | ok e => exact Empty.elim e

/-- Exact World.Run equality for the constructed adapter. This serves Step 1,
but does not claim that descriptor is a view of the deployed native heap or
that the spawn loop maintains that view. Those are separate missing proofs.
The bound holds for every source handle push (at most fifteen handles). -/
theorem push_erasure {S B : Type}
    (base : PV_V263_RetainedMethods.Runtime S)
    (resize : PV_V263_RawGrowth.Resize → Q S Nat) (stop : Q S Empty)
    (descriptor : State S → Allocation) (layouts : PV_V263_RetainedMethods.Layouts)
    (handles : Owner (PV_V263_RetainedSpine.Task S B))
    (task : PV_V263_RetainedSpine.Task S B) (w : State S)
    (view : descriptor w=handles.allocation)
    (bound : handles.initialized.values.length+1≤Usize.max) :
    mapAction (fun o => o.initialized.values)
      (PV_V263_GrowingPush.push (growth resize stop) handles task) w =
    mapAction (fun b => b.values)
      (PV_V263_RetainedMethods.push (runtime base resize stop descriptor)
        {layouts with item := layouts.handle} 2 0 handles.initialized task) w := by
  unfold PV_V263_RetainedMethods.push
  simp only [runtime,mapAction,PV_V263_World.bind,view]
  by_cases full : handles.initialized.values.length=capacity handles.allocation
  · by_cases zero : handles.allocation.layout.size=0
    · simp only [PV_V263_GrowingPush.push,dif_pos full,dif_pos zero,
        method,if_pos full,PV_V263_RawGrowth.grow,growth, mapAction,
        PV_V263_World.bind,stopAs]
      cases h : (stop w).outcome with
      | fault e => simp only [h]
      | exhausted => simp only [h]
      | returned r => cases r with
        | fail e => simp only [h]
        | div => simp only [h]
        | ok e => exact Empty.elim e
    · by_cases sized : PV_V263_RawGrowth.requestedCap handles.allocation.layout.size
          handles.allocation.rawCapacity≤Usize.max ∧
        PV_V263_RawGrowth.requestedCap handles.allocation.layout.size
          handles.allocation.rawCapacity*handles.allocation.layout.size≤Usize.max/2
      · simp only [PV_V263_GrowingPush.push,dif_pos full,dif_neg zero,dif_pos sized,
          method,if_pos full,PV_V263_RawGrowth.grow,growth]
        cases h : (resize ⟨release handles.allocation,
          PV_V263_RawGrowth.requestedCap handles.allocation.layout.size
            handles.allocation.rawCapacity*handles.allocation.layout.size,
          handles.allocation.layout.align⟩ w).outcome with
        | fault e => simp only [mapAction,PV_V263_World.bind,h]
        | exhausted => simp only [mapAction,PV_V263_World.bind,h]
        | returned r =>
          cases r with
          | fail e => simp only [mapAction,PV_V263_World.bind,h]
          | div => simp only [mapAction,PV_V263_World.bind,h]
          | ok pointer =>
            simp only [mapAction,PV_V263_World.bind,h,PV_V263_World.lift,
              dif_pos bound,PV_V263_RawGrowth.store,PV_V263_BufferLoop.stored,
              List.append_nil]
      · simp only [PV_V263_GrowingPush.push,dif_pos full,dif_neg zero,dif_neg sized,
          method,if_pos full,PV_V263_RawGrowth.grow,growth,mapAction,
          PV_V263_World.bind,stopAs]
        cases h : (stop w).outcome with
        | fault e => simp only [h]
        | exhausted => simp only [h]
        | returned r => cases r with
          | fail e => simp only [h]
          | div => simp only [h]
          | ok e => exact Empty.elim e
  · simp only [PV_V263_GrowingPush.push,dif_neg full,method,if_neg full,
      mapAction,PV_V263_World.bind,PV_V263_World.lift,dif_pos bound,
      PV_V263_RawGrowth.store,PV_V263_BufferLoop.stored,List.nil_append,
      List.append_nil]

#print axioms stopAs
#print axioms growth
#print axioms method
#print axioms runtime
#print axioms stop_map
#print axioms push_erasure
end R1Z.PV_V263_HandleAdapter
