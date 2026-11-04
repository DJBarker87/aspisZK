import R1Z.PV_V263_HandleAdapter
/-! Step 1 helper with no extra length bound. This is a model adapter law,
not a source binding, native allocation invariant or opsNative installation. -/
set_option autoImplicit false
namespace R1Z.PV_V263_HandleAdapterTotal
open Aeneas Aeneas.Std PV_V263_World PV_V263_OwnedDrain PV_V263_HandleAdapter
open PV_V263_BufferLoop (mapAction)

/-- Exact World.Run equality for the constructed adapter. This serves Step 1,
but does not claim that descriptor is a view of the deployed native heap or
that the spawn loop maintains that view. Those are separate missing proofs.
No capacity equality or callback success is required. -/
theorem push_erasure {S B : Type}
    (base : PV_V263_RetainedMethods.Runtime S)
    (resize : PV_V263_RawGrowth.Resize → Q S Nat) (stop : Q S Empty)
    (descriptor : State S → Allocation) (layouts : PV_V263_RetainedMethods.Layouts)
    (handles : Owner (PV_V263_RetainedSpine.Task S B))
    (task : PV_V263_RetainedSpine.Task S B) (w : State S)
    (view : descriptor w=handles.allocation) :
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
      · have raw : handles.initialized.values.length=handles.allocation.rawCapacity := by
          simpa only [capacity,zero,if_false] using full
        have bound : handles.initialized.values.length+1≤Usize.max := by
          rw [raw]
          exact (PV_V263_RawGrowth.enough _ _).trans sized.1
        simp only [PV_V263_GrowingPush.push,dif_pos full,dif_neg zero,dif_pos sized,
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
  · have fits := handles.initialized.fits.trans handles.reserved
    have room : handles.initialized.values.length+1≤capacity handles.allocation := by omega
    have bound := room.trans (capacity_bound handles.allocation)
    simp only [PV_V263_GrowingPush.push,dif_neg full,method,if_neg full,
      mapAction,PV_V263_World.bind,PV_V263_World.lift,dif_pos bound,
      PV_V263_RawGrowth.store,PV_V263_BufferLoop.stored,List.nil_append,
      List.append_nil]

#print axioms push_erasure
end R1Z.PV_V263_HandleAdapterTotal
