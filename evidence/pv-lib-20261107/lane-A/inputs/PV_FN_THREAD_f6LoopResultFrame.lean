import PV_FN_THREAD_f6LoopInduction
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6LoopResultFrame
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6LoopIteration

/-- The source's own issuance and loop writes never touch saved result LOCAL10.
This is by store-write shape, independent of values, counters and worlds. -/
theorem own {W E : Type} (k : Context W E) (x : Cursor W E) (r : Iteration W E) :
    (firstCall k x).store.cells ⟨k.activation,10,[]⟩ = x.store.cells ⟨k.activation,10,[]⟩ ∧
    (loadCall k x r).store.cells ⟨k.activation,10,[]⟩ = r.first.store.cells ⟨k.activation,10,[]⟩ ∧
    (derefCall k x r).store.cells ⟨k.activation,10,[]⟩ = r.load.store.cells ⟨k.activation,10,[]⟩ ∧
    (parkCall k x r).store.cells ⟨k.activation,10,[]⟩ = r.deref.store.cells ⟨k.activation,10,[]⟩ ∧
    (next k x r).store.cells ⟨k.activation,10,[]⟩ = r.park.store.cells ⟨k.activation,10,[]⟩ := by
  simp [firstCall,loadCall,derefCall,parkCall,next,afterFirst,afterLoad,beforeDeref,
    afterDeref,afterPark,PV_FN_THREAD_f6LoopIteration.resumed,PV_FN_THREAD_f6ReturnedContinuations.resumed,
    PV_FN_THREAD_f6LoopEntry.pending,PV_FN_THREAD_f6LoopEntry.prepared,
    PV_FN_THREAD_f6LoadCounter.pending,PV_FN_THREAD_f6LoadCounter.prepared,
    PV_FN_THREAD_f6CounterTest.prepared,
    PV_FN_THREAD_f6ParkDeref.pending,PV_FN_THREAD_f6ParkDeref.prepared,
    PV_FN_THREAD_f6ParkRequest.pending,PV_FN_THREAD_f6ParkRequest.prepared,
    PV_FN_THREAD_f6LoopBack.prepared,PV_THR2_StaticCall.pending,
    PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write]

/-- These four equations are INTERNAL projections of the callee Posts, at the
actual entries. They must be discharged by the callee frame clauses, not put in
f6 Pre and not asserted for an arbitrary native world or Post store. -/
def CalleeFrames {W E} (k : Context W E) (x : Cursor W E) (r : Iteration W E) : Prop :=
    r.first.store.cells ⟨k.activation,10,[]⟩ = (firstCall k x).store.cells ⟨k.activation,10,[]⟩ ∧
    r.load.store.cells ⟨k.activation,10,[]⟩ = (loadCall k x r).store.cells ⟨k.activation,10,[]⟩ ∧
    r.deref.store.cells ⟨k.activation,10,[]⟩ = (derefCall k x r).store.cells ⟨k.activation,10,[]⟩ ∧
    r.park.store.cells ⟨k.activation,10,[]⟩ = (parkCall k x r).store.cells ⟨k.activation,10,[]⟩

theorem iteration {W E : Type} (k : Context W E) (x : Cursor W E) (r : Iteration W E)
    (callee_frames : CalleeFrames k x r) :
    (next k x r).store.cells ⟨k.activation,10,[]⟩ = x.store.cells ⟨k.activation,10,[]⟩ := by
  rcases own k x r with ⟨h0,h1,h2,h3,h4⟩
  rcases callee_frames with ⟨f0,f1,f2,f3⟩
  exact h4.trans (f3.trans (h3.trans (f2.trans (h2.trans (f1.trans (h1.trans (f0.trans h0)))))))

def Frames {W E} (k : Context W E) : Cursor W E → List (Iteration W E) → Prop
  | _,[] => True
  | x,r :: rs => CalleeFrames k x r ∧ Frames k (next k x r) rs

/-- Saved125 result survives ANY number of own iterations when the actual
callee frame projections are supplied. No fixed125 value or success is used. -/
theorem iterations {W E : Type} (k : Context W E) (x : Cursor W E)
    (rs : List (Iteration W E)) (callee_frames : Frames k x rs) :
    (PV_FN_THREAD_f6LoopInduction.finish k x rs).store.cells ⟨k.activation,10,[]⟩ =
      x.store.cells ⟨k.activation,10,[]⟩ := by
  induction rs generalizing x with
  | nil => rfl
  | cons r rs ih =>
    exact (ih _ callee_frames.2).trans (iteration k x r callee_frames.1)

/-- Zero exit preserves LOCAL10 and uses just the two callee frames it reaches. -/
theorem zero_exit {W E : Type} (k : Context W E) (x : Cursor W E) (r : Iteration W E)
    (first_frame : r.first.store.cells ⟨k.activation,10,[]⟩ =
      (firstCall k x).store.cells ⟨k.activation,10,[]⟩)
    (load_frame : r.load.store.cells ⟨k.activation,10,[]⟩ =
      (loadCall k x r).store.cells ⟨k.activation,10,[]⟩) :
    (PV_FN_THREAD_f6LoopInduction.zeroCursor k x r).store.cells ⟨k.activation,10,[]⟩ =
      x.store.cells ⟨k.activation,10,[]⟩ := by
  have tail : (PV_FN_THREAD_f6LoopInduction.zeroCursor k x r).store.cells ⟨k.activation,10,[]⟩ =
      r.load.store.cells ⟨k.activation,10,[]⟩ := by
    simp [PV_FN_THREAD_f6LoopInduction.zeroCursor,afterLoad,PV_FN_THREAD_f6LoopIteration.resumed,
      PV_FN_THREAD_f6ReturnedContinuations.resumed,PV_FN_THREAD_f6CounterTest.prepared,write]
  exact tail.trans (load_frame.trans ((own k x r).2.1.trans (first_frame.trans (own k x r).1)))

#print axioms own
#print axioms iteration
#print axioms iterations
#print axioms zero_exit
end PV_FN_THREAD_f6LoopResultFrame
