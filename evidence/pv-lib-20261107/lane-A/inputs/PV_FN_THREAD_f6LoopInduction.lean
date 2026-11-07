import PV_FN_THREAD_f6LoopIteration
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6LoopInduction
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6SummaryTrace PV_FN_THREAD_f6LoopIteration

/-- Fold the source's own nonzero iterations. Each next cursor uses the park
callee's explicit Post store, then the four local deaths at the actual continue.
There is no counter bound and no claim that the sequence is exhaustive. -/
def finish {W E} (k : Context W E) : Cursor W E → List (Iteration W E) → Cursor W E
  | x,[] => x
  | x,r :: rs => finish k (next k x r) rs

/-- INTERNAL obligations indexed at the actual entry of EACH iteration.
This never substitutes for instantiation of the provider's full contract. -/
def Dependencies {W E} (C : Nat → CallPost W E) (k : Context W E) :
    Cursor W E → List (Iteration W E) → Prop
  | _,[] => True
  | x,r :: rs => r.load.value ≠ 0 ∧
      PV_FN_THREAD_f6LoopIteration.Dependencies C k x r ∧
      Dependencies C k (next k x r) rs

/-- Induction over all complete nonzero source iterations. The callee Post
obligations remain explicit and are indexed by the updated store/world/events.
This is a conditional loop-composition theorem, NOT a full f6 contract. -/
theorem iterations {W E : Type} (k : Context W E) (C : Nat → CallPost W E)
    (x : Cursor W E) (rs : List (Iteration W E))
    (callee_contract_applications : Dependencies C k x rs) :
    Trace (carrier k) k.ctl k.programs k.handler C
      (sourceState k PV_THR2_F6.block86 x)
      (sourceState k PV_THR2_F6.block86 (finish k x rs)) := by
  induction rs generalizing x with
  | nil => exact Trace.refl _
  | cons r rs ih =>
    rcases callee_contract_applications with ⟨nz,⟨h126,h127,h126park,h128⟩,tail⟩
    exact (iteration k C x r nz h126 h127 h126park h128).trans (ih _ tail)

/-- Actual saved loop exit, retaining arbitrary lower loops, caller stack,
suspended intrinsic stack, world and accumulated event prefix. -/
def exited {W E} (k : Context W E) (x : Cursor W E) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨.running ⟨{activation := k.activation,remaining := k.afterLoop,loops := k.lower},
    k.parents,x.store⟩,x.world,x.events⟩,k.suspended⟩

def zeroCursor {W E} (k : Context W E) (x : Cursor W E) (r : Iteration W E) : Cursor W E :=
  let y := afterLoad k x r
  {y with store := (write (PV_FN_THREAD_f6CounterTest.prepared y.store k.activation 0)
    ⟨k.activation,14,[]⟩ none)}

/-- Zero is a returned-127 CONCLUSION branch. It needs only the first126 and
127 call Posts; neither the park126 nor park128 contract is invoked on exit. -/
theorem zero_exit {W E : Type} (k : Context W E) (C : Nat → CallPost W E)
    (x : Cursor W E) (r : Iteration W E) (zero : r.load.value = 0)
    (callee126_at2097 : C 2097 (firstCall k x) x.world r.first.store
      ⟨.returned (.ok (ref r.first.value)),r.first.world,r.first.events⟩)
    (callee127_at2197 : C 2197 (loadCall k x r) (afterFirst k x r).world r.load.store
      ⟨.returned (.ok (.number r.load.value)),r.load.world,r.load.events⟩) :
    Trace (carrier k) k.ctl k.programs k.handler C
      (sourceState k PV_THR2_F6.block86 x) (exited k (zeroCursor k x r)) := by
  have e0 : Trace (carrier k) k.ctl k.programs k.handler C
      (sourceState k PV_THR2_F6.block86 x) (waiting k (firstCall k x) x) := by
    apply own_eq _ _ _ _ _ 7
    rw [carrier,PV_FN_THREAD_f6OperatorCarrier.agreement]
    exact PV_FN_THREAD_f6LoopEntry.run _ k.ctl k.programs k.handler x.store
      k.activation k.parents (loops k) k.flag x.world x.events k.suspended
  have c0 : Trace (carrier k) k.ctl k.programs k.handler C
      (waiting k (firstCall k x) x)
      (sourceState k (PV_THR2_F6.block86.drop 7) (afterFirst k x r)) := by
    exact returned _ _ _ _ C 2097 (firstCall k x) _ r.first.store
      x.store.nextActivation 17 (ref r.first.value) x.world r.first.world
      x.events r.first.events k.suspended rfl rfl callee126_at2097
  have e1 : Trace (carrier k) k.ctl k.programs k.handler C
      (sourceState k (PV_THR2_F6.block86.drop 7) (afterFirst k x r))
      (waiting k (loadCall k x r) (afterFirst k x r)) := by
    apply own_eq _ _ _ _ _ 5
    exact PV_FN_THREAD_f6ReturnedContinuations.after2097 k.base k.ctl k.programs k.handler
      r.first.store x.store.nextActivation k.activation k.parents (loops k) k.flag
      r.first.value r.first.world (x.events ++ r.first.events) k.suspended
  have c1 : Trace (carrier k) k.ctl k.programs k.handler C
      (waiting k (loadCall k x r) (afterFirst k x r))
      (sourceState k (PV_THR2_F6.block86.drop 12) (afterLoad k x r)) := by
    exact returned _ _ _ _ C 2197 (loadCall k x r) _ r.load.store
      (afterFirst k x r).store.nextActivation 15 (.number r.load.value)
      (afterFirst k x r).world r.load.world (afterFirst k x r).events r.load.events
      k.suspended rfl rfl callee127_at2197
  have exit : Trace (carrier k) k.ctl k.programs k.handler C
      (sourceState k (PV_THR2_F6.block86.drop 12) (afterLoad k x r))
      (exited k (zeroCursor k x r)) := by
    apply own_eq _ _ _ _ _ 5
    apply PV_FN_THREAD_f6CounterBranches.zero_exit k.base k.ctl k.programs k.handler
      (afterLoad k x r).store k.activation k.parents k.afterLoop k.lower k.flag
      (afterLoad k x r).world (afterLoad k x r).events k.suspended
    change (PV_FN_THREAD_f6ReturnedContinuations.resumed r.load.store
      (afterFirst k x r).store.nextActivation k.activation 15 (.number r.load.value)).cells
      ⟨k.activation,15,[]⟩ = some (.number 0)
    rw [zero]
    exact PV_FN_THREAD_f6PostStore.destination _ _ _ _ _
  exact e0.trans (c0.trans (e1.trans (c1.trans exit)))

/-- Any finite number of nonzero iterations followed by the actual zero exit.
The exit calls are instantiated at the FINAL cursor, never at entry or a reused
iteration. Infinite nonzero iteration sequences are not claimed to terminate. -/
theorem iterations_then_exit {W E : Type} (k : Context W E) (C : Nat → CallPost W E)
    (x : Cursor W E) (rs : List (Iteration W E)) (r : Iteration W E)
    (callee_contract_applications : Dependencies C k x rs) (zero : r.load.value = 0)
    (callee126_at2097 : C 2097 (firstCall k (finish k x rs)) (finish k x rs).world r.first.store
      ⟨.returned (.ok (ref r.first.value)),r.first.world,r.first.events⟩)
    (callee127_at2197 : C 2197 (loadCall k (finish k x rs) r)
      (afterFirst k (finish k x rs) r).world r.load.store
      ⟨.returned (.ok (.number r.load.value)),r.load.world,r.load.events⟩) :
    Trace (carrier k) k.ctl k.programs k.handler C
      (sourceState k PV_THR2_F6.block86 x)
      (exited k (zeroCursor k (finish k x rs) r)) := by
  exact (iterations k C x rs callee_contract_applications).trans
    (zero_exit k C (finish k x rs) r zero callee126_at2097 callee127_at2197)

#print axioms iterations
#print axioms zero_exit
#print axioms iterations_then_exit
end PV_FN_THREAD_f6LoopInduction
