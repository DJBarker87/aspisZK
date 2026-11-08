import PV_FN_THREAD_f6LoopResultFrame
import PV_FN_THREAD_f6FinalDerefRequest
import PV_FN_THREAD_f6TraceExpansion
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6LoopContinuation
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6SummaryTrace PV_FN_THREAD_f6LoopIteration

def scopeContext {W E} (k : Context W E) : Context W E :=
  {k with afterLoop := PV_THR2_F6.live.body.drop 52}

/-- Complete own loop and Ok125 continuation to actual source2659, preserving
125's saved result by the named callee frames. Every cell fact here is an
INTERNAL125 Post projection, never a new f6-entry or endpoint premise.
No callee body is unfolded and every explicit callee Post store is retained. -/
theorem to_final_request {W E : Type} (context : Context W E)
    (C : Nat → CallPost W E) (x : Cursor W E)
    (rs : List (Iteration W E)) (r : Iteration W E) (result : Data)
    (callee_contract_applications : PV_FN_THREAD_f6LoopInduction.Dependencies C (scopeContext context) x rs)
    (callee_frame_applications : PV_FN_THREAD_f6LoopResultFrame.Frames (scopeContext context) x rs)
    (zero : r.load.value = 0)
    (callee126_at2097 : C 2097 (firstCall (scopeContext context) (PV_FN_THREAD_f6LoopInduction.finish (scopeContext context) x rs))
      (PV_FN_THREAD_f6LoopInduction.finish (scopeContext context) x rs).world r.first.store
      ⟨.returned (.ok (ref r.first.value)),r.first.world,r.first.events⟩)
    (callee127_at2197 : C 2197 (loadCall (scopeContext context) (PV_FN_THREAD_f6LoopInduction.finish (scopeContext context) x rs) r)
      (afterFirst (scopeContext context) (PV_FN_THREAD_f6LoopInduction.finish (scopeContext context) x rs) r).world r.load.store
      ⟨.returned (.ok (.number r.load.value)),r.load.world,r.load.events⟩)
    (first_frame : r.first.store.cells ⟨context.activation,10,[]⟩ =
      (firstCall (scopeContext context) (PV_FN_THREAD_f6LoopInduction.finish (scopeContext context) x rs)).store.cells ⟨context.activation,10,[]⟩)
    (load_frame : r.load.store.cells ⟨context.activation,10,[]⟩ =
      (loadCall (scopeContext context) (PV_FN_THREAD_f6LoopInduction.finish (scopeContext context) x rs) r).store.cells ⟨context.activation,10,[]⟩)
    (saved125_result : x.store.cells ⟨context.activation,10,[]⟩ = some result)
    (ok_case : context.ctl.variant result = some 0) :
    let k := scopeContext context
    let z := PV_FN_THREAD_f6LoopInduction.zeroCursor k (PV_FN_THREAD_f6LoopInduction.finish k x rs) r
    Trace (carrier k) k.ctl k.programs k.handler C
      (sourceState k PV_THR2_F6.block86 x)
      (waiting k (PV_FN_THREAD_f6FinalDerefRequest.pending z.store k.activation k.parents k.lower) z) := by
  dsimp only
  let k := scopeContext context
  let y := PV_FN_THREAD_f6LoopInduction.finish k x rs
  let z := PV_FN_THREAD_f6LoopInduction.zeroCursor k y r
  have run := PV_FN_THREAD_f6LoopInduction.iterations_then_exit k C x rs r
    callee_contract_applications zero callee126_at2097 callee127_at2197
  have frame := (PV_FN_THREAD_f6LoopResultFrame.zero_exit k y r first_frame load_frame).trans
    (PV_FN_THREAD_f6LoopResultFrame.iterations k x rs callee_frame_applications)
  have cell : z.store.cells ⟨k.activation,10,[]⟩ = some result := frame.trans saved125_result
  have tail : Trace (carrier k) k.ctl k.programs k.handler C
      (PV_FN_THREAD_f6LoopInduction.exited k z)
      (waiting k (PV_FN_THREAD_f6FinalDerefRequest.pending z.store k.activation k.parents k.lower) z) := by
    apply own_eq _ _ _ _ _ 10
    rw [carrier,PV_FN_THREAD_f6OperatorCarrier.agreement]
    exact PV_FN_THREAD_f6FinalDerefRequest.run _ k.ctl k.programs k.handler z.store
      k.activation k.parents k.lower k.flag result z.world z.events k.suspended cell ok_case
  exact run.trans tail

#print axioms to_final_request
end PV_FN_THREAD_f6LoopContinuation
