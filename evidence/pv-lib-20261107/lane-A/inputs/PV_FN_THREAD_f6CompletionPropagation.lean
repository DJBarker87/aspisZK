import PV_FN_THREAD_f6CompletionReselection
set_option autoImplicit false
namespace PV_FN_THREAD_f6CompletionPropagation
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6CompletionReselection

/-- A completed child with its actual saved caller and explicit final store.
Its body is arbitrary: no provider internals are executed in this argument. -/
def child (parent : Config) (frame : Frame) : Config :=
  ⟨{frame with completed := some .div},
    parent.frame :: parent.callers,parent.store⟩

def propagated (parent : Config) : Config :=
  {parent with frame := {parent.frame with completed := some .div}}

/-- Non-success adoption leaves the old saved request in place. This is the
source of the selector collision, not an invented completed/waiting pair. -/
theorem source {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (parent : Config) (frame : Frame)
    (wait : PV_STX2_Native.Waiting Data) (w : W)
    (saved : parent.frame.waiting = some wait) (lower : parent.callers ≠ []) :
    PV_STX2_SliceMachine.step B K P H (child parent frame) w =
      ⟨.running (propagated parent),w,[]⟩ := by
  cases callers : parent.callers with
  | nil => exact False.elim (lower callers)
  | cons f rest =>
    simp only [child,PV_STX2_SliceMachine.step,saved,
      PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,
      PV_STX2_SliceMachine.adopt,callers,propagated]
    rfl

/-- Dynamic and aggregate completion wrappers preserve this interpreted
source transition; the intrinsic selector on the completed child is empty. -/
theorem intrinsic {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (parent : Config) (frame : Frame)
    (wait : PV_STX2_Native.Waiting Data) (w : W) (es : List E) (stack : List Config)
    (saved : parent.frame.waiting = some wait) (lower : parent.callers ≠ [])
    (ordinary : PV_THR2_Catch316Segment.select (child parent frame) = none) :
    PV_THR2_IntrinsicState.step B K P H
      ⟨⟨.running (child parent frame),w,es⟩,stack⟩ =
      ⟨⟨.running (propagated parent),w,es⟩,stack⟩ := by
  have old := source B K P H parent frame wait w saved lower
  have extended := PV_THR2_Execution.compatible B K P H
    (child parent frame) w (by simp only [PV_THR2_Dynamic.active,child])
    (by intro site s; rw [old]; intro h; cases h)
  simp only [PV_THR2_IntrinsicState.step,ordinary]
  change (⟨⟨(PV_THR2_Execution.step B K P H (child parent frame) w).status,
    (PV_THR2_Execution.step B K P H (child parent frame) w).world,
    es ++ (PV_THR2_Execution.step B K P H (child parent frame) w).events⟩,stack⟩ :
      PV_THR2_IntrinsicState.State W E) = _
  rw [extended,old,List.append_nil]

/-- Two ACTUAL machine steps propagate the child's divergence into the saved
catch318 and then re-enter callback316. No resolver/handler premise is needed. -/
theorem propagate_then_reenter {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a activation : Nat) (outer : Frame) (parents : List Frame)
    (body : List PV_STX2_SliceSyntax.Node) (w : W) (es : List E) (stack : List Config) :
    let parent := PV_THR2_Catch219Call318.pending s a (outer :: parents)
    let frame : Frame := {activation := activation,remaining := body}
    PV_THR2_IntrinsicState.advance B K P H 2
      ⟨⟨.running (child parent frame),w,es⟩,stack⟩ =
    PV_THR2_IntrinsicState.invoke
      ⟨⟨.running (completedCatch s a (outer :: parents)),w,es⟩,stack⟩
      (PV_THR2_CallbackSegment.enter (completedCatch s a (outer :: parents))
        PV_THR2_F316.live [PV_STX2_TypedReferences.reference ⟨a,2,[]⟩ .null]) := by
  intro parent frame
  change PV_THR2_IntrinsicState.step B K P H
    (PV_THR2_IntrinsicState.step B K P H
      ⟨⟨.running (child parent frame),w,es⟩,stack⟩) = _
  rw [intrinsic B K P H parent frame _ w es stack rfl (by intro h; cases h) (by rfl)]
  exact reentered B K P H s a (outer :: parents) w es stack

#print axioms source
#print axioms intrinsic
#print axioms propagate_then_reenter
end PV_FN_THREAD_f6CompletionPropagation
