import PV_FN_W2_ReturnOutcome
set_option autoImplicit false
namespace PV_FN_W2_BinaryReturnOutcome
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Native Result errors leave their own waiting record on the completed body
frame. For a two-argument source request, intrinsic callback selection is
excluded BY REQUEST SHAPE. Return to the saved BODY caller, on the complete
native-issued store. Pending is not completed and is not advanced here. -/
theorem completed {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a dest : Nat) (rest : List PV_STX2_SliceSyntax.Node)
    (loops : List LoopFrame) (parent : Frame) (parents : List Frame)
    (wait held : PV_STX2_Native.Waiting Data) (result : Result Data)
    (fn first second : Data) (child : Nat) (w : W) (es : List E) (stack : List Config)
    (saved : parent.waiting = some wait) (action : wait.action = .child a (.local dest))
    (request : held.request = .child fn child [first,second]) :
    PV_THR2_IntrinsicState.advance B K P H 1
      ⟨⟨.running ⟨{activation := a,remaining := rest,loops := loops,waiting := some held,completed := some result},parent :: parents,s⟩,w,es⟩,stack⟩ =
      ⟨PV_THR2_ChildBoundary.delivered B ⟨parent,parents,s⟩ wait ⟨.returned result,w,es⟩,stack⟩ := by
  cases result <;> cases parents <;>
    simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
      PV_THR2_Catch316Segment.select,request,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
      PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
      PV_STX2_SliceMachine.step,PV_THR2_ChildBoundary.delivered,saved,
      PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,
      PV_STX2_Native.storeResult,action,native,adopt,locate,writeAddress]
#print axioms completed
end PV_FN_W2_BinaryReturnOutcome
