import PV_FN_W2_BinaryReturnOutcome
set_option autoImplicit false
namespace PV_FN_W2_BinaryEnter
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Enter a resolved two-argument BODY with the actual saved cleanup. The
call was already issued: no new activation or argument binding happens here. -/
theorem enter {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a child : Nat) (rest : List PV_STX2_SliceSyntax.Node)
    (loops : List LoopFrame) (parents : List Frame) (held : PV_STX2_Native.Waiting Data)
    (fn first second : Data) (body : PV_STX2_SliceSyntax.Program)
    (w : W) (es : List E) (stack : List Config)
    (request : held.request = .child fn child [first,second]) (resolved : P fn = some body) :
    PV_THR2_IntrinsicState.advance B K P H 1
      ⟨⟨.running ⟨{activation := a,remaining := rest,loops := loops,waiting := some held},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := child,remaining := body.body},
        {activation := a,remaining := rest,loops := loops,waiting := some held} :: parents,s⟩,w,es⟩,stack⟩ := by
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
    PV_THR2_Catch316Segment.select,request,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,resolved]
#print axioms enter
end PV_FN_W2_BinaryEnter
