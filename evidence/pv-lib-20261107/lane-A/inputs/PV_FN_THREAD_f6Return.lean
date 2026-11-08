import PV_FN_THREAD_f6ReturnTail
import PV_THR2_IntrinsicParentReturn
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6Return
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Source2832 returns the actual LOCAL0 value, preserving the explicit store.
The caller continuation is arbitrary. This is the own return instruction only. -/
theorem source {W E : Type} (B : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parent : Frame) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (v : Data) (w : W) (es : List E) (stack : List Config)
    (cell : t.cells ⟨a,0,[]⟩ = some v) :
    PV_THR2_IntrinsicState.step B ctl P H
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.node156 :: rest,loops := loops},parent :: parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.node156 :: rest,loops := loops,completed := some (.ok v)},parent :: parents,t⟩,w,es⟩,stack⟩ := by
  simp [PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_GapCompletion.step,
    PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,PV_THR2_F6.node156,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.read,cell]

/-- The next administrative step restores the actual saved caller, with its
return destination written on f6's final store. Neither a new native call nor
an old issuance-store replacement occurs. -/
theorem parent {W E : Type} (B : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a dest : Nat) (parent : Frame) (parents : List Frame)
    (wait : PV_STX2_Native.Waiting Data) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (v : Data)
    (w : W) (es : List E) (stack : List Config)
    (saved : parent.waiting = some wait) (action : wait.action = .child a (.local dest)) :
    PV_THR2_IntrinsicState.step B ctl P H
      ⟨⟨.running ⟨{activation := a,remaining := rest,loops := loops,completed := some (.ok v)},parent :: parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{parent with waiting := none},parents,
        write (write t ⟨a,0,[]⟩ (some v)) ⟨parent.activation,dest,[]⟩ (some v)⟩,
        w,es⟩,stack⟩ := by
  simp [PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_GapCompletion.step,
    PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,saved,
    PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,
    PV_STX2_Native.storeResult,action,native,adopt,locate,writeAddress]

#print axioms source
#print axioms parent
end PV_FN_THREAD_f6Return
