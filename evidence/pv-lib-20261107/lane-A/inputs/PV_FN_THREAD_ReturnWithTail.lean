import PV_THR2_IntrinsicFrameReturnCall
set_option autoImplicit false
namespace PV_FN_THREAD_ReturnWithTail
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- A return exits its body even when source branch syntax has an enclosing
continuation. The complete pending return configuration keeps that syntax. -/
def result (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (site : Site) (tail : List PV_STX2_SliceSyntax.Node) : Status :=
  match s.cells ⟨a,0,[]⟩ with
  | none => .undefined (some site) s
  | some v => match parents with
    | [] => .returned (.ok v) s
    | _ :: _ => .running ⟨{activation := a,remaining := .leaf (.ret site (.local 0)) :: tail,loops := loops,completed := some (.ok v)},parents,s⟩
def after {W E : Type} (B : Carrier W Data) (s : Store Data) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (site : Site)
    (tail : List PV_STX2_SliceSyntax.Node) (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.State W E :=
  match s.cells ⟨a,0,[]⟩,parents with
  | some v,parent :: rest =>
    let p := PV_THR2_IntrinsicFrameCompleted.result B
      ⟨{activation := a,remaining := .leaf (.ret site (.local 0)) :: tail,loops := loops,completed := some (.ok v)},parent :: rest,s⟩ v w
    ⟨⟨p.status,p.world,es ++ p.events⟩,stack⟩
  | _,_ => ⟨⟨result s a parents loops site tail,w,es⟩,stack⟩
theorem source {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (site : Site) (tail : List PV_STX2_SliceSyntax.Node) (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance B K P H 1
      ⟨⟨.running ⟨{activation := a,remaining := .leaf (.ret site (.local 0)) :: tail,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨result s a parents loops site tail,w,es⟩,stack⟩ := by
  cases cell : s.cells ⟨a,0,[]⟩ <;> cases parents <;>
    simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
      PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
      PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
      PV_STX2_SliceMachine.step,native,adopt,PV_STX2_Native.step,PV_STX2_Store.read,cell,result]
/-- Full explicit-store return and saved caller administration, for every
return read and caller-action case. No enclosing suffix is executed. -/
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (site : Site) (tail : List PV_STX2_SliceSyntax.Node) (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance B K P H
      (1 + PV_THR2_IntrinsicFrameReturnCall.extra s a parents)
      ⟨⟨.running ⟨{activation := a,remaining := .leaf (.ret site (.local 0)) :: tail,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      after B s a parents loops site tail w es stack := by
  rw [PV_THR2_IntrinsicComposition.advance_add,source]
  cases cell : s.cells ⟨a,0,[]⟩ with
  | none => simp only [PV_THR2_IntrinsicFrameReturnCall.extra,cell,after,PV_THR2_IntrinsicState.advance]
  | some value =>
    cases parents with
    | nil => simp only [PV_THR2_IntrinsicFrameReturnCall.extra,cell,after,PV_THR2_IntrinsicState.advance]
    | cons parent parents =>
      simp only [PV_THR2_IntrinsicFrameReturnCall.extra,cell,result,after]
      exact PV_THR2_IntrinsicFrameCompleted.run B K P H _ value w es stack rfl rfl
#print axioms source
#print axioms run
end PV_FN_THREAD_ReturnWithTail
