import PV_THR2_IntrinsicSourceReturn
import PV_THR2_IntrinsicFrameCompleted
import PV_THR2_IntrinsicFrameReturnCall
set_option autoImplicit false
namespace PV_FN_W4_ReturnBoundary
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Read the actual return slot, retaining missing reads and the full caller frame. -/
def result (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (site : Site) (tail : List PV_STX2_SliceSyntax.Node) : Status :=
  match s.cells ⟨a,0,[]⟩ with
  | none => .undefined (some site) s
  | some v => match parents with
    | [] => .returned (.ok v) s
    | _ :: _ => .running ⟨{activation := a,remaining := .leaf (.ret site (.local 0)) :: tail,loops := loops,completed := some (.ok v)},parents,s⟩
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
The emitted return executes once; it neither polls a child nor resumes an intrinsic. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (site : Site) (tail : List PV_STX2_SliceSyntax.Node) (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance base ctl programs handler 1
      ⟨⟨.running ⟨{activation := a,remaining := .leaf (.ret site (.local 0)) :: tail,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨result s a parents loops site tail,w,es⟩,stack⟩ := by
  cases h : s.cells ⟨a,0,[]⟩ <;> cases parents <;>
    simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
      PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
      PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
      PV_STX2_SliceMachine.step,native,adopt,PV_STX2_Native.step,
      PV_STX2_Store.read,h,result]
#print axioms run

def extra := PV_THR2_IntrinsicFrameReturnCall.extra

def after {W E : Type} (C : Carrier W Data) (s : Store Data) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (site : Site)
    (tail : List PV_STX2_SliceSyntax.Node) (w : W) (es : List E)
    (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  match s.cells ⟨a,0,[]⟩,parents with
  | some v,parent :: rest =>
    let p : Prefix W E := PV_THR2_IntrinsicFrameCompleted.result C
      ⟨{activation := a,remaining := .leaf (.ret site (.local 0)) :: tail,loops := loops,
        completed := some (.ok v)},parent :: rest,s⟩ v w
    ⟨⟨p.status,p.world,es ++ p.events⟩,stack⟩
  | _,_ => ⟨⟨result s a parents loops site tail,w,es⟩,stack⟩

theorem returnRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (site : Site) (tail : List PV_STX2_SliceSyntax.Node)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance C ctl programs H (1 + extra s a parents)
      ⟨⟨.running ⟨{activation := a,remaining := .leaf (.ret site (.local 0)) :: tail,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      after C s a parents loops site tail w es stack := by
  rw [PV_THR2_IntrinsicComposition.advance_add,run]
  cases h : s.cells ⟨a,0,[]⟩ with
  | none => simp only [extra,PV_THR2_IntrinsicFrameReturnCall.extra,h,after,PV_THR2_IntrinsicState.advance]
  | some v =>
    cases parents with
    | nil => simp only [extra,PV_THR2_IntrinsicFrameReturnCall.extra,h,after,PV_THR2_IntrinsicState.advance]
    | cons parent parents =>
      simp only [extra,PV_THR2_IntrinsicFrameReturnCall.extra,h,result,after]
      exact PV_THR2_IntrinsicFrameCompleted.run C ctl programs H _ v w es stack rfl rfl
#print axioms returnRun
end PV_FN_W4_ReturnBoundary
