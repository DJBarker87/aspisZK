import PV_THR2_IntrinsicAtContinuation
import PV_THR2_IntrinsicFrameSteps
import PV_THR2_IntrinsicFrameEnter
set_option autoImplicit false
noncomputable section
namespace PV_FN_W4_CallBoundary
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- The source call instruction, with all actual operand moves. A Regular
callee token may name a function or a trait method; its body is never inspected. -/
structure Call where
  site : Site
  kind : Data
  generics : Data
  args : List Operand
  destination : Nat

def token (call : Call) : Data :=
  .object [("Regular",.object [("kind",call.kind),("generics",call.generics)])]
def node (call : Call) : PV_STX2_SliceSyntax.Node :=
  .leaf (.call call.site (token call) call.args (.local call.destination) [])

def issue {W E : Type} (C : Carrier W Data) (call : Call)
    (rest : List PV_STX2_SliceSyntax.Node) (c : Config) (w : W) (es : List E)
    (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  match (operands C w c.frame.activation call.args c.store).orElse
      (fun _ => operands (PV_THR2_AggregateCompletion.carrier C) w c.frame.activation call.args c.store) with
  | none => ⟨⟨.undefined (some call.site) c.store,w,es⟩,stack⟩
  | some (vs,t) => ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.pending t
      c.frame.activation c.callers c.frame.loops rest (token call) vs call.destination),w,es⟩,stack⟩

def steps {W E : Type} (call : Call) (rest : List PV_STX2_SliceSyntax.Node)
    (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (node call :: rest) (fun _ _ => 1) q

def after {W E : Type} (C : Carrier W Data) (call : Call)
    (rest : List PV_STX2_SliceSyntax.Node) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (node call :: rest) (issue C call rest) q

/-- One source call step, including missing operands. Subsequent BODY execution
belongs solely to the callee's named contract at this exact pending request. -/
theorem run {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (call : Call) (rest : List PV_STX2_SliceSyntax.Node)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (steps call rest q) q = after C call rest q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack ready
  rcases c with ⟨⟨a,remaining,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C ctl programs H 1
    ⟨⟨.running ⟨{activation := a,remaining := node call :: rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  cases h : operands C w a call.args s with
  | none =>
    cases k : operands (PV_THR2_AggregateCompletion.carrier C) w a call.args s with
    | none =>
      simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
        PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
        PV_THR2_Dynamic.operandOf,PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
        PV_STX2_SliceMachine.step,native,adopt,PV_STX2_Native.step,node,token,issue,h,k]
    | some pair =>
      rcases pair with ⟨vs,t⟩
      simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
        PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
        PV_THR2_Dynamic.operandOf,PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
        PV_STX2_SliceMachine.step,native,adopt,PV_STX2_Native.step,node,token,issue,h,k,
        PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticCall.issued,PV_THR2_StaticReply.wait]
  | some pair =>
    rcases pair with ⟨vs,t⟩
    simpa only [node,token,issue,h,Option.orElse_some,PV_THR2_IntrinsicFrameEnter.pending] using
      PV_THR2_IntrinsicFrameSteps.call C ctl programs H s t a parents loops rest
        call.site call.kind call.generics call.args vs call.destination w es stack h

#print axioms run
end PV_FN_W4_CallBoundary
