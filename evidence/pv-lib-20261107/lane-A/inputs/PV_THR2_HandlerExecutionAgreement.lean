import PV_THR2_IntrinsicHandlerLocal
import PV_THR2_TableDynamic
import PV_THR2_Execution
set_option autoImplicit false
namespace PV_THR2_HandlerExecutionAgreement
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Local complete-reply equality only at the actual saved native request.
Fresh instructions consult no native handler. This is an internal trace fact. -/
def Agree {W E : Type}
    (left right : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) : Prop :=
  ∀ wait, c.frame.waiting = some wait → left wait.request w = right wait.request w
/-- Dynamic issuance preserves the saved-request agreement; its new frame has
no waiting request. The existing symbolic slice-machine agreement is reused. -/
theorem dynamic {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (left right : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) (same : Agree left right c w) :
    PV_THR2_Dynamic.step B K P left c w = PV_THR2_Dynamic.step B K P right c w := by
  unfold PV_THR2_Dynamic.step
  cases active : PV_THR2_Dynamic.active c with
  | none => exact PV_THR2_IntrinsicHandlerLocal.source_step B K P left right c w same
  | some x =>
    obtain ⟨site,o,args,dest,cleanup⟩ := x
    have waiting := PV_THR2_TableDynamic.issuing c _ active
    simp only
    cases value : operand B c.store w c.frame.activation o with
    | none => simp only [value]
    | some pair =>
      obtain ⟨fn,s⟩ := pair
      simp only [value]
      apply PV_THR2_IntrinsicHandlerLocal.source_step
      intro wait eq
      change c.frame.waiting = some wait at eq
      rw [waiting] at eq
      cases eq
/-- Full ordinary interpreter agreement by instruction shape. No evaluated
store equality, resolver exclusion certificate or source run is required. -/
theorem step {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (left right : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) (same : Agree left right c w) :
    PV_THR2_Execution.step B K P left c w = PV_THR2_Execution.step B K P right c w := by
  unfold PV_THR2_Execution.step
  cases active : PV_THR2_Dynamic.active c with
  | some x => exact dynamic B K P left right c w same
  | none =>
    simp only [PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
      PV_THR2_IntrinsicHandlerLocal.source_step B K P left right c w same,
      PV_THR2_IntrinsicHandlerLocal.source_step (PV_THR2_AggregateCompletion.carrier B)
        K P left right c w same]
#print axioms Agree
#print axioms dynamic
#print axioms step
end PV_THR2_HandlerExecutionAgreement
