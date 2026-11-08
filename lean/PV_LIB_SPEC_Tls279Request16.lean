import PV_LIB_SPEC_Tls279Bound16
import PV_THR2_IntrinsicTraceLift
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls279Request16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

theorem trace (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_SourceTransport15.Trace cut p H 3
      (stage s a parents (PV_THR2_F170.live.body.drop 21) w es issued consumed) := by
  simp [PV_LIB_SPEC_SourceTransport15.Trace,PV_LIB_SPEC_SourceTransport15.sourceStep,
    PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_SPEC_ControlRuntime.ordinary,
    PV_LIB_StoreActionTable.Neutral,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformNeutral.configuration,
    PV_THR2_OwnUniformNeutral.instruction,PV_THR2_InterpreterAgreement.NativeAgree,
    PV_THR2_HandlerExecutionAgreement.Agree,stage,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,
    PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,PV_THR2_GapCompletion.step,
    PV_THR2_AggregateCompletion.complete,PV_THR2_AggregateCompletion.carrier,
    PV_STX2_SliceMachine.step,PV_THR2_F170.live,PV_THR2_F170.block66,
    PV_THR2_F170.node21,PV_THR2_F170.node22,PV_THR2_F170.node23,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,PV_STX2_Store.write]

def site : Site := match PV_THR2_F170.node23 with
  | .leaf (.call site _ _ _ _) => site | _ => ⟨0,0,.null⟩
def config (s : Store Data) (a : Nat) (parents : List Frame) (value : Data) : Config :=
  PV_THR2_RunTlsBranchRequest.pending s a parents value

theorem source (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (value : Data) (w : OWNER) (es : List Event)
    (cell : s.cells ⟨a,5,[]⟩ = some value) :
    PV_THR2_IntrinsicState.advance (runtime p).carrier (runtime p).control
      PV_LIB_SPEC_Full.programs H 3
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 21},parents,s⟩,w,es⟩,[]⟩ =
      ⟨⟨.running (config s a parents value),w,es⟩,[]⟩ := by
  have clear : ∀ k, k<3 → PV_THR2_IntrinsicTraceLift.Clear
      (PV_THR2_Execution.advance (runtime p).carrier (runtime p).control
        PV_LIB_SPEC_Full.programs H k
        ⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 21},parents,s⟩,w,es⟩) := by
    intro k hk
    interval_cases k <;>
      simp [PV_THR2_IntrinsicTraceLift.Clear,PV_THR2_Execution.advance,PV_THR2_Execution.step,
        PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,PV_THR2_GapCompletion.step,
        PV_THR2_AggregateCompletion.complete,PV_THR2_AggregateCompletion.carrier,
        PV_STX2_SliceMachine.step,PV_THR2_Catch316Segment.select,
        PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node21,
        PV_THR2_F170.node22,native,adopt,PV_STX2_Native.step,
        PV_STX2_Store.bind,evaluate,operands,operand,PV_STX2_Store.read,locate,
        writeAddress,PV_STX2_Store.write]
  rw [PV_THR2_IntrinsicTraceLift.run _ _ _ _ _ _ _ clear]
  rw [PV_THR2_RunTlsBranchRequest.request _ _ _ _ _ _ _ value _ _ cell]
  rfl

#print axioms trace
#print axioms site
#print axioms config
#print axioms source
end PV_LIB_SPEC_Tls279Request16
