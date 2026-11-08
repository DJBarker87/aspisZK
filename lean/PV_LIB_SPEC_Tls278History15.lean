import PV_LIB_SPEC_Tls278Lift15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls278History15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def site : Site := match PV_THR2_F170.node20 with
  | .leaf (.call site _ _ _ _) => site | _ => ⟨0,0,.null⟩

theorem issued (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (value : Data) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context)
    (cell : s.cells ⟨a,6,[]⟩ = some value) :
    (PV_LIB_SPEC_SourceTransport15.advance p H 4
      (stage s a parents (PV_THR2_F170.live.body.drop 17) w es issued consumed)).issued =
    ⟨site,a,.child PV_THR2_RunTlsErrorCompleted.callee s.nextActivation
      [value,PV_LIB_SPEC_Tls278Lift15.error]⟩ :: issued := by
  have missing : (runtime p).carrier.aggregate PV_THR2_RunTlsErrorCompleted.kind [] = none := rfl
  simp [PV_THR2_RunTlsErrorCompleted.kind,PV_THR2_F170.node19] at missing
  simp [PV_LIB_SPEC_SourceTransport15.advance,
    PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,PV_LIB_SPEC_SourceTransport15.sourceStep,
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
    PV_THR2_F170.node17,PV_THR2_F170.node18,PV_THR2_F170.node19,PV_THR2_F170.node20,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,PV_STX2_Store.write,missing,cell,site,PV_LIB_SPEC_Tls278Lift15.error,
    PV_THR2_RunTlsErrorCompleted.kind,PV_THR2_RunTlsErrorCompleted.callee]


theorem consumed (p : Parameters) (H : Handler) (n : Nat) (x : Execution) :
    (PV_LIB_SPEC_SourceTransport15.advance p H n x).consumed = x.consumed := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [PV_LIB_SPEC_SourceTransport15.advance,ih]
    rfl

#print axioms site
#print axioms issued
#print axioms consumed
end PV_LIB_SPEC_Tls278History15
