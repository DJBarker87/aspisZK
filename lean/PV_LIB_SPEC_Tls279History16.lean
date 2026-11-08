import PV_LIB_SPEC_Tls279Request16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls279History16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def site : Site := match PV_THR2_F170.node23 with
  | .leaf (.call site _ _ _ _) => site | _ => ⟨0,0,.null⟩

theorem issued (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (value : Data) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context)
    (cell : s.cells ⟨a,5,[]⟩ = some value) :
    (PV_LIB_SPEC_SourceTransport15.advance p H 3
      (stage s a parents (PV_THR2_F170.live.body.drop 21) w es issued consumed)).issued =
    ⟨site,a,.child PV_THR2_RunTlsBranchRequest.callee s.nextActivation
      [value]⟩ :: issued := by
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
    PV_THR2_F170.node21,PV_THR2_F170.node22,PV_THR2_F170.node23,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,PV_STX2_Store.write,cell,site,PV_THR2_RunTlsBranchRequest.callee]


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
end PV_LIB_SPEC_Tls279History16
