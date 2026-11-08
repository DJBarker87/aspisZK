import PV_LIB_SPEC_TlsOriginal15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsNone15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def kind : Data := PV_LIB_SPEC_TlsPoll15.kind

def after (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  stage (write (write s ⟨a,9,[]⟩ none) ⟨a,9,[]⟩ (some (PV_THR2_KeyValues.pack kind [])))
    a parents (PV_THR2_F170.live.body.drop 13) w es issued consumed

theorem construct (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_ReachedNative14.run cut p 2
      (stage s a parents (PV_THR2_F170.live.body.drop 11) w es issued consumed) =
    after s a parents w es issued consumed := by
  have missing : (runtime p).carrier.aggregate kind [] = none := rfl
  simp [kind,PV_LIB_SPEC_TlsPoll15.kind,PV_THR2_F170.node12] at missing
  simp [stage,after,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    PV_LIB_SPEC_ReachedNative14.run,PV_LIB_SPEC_ReachedNative14.step,
    PV_LIB_SPEC_ReachedNative14.control,PV_LIB_SPEC_ReachedNative14.transition,
    PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_StoreActionTable.step,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitInterpreterBridged.step,PV_THR2_OwnInitAction.selected,
    PV_THR2_OperatorInterpreter.step,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformBindings.step,
    PV_THR2_BindingRegister.register,PV_THR2_LocalBinding.selected,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,
    PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node11,PV_THR2_F170.node12,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,
    kind,PV_LIB_SPEC_TlsPoll15.kind,PV_THR2_AggregateCompletion.carrier,missing]
#print axioms kind
#print axioms after
#print axioms construct
end PV_LIB_SPEC_TlsNone15
