import PV_LIB_SPEC_TlsAt55
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls277Request15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def site : Site := match PV_THR2_F170.node16 with
  | .leaf (.call site _ _ _ _) => site | _ => ⟨0,0,.null⟩
def after (s : Store Data) (a : Nat) (value : Data) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  ⟨⟨⟨.running (PV_THR2_RunTlsNext.pending s a parents value),w,es⟩,[]⟩,
    ⟨site,a,.child PV_THR2_RunTlsNext.callee s.nextActivation [value]⟩ :: issued,consumed⟩

theorem request (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (value : Data) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context)
    (bound : s.cells ⟨a,7,[]⟩ = some value) :
    PV_LIB_SPEC_ReachedNative14.run cut p 3
      (stage s a parents (PV_THR2_F170.live.body.drop 14) w es issued consumed) =
    after s a value parents w es issued consumed := by
  simp [stage,after,site,PV_THR2_RunTlsNext.pending,PV_THR2_RunTlsNext.issued,PV_THR2_RunTlsNext.callee,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    PV_LIB_SPEC_ReachedNative14.run,PV_LIB_SPEC_ReachedNative14.step,
    PV_LIB_SPEC_ReachedNative14.control,PV_LIB_SPEC_ReachedNative14.transition,
    PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_StoreActionTable.step,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitInterpreterBridged.step,PV_THR2_OwnInitAction.selected,
    PV_THR2_OperatorInterpreter.step,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformBindings.step,
    PV_THR2_BindingRegister.register,PV_THR2_LocalBinding.selected,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,
    PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node14,PV_THR2_F170.node15,PV_THR2_F170.node16,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,
    bound,PV_STX2_Native.arguments]
#print axioms site
#print axioms after
#print axioms request
end PV_LIB_SPEC_Tls277Request15
