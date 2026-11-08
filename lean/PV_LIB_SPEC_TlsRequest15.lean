import PV_LIB_SPEC_TlsNone15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsRequest15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def site : Site := match PV_THR2_F170.node13 with
  | .leaf (.call site _ _ _ _) => site | _ => ⟨0,0,.null⟩
def issuedStore (s : Store Data) (a : Nat) (init : Data) : Store Data :=
  PV_STX2_Native.arguments s.nextActivation [init] 1
    {write (write s ⟨a,8,[]⟩ none) ⟨a,9,[]⟩ none with nextActivation := s.nextActivation+1}
def after (s : Store Data) (a : Nat) (fn init : Data) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 14, waiting := some ⟨.child fn s.nextActivation [init],.child s.nextActivation (.local 7),[]⟩},
    parents,issuedStore s a init⟩,w,es⟩,[]⟩,
    ⟨site,a,.child fn s.nextActivation [init]⟩ :: issued,consumed⟩

theorem request (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (fn init : Data) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context)
    (bound : s.cells ⟨a,8,[]⟩ = some fn)
    (initBound : s.cells ⟨a,9,[]⟩ = some init) :
    PV_LIB_SPEC_ReachedNative14.run cut p 1
      (stage s a parents (PV_THR2_F170.live.body.drop 13) w es issued consumed) =
    after s a fn init parents w es issued consumed := by
  simp [stage,after,site,issuedStore,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
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
    PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node13,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,
    bound,initBound,PV_STX2_Native.arguments]
#print axioms site
#print axioms issuedStore
#print axioms after
#print axioms request
end PV_LIB_SPEC_TlsRequest15
