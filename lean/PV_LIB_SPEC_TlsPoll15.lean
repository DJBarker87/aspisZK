import PV_LIB_SPEC_TlsOriginal14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsPoll15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def kind : Data := match PV_THR2_F170.node12 with
  | .leaf (.aggregateMove _ _ k _) => k | _ => .null

def prepared (s : Store Data) (a : Nat) : Store Data :=
  write (write (write (write (write (write (write (write (write (write s
    ⟨a,0,[]⟩ none) ⟨a,18,[]⟩ none) ⟨a,18,[]⟩ (some (.boolean false)))
    ⟨a,18,[]⟩ (some (.boolean true))) ⟨a,3,[]⟩ none) ⟨a,4,[]⟩ none)
    ⟨a,5,[]⟩ none) ⟨a,6,[]⟩ none) ⟨a,7,[]⟩ none) ⟨a,8,[]⟩ none

def after (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  stage (prepared s a) a parents (PV_THR2_F170.live.body.drop 10) w es issued consumed

theorem prepare (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_ReachedNative14.run cut p 10
      (stage s a parents PV_THR2_F170.live.body w es issued consumed) =
    after s a parents w es issued consumed := by
  have boolFalse : (runtime p).carrier.constant
    (.object [("kind",.object [("Literal",.object [("Bool",.boolean false)])]),("ty",.object [("Deduplicated",.number 556)])]) = some (.boolean false) := rfl
  have boolTrue : (runtime p).carrier.constant
    (.object [("kind",.object [("Literal",.object [("Bool",.boolean true)])]),("ty",.object [("Deduplicated",.number 556)])]) = some (.boolean true) := rfl
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
    PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node0,PV_THR2_F170.node1,PV_THR2_F170.node2,PV_THR2_F170.node3,PV_THR2_F170.node4,PV_THR2_F170.node5,PV_THR2_F170.node6,PV_THR2_F170.node7,PV_THR2_F170.node8,PV_THR2_F170.node9,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,
    prepared,boolFalse,boolTrue]
#print axioms kind
#print axioms prepared
#print axioms after
#print axioms prepare
end PV_LIB_SPEC_TlsPoll15
