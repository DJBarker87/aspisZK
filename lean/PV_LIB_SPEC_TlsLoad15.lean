import PV_LIB_SPEC_TlsPoll15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsLoad15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def after (s : Store Data) (a : Nat) (inner : Data) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  stage (write s ⟨a,8,[]⟩ (some inner)) a parents (PV_THR2_F170.live.body.drop 11) w es issued consumed

theorem load (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (q : Address) (key inner : Data) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context)
    (bound : s.cells ⟨a,1,[]⟩ = some (PV_STX2_TypedReferences.reference q .null))
    (keyRead : readAddress (runtime p).carrier s q = some key)
    (field : (runtime p).carrier.field key 0 = some inner) :
    PV_LIB_SPEC_ReachedNative14.run cut p 1
      (stage s a parents (PV_THR2_F170.live.body.drop 10) w es issued consumed) =
    after s a inner parents w es issued consumed := by
  have deref : (runtime p).carrier.dereference w (PV_STX2_TypedReferences.reference q .null) = some q := by
    simp only [runtime,PV_THR2_OwnInitExactReturnedCases.carrier,
      PV_THR2_EntryDynamic.carrier,PV_THR2_Scalars.carrier,
      PV_STX2_TypedReferences.carrier,PV_STX2_TypedReferences.roundtrip]
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
    PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node10,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,
    bound,deref,keyRead,field]
#print axioms after
#print axioms load
end PV_LIB_SPEC_TlsLoad15
