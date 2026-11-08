import PV_LIB_SPEC_TlsEntry14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F17Entry14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def site : Site := match PV_THR2_F17.node6 with
  | .leaf (.call site _ _ _ _) => site | _ => ⟨0,0,.null⟩
def after (s : Store Data) (a : Nat) (q : Address) (fn : Data) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  stage (PV_THR2_F17Call.issued s a q fn) s.nextActivation
    (PV_THR2_F17Call.parent s a q fn :: parents) PV_THR2_F170.live.body w es
    (⟨site,a,.child PV_THR2_F17Call.callee s.nextActivation
      [PV_STX2_TypedReferences.reference q .null,fn]⟩ :: issued) consumed

theorem enter (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (q : Address) (fn : Data) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context)
    (keyBound : s.cells ⟨a,1,[]⟩ = some (PV_STX2_TypedReferences.reference q .null))
    (fnBound : s.cells ⟨a,2,[]⟩ = some fn) :
    PV_LIB_SPEC_ReachedNative14.run cut p 8
      (stage s a parents PV_THR2_F17.live.body w es issued consumed) =
    after s a q fn parents w es issued consumed := by
  have unitLiteral : (runtime p).carrier.constant
      (.object [("kind",.object [("Adt",.array [.null,.array []])]),("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
  have reference (q : Address) : (runtime p).carrier.reference q .null = PV_STX2_TypedReferences.reference q .null := rfl
  have dereference (q : Address) : (runtime p).carrier.dereference w
      (PV_STX2_TypedReferences.reference q .null) = some q := by
    simp only [runtime,PV_THR2_OwnInitExactReturnedCases.carrier,
      PV_THR2_EntryDynamic.carrier,PV_THR2_Scalars.carrier,
      PV_STX2_TypedReferences.carrier,PV_STX2_TypedReferences.roundtrip]
  have lookup : PV_LIB_SPEC_Full.programs PV_THR2_F17Call.callee = some PV_THR2_F170.live := rfl
  simp [PV_THR2_F17Call.callee,PV_THR2_F17.node6] at lookup
  simp [stage,after,site,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
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
    PV_THR2_F17.live,PV_THR2_F17.block45,PV_THR2_F17.node0,PV_THR2_F17.node1,
    PV_THR2_F17.node2,PV_THR2_F17.node3,PV_THR2_F17.node4,PV_THR2_F17.node5,PV_THR2_F17.node6,PV_THR2_F17.node7,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,
    PV_THR2_F17Call.issued,PV_THR2_F17Call.callee,PV_THR2_F17Prefix.prepared,
    PV_THR2_F17Call.parent,PV_STX2_Native.arguments,keyBound,fnBound,unitLiteral,reference,dereference,lookup]

#print axioms site
#print axioms after
#print axioms enter
end PV_LIB_SPEC_F17Entry14
