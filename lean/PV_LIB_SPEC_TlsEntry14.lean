import PV_LIB_SPEC_F1Force14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsEntry14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def key (p : Parameters) : Data := PV_THR2_KeyInitConstruct.key p.needsDrop
def site : Site := match PV_THR2_F2.node5 with
  | .leaf (.call site _ _ _ _) => site | _ => ⟨0,0,.null⟩
def after (p : Parameters) (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  stage (PV_THR2_F2Call.issued s a (key p) PV_THR2_F2Call.descriptors.2) s.nextActivation
    (PV_THR2_F2Child.parent s a PV_THR2_F2Call.descriptors.2 :: parents)
    PV_THR2_F17.live.body w es
    (⟨site,a,.child PV_THR2_F2Call.descriptors.1 s.nextActivation
      [PV_STX2_TypedReferences.reference ⟨a,2,[]⟩ .null,PV_THR2_F2Call.descriptors.2]⟩ :: issued) consumed

theorem enter (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_ReachedNative14.run cut p 7
      (stage s a parents PV_THR2_F2.live.body w es issued consumed) =
    after p s a parents w es issued consumed := by
  have global : (runtime p).carrier.global w 1 = some (key p) := rfl
  have literal : (runtime p).carrier.constant PV_THR2_F2Call.descriptors.2 = some PV_THR2_F2Call.descriptors.2 := rfl
  have unitLiteral : (runtime p).carrier.constant
      (.object [("kind",.object [("Adt",.array [.null,.array []])]),("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
  have reference (q : Address) : (runtime p).carrier.reference q .null = PV_STX2_TypedReferences.reference q .null := rfl
  have lookup : PV_LIB_SPEC_Full.programs PV_THR2_F2Call.descriptors.1 = some PV_THR2_F17.live := rfl
  have different : PV_THR2_F2Call.descriptors.1 ≠ PV_THR2_Catch219Call318.fn := by
    intro h
    have eq := congrArg PV_THR2_OffPath.functionId h
    change some 17 = some 318 at eq
    cases eq
  simp [PV_THR2_F2Call.descriptors,PV_THR2_F2.node5] at literal lookup different
  simp [stage,after,site,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    PV_LIB_SPEC_ReachedNative14.run,PV_LIB_SPEC_ReachedNative14.step,
    PV_LIB_SPEC_ReachedNative14.control,PV_LIB_SPEC_ReachedNative14.transition,
    PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_StoreActionTable.step,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitInterpreterBridged.step,PV_THR2_OwnInitAction.selected,
    PV_THR2_OperatorInterpreter.step,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformBindings.step,
    PV_THR2_BindingRegister.register,PV_THR2_LocalBinding.selected,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,PV_THR2_GapCompletion.step,
    PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,
    PV_THR2_F2.live,PV_THR2_F2.block9,PV_THR2_F2.node0,PV_THR2_F2.node1,
    PV_THR2_F2.node2,PV_THR2_F2.node3,PV_THR2_F2.node4,PV_THR2_F2.node5,PV_THR2_F2.node6,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,
    PV_THR2_F2Call.issued,PV_THR2_F2Call.descriptors,PV_THR2_F2Prefix.prepared,
    PV_THR2_F2Child.parent,PV_STX2_Native.arguments,global,literal,unitLiteral,reference,lookup,different]

#print axioms key
#print axioms site
#print axioms after
#print axioms enter
end PV_LIB_SPEC_TlsEntry14
