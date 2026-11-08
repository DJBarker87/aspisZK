import PV_LIB_SPEC_Original14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F1Prefix14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory

def start (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) : Execution :=
  ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F1.live.body},parents,s⟩,w,es⟩,[]⟩,issued,consumed⟩
def after (s : Store Data) (a : Nat) (parents : List Frame) (n : Data)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F1.live.body.drop 6},parents,
    PV_FN_THREAD_f1Entry.prepared s a n⟩,w,es⟩,[]⟩,issued,consumed⟩

/-- Six actual f1 source instructions on the final concrete-Values assembly.
Only the existing source argument is used, preserving both history lists. -/
theorem prepare (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (parents : List Frame) (n : Data)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context)
    (nCell : s.cells ⟨a,1,[]⟩ = some n) :
    PV_LIB_SPEC_ReachedNative14.run cut p 6 (start s a parents w es issued consumed) =
      after s a parents n w es issued consumed := by
  have shape : PV_THR2_F1.live.body =
      [PV_THR2_F1.node0,PV_THR2_F1.node1,PV_THR2_F1.node2,PV_THR2_F1.node3,
       PV_THR2_F1.node4,PV_THR2_F1.node5] ++ PV_THR2_F1.live.body.drop 6 := rfl
  unfold start after
  rw [shape]
  generalize tail : PV_THR2_F1.live.body.drop 6 = rest
  simp [PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    PV_LIB_SPEC_ReachedNative14.run,PV_LIB_SPEC_ReachedNative14.step,
    PV_LIB_SPEC_ReachedNative14.control,PV_LIB_SPEC_ReachedNative14.transition,
    PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_StoreActionTable.step,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitInterpreterBridged.step,PV_THR2_OwnInitAction.selected,
    PV_THR2_OperatorInterpreter.step,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformBindings.step,
    PV_THR2_BindingRegister.register,PV_THR2_LocalBinding.selected,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_F1.node0,PV_THR2_F1.node1,
    PV_THR2_F1.node2,PV_THR2_F1.node3,PV_THR2_F1.node4,PV_THR2_F1.node5,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operand,
    PV_STX2_Store.read,locate,writeAddress,write,PV_FN_THREAD_f1Entry.prepared,nCell]

/-- Continuously from the SAME original entry: native-free f1 prologue ends
at the emitted multiplication36. This is not the ThreadInit milestone. -/
theorem original (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 13
      (initial PV_LIB_SPEC_Entry14.input) =
    after (PV_FN_THREAD_f0Entry.issued PV_LIB_SPEC_Entry13.store 1 (.number 1)
      PV_LIB_SPEC_ConcreteCaptures.closure (.boolean true)) 2
      [PV_FN_THREAD_f0Entry.parent PV_LIB_SPEC_Entry13.store 1 (.number 1)
        PV_LIB_SPEC_ConcreteCaptures.closure (.boolean true)] (.number 1)
      PV_LIB_SPEC_Entry14.state []
      (PV_LIB_SPEC_Original14.after PV_LIB_SPEC_Entry13.store 1 1
        PV_LIB_SPEC_ConcreteCaptures.closure PV_LIB_SPEC_Entry14.state []).issued [] := by
  rw [show 13=7+6 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_Original14.original_body]
  apply prepare
  simp [PV_FN_THREAD_f0Entry.issued,PV_FN_THREAD_f0Entry.prepared,PV_THR2_StaticCall.issued,
    PV_STX2_Native.arguments,PV_STX2_Store.write]

#print axioms start
#print axioms after
#print axioms prepare
#print axioms original
end PV_LIB_SPEC_F1Prefix14
