import PV_LIB_SPEC_F1Prefix14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F1Arithmetic14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory

def stage (s : Store Data) (a : Nat) (parents : List Frame) (rest : List PV_STX2_SliceSyntax.Node)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  ⟨⟨⟨.running ⟨{activation := a,remaining := rest},parents,s⟩,w,es⟩,[]⟩,issued,consumed⟩
def after (s : Store Data) (a : Nat) (parents : List Frame) (n : Nat)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  stage (PV_THR2_F1Arithmetic.compared s a (.number 32) (.boolean (decide (n<32))))
    a parents (PV_THR2_F1.live.body.drop 9) w es issued consumed

theorem comparison (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a n : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context)
    (nCell : s.cells ⟨a,5,[]⟩ = some (.number n)) :
    PV_LIB_SPEC_ReachedNative14.run cut p 3
      (stage s a parents (PV_THR2_F1.live.body.drop 6) w es issued consumed) =
    after s a parents n w es issued consumed := by
  have global : (runtime p).carrier.global w 0 = some (.number 16) := rfl
  have literal : (runtime p).carrier.constant PV_THR2_F1Arithmetic.descriptors.2 = some (.number 2) := rfl
  have mul : (runtime p).control.binary PV_THR2_F1Arithmetic.descriptors.1 (.number 16) (.number 2) = some (.number 32) := rfl
  have lt : (runtime p).carrier.binary "Lt" (.number n) (.number 32) = some (.boolean (decide (n<32))) := rfl
  simp [PV_THR2_F1Arithmetic.descriptors,PV_THR2_F1.node6] at literal mul
  simp [stage,after,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    PV_LIB_SPEC_ReachedNative14.run,PV_LIB_SPEC_ReachedNative14.step,
    PV_LIB_SPEC_ReachedNative14.control,PV_LIB_SPEC_ReachedNative14.transition,
    PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_StoreActionTable.step,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitInterpreterBridged.step,PV_THR2_OwnInitAction.selected,
    PV_THR2_OperatorInterpreter.step,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformBindings.step,
    PV_THR2_BindingRegister.register,PV_THR2_LocalBinding.selected,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_GapCompletion.step,
    PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,
    PV_THR2_F1.live,PV_THR2_F1.block192,PV_THR2_F1.node6,PV_THR2_F1.node7,PV_THR2_F1.node8,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,PV_THR2_F1Arithmetic.compared,
    nCell,global,literal,mul,lt]

def store : Store Data := PV_FN_THREAD_f1Entry.prepared
  (PV_FN_THREAD_f0Entry.issued PV_LIB_SPEC_Entry13.store 1 (.number 1)
    PV_LIB_SPEC_ConcreteCaptures.closure (.boolean true)) 2 (.number 1)
def parents : List Frame :=
  [PV_FN_THREAD_f0Entry.parent PV_LIB_SPEC_Entry13.store 1 (.number 1)
    PV_LIB_SPEC_ConcreteCaptures.closure (.boolean true)]
def issued : List Issued := (PV_LIB_SPEC_Original14.after PV_LIB_SPEC_Entry13.store 1 1
  PV_LIB_SPEC_ConcreteCaptures.closure PV_LIB_SPEC_Entry14.state []).issued

/-- Original step16 is the computed true n<32 comparison. No arithmetic,
source-global or future-cell premise is inserted into the original Pre. -/
theorem original (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 16
      (initial PV_LIB_SPEC_Entry14.input) =
    after store 2 parents 1 PV_LIB_SPEC_Entry14.state [] issued [] := by
  rw [show 16=13+3 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_F1Prefix14.original]
  apply comparison
  simp [store,PV_FN_THREAD_f1Entry.prepared,PV_STX2_Store.write]

#print axioms stage
#print axioms after
#print axioms comparison
#print axioms store
#print axioms parents
#print axioms issued
#print axioms original
end PV_LIB_SPEC_F1Arithmetic14
