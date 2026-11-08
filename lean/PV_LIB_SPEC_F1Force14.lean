import PV_LIB_SPEC_F1Arithmetic14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F1Force14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def after (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  stage (PV_THR2_F1Force.prepared s a (.boolean true) true) a parents
    (PV_THR2_F1.live.body.drop 10) w es issued consumed

theorem forced (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context)
    (small : s.cells ⟨a,4,[]⟩ = some (.boolean true))
    (force : s.cells ⟨a,3,[]⟩ = some (.boolean true)) :
    PV_LIB_SPEC_ReachedNative14.run cut p 6
      (stage s a parents (PV_THR2_F1.live.body.drop 9) w es issued consumed) =
    after s a parents w es issued consumed := by
  have truth : (runtime p).carrier.truth (.boolean true) = some true := rfl
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
    PV_THR2_F1.live,PV_THR2_F1.block192,PV_THR2_F1.node45,PV_THR2_F1.block41,
    PV_THR2_F1.block44,PV_THR2_F1.node42,PV_THR2_F1.node43,
    PV_THR2_F1.node9,PV_THR2_F1.node10,PV_THR2_F1.node11,PV_THR2_F1.node12,
    PV_THR2_F1.node40,PV_THR2_F1.block13,native,adopt,PV_STX2_Native.step,
    PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,locate,writeAddress,write,
    PV_THR2_F1Force.prepared,small,force,truth]

def store : Store Data := PV_THR2_F1Arithmetic.compared PV_LIB_SPEC_F1Arithmetic14.store
  2 (.number 32) (.boolean true)

theorem original (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 22
      (initial PV_LIB_SPEC_Entry14.input) =
    after store 2 PV_LIB_SPEC_F1Arithmetic14.parents PV_LIB_SPEC_Entry14.state []
      PV_LIB_SPEC_F1Arithmetic14.issued [] := by
  rw [show 22=16+6 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_F1Arithmetic14.original]
  apply forced
  · exact PV_STX2_Store.write_same _ _ _
  · simp [store,PV_THR2_F1Arithmetic.compared,PV_LIB_SPEC_F1Arithmetic14.store,
      PV_FN_THREAD_f1Entry.prepared,PV_FN_THREAD_f0Entry.issued,PV_FN_THREAD_f0Entry.prepared,
      PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,PV_STX2_Store.write,
      show PV_LIB_SPEC_Entry13.store.nextActivation = 2 from rfl]

#print axioms after
#print axioms forced
#print axioms store
#print axioms original
end PV_LIB_SPEC_F1Force14
