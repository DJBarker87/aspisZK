import PV_LIB_SPEC_F1Force14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Worker14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def site : Site := match PV_THR2_F1.node47 with
  | .leaf (.call site _ _ _ _) => site | _ => ⟨0,0,.null⟩
def after (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  stage (PV_THR2_F1Worker.issued s a) s.nextActivation
    (PV_THR2_F1Worker.parent s a :: parents) PV_THR2_F2.live.body w es
    (⟨site,a,.child PV_THR2_Table.workerCallee s.nextActivation []⟩ :: issued) consumed

def pending (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  ⟨⟨⟨.running ⟨PV_THR2_F1Worker.parent s a,parents,PV_THR2_F1Worker.issued s a⟩,w,es⟩,[]⟩,
    ⟨site,a,.child PV_THR2_Table.workerCallee s.nextActivation []⟩ :: issued,consumed⟩

theorem issue (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_ReachedNative14.run cut p 2
      (stage s a parents (PV_THR2_F1.live.body.drop 10) w es issued consumed) =
    pending s a parents w es issued consumed := by
  simp [stage,pending,site,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
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
    PV_THR2_F1.live,PV_THR2_F1.block192,PV_THR2_F1.node46,PV_THR2_F1.node47,
    PV_THR2_F1.node49,native,adopt,PV_STX2_Native.step,PV_STX2_Native.arguments,operands,
    PV_THR2_F1Worker.issued,PV_THR2_F1Worker.parent,
    PV_THR2_Table.workerCallee,write]

theorem push (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_ReachedNative14.step cut p (pending s a parents w es issued consumed) =
    after s a parents w es issued consumed := by
  have lookup : PV_LIB_SPEC_Full.programs PV_THR2_Table.workerCallee = some PV_THR2_F2.live := rfl
  have own : PV_THR2_OwnInitAction.selected
      ⟨PV_THR2_F1Worker.parent s a,parents,PV_THR2_F1Worker.issued s a⟩ = false := rfl
  have operator : PV_THR2_OperatorAction.selected
      ⟨PV_THR2_F1Worker.parent s a,parents,PV_THR2_F1Worker.issued s a⟩ = none := rfl
  simp only [PV_THR2_F1Worker.parent] at own operator
  simp only [PV_LIB_SPEC_ReachedNative14.step,pending,
    PV_LIB_SPEC_ControlRuntime.ordinary,PV_THR2_Catch316Segment.select,
    PV_THR2_F1Worker.parent,lookup,Option.isSome_some]
  simp [PV_LIB_SPEC_ReachedNative14.control,PV_LIB_SPEC_ReachedNative14.transition,
    PV_LIB_StoreActionTable.step,PV_LIB_StoreActionTable.select,
    PV_THR2_Catch316Segment.select,PV_THR2_OwnInitInterpreterBridged.step,own,
    PV_THR2_OperatorInterpreter.step,operator,PV_THR2_OwnUniformBindings.step,
    PV_THR2_BindingRegister.register,PV_THR2_LocalBinding.selected,
    PV_THR2_IntrinsicState.step,PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_STX2_SliceMachine.step,
    PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    after,stage,PV_THR2_F1Worker.parent,lookup]

theorem enter (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_ReachedNative14.run cut p 3
      (stage s a parents (PV_THR2_F1.live.body.drop 10) w es issued consumed) =
    after s a parents w es issued consumed := by
  rw [show 3=2+1 from rfl,PV_LIB_SPEC_Original14.run_add,issue]
  exact push cut p s a parents w es issued consumed

def store : Store Data := PV_THR2_F1Force.prepared PV_LIB_SPEC_F1Force14.store 2 (.boolean true) true

theorem original (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 25
      (initial PV_LIB_SPEC_Entry14.input) =
    after store 2 PV_LIB_SPEC_F1Arithmetic14.parents PV_LIB_SPEC_Entry14.state []
      PV_LIB_SPEC_F1Arithmetic14.issued [] := by
  rw [show 25=22+3 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_F1Force14.original]
  exact enter cut _ _ _ _ _ _ _ _

#print axioms site
#print axioms after
#print axioms pending
#print axioms issue
#print axioms push
#print axioms enter
#print axioms store
#print axioms original
end PV_LIB_SPEC_Worker14
