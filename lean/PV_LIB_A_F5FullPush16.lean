import PV_LIB_A_F5BoundaryGap16
import PV_LIB_A_HistoryAny16
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_A_F5FullPush16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

theorem push (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_ReachedNative14.run cut p 1
      ⟨⟨⟨.running (PV_THR2_ActiveRequest.pending s a parents p.needsDrop),w,es⟩,[]⟩,issued,consumed⟩ =
    stage (PV_THR2_ActiveRequest.issued s a p.needsDrop) s.nextActivation
      ((PV_THR2_ActiveRequest.pending s a parents p.needsDrop).frame::parents)
      PV_THR2_F17.live.body w es issued consumed := by
  have resolved := PV_LIB_A_F5BoundaryGap16.full_lookup
  simp [stage,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    PV_LIB_SPEC_ReachedNative14.run,PV_LIB_SPEC_ReachedNative14.step,
    PV_LIB_SPEC_ReachedNative14.control,PV_LIB_SPEC_ReachedNative14.transition,
    PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_StoreActionTable.step,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitInterpreterBridged.step,PV_THR2_OwnInitAction.selected,
    PV_THR2_OperatorInterpreter.step,PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,
    PV_THR2_OwnUniformBindings.step,PV_THR2_BindingRegister.register,PV_THR2_LocalBinding.selected,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,
    PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,PV_THR2_GapCompletion.step,
    PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,native,adopt,
    PV_THR2_ActiveRequest.pending,resolved,PV_THR2_F5.live,PV_THR2_F5.block15,PV_THR2_F5.node9]

def store : Store Data := PV_THR2_ActiveRequest.issued PV_LIB_A_F5History16.store
  PV_LIB_A_F5History16.activation PV_LIB_SPEC_ReachedEnvironment14.parameters.needsDrop
def activation : Nat := PV_LIB_A_F5History16.store.nextActivation
def parents : List Frame :=
  (PV_THR2_ActiveRequest.pending PV_LIB_A_F5History16.store PV_LIB_A_F5History16.activation
    PV_LIB_A_F5History16.parents PV_LIB_SPEC_ReachedEnvironment14.parameters.needsDrop).frame :: PV_LIB_A_F5History16.parents

def at133 (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  (stage store activation parents PV_THR2_F17.live.body e.world [] [] []).state

theorem original133 (e : PV_LIB_SPEC_EntryWorld18.Entry) (a : Nat) :
    (PV_LIB_SPEC_LaneAJoins18.history e a 133).state = at133 e := by
  apply PV_LIB_A_HistoryAny16.extend e a 132 1 (PV_LIB_A_F5Call16.at132 e) (at133 e)
    (PV_LIB_A_F5Call16.original132 e a)
  intro issued consumed
  simpa only [PV_LIB_A_F5Call16.at132,at133,store,activation,parents,stage] using congrArg Execution.state
    (push (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e a))
      PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_A_F5History16.store PV_LIB_A_F5History16.activation
      PV_LIB_A_F5History16.parents e.world [] issued consumed)

#print axioms push
#print axioms original133
end PV_LIB_A_F5FullPush16
