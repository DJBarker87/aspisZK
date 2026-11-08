import PV_LIB_A_F5History16
import PV_THR2_ActiveRequest
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_A_F5Call16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def site : Site := match PV_THR2_F5.node8 with | .leaf (.call site _ _ _ _) => site | _ => ⟨0,0,.null⟩
theorem shape : PV_THR2_F5.live.body.drop 8 =
    .leaf (.call site PV_THR2_ActivePrefix.descriptors.1 [.move (.local 2),.move (.local 4)] (.local 1) []) ::
      PV_THR2_F5.live.body.drop 9 := rfl

theorem run (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) :
    (PV_LIB_SPEC_ReachedNative14.run cut p 1
      (stage (PV_THR2_ActivePrefix.prepared s a p.needsDrop) a parents
        (PV_THR2_F5.live.body.drop 8) w es issued consumed)).state =
      ⟨⟨.running (PV_THR2_ActiveRequest.pending s a parents p.needsDrop),w,es⟩,[]⟩ := by
  apply PV_LIB_SPEC_SourceProjection15.transport cut p H 1 _ _
  · rw [shape]
    simp [PV_LIB_SPEC_SourceTransport15.Trace,PV_LIB_SPEC_SourceTransport15.Quiet,
      PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_StoreActionTable.Neutral,PV_LIB_StoreActionTable.select,
      PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,
      PV_THR2_OwnUniformNeutral.configuration,PV_THR2_OwnUniformNeutral.instruction,
      PV_THR2_InterpreterAgreement.NativeAgree,PV_THR2_HandlerExecutionAgreement.Agree,
      PV_THR2_Catch316Segment.select,stage,site,PV_THR2_F5.node8]
  · dsimp only [stage]
    rw [PV_THR2_IntrinsicTraceLift.run _ _ _ _ _ _ _ (by
      intro k hk
      have eq : k=0 := by omega
      subst k
      rfl)]
    exact congrArg (fun q => (⟨q,[]⟩ : PV_LIB_StoreActionTable.State))
      (PV_THR2_ActiveRequest.issue (runtime p).carrier (runtime p).control PV_LIB_SPEC_Full.programs H
        s a parents p.needsDrop w es)

def at132 (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  ⟨⟨.running (PV_THR2_ActiveRequest.pending PV_LIB_A_F5History16.store PV_LIB_A_F5History16.activation
    PV_LIB_A_F5History16.parents PV_LIB_SPEC_ReachedEnvironment14.parameters.needsDrop),e.world,[]⟩,[]⟩

theorem original132 (e : PV_LIB_SPEC_EntryWorld18.Entry) (frameActivation : Nat) :
    (PV_LIB_SPEC_LaneAJoins18.history e frameActivation 132).state = at132 e := by
  apply PV_LIB_A_HistoryExtend16.extend e frameActivation 131 1 PV_LIB_A_F5History16.prepared
    PV_LIB_A_F5History16.activation PV_LIB_A_F5History16.parents (PV_THR2_F5.live.body.drop 8) (at132 e)
  · exact PV_LIB_A_F5History16.original131 e frameActivation
  · intro issued consumed
    exact run (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e frameActivation))
      PV_LIB_SPEC_ReachedEnvironment14.parameters (fun _ w => ⟨.pending,w,[]⟩)
      PV_LIB_A_F5History16.store PV_LIB_A_F5History16.activation PV_LIB_A_F5History16.parents
      e.world [] issued consumed

#print axioms shape
#print axioms run
#print axioms original132
end PV_LIB_A_F5Call16
