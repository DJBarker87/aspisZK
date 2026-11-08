import PV_LIB_A_F17History16
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_A_F17Finish16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

theorem trace (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (s : Store Data) (a : Nat) (parent : Frame) (parents : List Frame) (v : Data)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context)
    (cell : s.cells ⟨a,0,[]⟩ = some v) :
    PV_LIB_SPEC_SourceTransport15.Trace cut p H 8
      (stage s a (parent::parents) (PV_THR2_F17.live.body.drop 15) w es issued consumed) := by
  have shape : PV_THR2_F17.live.body.drop 15 =
      [PV_THR2_F17.node38,PV_THR2_F17.node39,PV_THR2_F17.node40,
       PV_THR2_F17.node41,PV_THR2_F17.node42,PV_THR2_F17.node43,PV_THR2_F17.node44] := rfl
  rw [shape]
  simp [PV_LIB_SPEC_SourceTransport15.Trace,PV_LIB_SPEC_SourceTransport15.sourceStep,
    PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_SPEC_ControlRuntime.ordinary,
    PV_LIB_StoreActionTable.Neutral,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformNeutral.configuration,
    PV_THR2_OwnUniformNeutral.instruction,PV_THR2_InterpreterAgreement.NativeAgree,
    PV_THR2_HandlerExecutionAgreement.Agree,stage,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_F17.node38,PV_THR2_F17.node39,
    PV_THR2_F17.node40,PV_THR2_F17.node41,PV_THR2_F17.node42,
    PV_THR2_F17.node43,PV_THR2_F17.node44,native,adopt,
    PV_STX2_Native.step,PV_STX2_Store.read,cell,
    PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,
    PV_STX2_Native.storeResult,locate,writeAddress,write]

theorem clear (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parent : Frame) (parents : List Frame) (v : Data) (w : OWNER) (es : List Event)
    (cell : s.cells ⟨a,0,[]⟩ = some v) :
    ∀ k, k<8 → PV_THR2_IntrinsicTraceLift.Clear
      (PV_THR2_Execution.advance (runtime p).carrier (runtime p).control
        PV_LIB_SPEC_Full.programs H k
        ⟨.running ⟨{activation := a,remaining := PV_THR2_F17.live.body.drop 15},parent::parents,s⟩,w,es⟩) := by
  intro k hk
  have shape : PV_THR2_F17.live.body.drop 15 =
      [PV_THR2_F17.node38,PV_THR2_F17.node39,PV_THR2_F17.node40,
       PV_THR2_F17.node41,PV_THR2_F17.node42,PV_THR2_F17.node43,PV_THR2_F17.node44] := rfl
  rw [shape]
  interval_cases k <;>
    simp [PV_THR2_IntrinsicTraceLift.Clear,PV_THR2_Execution.advance,
      PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_F17.node38,PV_THR2_F17.node39,
    PV_THR2_F17.node40,PV_THR2_F17.node41,PV_THR2_F17.node42,
    PV_THR2_F17.node43,PV_THR2_F17.node44,native,adopt,
    PV_STX2_Native.step,PV_STX2_Store.read,cell,
    PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,
    PV_STX2_Native.storeResult,locate,writeAddress,write]

theorem run (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (s : Store Data) (a : Nat) (parent : Frame) (parents : List Frame)
    (wait : PV_STX2_Native.Waiting Data) (v : Data) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context)
    (cell : s.cells ⟨a,0,[]⟩ = some v)
    (saved : parent.waiting = some wait) (action : wait.action = .child a (.local 0)) :
    (PV_LIB_SPEC_ReachedNative14.run cut p 8
      (stage s a (parent::parents) (PV_THR2_F17.live.body.drop 15) w es issued consumed)).state =
    ⟨⟨.running ⟨{parent with waiting := none},parents,
      write (write (PV_THR2_RunWithReturn.prepared s a) ⟨a,0,[]⟩ (some v))
        ⟨parent.activation,0,[]⟩ (some v)⟩,w,es⟩,[]⟩ := by
  apply PV_LIB_SPEC_SourceProjection15.transport cut p H 8 _ _
    (trace cut p H s a parent parents v w es issued consumed cell)
  dsimp only [stage]
  rw [PV_THR2_IntrinsicTraceLift.run _ _ _ _ _ _ _ (clear p H s a parent parents v w es cell)]
  exact congrArg (fun q => (⟨q,[]⟩ : PV_LIB_StoreActionTable.State))
    (PV_THR2_RunWithReturn.finish (runtime p).carrier (runtime p).control PV_LIB_SPEC_Full.programs H
      s a parent parents wait v w es cell saved action)

#print axioms trace
#print axioms clear
#print axioms run
end PV_LIB_A_F17Finish16
