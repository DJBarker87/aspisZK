import PV_LIB_A_F5Entry16
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_A_F5Prefix16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

theorem trace (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_SourceTransport15.Trace cut p H 8
      (stage s a parents PV_THR2_F5.live.body w es issued consumed) := by
  have shape : PV_THR2_F5.live.body =
      [PV_THR2_F5.node0,PV_THR2_F5.node1,PV_THR2_F5.node2,PV_THR2_F5.node3,
       PV_THR2_F5.node4,PV_THR2_F5.node5,PV_THR2_F5.node6,PV_THR2_F5.node7] ++ PV_THR2_F5.live.body.drop 8 := rfl
  rw [shape]
  generalize hrest : PV_THR2_F5.live.body.drop 8 = rest
  have key : (runtime p).carrier.global w 1 = some (PV_THR2_KeyInitConstruct.key p.needsDrop) := rfl
  have unit : (runtime p).carrier.constant
      (.object [("kind",.object [("Adt",.array [.null,.array []])]),("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
  have missing : (runtime p).carrier.aggregate PV_THR2_ActivePrefix.descriptors.2 [] = none := rfl
  have ref : (runtime p).carrier.reference ⟨a,3,[]⟩ .null = PV_STX2_TypedReferences.reference ⟨a,3,[]⟩ .null := rfl
  simp only [PV_THR2_ActivePrefix.descriptors,PV_THR2_F5.node7,PV_THR2_F5.node8] at missing
  simp [PV_LIB_SPEC_SourceTransport15.Trace,PV_LIB_SPEC_SourceTransport15.sourceStep,
    PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_SPEC_ControlRuntime.ordinary,
    PV_LIB_StoreActionTable.Neutral,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformNeutral.configuration,
    PV_THR2_OwnUniformNeutral.instruction,PV_THR2_InterpreterAgreement.NativeAgree,
    PV_THR2_HandlerExecutionAgreement.Agree,stage,PV_THR2_IntrinsicState.step,
    PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,PV_THR2_AggregateCompletion.carrier,
    PV_STX2_SliceMachine.step,PV_THR2_F5.node0,PV_THR2_F5.node1,PV_THR2_F5.node2,
    PV_THR2_F5.node3,PV_THR2_F5.node4,PV_THR2_F5.node5,PV_THR2_F5.node6,PV_THR2_F5.node7,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,key,unit,missing,ref]

theorem clear (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (w : OWNER) (es : List Event) :
    ∀ k, k<8 → PV_THR2_IntrinsicTraceLift.Clear
      (PV_THR2_Execution.advance (runtime p).carrier (runtime p).control
        PV_LIB_SPEC_Full.programs H k
        ⟨.running ⟨{activation := a,remaining := PV_THR2_F5.live.body},parents,s⟩,w,es⟩) := by
  intro k hk
  have shape : PV_THR2_F5.live.body =
      [PV_THR2_F5.node0,PV_THR2_F5.node1,PV_THR2_F5.node2,PV_THR2_F5.node3,
       PV_THR2_F5.node4,PV_THR2_F5.node5,PV_THR2_F5.node6,PV_THR2_F5.node7] ++ PV_THR2_F5.live.body.drop 8 := rfl
  rw [shape]
  generalize hrest : PV_THR2_F5.live.body.drop 8 = rest
  have key : (runtime p).carrier.global w 1 = some (PV_THR2_KeyInitConstruct.key p.needsDrop) := rfl
  have unit : (runtime p).carrier.constant
      (.object [("kind",.object [("Adt",.array [.null,.array []])]),("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
  have missing : (runtime p).carrier.aggregate PV_THR2_ActivePrefix.descriptors.2 [] = none := rfl
  have ref : (runtime p).carrier.reference ⟨a,3,[]⟩ .null = PV_STX2_TypedReferences.reference ⟨a,3,[]⟩ .null := rfl
  simp only [PV_THR2_ActivePrefix.descriptors,PV_THR2_F5.node7,PV_THR2_F5.node8] at missing
  interval_cases k <;>
    simp [PV_THR2_IntrinsicTraceLift.Clear,PV_THR2_Execution.advance,
      PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,PV_THR2_AggregateCompletion.carrier,
    PV_STX2_SliceMachine.step,PV_THR2_F5.node0,PV_THR2_F5.node1,PV_THR2_F5.node2,
    PV_THR2_F5.node3,PV_THR2_F5.node4,PV_THR2_F5.node5,PV_THR2_F5.node6,PV_THR2_F5.node7,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,key,unit,missing,ref]

theorem source (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (w : OWNER) (es : List Event) :
    PV_THR2_IntrinsicState.advance (runtime p).carrier (runtime p).control
      PV_LIB_SPEC_Full.programs H 8
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F5.live.body},parents,s⟩,w,es⟩,[]⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F5.live.body.drop 8},parents,
        PV_THR2_ActivePrefix.prepared s a p.needsDrop⟩,w,es⟩,[]⟩ := by
  rw [PV_THR2_IntrinsicTraceLift.run _ _ _ _ _ _ _ (clear p H s a parents w es)]
  exact congrArg (fun q => (⟨q,[]⟩ : PV_LIB_StoreActionTable.State))
    (PV_THR2_ActivePrefix.prepare (PV_THR2_ThreadFields.carrier (PV_LIB_A_F17ValueLift16.base p))
      (PV_THR2_ThreadFields.control p.control) PV_LIB_SPEC_Full.programs H s a parents p.needsDrop w es)

theorem run (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) :
    (PV_LIB_SPEC_ReachedNative14.run cut p 8
      (stage s a parents PV_THR2_F5.live.body w es issued consumed)).state =
      (stage (PV_THR2_ActivePrefix.prepared s a p.needsDrop) a parents
        (PV_THR2_F5.live.body.drop 8) w es issued consumed).state := by
  exact PV_LIB_SPEC_SourceProjection15.transport cut p H 8 _ _
    (trace cut p H s a parents w es issued consumed) (source p H s a parents w es)

#print axioms trace
#print axioms clear
#print axioms source
#print axioms run
end PV_LIB_A_F5Prefix16
