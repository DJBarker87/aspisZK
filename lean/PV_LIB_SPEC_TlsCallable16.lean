import PV_LIB_SPEC_TlsAt75
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsCallable16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

theorem trace (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) (fn actual : Data) (pointer : Address)
    (callable : s.cells ⟨a,2,[]⟩ = some fn)
    (reference : s.cells ⟨a,3,[]⟩ = some actual)
    (address : (runtime p).carrier.dereference w actual = some pointer) :
    PV_LIB_SPEC_SourceTransport15.Trace cut p H 9
      (stage s a parents (PV_THR2_F170.live.body.drop 31) w es issued consumed) := by
  have ref : (runtime p).carrier.reference pointer .null = PV_STX2_TypedReferences.reference pointer .null := rfl
  have tupleMissing : (runtime p).carrier.aggregate PV_THR2_RunTlsCallable.descriptors.2
      [PV_STX2_TypedReferences.reference pointer .null] = none := rfl
  have flag : (runtime p).carrier.constant PV_THR2_RunTlsCallable.literals.1 = some (.boolean false) := rfl
  have metadata : (runtime p).carrier.constant PV_THR2_RunTlsCallable.literals.2 = some .null := rfl
  simp only [PV_THR2_RunTlsCallable.descriptors,PV_THR2_F170.node54] at tupleMissing
  simp only [PV_THR2_RunTlsCallable.literals,PV_THR2_F170.node49,PV_THR2_F170.node53] at flag metadata
  simp [PV_LIB_SPEC_SourceTransport15.Trace,PV_LIB_SPEC_SourceTransport15.sourceStep,
    PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_SPEC_ControlRuntime.ordinary,
    PV_LIB_StoreActionTable.Neutral,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformNeutral.configuration,
    PV_THR2_OwnUniformNeutral.instruction,PV_THR2_InterpreterAgreement.NativeAgree,
    PV_THR2_HandlerExecutionAgreement.Agree,stage,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,
    PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,PV_THR2_GapCompletion.step,
    PV_THR2_AggregateCompletion.complete,PV_THR2_AggregateCompletion.carrier,
    PV_STX2_SliceMachine.step,PV_THR2_F170.live,PV_THR2_F170.block66,
    PV_THR2_F170.node47,PV_THR2_F170.node48,PV_THR2_F170.node49,PV_THR2_F170.node50,PV_THR2_F170.node51,PV_THR2_F170.node52,PV_THR2_F170.node53,PV_THR2_F170.node54,PV_THR2_F170.node55,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,PV_STX2_Store.write,callable,reference,address,tupleMissing,flag,metadata,ref]

def config (s : Store Data) (a : Nat) (parents : List Frame) (fn : Data) (pointer : Address) : Config :=
  ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 40,
    waiting := some ⟨.child PV_THR2_RunTlsCallable.descriptors.1 s.nextActivation
      [fn,PV_THR2_KeyValues.pack PV_THR2_RunTlsCallable.descriptors.2
        [PV_STX2_TypedReferences.reference pointer .null]],.child s.nextActivation (.local 14),[]⟩},
    parents,PV_THR2_RunTlsCallable.issued s a fn pointer⟩

theorem source (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (fn actual : Data) (pointer : Address) (w : OWNER) (es : List Event)
    (callable : s.cells ⟨a,2,[]⟩ = some fn)
    (reference : s.cells ⟨a,3,[]⟩ = some actual)
    (address : (runtime p).carrier.dereference w actual = some pointer) :
    PV_THR2_Execution.advance (runtime p).carrier (runtime p).control
      PV_LIB_SPEC_Full.programs H 9
      ⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 31},parents,s⟩,w,es⟩ =
      ⟨.running (config s a parents fn pointer),w,es⟩ := by
  exact PV_THR2_RunTlsCallable.request _ _ _ _ _ _ _ fn actual pointer p.needsDrop _ _
    callable reference address

#print axioms trace
#print axioms config
#print axioms source
end PV_LIB_SPEC_TlsCallable16
