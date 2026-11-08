import PV_LIB_A_F5CallbackObstruction16
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_A_F5CallbackStall16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)

def config (s : Store Data) (a : Nat) (parents : List Frame) (p : Address) : Config :=
  PV_LIB_SPEC_TlsCallable16.config s a parents PV_LIB_A_F5FullEntry16.closure p

def wait (s : Store Data) (p : Address) : PV_STX2_Native.Waiting Data :=
  ⟨PV_LIB_A_F5ClosurePending16.request s.nextActivation p,.child s.nextActivation (.local 14),[]⟩

theorem quiet (s : Store Data) (a : Nat) (parents : List Frame) (pointer : Address)
    (w : OWNER) (es : List Event) (suspended : List Config) :
    PV_LIB_SPEC_SourceTransport15.Quiet ⟨⟨.running (config s a parents pointer),w,es⟩,suspended⟩ := by
  have table : PV_LIB_StoreActionTable.v2 PV_THR2_RunTlsCallable.descriptors.1 = none := rfl
  have lookup := PV_LIB_SPEC_Tls18Delivery16.lookup
  change PV_LIB_SPEC_Full.programs PV_THR2_RunTlsCallable.descriptors.1 = none at lookup
  have head : PV_THR2_F170.live.body.drop 40 = PV_THR2_F170.node56 :: PV_THR2_F170.live.body.drop 41 := rfl
  simp [PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,PV_LIB_StoreActionTable.select,
    config,PV_LIB_SPEC_TlsCallable16.config,PV_THR2_OwnInitAction.selected,
    PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,
    PV_THR2_OwnUniformNeutral.configuration,PV_THR2_OwnUniformNeutral.instruction,
    head,PV_THR2_F170.node56,lookup,table]

theorem transition (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources)
    (s : Store Data) (a : Nat) (parents : List Frame) (pointer : Address)
    (w : OWNER) (es : List Event) (suspended : List Config) :
    PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) (config s a parents pointer)
      ⟨⟨.running (config s a parents pointer),w,es⟩,suspended⟩ =
      ⟨⟨.running (config s a parents pointer),w,es⟩,suspended⟩ := by
  have polled := PV_LIB_SPEC_NativeDelivery16.full (PV_LIB_SPEC_TlsNative15.cut stack)
    (PV_LIB_SPEC_TlsBound15.parameters resources) (config s a parents pointer) w es suspended
    (wait s pointer) PV_THR2_RunTlsCallable.descriptors.1 s.nextActivation 14
    [PV_LIB_A_F5FullEntry16.closure,PV_THR2_KeyValues.pack PV_THR2_RunTlsCallable.descriptors.2
      [PV_STX2_TypedReferences.reference pointer .null]]
    (quiet s a parents pointer w es suspended) rfl rfl rfl rfl rfl PV_LIB_SPEC_Tls18Delivery16.lookup
  dsimp only [config] at polled
  have answer := PV_LIB_A_F5CallbackObstruction16.answer_pending stack resources s a parents pointer w
  simp only [PV_LIB_SPEC_ReachedNative14.handler,show (wait s pointer).request =
    PV_LIB_A_F5ClosurePending16.request s.nextActivation pointer from rfl,answer,Option.getD_some] at polled
  simpa [PV_THR2_ChildBoundary.delivered,PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,
    PV_STX2_Native.reply,PV_STX2_SliceMachine.adopt,PV_STX2_SliceMachine.native,config] using polled

#print axioms quiet
#print axioms transition
end PV_LIB_A_F5CallbackStall16
