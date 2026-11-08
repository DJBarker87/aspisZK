import PV_LIB_SPEC_TlsAt54
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsNative15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_TlsAt54

def cut (stack : PV_LIB_SPEC_PhysicalStack12.Frame) : PV_LIB_SPEC_ReachedNative14.Cut :=
  ⟨⟨⟨stack,65496⟩,PV_LIB_SPEC_Entry13.slot⟩,PV_LIB_SPEC_Entry14.hooksSlot⟩
def request : PV_STX2_Native.Request Data := .child token 6 [initValue]
def reference : Data := PV_STX2_TypedReferences.reference PV_LIB_SPEC_Entry13.slot.source .null

theorem source : config.store.cells PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
  simp [config,PV_LIB_SPEC_TlsRequest15.issuedStore,store53,store51,
    PV_LIB_SPEC_TlsOriginal15.store50,PV_LIB_SPEC_TlsPoll15.prepared,
    PV_LIB_SPEC_TlsOriginal15.store40,PV_THR2_F17Call.issued,
    PV_THR2_F17Prefix.prepared,PV_STX2_Native.arguments,PV_STX2_Store.write,
    PV_LIB_SPEC_Entry13.slot,
    show PV_LIB_SPEC_TlsOriginal14.withStore.nextActivation=5 from rfl]
  simp [PV_LIB_SPEC_TlsOriginal14.withStore,PV_THR2_F2Call.issued,
    PV_THR2_F2Prefix.prepared,PV_STX2_Native.arguments,PV_STX2_Store.write,
    show PV_LIB_SPEC_TlsOriginal14.workerStore.nextActivation=4 from rfl]
  simp [PV_LIB_SPEC_TlsOriginal14.workerStore,PV_THR2_F1Worker.issued,
    PV_STX2_Store.write,
    show PV_LIB_SPEC_Worker14.store.nextActivation=3 from rfl]
  simp [PV_LIB_SPEC_Worker14.store,PV_THR2_F1Force.prepared,
    PV_LIB_SPEC_F1Force14.store,PV_THR2_F1Arithmetic.compared,
    PV_LIB_SPEC_F1Arithmetic14.store,PV_FN_THREAD_f1Entry.prepared,
    PV_FN_THREAD_f0Entry.issued,PV_FN_THREAD_f0Entry.prepared,
    PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,PV_STX2_Store.write,
    PV_LIB_SPEC_Entry13.store,PV_LIB_SPEC_Entry13.slot]

theorem physical : PV_LIB_SPEC_Entry14.state.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 0 := by
  unfold PV_LIB_SPEC_Entry14.state
  simp only []
  rw [if_neg (by decide)]
  rw [PV_LIB_SPEC_ArcPhysical13.write_away _ _ _ _ (Or.inr (by decide))]
  rw [PV_LIB_SPEC_ArcPhysical13.write_away _ _ _ _ (Or.inl (by decide))]
  unfold PV_LIB_SPEC_Entry13.state
  simp only [ite_true]

theorem active : PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot
    PV_LIB_SPEC_ReachedEnvironment14.parameters config PV_LIB_SPEC_Entry14.state = some false := by
  unfold PV_LIB_SPEC_TlsBindings13.read
  have address : readAddress (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).carrier
      config.store PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
    unfold readAddress
    simp only [PV_LIB_SPEC_Entry13.slot,List.foldl_nil]
    exact source
  rw [address]
  change (if PV_LIB_SPEC_Entry14.state.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 0 then some false else none) = _
  rw [physical]; rfl

theorem value : PV_LIB_SPEC_TlsBindings13.value PV_LIB_SPEC_Entry13.slot
    PV_LIB_SPEC_ReachedEnvironment14.parameters config PV_LIB_SPEC_Entry14.state request = some reference := by
  unfold PV_LIB_SPEC_TlsBindings13.value
  simp only [request,token,PV_THR2_FnOnceDispatch.request,ite_true]
  have initializer : (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).control.variant initValue = some 0 := rfl
  rw [initializer]
  change (do let _ ← PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot
               PV_LIB_SPEC_ReachedEnvironment14.parameters config PV_LIB_SPEC_Entry14.state
             pure reference) = _
  rw [active]; rfl

#print axioms cut
#print axioms request
#print axioms reference
#print axioms source
#print axioms physical
#print axioms active
#print axioms value
end PV_LIB_SPEC_TlsNative15
