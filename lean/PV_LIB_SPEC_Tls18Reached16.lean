import PV_LIB_SPEC_Tls18Bound16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls18Reached16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_TlsAt75 (store75)
open PV_LIB_SPEC_TlsAt84 (config)
open PV_LIB_SPEC_TlsNative15 (cut)

theorem read_nil (C : Carrier OWNER Data) (s : Store Data) (a localIndex : Nat) :
    readAddress C s ⟨a,localIndex,[]⟩ = s.cells ⟨a,localIndex,[]⟩ := by
  cases h : s.cells ⟨a,localIndex,[]⟩ <;> simp [readAddress,readFields,h]

theorem source : config.store.cells PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
  simpa [PV_LIB_SPEC_TlsAt84.config,PV_LIB_SPEC_TlsCallable16.config,
    PV_THR2_RunTlsCallable.issued,PV_LIB_SPEC_Entry13.slot,store75,PV_LIB_SPEC_TlsForward16.prepared,PV_THR2_RunTlsForward.prepared,
    PV_LIB_SPEC_Tls68Data16.store68,PV_LIB_SPEC_Tls68Data16.config,
    PV_LIB_SPEC_Tls279Request16.config,PV_THR2_RunTlsBranchRequest.pending,
    PV_THR2_RunTlsBranchRequest.issued,PV_LIB_SPEC_Tls64Data16.store64,
    PV_LIB_SPEC_Tls64Data16.config,PV_LIB_SPEC_Tls278Reached15.config,
    PV_LIB_SPEC_Tls278Lift15.config,PV_THR2_RunTlsErrorCompleted.issued,
    PV_LIB_SPEC_Tls59Data15.store59,PV_LIB_SPEC_Tls59Data15.config,
    PV_THR2_RunTlsNext.pending,PV_THR2_RunTlsNext.issued,
    PV_LIB_SPEC_TlsDelivery15.store55,
    PV_STX2_Native.arguments,write,
    show PV_LIB_SPEC_TlsOriginal14.withStore.nextActivation=5 from rfl,
    show PV_LIB_SPEC_TlsDelivery15.store55.nextActivation=7 from rfl,
    show PV_LIB_SPEC_Tls59Data15.store59.nextActivation=8 from rfl,
    show PV_LIB_SPEC_Tls64Data16.store64.nextActivation=9 from rfl]
    using PV_LIB_SPEC_TlsNative15.source

theorem active (resources : PV_EVHB_OwnerHeap.Resources) :
    PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot
      (PV_LIB_SPEC_TlsBound15.parameters resources) config PV_LIB_SPEC_Entry14.state = some false := by
  unfold PV_LIB_SPEC_TlsBindings13.read
  have read : readAddress (runtime (PV_LIB_SPEC_TlsBound15.parameters resources)).carrier
      config.store PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
    change readAddress _ config.store ⟨0,20,[]⟩ = _
    rw [read_nil]
    exact source
  rw [read]
  change (if PV_LIB_SPEC_Entry14.state.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 0 then some false else none) = _
  rw [PV_LIB_SPEC_TlsNative15.physical]
  rfl

theorem reached (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : PV_EVHB_OwnerHeap.Resources) :
    let x := PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 84
      (PV_LIB_SPEC_ResourceHistory.initial PV_LIB_SPEC_Entry14.input)
    x.state.current.status = .running config ∧
    PV_LIB_SPEC_ReachedNative14.answer (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
      config (PV_LIB_SPEC_Tls18Bound16.request 10) x.state.current.world =
      some ⟨.returned (.ok (.boolean false)),x.state.current.world,[]⟩ := by
  dsimp only
  rw [PV_LIB_SPEC_TlsAt84.original84,PV_LIB_SPEC_TlsAt84.state84]
  exact ⟨rfl,PV_LIB_SPEC_Tls18Bound16.answer stack resources config PV_LIB_SPEC_Entry14.state 10 (active resources)⟩

#print axioms read_nil
#print axioms source
#print axioms active
#print axioms reached
end PV_LIB_SPEC_Tls18Reached16
