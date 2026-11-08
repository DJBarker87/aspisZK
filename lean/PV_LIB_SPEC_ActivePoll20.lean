import PV_LIB_SPEC_ActiveRequest20
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActivePoll20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_A_ActiveGetter17 (store154 token init)
open PV_LIB_A_F5FullEntry16 (activation parents)

def store : Store Data := PV_LIB_SPEC_TlsRequest15.issuedStore store154 activation init
def request : PV_STX2_Native.Request Data := .child token store154.nextActivation [init]
def wait : PV_STX2_Native.Waiting Data := ⟨request,.child store154.nextActivation (.local 7),[]⟩
def config : Config := ⟨{activation := activation,remaining := PV_THR2_F170.live.body.drop 14, waiting := some wait},parents,store⟩

theorem ordinary (e : Entry) (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_ControlRuntime.ordinary (PV_LIB_SPEC_ActiveRequest20.after e issued consumed).state =
      some (config,wait) := by
  have lookup : PV_LIB_SPEC_Full.programs token = none := rfl
  simp [PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_SPEC_ActiveRequest20.after,
    PV_LIB_SPEC_TlsRequest15.after,PV_THR2_Catch316Segment.select,lookup,config,wait,request,store]

theorem source : store.cells PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
  have old := PV_LIB_A_ActiveSource17.false154
  have frame : store.cells PV_LIB_SPEC_Entry13.slot.source = store154.cells PV_LIB_SPEC_Entry13.slot.source := by
    simp [store,PV_LIB_SPEC_TlsRequest15.issuedStore,PV_STX2_Native.arguments,write,
      PV_LIB_SPEC_Entry13.slot,show activation=13 from rfl,
      show store154.nextActivation=14 from rfl]
  exact frame.trans old

theorem active (e : Entry) (resources : PV_EVHB_OwnerHeap.Resources) :
    PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot
      (PV_LIB_A_ActiveTlsNative17.parameters resources) config e.world = some false := by
  unfold PV_LIB_SPEC_TlsBindings13.read
  have address : readAddress (runtime (PV_LIB_A_ActiveTlsNative17.parameters resources)).carrier
      config.store PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
    have h := source
    simp only [PV_LIB_SPEC_Entry13.slot] at h
    unfold readAddress
    simp only [PV_LIB_SPEC_Entry13.slot,config]
    rw [h]
    rfl
  rw [address]
  change (if e.world.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 0 then some false else none) = _
  exact if_pos e.active

/-- The complete native reply is computed on the reached world and source
store, even when the allocation channel is rebound to the actual origin. -/
theorem answer (e : Entry) (a : Nat) (resources : PV_EVHB_OwnerHeap.Resources) :
    PV_LIB_SPEC_ReachedNative14.answer
      (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e a))
      (PV_LIB_A_ActiveTlsNative17.parameters resources) config request e.world =
      some ⟨.returned (.ok PV_LIB_SPEC_TlsNative15.reference),e.world,[]⟩ :=
  PV_LIB_A_ActiveTlsNative17.answer _ resources config e.world store154.nextActivation (active e resources)

#print axioms store
#print axioms request
#print axioms wait
#print axioms config
#print axioms ordinary
#print axioms source
#print axioms active
#print axioms answer
end PV_LIB_SPEC_ActivePoll20
