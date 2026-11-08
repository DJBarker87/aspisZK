import PV_LIB_A_ActiveDelivery17
import PV_LIB_A_RootRead17
import PV_LIB_A_ActiveSource17
import PV_LIB_A_ActiveExtend17
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_A_ActiveGetterDelivery17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_A_ActiveGetter17 (store154 token init)
open PV_LIB_A_F5FullEntry16 (activation parents)

def request : PV_STX2_Native.Request Data := .child token store154.nextActivation [init]
def wait : PV_STX2_Native.Waiting Data := ⟨request,.child store154.nextActivation (.local 7),[]⟩
def config : Config :=
  ⟨{activation := activation,remaining := PV_THR2_F170.live.body.drop 14,
    waiting := some wait},parents,PV_LIB_SPEC_TlsRequest15.issuedStore store154 activation init⟩
def store156 : Store Data := write (write config.store ⟨store154.nextActivation,0,[]⟩
  (some PV_LIB_SPEC_TlsNative15.reference)) ⟨activation,7,[]⟩ (some PV_LIB_SPEC_TlsNative15.reference)
def after (w : OWNER) : State :=
  (stage store156 activation parents (PV_THR2_F170.live.body.drop 14) w [] [] []).state

theorem active (e : PV_LIB_SPEC_EntryWorld18.Entry) (resources : Resources) :
    PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot
      (PV_LIB_SPEC_TlsBound15.parameters resources) config e.world = some false := by
  have source : readAddress (runtime (PV_LIB_SPEC_TlsBound15.parameters resources)).carrier
      config.store PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
    rw [show PV_LIB_SPEC_Entry13.slot.source = (⟨0,20,[]⟩ : Address) from rfl,PV_LIB_A_RootRead17.root]
    have frame : config.store.cells PV_LIB_SPEC_Entry13.slot.source =
        store154.cells PV_LIB_SPEC_Entry13.slot.source := by
      simp [config,PV_LIB_SPEC_TlsRequest15.issuedStore,PV_STX2_Native.arguments,write,
      PV_LIB_SPEC_Entry13.slot,
      show store154.nextActivation=14 from rfl,show activation=13 from rfl]
    have value := frame.trans PV_LIB_A_ActiveSource17.false154
    simpa only [PV_LIB_SPEC_Entry13.slot] using value
  unfold PV_LIB_SPEC_TlsBindings13.read
  rw [source]
  change (if e.world.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 0 then some false else none) = _
  rw [e.active]
  rfl

theorem quiet (w : OWNER) : PV_LIB_SPEC_SourceTransport15.Quiet ⟨⟨.running config,w,[]⟩,[]⟩ := by
  have lookup : PV_LIB_SPEC_Full.programs token = none := rfl
  have table : PV_LIB_StoreActionTable.v2 token = none := rfl
  have head : PV_THR2_F170.live.body.drop 14 = PV_THR2_F170.node14 :: PV_THR2_F170.live.body.drop 15 := rfl
  simp [PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,PV_LIB_StoreActionTable.select,
    config,wait,request,PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformNeutral.configuration,
    PV_THR2_OwnUniformNeutral.instruction,head,PV_THR2_F170.node14,lookup,table]

theorem consume (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame)
    (issued : List Issued) (consumed : List Context) :
    (PV_LIB_SPEC_ReachedNative14.step (PV_LIB_SPEC_TlsNative15.cut stack)
      PV_LIB_SPEC_ReachedEnvironment14.parameters
      (PV_LIB_SPEC_TlsRequest15.after store154 activation token init parents e.world [] issued consumed)).state =
      after e.world := by
  have full := PV_LIB_A_ActiveDelivery17.consume (PV_LIB_SPEC_TlsNative15.cut stack)
    config wait PV_LIB_SPEC_TlsRequest15.site e.world [] issued consumed token store154.nextActivation 7 [init]
    ⟨.returned (.ok PV_LIB_SPEC_TlsNative15.reference),e.world,[]⟩
    (quiet e.world) rfl rfl rfl rfl rfl rfl (by rfl) (fun resources =>
      PV_LIB_A_ActiveTlsNative17.answer stack resources config e.world store154.nextActivation (active e resources))
  have result := congrArg Execution.state full
  exact result

theorem retained156 (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame)
    (issued : List Issued) (consumed : List Context) :
    (PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack)
      PV_LIB_SPEC_ReachedEnvironment14.parameters 15
      (stage PV_LIB_A_F5FullEntry16.store activation parents PV_THR2_F170.live.body e.world [] issued consumed)).state =
      after e.world := by
  rw [show 15=13+(1+1) from rfl,PV_LIB_SPEC_Original14.run_add,
    PV_LIB_A_ActiveGetter17.retained154,PV_LIB_SPEC_Original14.run_add]
  rw [PV_LIB_SPEC_TlsRequest15.request _ _ store154 activation token init parents e.world [] issued consumed
    (by simp [store154,PV_LIB_A_ActiveGetter17.store152,write]) (by simp [store154,write])]
  exact consume e stack issued consumed

theorem original156 (e : PV_LIB_SPEC_EntryWorld18.Entry) (a : Nat) :
    (PV_LIB_A_ActivePrefix17.history e a 156).state = after e.world := by
  apply PV_LIB_A_ActiveExtend17.extend e a 141 15 (PV_LIB_A_F5FullEntry16.at141 e) (after e.world)
    (PV_LIB_A_ActivePrefix17.original141 e a)
  intro issued consumed
  let stack := PV_LIB_SPEC_EntryWorld18.frame e a
  let x := stage PV_LIB_A_F5FullEntry16.store activation parents PV_THR2_F170.live.body e.world [] issued consumed
  have old := retained156 e stack issued consumed
  have fresh : PV_LIB_SPEC_LaneAJoins18.BodyEntry
      (PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack)
        PV_LIB_SPEC_ReachedEnvironment14.parameters 15 x) (PV_THR2_F170.live.body.drop 14) := by
    refine ⟨⟨{activation := activation,remaining := PV_THR2_F170.live.body.drop 14},parents,store156⟩,
      ?_,rfl,rfl,rfl,rfl⟩
    rw [old]; rfl
  change (PV_LIB_A_ActiveEnvironment17.run (PV_LIB_SPEC_TlsNative15.cut stack)
    PV_LIB_SPEC_ReachedEnvironment14.parameters 15 x).state = after e.world
  rw [PV_LIB_A_ActiveTransport17.to_fresh stack x 15 15 _ (by decide) fresh]
  exact old

#print axioms active
#print axioms quiet
#print axioms consume
#print axioms retained156
#print axioms original156
end PV_LIB_A_ActiveGetterDelivery17
