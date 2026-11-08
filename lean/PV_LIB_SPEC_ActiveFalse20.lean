import PV_LIB_SPEC_ActiveCallback20
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_SPEC_ActiveFalse20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_A_F5FullEntry16 (activation parents)
open PV_LIB_SPEC_ActiveForward20 (store169 store176)
open PV_LIB_SPEC_EntryWorld18 (Entry)

theorem false156 : PV_LIB_SPEC_ActiveDelivery20.stored.cells PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
  have frame : PV_LIB_SPEC_ActiveDelivery20.stored.cells PV_LIB_SPEC_Entry13.slot.source =
      PV_LIB_SPEC_ActivePoll20.store.cells PV_LIB_SPEC_Entry13.slot.source := by
    simp [PV_LIB_SPEC_ActiveDelivery20.stored,write,PV_LIB_SPEC_Entry13.slot]
  exact frame.trans PV_LIB_SPEC_ActivePoll20.source

theorem false160 : PV_LIB_SPEC_ActiveHistory16520.store160.cells PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
  have frame : PV_LIB_SPEC_ActiveHistory16520.store160.cells PV_LIB_SPEC_Entry13.slot.source =
      PV_LIB_SPEC_ActiveDelivery20.stored.cells PV_LIB_SPEC_Entry13.slot.source := by
    simp [PV_LIB_SPEC_ActiveHistory16520.store160,PV_LIB_SPEC_Active27720.stored,
      PV_THR2_RunTlsNext.issued,PV_STX2_Native.arguments,write,PV_LIB_SPEC_Entry13.slot,
      show activation=13 from rfl,show PV_LIB_SPEC_ActiveDelivery20.stored.nextActivation=15 from rfl]
  exact frame.trans false156

theorem false165 : PV_LIB_SPEC_ActiveHistory16920.store165.cells PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
  have frame : PV_LIB_SPEC_ActiveHistory16920.store165.cells PV_LIB_SPEC_Entry13.slot.source =
      PV_LIB_SPEC_ActiveHistory16520.store160.cells PV_LIB_SPEC_Entry13.slot.source := by
    simp [PV_LIB_SPEC_ActiveHistory16920.store165,PV_LIB_SPEC_Active27820.stored,
      PV_THR2_RunTlsErrorCompleted.issued,PV_STX2_Native.arguments,write,PV_LIB_SPEC_Entry13.slot,
      show activation=13 from rfl,show PV_LIB_SPEC_ActiveHistory16520.store160.nextActivation=16 from rfl]
  exact frame.trans false160

theorem false169 : store169.cells PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
  have frame : store169.cells PV_LIB_SPEC_Entry13.slot.source =
      PV_LIB_SPEC_ActiveHistory16920.store165.cells PV_LIB_SPEC_Entry13.slot.source := by
    simp [store169,PV_LIB_SPEC_Active27920.stored,
      PV_THR2_RunTlsBranchRequest.issued,PV_STX2_Native.arguments,write,PV_LIB_SPEC_Entry13.slot,
      show activation=13 from rfl,show PV_LIB_SPEC_ActiveHistory16920.store165.nextActivation=17 from rfl]
  exact frame.trans false165

theorem false176 : store176.cells PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
  have frame : store176.cells PV_LIB_SPEC_Entry13.slot.source = store169.cells PV_LIB_SPEC_Entry13.slot.source := by
    simp [store176,PV_LIB_SPEC_TlsForward16.prepared,PV_THR2_RunTlsForward.prepared,write,
      PV_LIB_SPEC_Entry13.slot,show activation=13 from rfl]
  exact frame.trans false169

theorem false185 : (PV_LIB_A_F5CallbackStall16.config store176 activation parents
    PV_LIB_SPEC_Entry13.slot.source).store.cells PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
  have frame : (PV_LIB_A_F5CallbackStall16.config store176 activation parents
      PV_LIB_SPEC_Entry13.slot.source).store.cells PV_LIB_SPEC_Entry13.slot.source =
      store176.cells PV_LIB_SPEC_Entry13.slot.source := by
    simp [PV_LIB_A_F5CallbackStall16.config,PV_LIB_SPEC_TlsCallable16.config,
      PV_THR2_RunTlsCallable.issued,PV_STX2_Native.arguments,write,PV_LIB_SPEC_Entry13.slot,
      show activation=13 from rfl,show store176.nextActivation=18 from rfl]
  exact frame.trans false176

theorem active185 (e : Entry) (ctx : PV_LIB_SPEC_ResourceHistory.Context) :
    PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot (PV_LIB_SPEC_ActiveConsumption19.bound ctx)
      (PV_LIB_A_F5CallbackStall16.config store176 activation parents PV_LIB_SPEC_Entry13.slot.source)
      e.world = some false := by
  unfold PV_LIB_SPEC_TlsBindings13.read
  have address : readAddress (runtime (PV_LIB_SPEC_ActiveConsumption19.bound ctx)).carrier
      (PV_LIB_A_F5CallbackStall16.config store176 activation parents PV_LIB_SPEC_Entry13.slot.source).store
      PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
    have source := false185
    simp only [PV_LIB_SPEC_Entry13.slot] at source
    unfold readAddress
    simp only [PV_LIB_SPEC_Entry13.slot]
    rw [source]
    rfl
  rw [address]
  change (if e.world.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 0 then some false else none) = _
  exact if_pos e.active

#print axioms false156
#print axioms false160
#print axioms false165
#print axioms false169
#print axioms false176
#print axioms false185
#print axioms active185
end PV_LIB_SPEC_ActiveFalse20
