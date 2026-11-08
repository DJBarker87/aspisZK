import PV_LIB_SPEC_ActiveForward20
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_SPEC_ActiveCells20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_A_F5FullEntry16 (activation closure)
open PV_LIB_SPEC_ActiveForward20 (store169 store176)

theorem callable141 : PV_LIB_A_F5FullEntry16.store.cells ⟨activation,2,[]⟩ = some closure := by
  simp [PV_LIB_A_F5FullEntry16.store,PV_THR2_F17Call.issued,PV_STX2_Native.arguments,write,
    activation,show PV_LIB_A_F5FullPush16.store.nextActivation=13 from rfl]

theorem callable154 : PV_LIB_A_ActiveGetter17.store154.cells ⟨activation,2,[]⟩ = some closure := by
  have frame : PV_LIB_A_ActiveGetter17.store154.cells ⟨activation,2,[]⟩ =
      PV_LIB_A_F5FullEntry16.store.cells ⟨activation,2,[]⟩ := by
    simp [PV_LIB_A_ActiveGetter17.store154,PV_LIB_A_ActiveGetter17.store152,
      PV_LIB_A_ActiveGetter17.store151,PV_LIB_SPEC_TlsPoll15.prepared,write]
  exact frame.trans callable141

theorem callable156 : PV_LIB_SPEC_ActiveDelivery20.stored.cells ⟨activation,2,[]⟩ = some closure := by
  have frame : PV_LIB_SPEC_ActiveDelivery20.stored.cells ⟨activation,2,[]⟩ =
      PV_LIB_A_ActiveGetter17.store154.cells ⟨activation,2,[]⟩ := by
    simp [PV_LIB_SPEC_ActiveDelivery20.stored,PV_LIB_SPEC_ActivePoll20.store,
      PV_LIB_SPEC_TlsRequest15.issuedStore,PV_STX2_Native.arguments,write,
      show activation=13 from rfl,show PV_LIB_A_ActiveGetter17.store154.nextActivation=14 from rfl]
  exact frame.trans callable154

theorem callable160 : PV_LIB_SPEC_ActiveHistory16520.store160.cells ⟨activation,2,[]⟩ = some closure := by
  have frame : PV_LIB_SPEC_ActiveHistory16520.store160.cells ⟨activation,2,[]⟩ =
      PV_LIB_SPEC_ActiveDelivery20.stored.cells ⟨activation,2,[]⟩ := by
    simp [PV_LIB_SPEC_ActiveHistory16520.store160,PV_LIB_SPEC_Active27720.stored,
      PV_THR2_RunTlsNext.issued,PV_STX2_Native.arguments,write,
      show activation=13 from rfl,show PV_LIB_SPEC_ActiveDelivery20.stored.nextActivation=15 from rfl]
  exact frame.trans callable156

theorem callable165 : PV_LIB_SPEC_ActiveHistory16920.store165.cells ⟨activation,2,[]⟩ = some closure := by
  have frame : PV_LIB_SPEC_ActiveHistory16920.store165.cells ⟨activation,2,[]⟩ =
      PV_LIB_SPEC_ActiveHistory16520.store160.cells ⟨activation,2,[]⟩ := by
    simp [PV_LIB_SPEC_ActiveHistory16920.store165,PV_LIB_SPEC_Active27820.stored,
      PV_THR2_RunTlsErrorCompleted.issued,PV_STX2_Native.arguments,write,
      show activation=13 from rfl,show PV_LIB_SPEC_ActiveHistory16520.store160.nextActivation=16 from rfl]
  exact frame.trans callable160

theorem callable169 : store169.cells ⟨activation,2,[]⟩ = some closure := by
  have frame : store169.cells ⟨activation,2,[]⟩ =
      PV_LIB_SPEC_ActiveHistory16920.store165.cells ⟨activation,2,[]⟩ := by
    simp [store169,PV_LIB_SPEC_Active27920.stored,
      PV_THR2_RunTlsBranchRequest.issued,PV_STX2_Native.arguments,write,
      show activation=13 from rfl,show PV_LIB_SPEC_ActiveHistory16920.store165.nextActivation=17 from rfl]
  exact frame.trans callable165

theorem callable176 : store176.cells ⟨activation,2,[]⟩ = some closure := by
  have frame : store176.cells ⟨activation,2,[]⟩ = store169.cells ⟨activation,2,[]⟩ := by
    simp [store176,PV_LIB_SPEC_TlsForward16.prepared,PV_THR2_RunTlsForward.prepared,write]
  exact frame.trans callable169

theorem reference176 : store176.cells ⟨activation,3,[]⟩ = some PV_LIB_SPEC_TlsNative15.reference := by
  simp [store176,PV_LIB_SPEC_TlsForward16.prepared,PV_THR2_RunTlsForward.prepared,write]

#print axioms callable141
#print axioms callable154
#print axioms callable156
#print axioms callable160
#print axioms callable165
#print axioms callable169
#print axioms callable176
#print axioms reference176
end PV_LIB_SPEC_ActiveCells20
