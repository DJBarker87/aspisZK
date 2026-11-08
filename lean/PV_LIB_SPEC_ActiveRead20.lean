import PV_LIB_SPEC_ActiveSource19
import PV_LIB_A_ActiveSource17
import PV_LIB_A_ActiveExtend17
import PV_LIB_A_ActiveTlsNative17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveRead20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_A_ActiveGetter17 (store154)

/-- Reuse the named TLS source segment; do not replay a callee or derive an A join. -/
theorem retained (e : Entry) (a : Nat) :
    (PV_LIB_SPEC_History18.history e a 154).state =
      (PV_LIB_SPEC_F1Arithmetic14.stage store154 PV_LIB_A_F5FullEntry16.activation
        PV_LIB_A_F5FullEntry16.parents (PV_THR2_F170.live.body.drop 13) e.world [] [] []).state := by
  apply PV_LIB_A_HistoryExtend16.extend e a 141 13 PV_LIB_A_F5FullEntry16.store
    PV_LIB_A_F5FullEntry16.activation PV_LIB_A_F5FullEntry16.parents PV_THR2_F170.live.body
  · exact PV_LIB_A_F5FullEntry16.original141 e a
  · intro issued consumed
    simpa only [PV_LIB_SPEC_F1Arithmetic14.stage] using congrArg Execution.state
      (PV_LIB_A_ActiveGetter17.retained154
        (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e a)) e.world issued consumed)

/-- Full transport through this fresh native preparation cut follows the
existing no-trap induction. It is not a transport beyond a repaired callback. -/
theorem original (e : Entry) (a : Nat) :
    (PV_LIB_SPEC_ActiveAdoption19.history e a 154).state =
      (PV_LIB_SPEC_F1Arithmetic14.stage store154 PV_LIB_A_F5FullEntry16.activation
        PV_LIB_A_F5FullEntry16.parents (PV_THR2_F170.live.body.drop 13) e.world [] [] []).state := by
  have fresh : PV_LIB_SPEC_LaneAJoins18.BodyEntry
      (PV_LIB_SPEC_History18.history e a 154) (PV_THR2_F170.live.body.drop 13) := by
    unfold PV_LIB_SPEC_LaneAJoins18.BodyEntry
    rw [retained]
    exact ⟨_,rfl,rfl,rfl,rfl,rfl⟩
  change (PV_LIB_A_ActiveEnvironment17.run
    (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e a))
    PV_LIB_SPEC_ReachedEnvironment14.parameters 154
    (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world))).state = _
  rw [PV_LIB_A_ActiveTransport17.to_fresh
    (PV_LIB_SPEC_EntryWorld18.frame e a)
    (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world))
    154 154 _ (Nat.le_refl _) fresh]
  exact retained e a

/-- Source/physical ACTIVE agree on this same reached source configuration. -/
theorem read (e : Entry) (resources : PV_EVHB_OwnerHeap.Resources) :
    PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot
      (PV_LIB_A_ActiveTlsNative17.parameters resources)
      ⟨{activation := PV_LIB_A_F5FullEntry16.activation,
        remaining := PV_THR2_F170.live.body.drop 13},PV_LIB_A_F5FullEntry16.parents,store154⟩
      e.world = some false := by
  unfold PV_LIB_SPEC_TlsBindings13.read
  have address : readAddress (runtime (PV_LIB_A_ActiveTlsNative17.parameters resources)).carrier
      store154 PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
    have source := PV_LIB_A_ActiveSource17.false154
    simp only [PV_LIB_SPEC_Entry13.slot] at source
    unfold readAddress
    simp only [PV_LIB_SPEC_Entry13.slot]
    rw [source]
    rfl
  rw [address]
  change (if e.world.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 0 then some false else none) = _
  exact if_pos e.active

#print axioms retained
#print axioms original
#print axioms read
end PV_LIB_SPEC_ActiveRead20
