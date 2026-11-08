import PV_LIB_SPEC_ActiveHistory16920
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveForward20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_A_F5FullEntry16 (activation parents)
open PV_LIB_SPEC_ActiveAdoption19 (history)
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_SPEC_TlsNative15 (reference)

def handler : Handler := fun _ w => ⟨.pending,w,[]⟩
def store169 : Store Data := PV_LIB_SPEC_Active27920.stored
  PV_LIB_SPEC_ActiveHistory16920.store165 activation PV_LIB_SPEC_Entry13.slot.source
def store176 : Store Data := PV_LIB_SPEC_TlsForward16.prepared store169 activation reference

theorem state169 (e : Entry) (a : Nat) :
    (history e a 169).state =
      (stage store169 activation parents (PV_THR2_F170.live.body.drop 24) e.world [] [] []).state := by
  rw [PV_LIB_SPEC_ActiveHistory16920.original169]
  rfl

def at176 (e : Entry) (a : Nat) : Execution :=
  PV_LIB_SPEC_SourceTransport15.advance PV_LIB_SPEC_ReachedEnvironment14.parameters handler 7
    (stage store169 activation parents (PV_THR2_F170.live.body.drop 24) e.world []
      (history e a 169).issued (history e a 169).consumed)

theorem cell : store169.cells ⟨activation,4,[]⟩ =
    some (PV_LIB_SPEC_Tls279Values16.value PV_LIB_SPEC_Entry13.slot.source) := write_same _ _ _

theorem original176 (e : Entry) (a : Nat) : history e a 176 = at176 e a := by
  apply PV_LIB_SPEC_HistoryExtend20.full e a 169 7
    (stage store169 activation parents (PV_THR2_F170.live.body.drop 24) e.world [] [] []).state
    (fun issued consumed => PV_LIB_SPEC_SourceTransport15.advance
      PV_LIB_SPEC_ReachedEnvironment14.parameters handler 7
      (stage store169 activation parents (PV_THR2_F170.live.body.drop 24) e.world [] issued consumed))
    (state169 e a)
  intro issued consumed
  exact PV_LIB_SPEC_ActiveTrace20.run _ _ handler _ _
    (PV_LIB_SPEC_TlsForward16.trace _ _ handler store169 activation parents e.world [] issued consumed
      (PV_LIB_SPEC_Tls279Values16.value PV_LIB_SPEC_Entry13.slot.source) reference cell rfl rfl)

theorem state176 (e : Entry) (a : Nat) :
    (history e a 176).state =
      (stage store176 activation parents (PV_THR2_F170.live.body.drop 31) e.world [] [] []).state := by
  rw [original176]
  unfold at176
  rw [PV_LIB_SPEC_SourceProjection15.state]
  exact PV_LIB_SPEC_TlsForwardLift16.source _ handler store169 activation parents
    (PV_LIB_SPEC_Tls279Values16.value PV_LIB_SPEC_Entry13.slot.source) reference e.world [] cell rfl rfl

theorem consumed176 (e : Entry) (a : Nat) :
    (history e a 176).consumed = (history e a 169).consumed := by
  rw [original176]
  exact PV_LIB_SPEC_Tls279History16.consumed _ handler 7 _

#print axioms handler
#print axioms store169
#print axioms store176
#print axioms state169
#print axioms at176
#print axioms cell
#print axioms original176
#print axioms state176
#print axioms consumed176
end PV_LIB_SPEC_ActiveForward20
