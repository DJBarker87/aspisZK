import PV_LIB_SPEC_ActiveOrigin18520
import PV_LIB_SPEC_ActiveFalse20
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveHistory18620
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_A_F5FullEntry16 (activation parents)
open PV_LIB_SPEC_ActiveForward20 (store176)
open PV_LIB_SPEC_ActiveAdoption19 (history)
open PV_LIB_SPEC_ActiveOrigin18520 (origin)

def reply (e : Entry) (a : Nat) : Prefix OWNER Event :=
  PV_LIB_SPEC_ActiveConsumption19.delivered (origin e a) store176 activation parents e.world

def out (e : Entry) (a : Nat) : State :=
  ⟨⟨(reply e a).status,(reply e a).world,(reply e a).events⟩,[]⟩

def after (e : Entry) (a : Nat) : Execution :=
  ⟨out e a,PV_LIB_SPEC_ControlRuntime.recordIssue
    (PV_LIB_A_F5CallbackTrap16.waiting store176 activation parents PV_LIB_SPEC_Entry13.slot.source e.world [])
    (out e a) (history e a 185).issued,origin e a :: (history e a 185).consumed⟩

/-- The local SPEC-C18 theorem is now instantiated on the SAME continuous
original execution. No native/source success or fresh internal start is assumed. -/
theorem original186 (e : Entry) (a : Nat) : history e a 186 = after e a := by
  let q := history e a 185
  let waiting := PV_LIB_A_F5CallbackTrap16.waiting store176 activation parents
    PV_LIB_SPEC_Entry13.slot.source e.world []
  have eq : q = ⟨waiting,q.issued,q.consumed⟩ :=
    PV_LIB_A_F170Return16.execution_ext q ⟨waiting,q.issued,q.consumed⟩
      (PV_LIB_SPEC_ActiveCallback20.state185 e a) rfl rfl
  have context : PV_LIB_SPEC_ResourceHistory.context ⟨waiting,q.issued,q.consumed⟩
      (PV_LIB_A_F5CallbackStall16.config store176 activation parents PV_LIB_SPEC_Entry13.slot.source)
      (PV_LIB_A_F5CallbackStall16.wait store176 PV_LIB_SPEC_Entry13.slot.source) = some (origin e a) := by
    rw [← eq]
    exact PV_LIB_SPEC_ActiveOrigin18520.context e a
  have consumed := PV_LIB_SPEC_ActiveConsumption19.consume
    (PV_LIB_SPEC_EntryWorld18.frame e a) store176 activation parents e.world []
    q.issued q.consumed (origin e a) context (PV_LIB_SPEC_ActiveFalse20.active185 e (origin e a))
  change PV_LIB_A_ActiveEnvironment17.run _ _ (185+1) _ = _
  rw [PV_LIB_A_ActiveEnvironment17.run_add]
  change PV_LIB_A_ActiveEnvironment17.step _ _ q = _
  calc
    _ = PV_LIB_A_ActiveEnvironment17.step _ _ ⟨waiting,q.issued,q.consumed⟩ := congrArg _ eq
    _ = after e a := by simpa only [after,out,reply,List.nil_append] using consumed

/-- Actual source ACTIVE write after contracted callback delivery. -/
theorem source (e : Entry) (a : Nat) :
    (PV_W1_LeafBoundary.statusStore (history e a 186).state.current.status).cells
      PV_LIB_SPEC_Entry13.slot.source = some (.boolean true) := by
  rw [original186]
  exact PV_LIB_SPEC_ActiveSource19.cell (origin e a) store176 activation parents e.world

theorem physical (e : Entry) (a : Nat) :
    (history e a 186).state.current.world.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 1 := by
  rw [original186]
  exact PV_LIB_SPEC_ActiveConsumption19.physical (origin e a) store176 activation parents e.world

theorem consumed (e : Entry) (a : Nat) :
    (history e a 186).consumed = origin e a :: (history e a 185).consumed := by
  rw [original186]
  rfl

theorem events (e : Entry) (a : Nat) : (history e a 186).state.current.events = [] := by
  rw [original186]
  exact PV_LIB_SPEC_ActiveConsumption19.events (origin e a) store176 activation parents e.world

#print axioms reply
#print axioms out
#print axioms after
#print axioms original186
#print axioms source
#print axioms physical
#print axioms consumed
#print axioms events
end PV_LIB_SPEC_ActiveHistory18620
