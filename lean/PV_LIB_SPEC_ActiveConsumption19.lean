import PV_LIB_SPEC_ActiveBoundary19
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveConsumption19
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerHeap PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_A_F5CallbackStall16 (config wait)
open PV_LIB_SPEC_TlsNative15 (cut)

def bound (ctx : Context) : Parameters :=
  PV_LIB_SPEC_TlsBound15.parameters
    (PV_LIB_SPEC_ResourceHistory.allocationResources
      PV_LIB_SPEC_ReachedEnvironment14.parameters.environment ctx)

def delivered (ctx : Context) (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) :
    Prefix OWNER Event :=
  PV_THR2_ChildBoundary.delivered (runtime (bound ctx)).carrier
    (PV_LIB_SPEC_ActiveBoundary19.changed (config s a parents PV_LIB_SPEC_Entry13.slot.source))
    (wait s PV_LIB_SPEC_Entry13.slot.source)
    ⟨.returned (.ok (.boolean false)),PV_LIB_SPEC_CellPhysical13.setByte PV_LIB_SPEC_Entry13.slot w true,[]⟩

/-- Actual outer origin consumption and complete Execution at one contracted
callback step. Origin and active are local reached-state facts; no post-store,
success reply, invented inner origin, fresh entry or changed world is supplied.
Original-history reachability must separately instantiate these facts. -/
theorem consume (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (s : Store Data) (a : Nat)
    (parents : List Frame) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) (ctx : Context)
    (origin : PV_LIB_SPEC_ResourceHistory.context
      ⟨PV_LIB_A_F5CallbackTrap16.waiting s a parents PV_LIB_SPEC_Entry13.slot.source w es,issued,consumed⟩
      (config s a parents PV_LIB_SPEC_Entry13.slot.source)
      (wait s PV_LIB_SPEC_Entry13.slot.source) = some ctx)
    (active : PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot (bound ctx)
      (config s a parents PV_LIB_SPEC_Entry13.slot.source) w = some false) :
    PV_LIB_A_ActiveEnvironment17.step (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters
      ⟨PV_LIB_A_F5CallbackTrap16.waiting s a parents PV_LIB_SPEC_Entry13.slot.source w es,issued,consumed⟩ =
    let out : State := ⟨⟨(delivered ctx s a parents w).status,
      (delivered ctx s a parents w).world,es ++ (delivered ctx s a parents w).events⟩,[]⟩
    ⟨out,PV_LIB_SPEC_ControlRuntime.recordIssue
      (PV_LIB_A_F5CallbackTrap16.waiting s a parents PV_LIB_SPEC_Entry13.slot.source w es)
      out issued,ctx :: consumed⟩ := by
  have corrected : PV_LIB_A_ActiveEnvironment17.Corrected
      (PV_LIB_A_F5CallbackTrap16.waiting s a parents PV_LIB_SPEC_Entry13.slot.source w es) :=
    ⟨s,a,parents,PV_LIB_SPEC_Entry13.slot.source,w,es,rfl⟩
  unfold PV_LIB_A_ActiveEnvironment17.step
  rw [if_pos corrected]
  unfold PV_LIB_A_ActiveEnvironment17.corrected
  rw [PV_LIB_A_F5CallbackTrap16.ordinary]
  dsimp only
  rw [origin]
  have boundary := PV_LIB_SPEC_ActiveBoundary19.successful stack
    (PV_LIB_SPEC_ResourceHistory.allocationResources
      PV_LIB_SPEC_ReachedEnvironment14.parameters.environment ctx)
    (config s a parents PV_LIB_SPEC_Entry13.slot.source)
    (wait s PV_LIB_SPEC_Entry13.slot.source) s.nextActivation w rfl active
  change PV_LIB_A_ActiveDispatch17.boundary (cut stack) (bound ctx)
    (config s a parents PV_LIB_SPEC_Entry13.slot.source)
    (wait s PV_LIB_SPEC_Entry13.slot.source) w = some (delivered ctx s a parents w) at boundary
  change (match PV_LIB_A_ActiveDispatch17.boundary (cut stack) (bound ctx)
    (config s a parents PV_LIB_SPEC_Entry13.slot.source)
    (wait s PV_LIB_SPEC_Entry13.slot.source) w with
    | none => _
    | some reply => _) = _
  rw [boundary]
  rfl

theorem physical (ctx : Context) (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) :
    (delivered ctx s a parents w).world.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 1 := by
  rw [show (delivered ctx s a parents w).world =
    PV_LIB_SPEC_CellPhysical13.setByte PV_LIB_SPEC_Entry13.slot w true from
      (PV_LIB_SPEC_ActiveBoundary19.effects (bound ctx) _ _ _).1]
  exact PV_LIB_SPEC_CellPhysical13.byte _ _ _

theorem events (ctx : Context) (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) :
    (delivered ctx s a parents w).events = [] :=
  (PV_LIB_SPEC_ActiveBoundary19.effects (bound ctx) _ _ _).2

#print axioms bound
#print axioms delivered
#print axioms consume
#print axioms physical
#print axioms events
end PV_LIB_SPEC_ActiveConsumption19
