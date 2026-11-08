import PV_LIB_SPEC_ActiveCallback20
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveOrigin18520
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_A_F5FullEntry16 (activation parents)
open PV_LIB_SPEC_ActiveForward20 (store176)
open PV_LIB_SPEC_ActiveAdoption19 (history)
open PV_LIB_A_F5CallbackStall16 (config wait)
local instance : DecidableEq Site := Classical.decEq _

def origin (e : Entry) (a : Nat) : Context :=
  ⟨PV_LIB_SPEC_TlsCallableHistory16.site,
    ((history e a 185).consumed.filter
      (fun (old : Context) => decide (old.site=PV_LIB_SPEC_TlsCallableHistory16.site))).length,
    PV_LIB_SPEC_ResourceHistory.arguments
      (PV_LIB_A_F5ClosurePending16.request store176.nextActivation PV_LIB_SPEC_Entry13.slot.source),
    activation,PV_LIB_A_F5ClosurePending16.request store176.nextActivation PV_LIB_SPEC_Entry13.slot.source⟩

theorem context (e : Entry) (a : Nat) :
    PV_LIB_SPEC_ResourceHistory.context (history e a 185)
      (config store176 activation parents PV_LIB_SPEC_Entry13.slot.source)
      (wait store176 PV_LIB_SPEC_Entry13.slot.source) = some (origin e a) := by
  classical
  unfold PV_LIB_SPEC_ResourceHistory.context
  rw [PV_LIB_SPEC_ActiveCallback20.issued185]
  simp [config,wait,PV_LIB_SPEC_TlsCallable16.config,origin]

theorem ordinary (e : Entry) (a : Nat) :
    PV_LIB_SPEC_ControlRuntime.ordinary (history e a 185).state =
      some (config store176 activation parents PV_LIB_SPEC_Entry13.slot.source,
        wait store176 PV_LIB_SPEC_Entry13.slot.source) := by
  rw [PV_LIB_SPEC_ActiveCallback20.state185]
  exact PV_LIB_A_F5CallbackTrap16.ordinary _ _ _ _ _ _

theorem site (e : Entry) (a : Nat) :
    (origin e a).site.function = 170 ∧ (origin e a).site.statement = 8162 := ⟨rfl,rfl⟩

/-- D877 contracts the callback; its origin is the enclosing source8162
request. The inner8248 computation is not a second source-issued origin. -/
theorem not_inner (e : Entry) (a : Nat) : (origin e a).site.statement ≠ 8248 := by
  rw [(site e a).2]
  decide

#print axioms origin
#print axioms context
#print axioms ordinary
#print axioms site
#print axioms not_inner
end PV_LIB_SPEC_ActiveOrigin18520
