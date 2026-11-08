import PV_LIB_SPEC_ActiveAdoption19
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveAway20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)

/-- A nonpolling control step is outside the one repaired callback case. -/
theorem nonpoll (q : State)
    (ordinary : PV_LIB_SPEC_ControlRuntime.ordinary q = none) :
    ¬ PV_LIB_A_ActiveEnvironment17.Corrected q := by
  rintro ⟨s,a,parents,pointer,w,es,eq⟩
  rw [eq,PV_LIB_A_F5CallbackTrap16.ordinary] at ordinary
  cases ordinary

theorem step (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (x : Execution)
    (ordinary : PV_LIB_SPEC_ControlRuntime.ordinary x.state = none) :
    PV_LIB_A_ActiveEnvironment17.step cut p x = PV_LIB_SPEC_ReachedNative14.step cut p x :=
  PV_LIB_A_ActiveEnvironment17.away cut p x (nonpoll x.state ordinary)

/-- A different emitted native token cannot select the callback correction. -/
theorem token (q : State) (c : Config) (wait : PV_STX2_Native.Waiting Data)
    (ordinary : PV_LIB_SPEC_ControlRuntime.ordinary q = some (c,wait))
    (different : ∀ s pointer, wait.request ≠ (PV_LIB_A_F5CallbackStall16.wait s pointer).request) :
    ¬ PV_LIB_A_ActiveEnvironment17.Corrected q := by
  rintro ⟨s,a,parents,pointer,w,es,eq⟩
  rw [eq,PV_LIB_A_F5CallbackTrap16.ordinary] at ordinary
  have pair := Option.some.inj ordinary
  have same := congrArg (fun pair => pair.2.request) pair
  exact different s pointer same.symm

#print axioms nonpoll
#print axioms step
#print axioms token
end PV_LIB_SPEC_ActiveAway20
