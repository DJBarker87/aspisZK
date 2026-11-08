import PV_LIB_A_ActiveEnvironment17
import PV_LIB_A_ActiveFrames17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActiveAgreement17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)
open PV_LIB_A_ActiveEnvironment17

theorem other_resolution (q : State) (c : Config) (wait : PV_STX2_Native.Waiting Data)
    (status : q.current.status = .running c) (waiting : c.frame.waiting = some wait)
    (other : PV_LIB_A_ActiveDispatch17.resolve wait.request = none) : ¬Corrected q := by
  rintro ⟨s,a,parents,pointer,w,events,eq⟩
  rw [eq] at status
  cases status
  change some (PV_LIB_A_F5CallbackStall16.wait s pointer) = some wait at waiting
  cases waiting
  change PV_LIB_A_ActiveDispatch17.resolve
    (PV_LIB_A_F5ClosurePending16.request s.nextActivation pointer) = none at other
  rw [PV_LIB_A_ActiveDispatch17.actual] at other
  cases other

/-- Complete source/context/history step equality at EVERY other resolution,
not just equality of returned values or final source cells. -/
theorem step_other (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (x : Execution) (c : Config) (wait : PV_STX2_Native.Waiting Data)
    (status : x.state.current.status = .running c) (waiting : c.frame.waiting = some wait)
    (other : PV_LIB_A_ActiveDispatch17.resolve wait.request = none) :
    step cut p x = PV_LIB_SPEC_ReachedNative14.step cut p x :=
  away cut p x (other_resolution x.state c wait status waiting other)

#print axioms other_resolution
#print axioms step_other
end PV_LIB_A_ActiveAgreement17
