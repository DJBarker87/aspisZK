import PV_LIB_SPEC_ActiveAway20
import PV_LIB_SPEC_NativeDelivery16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_NativePoll20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)

/-- Generic administrative consumption only. Consumers derive both input
facts at the SAME reached poll, and instantiate the computed native answer
and transition by named contracts. This is never a machine assumption. -/
theorem consume (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (x : Execution) (c : Config) (wait : PV_STX2_Native.Waiting Data) (ctx : Context)
    (r : Reply OWNER Event Data) (out : State)
    (away : ¬ PV_LIB_A_ActiveEnvironment17.Corrected x.state)
    (ordinary : PV_LIB_SPEC_ControlRuntime.ordinary x.state = some (c,wait))
    (origin : PV_LIB_SPEC_ResourceHistory.context x c wait = some ctx)
    (answer : PV_LIB_SPEC_ReachedNative14.answer cut
      {p with resources := PV_LIB_SPEC_ResourceHistory.allocationResources p.environment ctx}
      c wait.request x.state.current.world = some r)
    (transition : PV_LIB_SPEC_ReachedNative14.transition cut
      {p with resources := PV_LIB_SPEC_ResourceHistory.allocationResources p.environment ctx}
      c x.state = out) :
    PV_LIB_A_ActiveEnvironment17.step cut p x =
      ⟨out,PV_LIB_SPEC_ControlRuntime.recordIssue x.state out x.issued,ctx :: x.consumed⟩ := by
  rw [PV_LIB_A_ActiveEnvironment17.away cut p x away]
  unfold PV_LIB_SPEC_ReachedNative14.step
  rw [ordinary]
  dsimp only
  rw [origin]
  dsimp only
  rw [answer]
  dsimp only
  rw [transition]

/-- A waiting poll cannot issue a second source origin during delivery. -/
theorem no_issue (c : Config) (wait : PV_STX2_Native.Waiting Data) (w : OWNER)
    (es : List Event) (suspended : List Config) (out : State) (issued : List Issued)
    (saved : c.frame.waiting = some wait) :
    PV_LIB_SPEC_ControlRuntime.recordIssue ⟨⟨.running c,w,es⟩,suspended⟩ out issued = issued := by
  simp [PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,saved]

#print axioms consume
#print axioms no_issue
end PV_LIB_SPEC_NativePoll20
