import PV_LIB_A_ActiveDispatch17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActiveEnvironment17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)

/-- Only the actual, source-issued Adt56 callback continuation is corrected.
No program table, f2 forwarding, allocation schedule or other reply changes. -/
def Corrected (q : State) : Prop :=
  ∃ s a parents pointer w events,
    q = PV_LIB_A_F5CallbackTrap16.waiting s a parents pointer w events

/-- D727/contract-first callback delivery. The request's origin remains the
actual emitted8162 origin; the pure setter uses no allocation channel. -/
def corrected (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (x : Execution) : Execution :=
  match PV_LIB_SPEC_ControlRuntime.ordinary x.state with
  | none => PV_LIB_SPEC_ReachedNative14.step cut p x
  | some (c,wait) =>
    match PV_LIB_SPEC_ResourceHistory.context x c wait with
    | none => PV_LIB_SPEC_ReachedNative14.step cut p x
    | some ctx =>
      let bound := {p with resources := PV_LIB_SPEC_ResourceHistory.allocationResources p.environment ctx}
      match PV_LIB_A_ActiveDispatch17.boundary cut bound c wait x.state.current.world with
      | none => {x with state := ⟨⟨.undefined none c.store,x.state.current.world,x.state.current.events⟩,
          x.state.suspended⟩,consumed := ctx :: x.consumed}
      | some reply =>
        let out : State := ⟨⟨reply.status,reply.world,x.state.current.events ++ reply.events⟩,x.state.suspended⟩
        ⟨out,PV_LIB_SPEC_ControlRuntime.recordIssue x.state out x.issued,ctx :: x.consumed⟩

local instance : DecidablePred Corrected := Classical.decPred _

def step (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (x : Execution) : Execution :=
  if Corrected x.state then corrected cut p x else PV_LIB_SPEC_ReachedNative14.step cut p x

def run (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) : Nat → Execution → Execution
  | 0,x => x
  | n+1,x => run cut p n (step cut p x)

theorem away (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (x : Execution)
    (other : ¬Corrected x.state) : step cut p x = PV_LIB_SPEC_ReachedNative14.step cut p x := by
  simp only [step,other,if_false]

theorem run_add (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (n m : Nat) (x : Execution) :
    run cut p (n+m) x = run cut p m (run cut p n x) := by
  induction n generalizing x with
  | zero => simp only [Nat.zero_add,run]
  | succ n ih => simpa only [Nat.succ_add,run] using ih (step cut p x)

/-- Symbolic trace transport, with full Execution equality (including origins,
consumption, every world/event/store and saved frame). -/
theorem transport (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (x : Execution) (n : Nat)
    (other : ∀ k, k<n → ¬Corrected (PV_LIB_SPEC_ReachedNative14.run cut p k x).state) :
    run cut p n x = PV_LIB_SPEC_ReachedNative14.run cut p n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [run,away cut p x (other 0 (Nat.zero_lt_succ n))]
    apply ih
    intro k hk
    exact other (k+1) (Nat.succ_lt_succ hk)

#print axioms Corrected
#print axioms corrected
#print axioms step
#print axioms run
#print axioms away
#print axioms run_add
#print axioms transport
end PV_LIB_A_ActiveEnvironment17
