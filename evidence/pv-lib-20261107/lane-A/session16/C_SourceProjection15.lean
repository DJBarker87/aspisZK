import PV_LIB_SPEC_SourceTransport15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_SourceProjection15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)
open PV_LIB_SPEC_SourceTransport15

theorem state (p : Parameters) (H : Handler) (n : Nat) (x : Execution) :
    (advance p H n x).state =
      PV_THR2_IntrinsicState.advance (runtime p).carrier (runtime p).control
        PV_LIB_SPEC_Full.programs H n x.state := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change (advance p H n (sourceStep p H x)).state = _
    rw [ih]
    rfl

/-- Direct consumer interface: reuse the old segment's result by one equality
transport. The finite Trace is internal; all action/poll exceptions remain. -/
theorem transport (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (H : Handler) (n : Nat) (x : Execution) (out : State)
    (trace : Trace cut p H n x)
    (existing : PV_THR2_IntrinsicState.advance (runtime p).carrier (runtime p).control
      PV_LIB_SPEC_Full.programs H n x.state = out) :
    (PV_LIB_SPEC_ReachedNative14.run cut p n x).state = out := by
  rw [run cut p H n x trace,state,existing]

/-- Fresh source instructions never consult a native handler. This reuses
Agree's exact saved-request definition and adds no native value assumption. -/
theorem no_wait (left right : Handler) (q : State)
    (waiting : ∀ c, q.current.status = .running c → c.frame.waiting = none) :
    PV_THR2_InterpreterAgreement.NativeAgree left right q := by
  intro c hc wait hw
  rw [waiting c hc] at hw
  cases hw

#print axioms state
#print axioms transport
#print axioms no_wait
end PV_LIB_SPEC_SourceProjection15
