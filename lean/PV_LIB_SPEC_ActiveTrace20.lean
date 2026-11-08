import PV_LIB_SPEC_ActiveAway20
import PV_LIB_SPEC_SourceProjection15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveTrace20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)
open PV_LIB_SPEC_SourceTransport15 (Trace advance sourceStep)

/-- The old instruction-shape certificate is sufficient for the adopted
machine on a nonpolling source segment. Symbolic induction preserves ALL
Execution fields, including issued origins and consumed resource contexts. -/
theorem run (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (n : Nat) (x : Execution) (trace : Trace cut p H n x) :
    PV_LIB_A_ActiveEnvironment17.run cut p n x = advance p H n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have one : Trace cut p H 1 x := ⟨trace.1,trace.2.1,trace.2.2.1,True.intro⟩
    have old : PV_LIB_SPEC_ReachedNative14.step cut p x = sourceStep p H x :=
      PV_LIB_SPEC_SourceTransport15.run cut p H 1 x one
    rw [PV_LIB_A_ActiveEnvironment17.run,
      PV_LIB_SPEC_ActiveAway20.step cut p x trace.1,old]
    exact ih _ trace.2.2.2

theorem transport (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (n : Nat) (x : Execution) (out : State) (trace : Trace cut p H n x)
    (existing : PV_THR2_IntrinsicState.advance (runtime p).carrier (runtime p).control
      PV_LIB_SPEC_Full.programs H n x.state = out) :
    (PV_LIB_A_ActiveEnvironment17.run cut p n x).state = out := by
  rw [run cut p H n x trace,PV_LIB_SPEC_SourceProjection15.state,existing]

#print axioms run
#print axioms transport
end PV_LIB_SPEC_ActiveTrace20
