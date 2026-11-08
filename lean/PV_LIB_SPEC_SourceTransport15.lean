import PV_LIB_SPEC_TlsAt59
import PV_THR2_InterpreterAgreement
import PV_THR2_OwnUniformNeutral
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_SourceTransport15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)

def Quiet (q : State) : Prop :=
  PV_LIB_StoreActionTable.Neutral PV_LIB_SPEC_Full.programs q ∧
  ∀ c, q.current.status = .running c →
    PV_THR2_OwnInitAction.selected c = false ∧
    PV_THR2_OperatorAction.selected c = none ∧ PV_THR2_OwnUniformNeutral.configuration c

/-- Reuse the existing symbolic OWNER/operator/binding neutrality and native
handler agreement. This lemma never inspects or normalizes source cells. -/
theorem transition (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (c : Config) (q : State) (H : Handler) (quiet : Quiet q)
    (same : PV_THR2_InterpreterAgreement.NativeAgree
      (PV_LIB_SPEC_ReachedNative14.handler cut p c) H q) :
    PV_LIB_SPEC_ReachedNative14.transition cut p c q =
      PV_THR2_IntrinsicState.step (runtime p).carrier (runtime p).control
        PV_LIB_SPEC_Full.programs H q := by
  unfold PV_LIB_SPEC_ReachedNative14.transition
  rw [PV_LIB_StoreActionTable.agreement _ _ _ _ _ _ _ _ quiet.1]
  rw [PV_THR2_OwnInitInterpreterBridged.agreement _ _ _ _ _ _ _
    (fun c hc => (quiet.2 c hc).1)]
  have operators : PV_THR2_OperatorInterpreter.step (runtime p).carrier (runtime p).control
      PV_LIB_SPEC_Full.programs (PV_LIB_SPEC_ReachedNative14.handler cut p c) q =
      PV_THR2_OwnUniformBindings.step (runtime p).carrier (runtime p).control
        PV_LIB_SPEC_Full.programs (PV_LIB_SPEC_ReachedNative14.handler cut p c) q := by
    unfold PV_THR2_OperatorInterpreter.step
    cases hs : q.current.status <;> try rfl
    rename_i frame
    simp only [(quiet.2 frame hs).2.1]
  rw [operators,PV_THR2_OwnUniformNeutral.step _ _ _ _ _
    (fun c hc => (quiet.2 c hc).2.2)]
  exact PV_THR2_InterpreterAgreement.handler_step _ _ _ _ _ _ same

def sourceStep (p : Parameters) (H : Handler) (x : Execution) : Execution :=
  let out := PV_THR2_IntrinsicState.step (runtime p).carrier (runtime p).control
    PV_LIB_SPEC_Full.programs H x.state
  {x with state := out,issued := PV_LIB_SPEC_ControlRuntime.recordIssue x.state out x.issued}

def advance (p : Parameters) (H : Handler) : Nat → Execution → Execution
  | 0,x => x
  | n+1,x => advance p H n (sourceStep p H x)

def Trace (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler) :
    Nat → Execution → Prop
  | 0,_ => True
  | n+1,x =>
    PV_LIB_SPEC_ControlRuntime.ordinary x.state = none ∧ Quiet x.state ∧
    (∀ c, PV_THR2_InterpreterAgreement.NativeAgree
      (PV_LIB_SPEC_ReachedNative14.handler cut p c) H x.state) ∧
    Trace cut p H n (sourceStep p H x)

/-- One trace-indexed lift for an already proved source segment. Native polls
and OWNER/operator/store action sites are explicit exceptions. The caller must
discharge the finite shape certificate; no endpoint premise is introduced. -/
theorem run (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (n : Nat) (x : Execution) (trace : Trace cut p H n x) :
    PV_LIB_SPEC_ReachedNative14.run cut p n x = advance p H n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have first : PV_LIB_SPEC_ReachedNative14.step cut p x = sourceStep p H x := by
      unfold PV_LIB_SPEC_ReachedNative14.step
      simp only [trace.1]
      unfold PV_LIB_SPEC_ReachedNative14.control
      cases hs : x.state.current.status with
      | running c =>
        simp only []
        rw [transition cut p c x.state H trace.2.1 (trace.2.2.1 c)]
        rfl
      | returned result store =>
        simp only []
        rw [transition cut p _ x.state H trace.2.1 (trace.2.2.1 _)]
        rfl
      | fault f store =>
        simp only []
        rw [transition cut p _ x.state H trace.2.1 (trace.2.2.1 _)]
        rfl
      | undefined site store =>
        simp only []
        rw [transition cut p _ x.state H trace.2.1 (trace.2.2.1 _)]
        rfl
    rw [PV_LIB_SPEC_ReachedNative14.run,first]
    exact ih _ trace.2.2.2

#print axioms Quiet
#print axioms transition
#print axioms sourceStep
#print axioms advance
#print axioms Trace
#print axioms run
end PV_LIB_SPEC_SourceTransport15
