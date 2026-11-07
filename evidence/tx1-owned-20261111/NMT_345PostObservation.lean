import NMT_345Observation
set_option autoImplicit false
namespace NMT_345PostObservation
open RSL NMT_345Observation
/-- Complete observable post-child continuation, including a length rejection
AFTER328's hash/log events. A stopped child never runs this test. -/
def finish (checkpointLength : Nat) (child : Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs child fun bytes =>
  ⟨.ret (if bytes.length != checkpointLength then .error .invalidAccountData else .ok bytes),[]⟩

theorem finish_abort (n : Nat) (prefixEvents : List Event) :
 finish n ⟨.abort,prefixEvents⟩ = ⟨.abort,prefixEvents⟩ := rfl

theorem finish_diverge (n : Nat) (prefixEvents : List Event) :
 finish n ⟨.diverge,prefixEvents⟩ = ⟨.diverge,prefixEvents⟩ := rfl

theorem finish_error (n : Nat) (e : ProgramError) (events : List Event) :
 finish n ⟨.ret (.error e),events⟩ = ⟨.ret (.error e),events⟩ := by
 simp [finish,tryObs,bindObs]

theorem finish_events (n : Nat) (child : Obs (Except ProgramError Bytes)) :
 (finish n child).events = child.events := by
 cases child with
 | mk exit events =>
  cases exit with
  | abort => rfl
  | diverge => rfl
  | ret r => cases r <;> simp [finish,tryObs,bindObs]

/-- Full canonical328 packet at the actual site supplies the full suffix.
This is a SUFFIX fold; no whole345 candidate or full parent fold is claimed. -/
theorem suffix_packet (V : VLib) (P : PreparedNew V)
 (impl : TX1_328.Args V → Env → Obs (Except ProgramError Bytes))
 (child : TX1_328.RowSpec_328 V P impl) (a : TX1_328.Args V) (env : Env)
 (domain : TX1_328.Domain V a) (checkpointLength : Nat) :
 RS.bind (Spec.call (TX1_328.Domain V) (TX1_328.Ref V P) a)
  (fun bytes => RS.seq (RS.check (bytes.length != checkpointLength) .invalidAccountData) (RS.pure bytes))
  env (finish checkpointLength (impl a env)) := by
 apply try_valid _ _ _ _ env (first328_packet V P impl child a env domain)
 intro bytes
 cases h : (bytes.length != checkpointLength) <;>
  simp only [h,RS.check,Bool.false_eq_true,if_false,if_true,RS.seq_pure,RS.seq_throw] <;> rfl
#print axioms finish_abort
#print axioms finish_diverge
#print axioms finish_error
#print axioms finish_events
#print axioms suffix_packet
end NMT_345PostObservation
