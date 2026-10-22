import OraclePortCkptAbiReference

/-! A checkpoint cannot be erased from an ordered-read program. This is an
obstruction to that particular driver substitution, not a counterexample to
an as-yet-uninstantiated complete frozen source/model caller identity. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCkptAbi2DriverObstruction
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5

attribute [local instance] Classical.propDecidable

def checkpointThen (stored pub : Bytes) (c : Context) (d : MatchingSupport.Data E)
    (rho : K) (q : Fin 22 → Fin 262144) (tail : Program Bytes State Bool) :
    Program Bytes State Bool :=
  bind (OraclePortCkptAbiReference.writeResume stored pub c d rho q) fun result =>
    match result with
    | none => .done false
    | some _ => tail

/-- All six reads remain in the log, including repeated addresses. -/
theorem checkpointThen_length (H : Bytes → State) (stored pub : Bytes)
    (c : Context) (d : MatchingSupport.Data E) (rho : K)
    (q : Fin 22 → Fin 262144) (unique : Function.Injective q)
    (tail : Program Bytes State Bool) :
    (eval H (checkpointThen stored pub c d rho q tail)).1.length =
      6 + (eval H tail).1.length := by
  simp only [checkpointThen,eval_bind,OraclePortCkptAbiReference.writeResume_trace,
    if_pos unique,List.length_append,List.length_cons,List.length_nil]

/-- Successful resumption preserves the tail verdict; it does not erase reads. -/
theorem checkpointThen_verdict (H : Bytes → State) (stored pub : Bytes)
    (c : Context) (d : MatchingSupport.Data E) (rho : K)
    (q : Fin 22 → Fin 262144) (unique : Function.Injective q)
    (tail : Program Bytes State Bool) :
    (eval H (checkpointThen stored pub c d rho q tail)).2 = (eval H tail).2 := by
  simp only [checkpointThen,eval_bind,OraclePortCkptAbiReference.writeResume_trace,
    if_pos unique]

/-- Applies also to accepted tails: equality of verdicts is insufficient for
an AcceptedVerifierJoin, whose observation includes the complete ordered log. -/
theorem checkpointThen_not_erased (H : Bytes → State) (stored pub : Bytes)
    (c : Context) (d : MatchingSupport.Data E) (rho : K)
    (q : Fin 22 → Fin 262144) (unique : Function.Injective q)
    (tail : Program Bytes State Bool) :
    eval H (checkpointThen stored pub c d rho q tail) ≠ eval H tail := by
  intro same
  have lengths := congrArg (fun result => result.1.length) same
  rw [checkpointThen_length H stored pub c d rho q unique tail] at lengths
  omega

#print axioms checkpointThen_length
#print axioms checkpointThen_verdict
#print axioms checkpointThen_not_erased
end AspisR1.OraclePortCkptAbi2DriverObstruction
end
