import OraclePortCkptAbi2DriverObstruction

/-! Local obstruction after an arbitrary preceding batch. This keeps the
checkpoint between batches instead of incorrectly prepending it to TX1.
It does not assert that either parameterized caller is the frozen source. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCkptAbi4Interleaved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5
open OraclePortCkptAbi2DriverObstruction
attribute [local instance] Classical.propDecidable

theorem interleaved_length (H : Bytes → State) (stored pub : Bytes)
    (c : Context) (d : MatchingSupport.Data E) (rho : K)
    (q : Fin 22 → Fin 262144) (unique : Function.Injective q)
    (before : Program Bytes State Unit) (after : Program Bytes State Bool) :
    (eval H (bind before fun _ => checkpointThen stored pub c d rho q after)).1.length =
      (eval H before).1.length + 6 + (eval H after).1.length := by
  simp only [eval_bind,List.length_append,
    checkpointThen_length H stored pub c d rho q unique after]
  omega

/-- Even accepted observations differ when the checkpoint is inserted between
otherwise unchanged batches. Repeated digest addresses still count as reads. -/
theorem interleaved_not_erased (H : Bytes → State) (stored pub : Bytes)
    (c : Context) (d : MatchingSupport.Data E) (rho : K)
    (q : Fin 22 → Fin 262144) (unique : Function.Injective q)
    (before : Program Bytes State Unit) (after : Program Bytes State Bool) :
    eval H (bind before fun _ => checkpointThen stored pub c d rho q after) ≠
      eval H (bind before fun _ => after) := by
  intro same
  have lengths := congrArg (fun result => result.1.length) same
  rw [interleaved_length H stored pub c d rho q unique before after] at lengths
  simp only [eval_bind,List.length_append] at lengths
  omega

#print axioms interleaved_length
#print axioms interleaved_not_erased
end AspisR1.OraclePortCkptAbi4Interleaved
end
